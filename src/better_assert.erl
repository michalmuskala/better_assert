-module(better_assert).

-export([assert/2, refute/2, match/1, equal/2, parse_transform/2, format_error/1]).

-define(call(A, M, F, As),
    {call, A, {remote, A, {atom, A, M}, {atom, A, F}}, As}
).

-define(key(A, K, V), {map_field_assoc, A, {atom, A, K}, V}).

-define(string(A, Expr), {string, A, unicode:characters_to_list(Expr)}).

assert(Value, Details) when is_map(Details) ->
    case Value of
        true -> true;
        _ -> error({badassert, Details})
    end.

refute(Value, Details) when is_map(Details) ->
    case Value of
        false -> false;
        _ -> error({badassert, Details})
    end.

match(Value) -> Value.

equal(Left, Right) -> Left =:= Right.

parse_transform(Forms, _Options) ->
    put(gen_sym, 0),
    try [transform_form(Form) || Form <- Forms]
    after erase(gen_sym)
    end.

format_error({assert_match, Expr}) ->
    "invalid expression for ?assertMatch: " ++ erl_prettypr:format(Expr).

transform_form(Form) ->
    case erl_syntax:type(Form) of
        function ->
            Annotated = erl_syntax_lib:annotate_bindings(Form, ordsets:new()),
            try erl_syntax:revert(erl_syntax_lib:map(fun transform_expr/1, Annotated))
            catch
                {error_marker, Line, Reason} -> {error, {erl_anno:location(Line), ?MODULE, Reason}}
            end;
        _ ->
            Form
    end.

transform_expr(Expr) ->
    try erl_syntax_lib:analyze_application(Expr) of
        {?MODULE, {'$marker', 2}} ->
            process_assertion(erl_syntax:get_pos(Expr), erl_syntax:application_arguments(Expr));
        {?MODULE, {'$marker_assert_match', A}} when A =:= 1; A =:= 2 ->
            process_assert_match(erl_syntax:get_pos(Expr), erl_syntax:application_arguments(Expr));
        {?MODULE, {'$marker_refute_match', A}} when A =:= 1; A =:= 2 ->
            process_refute_match(erl_syntax:get_pos(Expr), erl_syntax:application_arguments(Expr));
        {?MODULE, {'$marker_receive', A}} when A =:= 2; A =:= 3 ->
            process_receive_assertion(erl_syntax:get_pos(Expr), erl_syntax:application_arguments(Expr));
        _ -> Expr
    catch
        syntax_error -> Expr
    end.

process_assertion(Anno0, [Atom, Expr]) ->
    Anno = erl_anno:set_generated(true, Anno0),
    Kind = erl_syntax:atom_value(Atom),
    case erl_syntax:type(Expr) of
        infix_expr ->
            Op = erl_syntax:operator_name(erl_syntax:infix_expr_operator(Expr)),
            OpAnno = erl_syntax:get_pos(Expr),
            Left = erl_syntax:infix_expr_left(Expr),
            Right = erl_syntax:infix_expr_right(Expr),
            process_operator(Anno, Kind, Op, OpAnno, Left, Right, Expr);
        _ ->
            process_other(Anno, Kind, Expr)
    end.

process_assert_match(Anno0, Args) ->
    {Expr, Pattern0, Guards0, Message} = decompose_match_args(Anno0, Args),
    Anno = erl_anno:set_generated(true, Anno0),
    Value = gen_var(Anno, value),
    Attrs = erl_syntax:get_ann(Pattern0),

    ErrorInfo =
        case Message of
            default ->
                match_default_message(Anno, Attrs, Value, Expr, Pattern0, Guards0);
            {custom, Custom} ->
                {map, Anno, [
                    ?key(Anno, message, erl_syntax:revert(Custom))
                ]}
        end,

    {bound, Bound} = lists:keyfind(bound, 1, Attrs),
    BoundVars = [{var, Anno, Name} || Name <- Bound],
    TmpVars = [gen_var(Anno, tmp) || _ <- Bound],
    Subs = maps:from_list(lists:zip(Bound, TmpVars)),
    Pattern = rewrite_vars(Pattern0, Subs),
    Guards = rewrite_vars(Guards0, Subs),

    {block, Anno, [
        {match, Anno, Value, erl_syntax:revert(Expr)},
        {match, Anno, {tuple, Anno, BoundVars},
            {'case', Anno, Value, [
                {clause, Anno, [Pattern], Guards, [{tuple, Anno, TmpVars}]},
                {clause, Anno, [{var, Anno, '_'}], [], [
                    ?call(Anno, ?MODULE, assert, [{atom, Anno, false}, ErrorInfo])
                ]}
            ]}},
        Value
    ]}.

process_refute_match(Anno0, Args) ->
    {Expr, Pattern, Guards, Message} = decompose_match_args(Anno0, Args),
    Anno = erl_anno:set_generated(true, Anno0),
    Value = gen_var(Anno, value),

    ErrorInfo =
        case Message of
            default ->
                Attrs = erl_syntax:get_ann(Pattern),
                match_default_message(Anno, Attrs, Value, Expr, Pattern, Guards);
            {custom, Custom} ->
                {map, Anno, [
                    ?key(Anno, message, erl_syntax:revert(Custom))
                ]}
        end,

    {block, Anno, [
        {match, Anno, Value, erl_syntax:revert(Expr)},
        {'case', Anno, Value, [
            {clause, Anno, [erl_syntax:revert(Pattern)], revert(Guards), [
                ?call(Anno, ?MODULE, refute, [{atom, Anno, true}, ErrorInfo])
            ]},
            {clause, Anno, [{var, Anno, '_'}], [], [Value]}
        ]}
    ]}.


match_default_message(Anno, Attrs, Value, Expr, Pattern, Guards) ->
    {free, Pins} = lists:keyfind(free, 1, Attrs),
    {map, Anno, [
        ?key(Anno, value, Value),
        ?key(Anno, pins, {map, Anno, [?key(Anno, Name, {var, Anno, Name}) || Name <- Pins]}),
        ?key(Anno, expr, ?string(Anno, print_match(assert, Expr, Pattern, Guards))),
        ?key(Anno, pattern, erl_parse:abstract(erl_syntax:revert(Pattern))),
        ?key(Anno, guards, erl_parse:abstract(revert(Guards))),
        ?key(Anno, message, ?string(Anno, message(assert, match)))
    ]}.

decompose_match_args(Anno, [Expr]) ->
    decompose_match_args(Anno, Expr, default);
decompose_match_args(Anno, [Message, Expr]) ->
    decompose_match_args(Anno, Expr, {custom, Message}).

decompose_match_args(Anno, Expr, Message) ->
    case erl_syntax:type(Expr) of
        match_expr ->
            Body = erl_syntax:match_expr_body(Expr),
            Pattern = erl_syntax:match_expr_pattern(Expr),
            {Body, Pattern, none, Message};
        case_expr ->
            Body = erl_syntax:case_expr_argument(Expr),
            [Clause] = erl_syntax:case_expr_clauses(Expr),
            Guards = erl_syntax:clause_guard(Clause),
            [Pattern] = erl_syntax:clause_patterns(Clause),
            {Body, Pattern, Guards, Message};
        _ ->
            throw({error_marker, Anno, {assert_match, Expr}})
    end.

process_receive_assertion(Anno0, [Atom, Receive]) ->
    Anno = erl_anno:set_generated(true, Anno0),
    Kind = erl_syntax:atom_value(Atom),
    process_receive(Anno, Kind, Receive, default);
process_receive_assertion(Anno0, [Atom, Message, Receive]) ->
    Anno = erl_anno:set_generated(true, Anno0),
    Kind = erl_syntax:atom_value(Atom),
    process_receive(Anno, Kind, Receive, {custom, Message}).

process_other(Anno, Kind, Expr) ->
    Value = gen_var(Anno, value),

    ErrorInfo = {map, Anno, [
        ?key(Anno, value, Value),
        ?key(Anno, expr, ?string(Anno, print_assert(Kind, Expr))),
        ?key(Anno, message, ?string(Anno, message(Kind, Expr)))
    ]},

    {block, Anno, [
        {match, Anno, Value, erl_syntax:revert(Expr)},
        ?call(Anno, ?MODULE, Kind, [Value, ErrorInfo])
    ]}.

rewrite_vars(none, _Subs) ->
    [];
rewrite_vars(Tree, Subs) ->
    Rewrite = fun (Expr) ->
        case erl_syntax:type(Expr) of
            variable -> maps:get(erl_syntax:variable_name(Expr), Subs, Expr);
            _ -> Expr
        end
    end,
    revert(erl_syntax_lib:map(Rewrite, Tree)).

%% erl_syntax:revert/1 does not revert "guard" nodes, need to do that manually
revert(none) ->
    [];
revert(Expr) ->
    Reverted = erl_syntax:revert(Expr),
    case erl_syntax:is_tree(Reverted) of
        true ->
            [erl_syntax:conjunction_body(Node) || Node <- erl_syntax:disjunction_body(Reverted)];
        false ->
            Reverted
    end.

process_receive(Anno, Kind, Receive, Message) ->
    TimeoutVar = gen_var(Anno, timeout),

    Timeout0 = erl_syntax:revert(erl_syntax:receive_expr_timeout(Receive)),
    TimeoutExpr = receive_default_timeout(Anno, Timeout0),
    [Clause] = erl_syntax:receive_expr_clauses(Receive),
    Guards0 = erl_syntax:clause_guard(Clause),
    [Pattern0] = erl_syntax:clause_patterns(Clause),

    Attrs = erl_syntax:get_ann(Pattern0),
    {free, Pins} = lists:keyfind(free, 1, Attrs),

    ErrorInfo =
        case Message of
            default ->
                {map, Anno, [
                    ?key(Anno, pins, {map, Anno, [?key(Anno, Name, {var, Anno, Name}) || Name <- Pins]}),
                    ?key(Anno, expr, ?string(Anno, print_receive(Kind, Pattern0, Guards0, Timeout0))),
                    ?key(Anno, pattern, erl_parse:abstract(erl_syntax:revert(Pattern0))),
                    ?key(Anno, guards, erl_parse:abstract(revert(Guards0))),
                    ?key(Anno, timeout, TimeoutVar),
                    ?key(Anno, message, ?string(Anno, message(Kind, 'receive')))
                ]};
            {custom, Custom} ->
                {map, Anno, [
                    ?key(Anno, message, erl_syntax:revert(Custom))
                ]}
        end,

    {block, Anno, [
        {match, Anno, {tuple, Anno, [{atom, Anno, ok}, TimeoutVar]}, TimeoutExpr},
        case Kind of
            assert ->
                {bound, Bound} = lists:keyfind(bound, 1, Attrs),
                BoundVars = [{var, Anno, Name} || Name <- Bound],
                TmpVars = [gen_var(Anno, tmp) || _ <- Bound],
                Subs = maps:from_list(lists:zip(Bound, TmpVars)),
                Pattern = rewrite_vars(Pattern0, Subs),
                Guards = rewrite_vars(Guards0, Subs),

                NewClause = {clause, Anno, [Pattern], Guards, [{tuple, Anno, TmpVars}]},
                After = ?call(Anno, ?MODULE, assert, [{atom, Anno, false}, ErrorInfo]),

                % TODO: make whole expression evaluate to received message
                {match, Anno, {tuple, Anno, BoundVars},
                    {'receive', Anno, [NewClause], TimeoutVar, [After]}};
            refute ->
                NewClause = {clause, Anno, [erl_syntax:revert(Pattern0)], revert(Guards0), [
                    ?call(Anno, ?MODULE, refute, [{atom, Anno, true}, ErrorInfo])
                ]},
                {'receive', Anno, [NewClause], TimeoutVar, [{atom, Anno, false}]}
        end
    ]}.

process_operator(Anno, Kind, Op, OpAnno, LeftExpr, RightExpr, Expr) ->
    Left = gen_var(Anno, left),
    Right = gen_var(Anno, right),
    Call = {op, OpAnno, Op, Left, Right},
    Message = message(Kind, Expr),
    ExprString = ?string(Anno, print_assert(Kind, Expr)),

    ErrorInfo = {map, Anno, [
        ?key(Anno, left, Left),
        ?key(Anno, right, Right),
        ?key(Anno, expr, ExprString),
        ?key(Anno, message, ?string(Anno, Message))
    ]},

    {block, Anno, [
        {match, Anno, Left, erl_syntax:revert(LeftExpr)},
        {match, Anno, Right, erl_syntax:revert(RightExpr)},
        case include_equality_check(Kind, Op) of
            true ->
                EqMessage = ?string(Anno, [Message, ", both sides are exactly equal"]),
                EqErrorInfo = {map, Anno, [
                    ?key(Anno, value, Left),
                    ?key(Anno, expr, ExprString),
                    ?key(Anno, message, EqMessage)
                ]},

                {'case', Anno, ?call(Anno, ?MODULE, equal, [Left, Right]), [
                    {clause, Anno, [{atom, Anno, true}], [], [
                        ?call(Anno, ?MODULE, assert, [{atom, Anno, false}, EqErrorInfo])
                    ]},
                    {clause, Anno, [{var, Anno, '_'}], [], [
                        ?call(Anno, ?MODULE, Kind, [Call, ErrorInfo])
                    ]}
                ]};
            false ->
                ?call(Anno, ?MODULE, Kind, [Call, ErrorInfo])
        end
    ]}.

message(assert, {op, _, Op, _, _}) -> ["Assertion with ", atom_to_list(Op), " failed"];
message(refute, {op, _, Op, _, _}) -> ["Refute with ", atom_to_list(Op), " failed"];
message(assert, 'receive') -> "Assertion failed, no matching message received";
message(refute, 'receive') -> "Refute failed, unexpectedly received a matching message";
message(assert, match) -> "Match failed";
message(refute, match) -> "Match succeeded, but should have failed";
message(assert, _Expr) -> "Assertion failed";
message(refute, _Expr) -> "Refute failed".

receive_default_timeout(Anno, none) ->
    % TODO: for CT scale the timeout with the CT scale setting
    Args = [{atom, Anno, better_assert}, {atom, Anno, receive_timeout}],
    ?call(Anno, application, get_env, Args);
receive_default_timeout(Anno, Expr) ->
    {tuple, Anno, [{atom, Anno, ok}, Expr]}.

include_equality_check(assert, Op) ->
    lists:member(Op, ['>', '>', '=/=', '/=']);
include_equality_check(refute, Op) ->
    lists:member(Op, ['=<', '>=', '=:=', '==']).

print_assert(Kind, Expr) ->
    ["?", atom_to_list(Kind), "(", erl_prettypr:format(Expr) ,")"].

print_match(Kind, Expr, Pattern, none) ->
    ["?", atom_to_list(Kind), "Match(", erl_prettypr:format(Pattern), " = ", erl_prettypr:format(Expr), ")"];
print_match(Kind, Expr, Pattern, Guards) ->
    ["?", atom_to_list(Kind), "Match(", erl_prettypr:format(Pattern), " when ", erl_prettypr:format(Guards), ", ", erl_prettypr:format(Expr), ")"].

print_receive(Kind, Pattern, none, none) ->
    ["?", atom_to_list(Kind), "Receive(", erl_prettypr:format(Pattern), ")"];
print_receive(Kind, Pattern, Guards, none) ->
    ["?", atom_to_list(Kind), "Receive(", erl_prettypr:format(Pattern), " when ", erl_prettypr:format(Guards), ")"];
print_receive(Kind, Pattern, none, {integer, _, 0}) ->
    ["?", atom_to_list(Kind), "Received(", erl_prettypr:format(Pattern), ")"];
print_receive(Kind, Pattern, Guards, {integer, _, 0}) ->
    ["?", atom_to_list(Kind), "Received(", erl_prettypr:format(Pattern), " when ", erl_prettypr:format(Guards), ")"];
print_receive(Kind, Pattern, none, Timeout) ->
    ["?", atom_to_list(Kind), "Received(", erl_prettypr:format(Pattern), ", ", erl_prettypr:format(Timeout), ")"];
print_receive(Kind, Pattern, Guards, Timeout) ->
    ["?", atom_to_list(Kind), "Received(", erl_prettypr:format(Pattern), " when ", erl_prettypr:format(Guards), ", ", erl_prettypr:format(Timeout), ")"].

gen_var(Anno, Name) ->
    Num = get(gen_sym),
    put(gen_sym, Num + 1),
    {var, Anno, list_to_atom("_" ++ atom_to_list(Name) ++ "@" ++ integer_to_list(Num))}.
