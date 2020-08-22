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
        {?MODULE, {'$marker_match', A}} when A =:= 2; A =:= 3 ->
            process_match_assertion(erl_syntax:get_pos(Expr), erl_syntax:application_arguments(Expr));
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

process_match_assertion(Anno0, [Atom, Expr]) ->
    Anno = erl_anno:set_generated(true, Anno0),
    Kind = erl_syntax:atom_value(Atom),
    process_match_assertion(Anno, Kind, Expr, default);
process_match_assertion(Anno0, [Atom, Message, Expr]) ->
    Anno = erl_anno:set_generated(true, Anno0),
    Kind = erl_syntax:atom_value(Atom),
    process_match_assertion(Anno, Kind, Expr, {custom, Message}).

process_match_assertion(Anno, Kind, Expr, Message) ->
    case erl_syntax:type(Expr) of
        match_expr ->
            Body = erl_syntax:match_expr_body(Expr),
            Pattern = erl_syntax:match_expr_pattern(Expr),
            process_match(Anno, Kind, Body, Pattern, none, Message);
        case_expr ->
            Body = erl_syntax:case_expr_argument(Expr),
            [Clause] = erl_syntax:case_expr_clauses(Expr),
            Guards = erl_syntax:clause_guard(Clause),
            [Pattern] = erl_syntax:clause_patterns(Clause),
            process_match(Anno, Kind, Body, Pattern, Guards, Message);
        _ ->
            throw({error_marker, Anno, {assert_match, Expr}})
    end.

process_receive_assertion(Anno0, [Atom, Receive]) ->
    Anno = erl_anno:set_generated(true, Anno0),
    Kind = erl_syntax:atom_value(Atom),
    proces_receive(Anno, Kind, Receive, default);
process_receive_assertion(Anno0, [Atom, Message, Receive]) ->
    Anno = erl_anno:set_generated(true, Anno0),
    Kind = erl_syntax:atom_value(Atom),
    process_receive(Anno, Kind, Receive, {custom, Message}).

process_other(Anno, Kind, Expr) ->
    Value = gen_var(Anno, value),

    ErrorInfo = {map, Anno, [
        ?key(Anno, value, Value),
        ?key(Anno, expr, ?string(Anno, print_code(Kind, Expr))),
        ?key(Anno, message, ?string(Anno, message(Kind, Expr)))
    ]},

    {block, Anno, [
        {match, Anno, Value, erl_syntax:revert(Expr)},
        ?call(Anno, ?MODULE, Kind, [Value, ErrorInfo])
    ]}.

process_match(Anno, Kind, Expr, Pattern0, Guards0, Message) ->
    Value = gen_var(Anno, value),
    Attrs = erl_syntax:get_ann(Pattern0),
    {free, Pins} = lists:keyfind(free, 1, Attrs),

    ErrorInfo =
        case Message of
            default ->
                {map, Anno, [
                    ?key(Anno, value, Value),
                    ?key(Anno, pins, {map, Anno, [?key(Anno, Name, {var, Anno, Name}) || Name <- Pins]}),
                    ?key(Anno, expr, ?string(Anno, print_match(Kind, Expr, Pattern0, Guards0))),
                    ?key(Anno, pattern, erl_parse:abstract(erl_syntax:revert(Pattern0))),
                    ?key(Anno, guards, erl_parse:abstract(revert(Guards0))),
                    ?key(Anno, message, ?string(Anno, message(Kind, match)))
                ]};
            {custom, Custom} ->
                {map, Anno, [
                    ?key(Anno, message, erl_syntax:revert(Custom))
                ]}
        end,

    {block, Anno, [
        {match, Anno, Value, erl_syntax:revert(Expr)},
        case Kind of
            assert ->
                {bound, Bound} = lists:keyfind(bound, 1, Attrs),
                BoundVars = [{var, Anno, Name} || Name <- Bound],
                TmpVars = [gen_var(Anno, tmp) || _ <- Bound],
                Subs = maps:from_list(lists:zip(Bound, TmpVars)),
                Pattern = rewrite_vars(Pattern0, Subs),
                Guards = rewrite_vars(Guards0, Subs),

                {match, Anno, {tuple, Anno, BoundVars},
                    {'case', Anno, Value, [
                        {clause, Anno, [Pattern], Guards, [{tuple, Anno, TmpVars}]},
                        {clause, Anno, [{var, Anno, '_'}], [], [
                            ?call(Anno, ?MODULE, assert, [{atom, Anno, false}, ErrorInfo])
                        ]}
                    ]}};
            refute ->
                {'case', Anno, Value, [
                    {clause, Anno, [erl_syntax:revert(Pattern0)], revert(Guards0), [
                        ?call(Anno, ?MODULE, refute, [{atom, Anno, true}, ErrorInfo])
                    ]},
                    {clause, Anno, [{var, Anno, '_'}], [], [Value]}
                ]}
        end
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
revert(Expr) ->
    Reverted = erl_syntax:revert(Expr),
    case erl_syntax:is_tree(Reverted) of
        true ->
            [erl_syntax:conjunction_body(Node) || Node <- erl_syntax:disjunction_body(Reverted)];
        false ->
            Reverted
    end.

process_receive(Anno, Kind, Receive, Message) ->
    Value = gen_var(Anno, value),
    Attrs = erl_syntax:get_ann(Pattern0),
    {free, Pins} = lists:keyfind(free, 1, Attrs),

    Timeout = receive_default_timeout(Receive),
    [Clause] = erl_syntax:receive_expr_clauses(Receive),
    Guards = erl_syntax:clause_guard(Clause),
    [Pattern] = erl_syntax:clause_patterns(Clause),

    ErrorInfo =
        case Message of
            default ->
                {map, Anno, [
                    ?key(Anno, value, Value),
                    ?key(Anno, pins, {map, Anno, [?key(Anno, Name, {var, Anno, Name}) || Name <- Pins]}),
                    ?key(Anno, expr, ?string(Anno, print_match(Kind, Expr, Pattern0, Guards0))),
                    ?key(Anno, pattern, erl_parse:abstract(erl_syntax:revert(Pattern0))),
                    ?key(Anno, guards, erl_parse:abstract(revert(Guards0))),
                    ?key(Anno, message, ?string(Anno, message(Kind, match)))
                ]};
            {custom, Custom} ->
                {map, Anno, [
                    ?key(Anno, message, erl_syntax:revert(Custom))
                ]}
        end,



process_operator(Anno, Kind, Op, OpAnno, LeftExpr, RightExpr, Expr) ->
    Left = gen_var(Anno, left),
    Right = gen_var(Anno, right),
    Call = {op, OpAnno, Op, Left, Right},
    Message = message(Kind, Expr),
    ExprString = ?string(Anno, print_code(Kind, Expr)),

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
message(assert, match) -> "Match failed";
message(refute, match) -> "Match succeeded, but should have failed";
message(assert, _Expr) -> "Assertion failed";
message(refute, _Expr) -> "Refute failed".

receive_default_timeout(Receive) ->
    case erl_syntax:receive_expr_timeout(Receive) of
        none -> erl_syntax:abstract(application:get_env(better_assert, default_timeout));
        Other -> Other
    end.

include_equality_check(assert, Op) ->
    lists:member(Op, ['>', '>', '=/=', '/=']);
include_equality_check(refute, Op) ->
    lists:member(Op, ['=<', '>=', '=:=', '==']).

print_code(Kind, Expr) ->
    ["?", atom_to_list(Kind), "(", erl_prettypr:format(Expr) ,")"].

print_match(Kind, Expr, Pattern, none) ->
    ["?", atom_to_list(Kind), "Match(", erl_prettypr:format(Pattern), " = ", erl_prettypr:format(Expr), ")"];
print_match(Kind, Expr, Pattern, Guards) ->
    ["?", atom_to_list(Kind), "Match(", erl_prettypr:format(Pattern), " when ", erl_prettypr:format(Guards), ", ", erl_prettypr:format(Expr), ")"].

gen_var(Anno, Name) ->
    Num = get(gen_sym),
    put(gen_sym, Num + 1),
    {var, Anno, list_to_atom("_" ++ atom_to_list(Name) ++ "@" ++ integer_to_list(Num))}.
