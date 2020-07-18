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
        {?MODULE, {'$marker_match', 2}} ->
            process_match_assertion(erl_syntax:get_pos(Expr), erl_syntax:application_arguments(Expr));
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
    case erl_syntax:type(Expr) of
        match_expr ->
            Body = erl_syntax:match_expr_body(Expr),
            Pattern = erl_syntax:match_expr_pattern(Expr),
            process_match(Anno, Kind, Body, Pattern, []);
        case_expr ->
            [Case] = erl_syntax:application_arguments(Expr),
            Body = erl_syntax:case_expr_argument(Case),
            [Clause] = erl_syntax:case_expr_clauses(Case),
            Guards = erl_syntax:clause_guard(Clause),
            [Pattern] = erl_synax:clause_patterns(Clause),
            process_match(Anno, Kind, Body, Pattern, Guards);
        _ ->
            throw({error_marker, Anno, {assert_match, Expr}})
    end.

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

process_match(Anno, Kind, Expr, Pattern0, Guards0) ->
    Value = gen_var(Anno, value),
    Attrs = erl_syntax:get_ann(Pattern0),
    {free, Pins} = lists:keyfind(free, 1, Attrs),

    ErrorInfo = {map, Anno, [
        ?key(Anno, value, Value),
        ?key(Anno, pins, {map, Anno, [?key(Anno, Name, {var, Anno, Name}) || Name <- Pins]}),
        ?key(Anno, expr, ?string(Anno, print_match(Kind, Expr, Pattern0, Guards0))),
        ?key(Anno, pattern, erl_parse:abstract(erl_syntax:revert(Pattern0))),
        ?key(Anno, guards, erl_parse:abstract(erl_syntax:revert(Guards0))),
        ?key(Anno, message, ?string(Anno, message(Kind, match)))
    ]},

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
                    {clause, Anno, [Pattern0], Guards0, [
                        ?call(Anno, ?MODULE, refute, [{atom, Anno, true}, ErrorInfo])
                    ]},
                    {clause, Anno, [{var, Anno, '_'}], [], [Value]}
                ]}
        end
    ]}.

rewrite_vars([], _Subs) ->
    [];
rewrite_vars(Tree, Subs) ->
    Rewrite = fun (Expr) ->
        case erl_syntax:type(Expr) of
            variable -> maps:get(erl_syntax:variable_name(Expr), Subs, Expr);
            _ -> Expr
        end
    end,
    erl_syntax:revert(erl_syntax_lib:map(Rewrite, Tree)).

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

include_equality_check(assert, Op) ->
    lists:member(Op, ['>', '>', '=/=', '/=']);
include_equality_check(refute, Op) ->
    lists:member(Op, ['=<', '>=', '=:=', '==']).

print_code(Kind, Expr) ->
    ["?", atom_to_list(Kind), "(", erl_prettypr:format(Expr) ,")"].

print_match(Kind, Expr, Pattern, []) ->
    ["?", atom_to_list(Kind), "(", erl_prettypr:format(Pattern), " = ", erl_prettypr:format(Expr), ")"];
print_match(Kind, Expr, Pattern, Guards) ->
    GuardsTree = erl_syntax:disjunction([erl_syntax:conjunction(Exprs) || Exprs <- Guards]),
    ["?", atom_to_list(Kind), "(?match(", erl_prettypr:format(Pattern), " when ", erl_prettypr:format(GuardsTree), ", ", erl_prettypr:format(Expr), "))"].

gen_var(Anno, Name) ->
    Num = get(gen_sym),
    put(gen_sym, Num + 1),
    {var, Anno, list_to_atom("_" ++ atom_to_list(Name) ++ "@" ++ integer_to_list(Num))}.
