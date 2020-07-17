-module(better_assert).

-export([assert/2, refute/2, match/1, equal/2, parse_transform/2]).

-define(call(A, M, F, As), 
    {call, A, {remote, A, {atom, A, M}, {atom, A, F}}, As}
).

-define(key(A, K, V), {map_field_assoc, A, {atom, A, K}, V}).

-define(string(A, Expr), {string, A, unicode:characters_to_list(Expr)}).

assert(Value, Message) when is_list(Message) ->
    assert(Value, #{message => Message});
assert(Value, Details) when is_map(Details) ->
    case Value of
        true -> true;
        _ -> error({badassert, Details})
    end.

refute(Value, Message) when is_list(Message) ->
    refute(Value, #{message => Message});
refute(Value, Details) when is_map(Details) ->
    case Value of
        false -> false;
        _ -> error({badassert, Details})
    end.

match(Value) -> Value.

equal(Left, Right) -> Left =:= Right.

parse_transform(Forms0, _Options) ->
    put(gen_sym, 0),
    try ba_map_call_transform:transform(Forms0, {better_assert, '$marker', 2}, fun process_call/1)
    after erase(gen_sym)
    end.

process_call({call, Anno0, _, [{atom, _, Kind}, Expr]}) ->
    Anno = erl_anno:set_generated(true, Anno0),
    process_assertion(Anno, Kind, Expr).

process_assertion(Anno, Kind, {op, _, _, _, _} = Expr) ->
    process_operator(Anno, Kind, Expr);
process_assertion(Anno, Kind, {match, _MAnno,  Pattern, Expr}) ->
    process_match(Anno, Kind, Expr, Pattern, []);
process_assertion(Anno, Kind, ?call(_, ?MODULE, match, [Case])) ->
    {'case', _, Expr, [{clause, _, [Pattern], Guards, [_]}, _]} = Case,
    process_match(Anno, Kind, Expr, Pattern, Guards);
process_assertion(Anno, Kind, Expr) ->
    Value = gen_var(Anno, value),

    ErrorInfo = {map, Anno, [
        ?key(Anno, value, Value),
        ?key(Anno, expr, ?string(Anno, print_code(Kind, Expr))),
        ?key(Anno, message, ?string(Anno, message(Kind, Expr)))
    ]},

    {block, Anno, [
        {match, Anno, Value, Expr},
        ?call(Anno, ?MODULE, Kind, [Value, ErrorInfo])
    ]}.

process_match(Anno, Kind, Expr, Pattern0, Guards0) ->
    Value = gen_var(Anno, value),
    {Pattern, VarSubs} = extract_pattern_vars(Pattern0, #{}),
    Guards = rewrite_guards(Guards, VarSubs),
    TmpVars = [{var, Anno, Var} || Var <- map:values(VarSubs)],
    Vars = [{var, Anno, Var} || Var <- map:keys(VarSubs)],

    ErrorInfo = {map, Anno, [
        ?key(Anno, value, Value),
        ?key(Anno, expr, ?string(Anno, print_match(Kind, Expr, Pattern, Guards))),
        ?key(Anno, pattern, erl_parse:abstract(Pattern)),
        ?key(Anno, guards, erl_parse:abstract(Guards)),
        ?key(Anno, message, ?string(Anno, message(Kind, match)))
    ]},

    {block, Anno, [
        {match, Anno, Value, Expr},
        case Kind of    
            assert ->
                {match, Anno, {tuple, Anno, Vars}, 
                    {'case', Anno, Value, [
                        {clause, Anno, [Pattern], Guards, [{tuple, Anno, TmpVars}]},
                        {clause, Anno, [{var, Anno, '_'}], [], [
                            ?call(Anno, ?MODULE, assert, [{atom, Anno, false}, ErrorInfo])
                        ]}
                    ]}};
            refute ->
                {'case', Anno, Value, [
                    {clause, Anno, [Pattern], Guards, [
                        ?call(Anno, ?MODULE, refute, [{atom, Anno, true}, ErrorInfo])
                    ]},
                    {clause, Anno, [{var, Anno, '_'}], [], [Value]}
                ]}
        end
    ]}.

process_operator(Anno, Kind, {op, OpAnno, Op, LeftExpr, RightExpr} = Expr) ->
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
        {match, Anno, Left, LeftExpr},
        {match, Anno, Right, RightExpr},
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