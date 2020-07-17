-ifndef(BETTER_ASSERT_HRL).
-define(BETTER_ASSERT_HRL, true).

-compile({parse_transform, better_assert}).

-define(assert(Expr), better_assert:'$marker'(assert, Expr)).
-define(assert(Expr, Message), better_assert:assert(Expr, #{message => Message})).
-define(refute(Expr), better_assert:'$marker'(refute, Expr)).
-define(refute(Expr, Message), not better_assert:assert(not (Expr), #{message => Message})).

-define(match(Guard, Value),
    better_assert:match(
        case (Value) of
            Guard -> true;
            _ -> false
        end
    )
).

-endif.