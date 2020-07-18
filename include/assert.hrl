-ifndef(BETTER_ASSERT_HRL).
-define(BETTER_ASSERT_HRL, true).

-compile({parse_transform, better_assert}).

-define(assert(Expr), better_assert:'$marker'(assert, Expr)).
-define(assert(Expr, Message), better_assert:assert(Expr, #{message => Message})).
-define(refute(Expr), better_assert:'$marker'(refute, Expr)).
-define(refute(Expr, Message), better_assert:refute(Expr, #{message => Message})).

-define(assertMatch(Expr), better_assert:'$marker_match'(assert, Expr)).
-define(refuteMatch(Expr), better_assert:'$marker_match'(refute, Expr)).

-define(assertMatch(Pattern, Value),
    better_assert:'$marker_match'(
        assert,
        case (Value) of
            Guard -> true
        end
    )
).


-define(refuteMatch(Pattern, Value),
    better_assert:'$marker_match'(
        refute,
        case (Value) of
            Guard -> false
        end
    )
).


-endif.
