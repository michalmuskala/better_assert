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
    better_assert:'$marker_assert_match'(
        case (Value) of
            Pattern -> true
        end
    )
).

-define(assertMatch(Pattern, Value, Message),
    better_assert:'$marker_assert_match'(
        Message,
        case (Value) of
            Pattern -> true
        end
    )
).


-define(refuteMatch(Pattern, Value),
    better_assert:'$marker_refute_match'(
        case (Value) of
            Guard -> false
        end
    )
).

-define(refuteMatch(Pattern, Value, Message),
    better_assert:'$marker_refute_match'(
        Message
        case (Value) of
            Guard -> false
        end
    )
).

-define(assertReceive(Pattern),
    better_assert:'$marker_receive'(
        assert,
        receive
            Pattern -> true
        end
    )
).

-define(assertReceive(Pattern, Timeout),
    better_assert:'$marker_receive'(
        assert,
        receive
            Pattern -> true
        after Timeout -> false
        end
    )
).

-define(assertReceive(Pattern, Timeout, Message),
    better_assert:'$marker_receive'(
        assert,
        Message,
        receive
            Pattern -> true
        after Timeout -> false
        end
    )
).

-define(assertReceived(Pattern),
    better_assert:'$marker_receive'(
        assert,
        receive
            Pattern -> true
        after 0 -> false
        end
    )
).

-define(assertReceived(Pattern, Message),
    better_assert:'$marker_receive'(
        assert,
        Message
        receive
            Pattern -> true
        after 0 -> false
        end
    )
).

-define(refuteReceive(Pattern),
    better_assert:'$marker_receive'(
        refute,
        receive
            Pattern -> false
        end
    )
).

-define(refuteReceive(Pattern, Timeout),
    better_assert:'$marker_receive'(
        refute,
        receive
            Pattern -> false
        after Timeout -> true
        end
    )
).

-define(refuteReceive(Pattern, Timeout, Message),
    better_assert:'$marker_receive'(
        refute,
        Message,
        receive
            Pattern -> false
        after Timeout -> true
        end
    )
).

-define(refuteReceived(Pattern),
    better_assert:'$marker_receive'(
        refute,
        receive
            Pattern -> false
        after 0 -> true
        end
    )
).

-define(refuteReceived(Pattern, Message),
    better_assert:'$marker_receive'(
        refute,
        Message
        receive
            Pattern -> false
        after 0 -> true
        end
    )
).

-endif.
