:- op(600, yfx, '@').  % Function application
:- op(650, xfy, '=>'). % Type variable introduction
:- op(1150, fx, mode).

/*
The `inference` predicate makes a distinction between Inference Variables and
Generic Variables.

An Inference Variable is one that needs to be solved in to give a type to the
term. All Inference Variables should be gone by the time type inference is done.
If any unbound Inference Variables are left after type inference, this is a type
error. The user should annotate the term so that the type can be inferred
(Though I'm not sure this is possible).

Generic Variables are variables that are generalized. Like in Rust, the
function `fn identity<T>(x: T) -> T { x }` would be inferred to have type
`T -> T` where `T` is a Generic Variable. This is in contrast to the lambda
function in the expression `(|x| x)(123)` which has type `T -> T` but with `T`
being a temporary Inference Variable (even though the entire expression ends
up having type `nat`).
*/

:- mode inference(+_TypeContext, +_Term, -_GenericVariables, -_Type).

inference(_Tcx, N, [], nat) :- integer(N), N >= 0.

inference(_Tcx, true,  [], bool).
inference(_Tcx, false, [], bool).

inference(Tcx, pair(A, B), Vs, pair(ATy, BTy)) :-
    inference(Tcx, A, AVs, ATy),
    inference(Tcx, B, BVs, BTy),
    term_variables(AVs-BVs, Vs). % The poor man's set union.

inference(Tcx, X, Vs, Ty) :-
    atom(X),
    member(X:forall(Vs, Ty), Tcx).

inference(Tcx, X->B, Vs, XTy->BTy) :-
    atom(X),
    % Function parameters are not allowed to have generic types. For example
    % this is not allowed:
    % `fn thing(x: for<T> (T, T)) -> int`
    HypotheticalTcx = [X:forall([], XTy) | Tcx],
    inference(HypotheticalTcx, B, Vs, BTy).

inference(Tcx, let(X, E, B), BVs, BTy) :-
    atom(X),
    inference(Tcx, E, _, ETy),
    term_variables(ETy, EVs),
    inference([X:forall(EVs, ETy) | Tcx], B, BVs, BTy).

inference(Tcx, Fn@Arg, Vs, RetTy) :-
    inference(Tcx, Arg, ArgVs, ArgTy),
    inference(Tcx, Fn, FnVs0, FnTy),
    copy_term(FnVs0-FnTy, FnVs-(ParamTy->RetTy)),
    ParamTy = ArgTy,
    term_variables(FnVs-ArgVs, Vs). % The poor man's set union.


:- mode test_case(+_Tcx, +_Tm, +_ExpectedGenericVariables, +_ExpectedType).

test_case([], 123, [], nat).
test_case([], true, [], bool).
test_case([], false, [], bool).
test_case([], pair(123, true), [], pair(nat, bool)).
test_case([], x->123, [], _T->nat).
test_case([], x->x, [], T->T).
test_case([], let(f, x->x, f), [T], T->T).
test_case([], let(f, x->y->pair(x,y), f), [A, B], A->B->pair(A, B)).
test_case([], let(f, x->x, f@123), [], nat).
test_case([], let(f, x->x, pair(f@123, f@true)), [], pair(nat, bool)).
test_case([], let(id, x->x, let(f, y->id@y, f)), [A], A->A).
test_case([], let(x, 123, x), [], nat).
test_case([], let(add, x->y->123, add@123@123), [], nat).
test_case([x:forall([], nat)], x, [], nat).


test :-
    forall(
        test_case(Tcx, Tm, ExpectedVs, ExpectedTy),
        (
            inference(Tcx, Tm, ActualVs, ActualTy) ->
            (
                ExpectedVs-ExpectedTy =@= ActualVs-ActualTy -> true
                ; format('!!! Test Failure:~n  Term: ~p~n  Expected type: ~p=>~p~n  Actual type:   ~p=>~p~n~n', [Tm, ExpectedVs, ExpectedTy, ActualVs, ActualTy])
            )
            ; format('!!! Inference Failure:~n  Term: ~p~n~n', [Tm])
        )
    ).
