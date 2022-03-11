:- op(600, yfx, '@').  % Function application
:- op(1060, xfy, '=>'). % Type variable introduction
:- op(1150, fx, mode).

% Defines/validates a typing context.
tcx([]).
tcx([X;Sigma | Tcx]) :-
    atom(X),
    sigma_type(Sigma),
    tcx(Tcx).

% Defines/validates an abstracted ("sigma") type. These are often called "type
% schemes".
sigma_type(Vs=>Tau) :-
    set_of_vars(Vs),
    tau_type(Tau).

% Defines/validates a set of variables.
set_of_vars([]).
set_of_vars([V | Vs]) :-
    var(V),
    set_of_vars(Vs),
    maplist(\==(V), Vs).

% Defines/validates a simple ("tau") type.
tau_type(A->B) :-
    tau_type(A),
    tau_type(B).
tau_type(tuple(Ts)) :-
    maplist(tau_type, Ts).
tau_type(Constructor) :-
    Constructor =.. [Name | Args],
    length(Args, Arity),
    type_constructor(Name/Arity),
    maplist(tau_type, Args).
tau_type(V) :- var(V). % An Inference/Generic Variable.

type_constructor(nat/0).
type_constructor(bool/0).
type_constructor(list/1).

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

:- mode inference(+_TypeContext, +_Term, -(_GenericVariables=>_Type)).

inference(_Tcx, N, []=>nat) :- integer(N), N >= 0.
inference(Tcx, A+B, []=>nat) :-
    inference(Tcx, A, []=>nat),
    inference(Tcx, B, []=>nat).

inference(_Tcx, true,  []=>bool).
inference(_Tcx, false, []=>bool).

inference(_Tcx, [], [T]=>list(T)).
inference(Tcx, [Tm | Tms], Vs=>list(EleTy)) :-
    inference(Tcx, Tm, TmVs=>EleTy),
    inference(Tcx, Tms, TmsVs=>list(EleTy)),
    var_set_union([TmVs, TmsVs], Vs).

inference(Tcx, tuple(Tms), Vs=>tuple(Tys)) :-
    Mapper = {Tcx}/[E, EVs, ETy]>>inference(Tcx, E, EVs=>ETy),
    maplist(Mapper, Tms, VsList, Tys),
    var_set_union(VsList, Vs).

inference(Tcx, X, Vs=>Ty) :-
    atom(X),
    member(X;Vs=>Ty, Tcx).

inference(Tcx, X->B, Vs=>XTy->BTy) :-
    atom(X),
    % Function parameters are not allowed to have generic types. For example
    % this is not allowed:
    % `fn thing(x: for<T> (T, T)) -> int`
    HypotheticalTcx = [X;[]=>XTy | Tcx],
    inference(HypotheticalTcx, B, Vs=>BTy).

inference(Tcx, let(X, E, B), BVs=>BTy) :-
    atom(X),
    inference(Tcx, E, _EGenVs=>ETy),
    % Collect all the variables in `ETy`. These are the union of both Generic
    % and Inference Variables from `ETy`.
    term_variables(ETy, EInfAndGenVs),
    % Treat all Inference Varibles in `E` as Generic in the body.
    EVs = EInfAndGenVs,
    HypotheticalTcx = [X;EVs=>ETy | Tcx],
    inference(HypotheticalTcx, B, BVs=>BTy).

inference(Tcx, Fn@Arg, Vs=>RetTy) :-
    inference(Tcx, Arg, ArgVs=>ArgTy),
    inference(Tcx, Fn, FnVs0=>FnTy),
    copy_term(FnVs0=>FnTy, FnVs=>(ParamTy->RetTy)), % Make a copy for instantiation.
    ParamTy = ArgTy, % Instantiate.
    var_set_union([FnVs, ArgVs], Vs).


:- mode var_set_union(+_ListOfVarSets, -_Union).

var_set_union(ListOfVarSets, Union) :-
    term_variables(ListOfVarSets, Union).


:- mode test_case(+_Tcx, +_Tm, +(_ExpectedGenericVariables=>_ExpectedType)).

test_case([], 123, []=>nat).
test_case([], 123+456, []=>nat).
test_case([], true, []=>bool).
test_case([], false, []=>bool).
test_case([], tuple([123, true]), []=>tuple([nat, bool])).
test_case([], [], [T]=>list(T)).
test_case([], [1, 2, 3], []=>list(nat)).
test_case([], [[], [], []], [T]=>list(list(T))).
test_case([], x->123, []=>_T->nat).
test_case([], x->x, []=>T->T).
test_case([], let(f, x->x, f), [T]=>T->T).
test_case([], let(f, x->y->tuple([x,y]), f), [A, B]=>A->B->tuple([A, B])).
test_case([], let(add, x->y->x+y, add), []=>nat->nat->nat).
test_case([], let(f, x->x, f@123), []=>nat).
test_case([], let(f, x->x, tuple([f@123, f@true])), []=>tuple([nat, bool])).
test_case([], let(id, x->x, let(f, y->id@y, f)), [A]=>A->A).
test_case([], let(x, 123, x), []=>nat).
test_case([], let(add, x->y->123, add@123@123), []=>nat).
test_case([x;[]=>nat], x, []=>nat).


test :-
    forall(
        test_case(Tcx, Tm, ExpectedVs=>ExpectedTy),
        (
            inference(Tcx, Tm, ActualVs=>ActualTy) ->
            (
                ExpectedVs-ExpectedTy =@= ActualVs-ActualTy -> true
                ; format('!!! Test Failure:~n  Term: ~p~n  Expected type: ~p=>~p~n  Actual type:   ~p=>~p~n~n', [Tm, ExpectedVs, ExpectedTy, ActualVs, ActualTy])
            )
            ; format('!!! Inference Failure:~n  Term: ~p~n~n', [Tm])
        )
    ).
