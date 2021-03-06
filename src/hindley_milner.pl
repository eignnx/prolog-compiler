:- op(350, yfx, '@').  % Function application
:- op(1150, fx, mode).

% Defines/validates a typing context.
tcx([]).
tcx([X-Sigma | Tcx]) :-
    atom(X),
    sigma_type(Sigma),
    tcx(Tcx).

% Defines/validates an abstracted ("sigma") type. These are often called "type
% schemes".
sigma_type(forall(Vs, Tau)) :-
    set_of_vars(Vs),
    tau_type(Tau).

% Defines/validates a set of variables.
set_of_vars([]).
set_of_vars([V | Vs]) :-
    var(V),
    maplist(\==(V), Vs),
    set_of_vars(Vs).

% Defines/validates a simple ("tau") type.
tau_type(A->B) :-
    tau_type(A),
    tau_type(B).
tau_type([Child]) :-
    tau_type(Child).
tau_type(Tuple) :-
    Tuple =.. [tuple | Ts],
    maplist(tau_type, Ts).
tau_type(Constructor) :-
    Constructor =.. [Name | Args],
    length(Args, Arity),
    type_constructor(Name/Arity),
    maplist(tau_type, Args).
tau_type(V) :- var(V). % An Inference/Generic Variable.

type_constructor(nat/0).
type_constructor(bool/0).


:- mode inference(+_TypeContext, +_Term, -_Type).

inference(_Tcx, N, nat) :- integer(N), N >= 0, !.
inference(Tcx, A+B, nat) :-
    !,
    inference(Tcx, A, ATy),
    inference(Tcx, B, BTy),
    ( ATy = nat, BTy = nat -> true
    ; throw(type_check_err('The arguments to `+` must have type nat'(ATy, BTy)))
    ).

inference(_Tcx, true,  bool) :- !.
inference(_Tcx, false, bool) :- !.

inference(_Tcx, [], [_]) :- !.
inference(Tcx, [Tm | Tms], [EleTy]) :-
    !,
    inference(Tcx, Tm, EleTy),
    inference(Tcx, Tms, [TailEleTy]),
    ( EleTy = TailEleTy -> true
    ; throw(type_check_err('You can''t add an element of type A to a list of type list(B)'(EleTy, TailEleTy)))
    ).

inference(Tcx, Tuple, Ty) :-
    Tuple =.. [tuple | Tms],
    !,
    maplist({Tcx}/[E, ETy]>>inference(Tcx, E, ETy), Tms, Tys),
    Ty =.. [tuple | Tys].

inference(Tcx, X->Body, FreshXTy->BodyTy) :-
    atom(X),
    !,
    % Function parameters are not allowed to have generic (sigma) types. For
    % example this is not allowed:
    % `fn thing(x: for<T> T->T) -> int`
    inference([X-forall([], FreshXTy) | Tcx], Body, BodyTy).

inference(Tcx, let(X, Binding, Body), BodyTy) :-
    atom(X),
    !,
    inference(Tcx, Binding, BindingTy),
    generalization(Tcx, BindingTy, BindingScheme),
    inference([X-BindingScheme | Tcx], Body, BodyTy).

inference(Tcx, Fn@Arg, RetTy) :-
    !,
    inference(Tcx, Arg, ArgTy),
    inference(Tcx, Fn, ParamTy->RetTy),
    ( ParamTy = ArgTy -> true
    ; throw(type_check_err('Expected argument of type A, got B'(ParamTy, ArgTy)))
    ).

inference(Tcx, X, Ty) :-
    atom(X),
    !,
    ( member(X-forall(Vs, Ty0), Tcx) -> instantiation(forall(Vs, Ty0), Ty)
    ; throw(type_check_err('Unbound variable'(X)))
    ).


:- mode instantiation(+_TypeScheme, -_SimpleType).

instantiation(forall(Vs, Ty0), Ty) :-
    copy_term(Vs, Ty0, _, Ty).


:- mode generalization(+_TypeContext, +_SimpleType, -_TypeScheme).

generalization(Tcx, Ty0, forall(Vs, Ty)) :-
    term_variables(Ty0, TyVars),
    term_variables(Tcx, TcxVars),
    include({TcxVars}/[X]>>maplist(\==(X), TcxVars), TyVars, Vs0),
    copy_term(Vs0-Ty0, Vs-Ty).


:- mode test_case(+_Tcx, +_Tm, +_ExpectedResult).

test_case([], 123, ok(nat)).
test_case([], 123+456, ok(nat)).
test_case([], true, ok(bool)).
test_case([], false, ok(bool)).
test_case([], tuple(123, true), ok(tuple(nat, bool))).
test_case([], [], ok([_])).
test_case([], [1, 2, 3], ok([nat])).
test_case([], [[], [], []], ok([[_]])).
test_case([], x->123, ok(_T->nat)).
test_case([], x->x, ok(T->T)).
test_case([],
    f->tuple(f@3, f@true),
    failure('Luca Cardelli says this term can''t be typed.')).
test_case([succ-forall([], nat->nat)],
    (f->tuple(f@3, f@true))@succ,
    failure('Luca Cardelli says this term can''t be typed.')).
test_case([],
    g->let(f, g, tuple(f@3, f@true)),
    failure('Luca Cardelli says this term can''t be typed.')).
test_case([],
    true+false,
    failure('Operator `+` is not defined on booleans.')).
test_case([], let(f, x->x, f), ok(T->T)).
test_case([], let(f, x->y->tuple(x,y), f), ok(A->B->tuple(A, B))).
test_case([], let(add, x->y->x+y, add), ok(nat->nat->nat)).
test_case([], let(f, x->x, f@123), ok(nat)).
test_case([], let(f, x->x, tuple(f@123, f@true)), ok(tuple(nat, bool))).
test_case([], let(id, x->x, let(f, y->id@y, f)), ok(A->A)).
test_case([], let(x, 123, x), ok(nat)).
test_case([], let(add, x->y->123, add@123@123), ok(nat)).
test_case([x-forall([], nat)], x, ok(nat)).


test :-
    % Test that all expected successes suceed.
    forall(
        test_case(Tcx, Tm, ok(ExpectedTy)),
        (
            catch(inference(Tcx, Tm, ActualTy), Err,
                (
                    format('!!! Error encountered during test:~n'),
                    format('  Tm = ~p~n', [Tm]),
                    format('  Err = ~p~n~n', [Err])
                )
            )
        ->
            (
                ExpectedTy =@= ActualTy
            ;
                format('!!! Test Failure:~n'),
                format('  Term: ~p~n', [Tm]),
                format('  Expected type: ~p~n', [ExpectedTy]),
                format('  Actual type:   ~p~n~n', [ActualTy])
            )
        ;
            format('!!! Inference Failure:~n'),
            format('  Term: ~p~n~n', [Tm])
        )
    ),

    % Test that all expected failures fail.
    forall(
        test_case(Tcx, Tm, failure(Msg)),
        (
            catch(inference(Tcx, Tm, Res), type_check_err(_), false) % Ignore any type check errors
        ->
            format('!!! Unexpected Inference Success:~n'),
            format('  Expected inference failure for term: ~p~n', [Tm]),
            format('  Inferred incorrect type: ~p~n', [Res]),
            format('  Message: ~a~n~n', [Msg])
        ;
            true
        )
    ).
