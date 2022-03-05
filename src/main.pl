:- use_module(library(lists), [member/2, append/3]).

:- op(2, fx, '?').
:- op(600, yfx, '@').
:- op(600, yfx, '@@').
:- op(600, xfy, '::').
:- op(700, xfx, '<:').

builtin(true, bool).
builtin(false, bool).
builtin(some, forall(?t, ?t -> opt(?t))).
builtin(none, forall(?t, opt(?t))).
builtins(Builtins) :-
    bagof(Tm:Ty, builtin(Tm, Ty), Builtins).

tyck(Tm, Ty) :-
    builtins(Builtins),
    phrase(tm_ty(Tm, Ty), [Builtins], _).

never <: _ --> [].
Ty <: Ty --> [].
F1 <: F2 -->
    { F1 =.. [Functor, A1], F2 =.. [Functor, A2] },
    A1 <: A2.
Sub <: Super -->
    { child_parent_type(Middle, Super) },
    Sub <: Middle.
child_parent_type(nat, int).
child_parent_type(int, float).

tm_ty(N, nat) -->
    { integer(N), N >= 0 },
    !.

tm_ty(N, int) -->
    { integer(N), N < 0 },
    !.

tm_ty(N, float) -->
    { float(N) },
    !.

tm_ty(Var, Ty) -->
    { atom(Var) },
    (
        lookup(Var, Ty)
    ->
        !
    ;
        type_check_error('unbound variable', [variable(Var)])
    ).

tm_ty(if(Condition, Consequent, Alternative), Ty) -->
    tm_ty(Condition, bool),
    tm_ty(Consequent, Ty),
    tm_ty(Alternative, Ty),
    !.

tm_ty(if(Condition, _, _), _) -->
    tm_ty(Condition, NonBool),
    { dif(NonBool, bool) },
    type_check_error(
        'the condition of an if expression must have type bool',
        [condition(Condition), condition_type(NonBool)]
    ).

tm_ty(if(_, Consequent, Alternative), _) -->
    tm_ty(Consequent, T1),
    tm_ty(Alternative, T2),
    { dif(T1, T2) },
    type_check_error(
        'the branches of an if expression must have the same type',
        [consequent_type(T1), alternative_type(T2)]
    ).

tm_ty(A + B, Ty) -->
    tm_ty(A, Ty),
    tm_ty(B, Ty),
    Ty <: float,
    !.
tm_ty(A + B, _) -->
    tm_ty(A, T1),
    tm_ty(B, T2),
    type_check_error('operands to + operator must both be `nat`s', [left(T1), right(T2)]).

tm_ty([], list(_)) --> !.
tm_ty([A|B], list(Ty)) -->
    tm_ty(A, Ty),
    tm_ty(B, list(Ty)),
    !.
tm_ty([A|B], _) -->
    tm_ty(A, T1),
    tm_ty(B, list(T2)),
    { dif(T1, T2) },
    type_check_error('lists must only contain items of one type', [element_type(T1), list_type(T2)]).

tm_ty(struct([]), struct([])) --> !.
tm_ty(struct([K=V | Rest]), struct([K:TyV | TyRest])) -->
    { atom(K) },
    tm_ty(V, TyV),
    tm_ty(struct(Rest), struct(TyRest)),
    !.

tm_ty(let(Binder, Expr, Body), BodyTy) -->
    { atom(Binder) },
    tm_ty(Expr, ExprTy),
    defining(Binder:ExprTy, tm_ty(Body, BodyTy)),
    !.

tm_ty((Param:ParamTy->Body), ParamTy->BodyTy) -->
    { atom(Param) },
    defining(Param:ParamTy, tm_ty(Body, BodyTy)),
    !.

tm_ty((?TyVar->Body), forall(?TyVar, BodyTy)) -->
    { atom(TyVar) },
    defining(?TyVar, tm_ty(Body, BodyTy)),
    !.

tm_ty(Fn@@AppTy, T2) -->
    tm_ty(Fn, forall(?TyVar, ResTy)),
    { replacement_type_replaced(?TyVar->AppTy, ResTy, T2) },
    !.

tm_ty(Fn@Arg, RetTy) -->
    tm_ty(Arg, ArgTy),
    tm_ty(Fn, (ArgTy->RetTy)),
    !.
tm_ty(Fn@Arg, _) -->
    tm_ty(Arg, ArgTy),
    tm_ty(Fn, (ParamTy->_)),
    { dif(ArgTy, ParamTy) },
    type_check_error('wrong type passed to function', [expected(ParamTy), actual(ArgTy)]).

type_check_error(Msg, Info) -->
    tcx(Tcx),
    { append(Info, [tcx(Tcx)], InfoAndTcx) },
    { throw(err(Msg, InfoAndTcx)) }.

tcx(Tcx), [Tcx] --> [Tcx].
tcx(Tcx0, Tcx), [Tcx] --> [Tcx0].

lookup(Var, Ty) -->
    tcx(Tcx),
    { member(Var:Ty, Tcx) }.

define(Var:Ty) --> tcx(Tcx0, [Var:Ty | Tcx0]).
define(?TyVar) --> tcx(Tcx0, [?TyVar | Tcx0]).

defining(Var:Ty, Program) -->
    tcx(Tcx),
    { phrase((define(Var:Ty), Program), [Tcx], [_])}.

defining(?TyVar, Program) -->
    tcx(Tcx),
    { phrase((define(?TyVar), Program), [Tcx], [_])}.

replacement_type_replaced(?V->_, forall(?V, Body), forall(?V, Body)) :- !.
replacement_type_replaced(?V->New, ?V, New) :- !.
replacement_type_replaced(?V->_, ?W, ?W) :- dif(V, W), !.
replacement_type_replaced(?V->New, Ty0, Ty) :-
    Ty0 =.. [Head | Args0],
    maplist(replacement_type_replaced(?V->New), Args0, Args),
    Ty =.. [Head | Args],
    !.
replacement_type_replaced(?_->_, Other, Other) :- !.

:- op(1100, fx, 'defn').
:- op(1150, xfy, 'do').

tcx_item_tcx(Tcx0, (defn SigHead -> RetTy do _Body), Tcx) :-
    SigHead =.. [Name | Params],
    maplist([_Param:ParamTy, ParamTy]>>true, Params, ParamTys),
    FnTy = (tuple(ParamTys)->RetTy),
    Tcx = [Name:FnTy | Tcx0].
    
defn fib(n: nat) -> nat do {
    if(n < 2,
        n,
        fib(n - 2) + fib(n - 1))
}.
