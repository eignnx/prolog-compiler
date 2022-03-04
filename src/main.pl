:- use_module(library(lists), [member/2]).

:- op(2, fx, '?').
:- op(600, xfy, '@').
:- op(600, xfy, '::').


tcx_tm_ty(_, true, bool) :- !.
tcx_tm_ty(_, false, bool) :- !.

tcx_tm_ty(Tcx, if(Condition, Consequent, Alternative), Ty) :-
    tcx_tm_ty(Tcx, Condition, bool),
    tcx_tm_ty(Tcx, Consequent, Ty),
    tcx_tm_ty(Tcx, Alternative, Ty),
    !.

tcx_tm_ty(Tcx, if(Condition, _, _), _) :-
    tcx_tm_ty(Tcx, Condition, NonBool),
    dif(NonBool, bool),
    throw(err('the condition of an if expression must have type bool'(condition(Condition), Tcx))).

tcx_tm_ty(Tcx, if(_, Consequent, Alternative), _) :-
    tcx_tm_ty(Tcx, Consequent, T1),
    tcx_tm_ty(Tcx, Alternative, T2),
    dif(T1, T2),
    throw(err('the branches of an if expression must have the same type'(consequent(T1), alternative(T2), tcx(Tcx)))).

tcx_tm_ty(_, N, nat) :- number(N).
tcx_tm_ty(Tcx, A + B, nat) :-
    tcx_tm_ty(Tcx, A, nat),
    tcx_tm_ty(Tcx, B, nat),
    !.
tcx_tm_ty(Tcx, A + B, _) :-
    tcx_tm_ty(Tcx, A, T1),
    tcx_tm_ty(Tcx, B, T2),
    throw(err('operands to + operator must both be `nat`s'(left(T1), right(T2), tcx(Tcx)))).

tcx_tm_ty(_, [], list(_)) :- !.
tcx_tm_ty(Tcx, [A|B], list(Ty)) :-
    tcx_tm_ty(Tcx, A, Ty),
    tcx_tm_ty(Tcx, B, list(Ty)),
    !.
tcx_tm_ty(Tcx, [A|B], _) :-
    tcx_tm_ty(Tcx, A, T1),
    tcx_tm_ty(Tcx, B, list(T2)),
    dif(T1, T2),
    throw(err('lists must only contain items of one type'(element_type(T1), list_type(T2), tcx(Tcx)))).

tcx_tm_ty(_, struct([]), struct([])) :- !.
tcx_tm_ty(Tcx, struct([K=V | Rest]), struct([K:TyV | TyRest])) :-
    atom(K),
    tcx_tm_ty(Tcx, V, TyV),
    tcx_tm_ty(Tcx, struct(Rest), struct(TyRest)),
    !.

tcx_tm_ty(Tcx0, let(Binder, Expr, Body), BodyTy) :-
    atom(Binder),
    tcx_tm_ty(Tcx0, Expr, ExprTy),
    Tcx = [Binder:ExprTy | Tcx0],
    tcx_tm_ty(Tcx, Body, BodyTy),
    !.

tcx_tm_ty(Tcx, Var, Ty) :-
    atom(Var),
    member(Var:Ty, Tcx),
    !.
tcx_tm_ty(Tcx, Var, _) :-
    atom(Var),
    throw(err('unbound variable'(variable(Var), tcx(Tcx)))).

tcx_tm_ty(Tcx0, (Param:ParamTy->Body), ParamTy->BodyTy) :-
    atom(Param),
    Tcx = [Param:ParamTy | Tcx0],
    tcx_tm_ty(Tcx, Body, BodyTy),
    !.

tcx_tm_ty(Tcx0, (?TyVar->Body), forall(?TyVar, BodyTy)) :-
    atom(TyVar),
    Tcx = [?TyVar | Tcx0],
    tcx_tm_ty(Tcx, Body, BodyTy),
    !.

tcx_tm_ty(Tcx, Fn@AppTy, T2) :-
    tcx_tm_ty(Tcx, Fn, forall(?TyVar, ResTy)),
    replacement_type_replaced(?TyVar->AppTy, ResTy, T2).

tcx_tm_ty(Tcx, Call, RetTy) :-
    Call =.. [Fn, Arg],
    tcx_tm_ty(Tcx, Arg, ArgTy),
    tcx_tm_ty(Tcx, Fn, (ArgTy->RetTy)),
    !.
tcx_tm_ty(Tcx, Call, _) :-
    Call =.. [Fn, Arg],
    tcx_tm_ty(Tcx, Arg, ArgTy),
    tcx_tm_ty(Tcx, Fn, (ParamTy->_)),
    dif(ArgTy, ParamTy),
    throw(err('wrong type passed to function'(expected(ParamTy), actual(ArgTy), Tcx))).

tcx_tm_ty(Tcx, Tm, _) :-
    throw(err('unable to type the term'(term(Tm), tcx(Tcx)))).

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
