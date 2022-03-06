:- op(2, fx, '?').
:- op(600, xfy, '@').  % Function application
:- op(600, xfy, '@@'). % Type application
:- op(600, xfy, '::'). % Kind signature
:- op(1050, xfy, '=>'). % Type variable introduction

eval_state(Program, InitState) :-
    phrase(Program, [InitState], [_]).

:- discontiguous tm_ty//2.

tm_ty(N, nat) -->
    { integer(N), N >= 0 },
    !.

tm_ty(true, bool) --> !.
tm_ty(false, bool) --> !.

tm_ty(nil, T=>list@@T) --> !.
tm_ty(cons, T=>T->list@@T->list@@T) --> !.

tm_ty(none, T=>opt@@T) --> !.
tm_ty(some, T=>T->opt@@T) --> !.

tm_ty(ok,  T=>E=>T->res@@E@@T) --> !.
tm_ty(err, T=>E=>E->res@@E@@T) --> !.

tm_ty(Fn@Arg, OutTy) -->
    tm_ty(Arg, ArgTy),
    (
        tm_ty(Fn, AbstractTy), { AbstractTy = (_=>_) }
    ->
        { skip_foralls(AbstractTy, TyVarChain, Hole, StrippedTy) },
        { StrippedTy = (ArgTy->RetTy) },
        { Hole = RetTy },
        { skip_instantiated_foralls(TyVarChain, OutTy) }
    ;
        tm_ty(Fn, ArgTy->RetTy),
        { OutTy = RetTy }
    ),
    !.

:- discontiguous test/1.
test((
    Tm = (cons@123)@(nil@@nat),
    eval_state(tm_ty(Tm, _), [])
)).

skip_foralls(F, Hole, Hole, F) :- F =.. [Head | _], dif(Head, '=>').
skip_foralls(V=>T0, V=>Vs, Hole, T) :-
    skip_foralls(T0, Vs, Hole, T).

skip_instantiated_foralls(F, F) :- F =.. [Head | _], dif(Head, '=>').
skip_instantiated_foralls(V=>T0, Out) :-
    skip_instantiated_foralls(T0, T),
    ( nonvar(V) -> Out = T ; Out = (V=>T) ).

tm_ty(Expr@@Ty, ExprTy) -->
    tm_ty(Expr, TyVar0=>ExprTy0),
    { copy_term(TyVar0=>ExprTy0, TyVar=>ExprTy) },
    { TyVar = Ty },
    !.

:- discontiguous trait/2, impl/3.

trait(map@@Self, [map : (T=>U=>Self@@T->(T->U)->Self@@U)]).
impl(map@@list, [], [map = map_list]).
impl(map@@opt, [], [map = map_opt]).
impl(map@@(res@@_E), [], [map = map_res]).

trait(eq@@Self, ['==' : (Self->Self->bool)]).
impl(eq@@nat, [], ['==' = eq_nat]).
impl(eq@@bool, [], ['==' = eq_bool]).
impl(eq@@(list@@T), [impl(eq@@T)], ['==' = eq_list]).
impl(eq@@(opt@@T), [impl(eq@@T)], ['==' = eq_opt]).
impl(eq@@(res@@E@@T), [impl(eq@@E), impl(eq@@T)], ['==' = eq_res]).

resolve_trait(Trait, Methods, OutConstraints) :-
    trait(TraitSig0, Methods0), copy_term(TraitSig0-Methods0, TraitSig-Methods),
    impl(ImplSig0, Constraints0, _MethodImpls0), copy_term(ImplSig0-Constraints0, ImplSig-Constraints),
    Trait = TraitSig, Trait = ImplSig,
    maplist(try_resolve_trait, Constraints, OutConstraintsUnflattened),
    flatten(OutConstraintsUnflattened, OutConstraints).

try_resolve_trait(impl(Trait@@Self), Constraints) :-
    var(Self) -> Constraints = [impl(Trait@@Self)]
               ; resolve_trait(Trait@@Self, _MethodImpls, Constraints).
