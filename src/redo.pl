:- op(2, fx, '?').
:- op(600, xfy, '@').  % Function application
:- op(600, xfy, '@@'). % Type application
:- op(600, xfy, '::'). % Kind signature

:- discontiguous tm_ty//2.

tm_ty(N, nat) -->
    { integer(N), N >= 0 },
    !.

tm_ty(true, bool) --> !.
tm_ty(false, bool) --> !.

tm_ty([], list@@_) --> !.
tm_ty([Head | Tail], list@@T) -->
    tm_ty(Head, T),
    tm_ty(Tail, list@@T),
    !.

tm_ty(none, opt@@_) --> !.
tm_ty(some@X, opt@@T) --> tm_ty(X, T), !.

:- discontiguous trait/2, impl/3.

trait(map@@Self, [map : (T::'*'->U::'*'->Self@@T->(T->U)->Self@@U)]).
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
    copy_term(Trait, TraitCopy1),
    copy_term(Trait, TraitCopy2),
    trait(TraitCopy1, Methods),
    impl(TraitCopy2, Constraints, _MethodImpls),
    maplist(try_resolve_trait, Constraints, OutConstraintsUnflattened),
    flatten(OutConstraintsUnflattened, OutConstraints).

try_resolve_trait(impl(TraitSig), Constraints) :-
    ground(TraitSig) -> resolve_trait(TraitSig, _MethodImpls, Constraints)
                      ; Constraints = [impl(TraitSig)].