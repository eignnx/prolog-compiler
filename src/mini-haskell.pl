:- use_module(library(ordsets), [ord_union/3]).

:- op(350, yfx, '@').  % Function application
:- op(1150, fx, mode).


:- mode inference(+_Term, -_Type).
:- mode inference(+_TypeContext, +_Term, -_Type).

inference(Tm, Ty) :-
    initial_tcx(Tcx),
    inference(Tcx, Tm, Ty).

inference(_Tcx, N, nat) :- integer(N), N >= 0, !.
inference(Tcx, A+B, Ty) :-
    !,
    inference(Tcx, add@A@B, Ty).

inference(Tcx, A==B, Ty) :-
    !,
    inference(Tcx, eq@A@B, Ty).

inference(_Tcx, true,  bool) :- !.
inference(_Tcx, false, bool) :- !.

inference(_Tcx, [], list(_)) :- !.
inference(Tcx, [Tm | Tms], list(EleTy)) :-
    !,
    inference(Tcx, Tm, EleTy),
    inference(Tcx, Tms, list(TailEleTy)),
    ( EleTy = TailEleTy -> true
    ; format(atom(Msg), 'You can''t add an element of type `~p` to a list of type `list(~p)`', [EleTy, TailEleTy]),
      throw(type_check_err(Msg))
    ).

inference(Tcx, tuple(Tms), tuple(Tys)) :-
    !,
    maplist({Tcx}/[E, ETy]>>inference(Tcx, E, ETy), Tms, Tys).

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
    inference(Tcx, Fn, FnTy),
    inference(Tcx, Arg, ArgTy),
    ( FnTy = (ParamTy -> RetTy), !
        ; format(atom(Msg), 'The term `~p` is not a function, so can''t be called', [Fn]),
          throw(type_check_err(Msg))),
    ( ArgTy = ParamTy, !
        ; format(atom(Msg), 'Function `~p` expected an argument of type `~p`, but got type `~p`', [Fn, ParamTy, ArgTy]),
          throw(type_check_err(Msg))).

inference(Tcx, (typeclass(Class, X-XScheme) ; P), PTy) :-
    atom(Class), atom(X), !,
    assert(typeclass(Class, X-XScheme)),
    inference([X-XScheme | Tcx], P, PTy).

inference(Tcx, (instance(Class, Signature, X, Impl) ; P), PTy) :-
    atom(Class), atom(X), Signature =.. [Ctor | SortVec], !,

    member(X-forall([Self-[Class]], XTy), Tcx),

    % Unify a copy of X's scheme with `Ctor(...FreshVars)`.
    length(SortVec, N),
    length(FreshVs, N),
    maplist([V, Sort]>>put_attr(V, sort_constraint, Sort), FreshVs, SortVec),
    copy_term([Self], XTy, [InstantiatedSelf], XTySelfInstantiated),
    FreshSig =.. [Ctor | FreshVs],
    InstantiatedSelf = FreshSig,
    inference(Tcx, Impl, ImplTy),
    ( XTySelfInstantiated = ImplTy, !
        ; format(atom(Msg), 'The type of `~p` must conform to the type `~p`', [X, XTySelfInstantiated]),
          throw(type_check_err(Msg))),
    format('[INFO] ImplTy = ~p~n', [ImplTy]),

    assert(instance(Class, Signature, Impl)),
    inference(Tcx, P, PTy).

inference(Tcx, X, Ty) :-
    atom(X),
    !,
    ( member(X-forall(Vs, Ty0), Tcx) -> instantiation(forall(Vs, Ty0), Ty)
    ; throw(type_check_err('Unbound variable'(X)))
    ).


:- mode instantiation(+_TypeScheme, -_SimpleType).

instantiation(forall(Vs, Ty0), Ty) :-
    % Replace all vars in `Vs` with fresh variables.
    copy_term(Vs, Ty0, VsFresh, Ty),
    % Make sure to copy the constraints over to the new variables.
    maplist(copy_sort_attr, Vs, VsFresh).


copy_sort_attr(V0, V) :-
    ( get_attr(V0, sort_constraint, Attr) -> true
    ; Attr = []
    ),
    put_attr(V, sort_constraint, Attr).


:- mode generalization(+_TypeContext, +_SimpleType, -_TypeScheme).

generalization(Tcx, Ty, forall(Vs, Ty)) :-
    term_variables(Ty, TyVars),
    term_variables(Tcx, TcxVars),
    % Keep only the free variables that are not involved in constraints from
    % their environment (`Tcx`).
    include({TcxVars}/[X]>>maplist(\==(X), TcxVars), TyVars, Vs).


attr_unify_hook(Sort, Ty) :-
    constrain(Ty, Sort).

% Display sort constraints `Sort` on a type variable `X` as `X-Sort`.
attribute_goals(X) -->
    { get_attr(X, sort_constraint, Sort) },
    [X-Sort].


constrain(TyVar, Sort1) :-
    var(TyVar),
    !,
    ( get_attr(TyVar, sort_constraint, Sort2) ; Sort2 = [] ),
    ord_union(Sort1, Sort2, Sort),
    put_attr(TyVar, sort_constraint, Sort).

constrain(Ty, Sort) :-
    Ty =.. [Ctor | Args],
    !,
    maplist(
        {Ctor, Args}/[Class]>>(
            most_general_typeclass_constraints(Ctor, Class, SortVec),
            maplist(constrain, Args, SortVec)
        ),
        Sort
    ).

most_general_typeclass_constraints(Ctor, Class, SortVec) :-
    setof(SortVec, Impl^instance_lookup(Class, Ctor, SortVec, Impl), SortVecs) ->
        most_general_sortvec(SortVecs, SortVec)
    ;
        format(atom(Msg), 'The type `~p` doesn''t have an instance of `~w`', [Ctor, Class]),
        throw(type_check_err(Msg)).

most_general_sortvec([], _) :-
    throw(type_check_err('ICE: Empty set of SortVecs')).
most_general_sortvec([FirstSV | SortVecs], SortVec) :-
    foldl(more_general_sortvec, SortVecs, FirstSV, SortVec).
    

more_general_sortvec(SV1, SV2, SV) :-
      maplist(ord_subset, SV1, SV2) -> SV = SV1
    ; maplist(ord_subset, SV2, SV1) -> SV = SV2
    ; throw(type_check_err('Non-comparable sort vecs'(SV1, SV2))).


:- dynamic typeclass/2.

typeclass('Eq', eq-forall([Self-['Eq']], Self->Self->bool)).
typeclass('Add', add-forall([Self-['Add']], Self->Self->Self)).
typeclass('Monoid', mappend-forall([Self-['Monoid']], Self->Self->Self)).


:- dynamic instance/3.

instance('Eq', bool, bool_eq_impl).

instance('Eq', nat, nat_eq_impl).
instance('Add', nat, nat_add_impl).

instance('Eq', list(['Eq']), todo_impl_eq_list).
instance('Monoid', list([]), todo_impl_list_concat).

instance('Eq', pair(['Eq'], ['Eq']),
    p1->p2->and@(
            eq@(fst@p1)@(fst@p2)
        )@(
            eq@(snd@p1)@(snd@p2)
        )).
instance('Add', pair(['Add'], ['Add']),
    p1->p2->pair(add@(fst@p1)@(fst@p2),
                 add@(snd@p1)@(snd@p2))).

instance('Eq', opt(['Eq']), todo_impl_eq_opt).
instance('Monoid', opt(['Monoid']), todo_impl_monoid_opt).

% instance('Eq', pair(['Eq'], ['Eq', 'Debug']), i_print_snd_also).

instance_lookup(Class, Ctor, SortVec, Impl) :-
    instance(Class, Signature, Impl),
    Signature =.. [Ctor | SortVec].

initial_tcx(and, forall([], bool->bool->bool)).
initial_tcx(or, forall([], bool->bool->bool)).
initial_tcx(nat_eq_impl, forall([], nat->nat->bool)).
initial_tcx(nat_add_impl, forall([], nat->nat->nat)).
initial_tcx(pair, forall([A-[], B-[]], A->B->pair(A, B))).
initial_tcx(fst, forall([A-[], B-[]], pair(A, B)->A)).
initial_tcx(snd, forall([A-[], B-[]], pair(A, B)->B)).
initial_tcx(some, forall([A-[]], A->opt(A))).
initial_tcx(none, forall([A-[]], opt(A))).

initial_tcx(Tcx) :-
    bagof(X-Ty, initial_tcx(X, Ty), Tcx0),
    % Add the typeclass identifiers too.
    bagof(X-Ty, Class^typeclass(Class, X-Ty), Tcx1),
    append(Tcx0, Tcx1, Tcx2),
    maplist(bind_forall_tyvar_constraints, Tcx2, Tcx).

bind_forall_tyvar_constraints(Id-forall(VsAndSorts, Ty), Id-forall(Vs, Ty)) :-
    maplist(
        [V-Sort, V]>>put_attr(V, sort_constraint, Sort),
        VsAndSorts,
        Vs
    ).


repl :-
    read(Tm),
    Tm \= quit ->
        initial_tcx(Tcx),
        catch(inference(Tcx, Tm, Ty),
            type_check_err(Msg),
            (format('Typecheck Error: ~w~n', [Msg]), repl, false)),
        !,
        display_tm_ty(Tm, Ty),
        repl
    ;
        true. 


display_tm_ty(Tm, Ty) :-
    term_variables(Ty, FVs),
    maplist(var_sort_pair_wo_attr, FVs, VsSs), % Remove attrs so `numbervars` will work.
    numbervars(Tm-Ty),
    format('   ~p : ~p~n', [Tm, Ty]),
    include(\=(_-[]), VsSs, VsSsNoUnconstrained),
    display_constraints(VsSsNoUnconstrained).


get_sort(V, S) :-
    get_attr(V, sort_constraint, S), !.
get_sort(_, []).


var_sort_pair(V, V-S) :- get_sort(V, S).


var_sort_pair_wo_attr(V, V-S) :-
    var_sort_pair(V, V-S),
    del_attr(V, sort_constraint).
    

display_constraints([]) :- !.
display_constraints(VsSs) :-
    format('     where~n'),
    maplist([V-Sort]>>(
            (Sort = [First, Snd | Rest] ->
                format('       ~p implements ~w', [V, First]),
                foldl([C, N, N]>>format(' + ~w', [C]), [Snd | Rest], First, _),
                format('~n')
            ;
            Sort = [Class] ->
                format('       ~p implements ~w~n', [V, Class])
            )
        ), VsSs).


:- mode test_case(+_Tcx, +_Tm, +_ExpectedResult).

test_case([], 123, ok(nat)).
test_case([], 123+456, ok(nat)).
test_case([], true, ok(bool)).
test_case([], false, ok(bool)).
test_case([], tuple([123, true]), ok(tuple([nat, bool]))).
test_case([], [], ok(list(_))).
test_case([], [1, 2, 3], ok(list(nat))).
test_case([], [[], [], []], ok(list(list(_)))).
test_case([], x->123, ok(_T->nat)).
test_case([], x->x, ok(T->T)).
test_case([],
    f->tuple([f@3, f@true]),
    failure('Luca Cardelli says this term can''t be typed.')).
test_case([succ-forall([], nat->nat)],
    (f->tuple([f@3, f@true]))@succ,
    failure('Luca Cardelli says this term can''t be typed.')).
test_case([],
    g->let(f, g, tuple([f@3, f@true])),
    failure('Luca Cardelli says this term can''t be typed.')).
test_case([],
    true+false,
    failure('Operator `+` is not defined on booleans.')).
test_case([], let(f, x->x, f), ok(T->T)).
test_case([], let(f, x->y->tuple([x,y]), f), ok(A->B->tuple([A, B]))).
test_case([], let(add, x->y->x+y, add), ok(nat->nat->nat)).
test_case([], let(f, x->x, f@123), ok(nat)).
test_case([], let(f, x->x, tuple([f@123, f@true])), ok(tuple([nat, bool]))).
test_case([], let(id, x->x, let(f, y->id@y, f)), ok(A->A)).
test_case([], let(x, 123, x), ok(nat)).
test_case([], let(add, x->y->123, add@123@123), ok(nat)).
test_case([x-forall([], nat)], x, ok(nat)).


test :-
    % Test that all expected successes suceed.
    forall(
        test_case(Tcx1, Tm, ok(ExpectedTy)),
        (
            initial_tcx(Tcx0),
            append(Tcx0, Tcx1, Tcx),
            catch(inference(Tcx, Tm, ActualTy), Err,
                (
                    format('!!! Error encountered during test:~n'),
                    format('  Tm = ~p~n', [Tm]),
                    format('  Err = ~p~n~n', [Err])
                )
            )
        ->
            (
                ExpectedTy =@= ActualTy, !
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
        test_case(Tcx1, Tm, failure(Msg)),
        (
            initial_tcx(Tcx0),
            append(Tcx0, Tcx1, Tcx),
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
