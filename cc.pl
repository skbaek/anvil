:- [basic].

:- op(1130, xfy, <=>). % equivalence
:- op(1110, xfy, =>).  % implication
:- op(1110, xfy, &).   % conjunction
:- op( 500, fy, ~).    % negation
:- op( 500, fy, !).    % universal quantifier
:- op( 500, fy, ?).    % existential quantifier
:- op( 500, xfy, :).

all_sub_terms(Term, Terms) :-
  findall(SubTerm, sub_term(SubTerm, Term), SubTerms),
  sort(SubTerms, Terms).

atom_sub_terms($false, []) :- !.
atom_sub_terms($true,  []) :- !.
atom_sub_terms(Atom, Terms) :-
  Atom =.. [_ | Args],
  maplist(all_sub_terms, Args, Termss),
  union(Termss, TempTerms),
  sort(TempTerms, Terms).

lits_sub_terms(Lits, Terms) :- 
  maplist(unneg, Lits, Atoms),
  maplist(atom_sub_terms, Atoms, Termss),
  union(Termss, Terms).

member_tree(Elem, elem(Elem)).
member_tree(Elem, bridge(EC, _, _)) :- 
  member_tree(Elem, EC).
member_tree(Elem, bridge(_, _, EC)) :- 
  member_tree(Elem, EC).
member_ec(Elem, (Tree, _)) :-
  member_tree(Elem, Tree).

% Propagate the effects of equating TermA and TermB
propagate((TermA, Prf, TermB), ECs, NewECs) :- 
  pick(member_ec(TermA), ECs, ECL, ECs1),
  pick(member_ec(TermB), ECs1, ECR, ECs2),
  ECL = (TreeL, SupsL),
  ECR = (TreeR, SupsR),
  union(SupsL, SupsR, Sups),
  list_prod(SupsL, SupsR, SupPairs), 
  ECs3 = [(bridge(TreeL, (TermA, Prf, TermB), TreeR), Sups) | ECs2], 
  collect(mono_eqprf(ECs3), SupPairs, EqPrfs), 
  foldl(propagate, EqPrfs, ECs3, NewECs).
  
mono_eqprf(ECs, (TermA, TermB), (TermA, Prf, TermB)) :- 
  mono_eq(ECs, TermA, TermB, Prf). 

% Prove TermA = TermB by monotonicity + equivalences classes
mono_imp(ECs, AtomA, AtomB, ImpPrf) :- 
  AtomA =.. [Rel | TermsA],
  AtomB =.. [Rel | TermsB],
  length(TermsA, Lth),
  mk_mono_rel(Lth, Rel, Mono), 
  mono_ecs(ECs, Mono, TermsA, TermsB, ImpPrf).

% Prove TermA = TermB by monotonicity + equivalences classes
mono_eq(ECs, TermA, TermB, EqPrf) :- 
  TermA =.. [Fun | TermsA],
  TermB =.. [Fun | TermsB],
  length(TermsA, Lth),
  mk_mono_fun(Lth, Fun, Mono), 
  mono_ecs(ECs, Mono, TermsA, TermsB, EqPrf).

mono_ecs(_, (AtomA => AtomB), [], [], beta((AtomA => AtomB), close, close)). 

mono_ecs(_, (_ = _), [], [], close).

mono_ecs(ECs, Mono, [TermA | TermsA], [TermB | TermsB], 
  gamma(TermA, Mono, 
    gamma(TermB, MonoA, 
      beta(MonoAB, PrfA, PrfB)))) :-
  break_gamma(TermA, Mono, MonoA),
  break_gamma(TermB, MonoA, MonoAB),
  MonoAB = (_ => NewMono),
  ecs_eq(ECs, TermA, TermB, PrfA),
  mono_ecs(ECs, NewMono, TermsA, TermsB, PrfB).

ecs_eq(ECs, TermA, TermB, Prf) :- 
  first(ec_eq(TermA, TermB), ECs, Prf).

ec_eq(TermA, TermB, (Tree, _), Eqn) :- 
  et_eq(TermA, TermB, Tree, Eqn).

et_eq(Term, Term, elem(Term), gamma(Term, (! 0: (#(0) = #(0))), close)).

et_eq(TermA, TermB, bridge(TreeL, (TermL, PrfLR, TermR), TreeR), PrfAB) :- 
  ( member_tree(TermA, TreeL), 
    member_tree(TermB, TreeL), 
    et_eq(TermA, TermB, TreeL, PrfAB) ) ; 
  ( member_tree(TermA, TreeR), 
    member_tree(TermB, TreeR), 
    et_eq(TermA, TermB, TreeR, PrfAB) ) ; 
  ( et_eq(TermA, TermL, TreeL, PrfL), 
    et_eq(TermR, TermB, TreeR, PrfR), 
    prove_eqs_trans([TermA, TermL, TermR, TermB], [PrfL, PrfLR, PrfR], TermB, PrfAB) ) ;
  ( et_eq(TermL, TermB, TreeL, PrfLB), 
    et_eq(TermA, TermR, TreeR, PrfAR), 
    prove_eq_symm(TermL, PrfLR, TermR, PrfRL),
    prove_eqs_trans([TermA, TermR, TermL, TermB], [PrfAR, PrfRL, PrfLB], TermB, PrfAB) ).

prove_eqs_trans([_, TermB], [Prf], TermB, Prf). 

prove_eqs_trans([TermA, TermB | Terms], [PrfAB | Prfs], TermC, Prf) :-
  prove_eqs_trans([TermB | Terms], Prfs, TermC, PrfBC), 
  prove_eq_trans(TermA, PrfAB, TermB, PrfBC, TermC, Prf, close).

cc(EqHyps, ECs, NewECs) :- 
  foldl(propagate, EqHyps, ECs, NewECs).

direct_sub_term(SubTerm, Term) :-
  Term =.. [_ | Args],
  member(SubTerm, Args).

init_ec(Terms, Term, (elem(Term), Sups)) :- 
  include(direct_sub_term(Term), Terms, Sups).

init_ecs(Terms, ECs) :- 
  maplist(init_ec(Terms), Terms, ECs).

mk_eqhyp((TermA = TermB), (TermA, close, TermB)).

eq_mod_ec(TermA, TermB, EC) :- 
  member_ec(TermA, EC),
  member_ec(TermB, EC).

eq_mod_ecs(ECs, TermA, TermB) :- 
  any(eq_mod_ec(TermA, TermB), ECs).

eqv_mod_ecs(ECs, AtomA, AtomB) :- 
  AtomA =.. [Rel | TermsA],
  AtomB =.. [Rel | TermsB],
  maplist(eq_mod_ecs(ECs), TermsA, TermsB).

ecs_lits_prf(ECs, Lits, Prf) :- 
  member(~ (TermA = TermB), Lits),
  eq_mod_ecs(ECs, TermA, TermB),
  ecs_eq(ECs, TermA, TermB, Prf).

ecs_lits_prf(ECs, Lits, Prf) :- 
  member(AtomA, Lits),
  not(AtomA = ~ _), 
  member(~ AtomB, Lits),
  eqv_mod_ecs(ECs, AtomA, AtomB), 
  mono_imp(ECs, AtomA, AtomB, Prf).

lits_ecs(Lits, ECs) :- 
  lits_sub_terms(Lits, Terms),
  init_ecs(Terms, InitECs), 
  collect(mk_eqhyp, Lits, EqHyps),
  cc(EqHyps, InitECs, ECs).


close_cc(Lits, Prf) :- 
  lits_sub_terms(Lits, Terms),
  init_ecs(Terms, InitECs), 
  collect(mk_eqhyp, Lits, EqHyps),
  cc(EqHyps, InitECs, ECs),
  ecs_lits_prf(ECs, Lits, Prf), !.
