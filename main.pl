:- [basic, cc].

:- op(1130, xfy, <=>). % equivalence
:- op(1110, xfy, =>).  % implication
:- op(1110, xfy, &).   % conjunction
:- op( 500, fy, ~).    % negation
:- op( 500, fy, !).    % universal quantifier
:- op( 500, fy, ?).    % existential quantifier
:- op( 500, xfy, :).

theorem(_, _).
fof(_, _, _, _).

number_letter(Num, "x") :- 0 is Num mod 6.
number_letter(Num, "y") :- 1 is Num mod 6.
number_letter(Num, "z") :- 2 is Num mod 6.
number_letter(Num, "w") :- 3 is Num mod 6.
number_letter(Num, "v") :- 4 is Num mod 6.
number_letter(Num, "u") :- 5 is Num mod 6.

number_subscript(Num, Sub) :-
  Quo is Num div 6,
  number_string(Quo, Sub).

var_atom(Num, Atom) :-
  number_letter(Num, Ltr),
  number_subscript(Num, Sub),
  string_concat(Ltr, Sub, Str),
  atom_string(Atom, Str).

fix_variables(_, []).

fix_variables(Num, [X | Xs]) :-
  var_atom(Num, X),
  SuccNum is Num + 1,
  fix_variables(SuccNum, Xs).

form_string(Frm, Str) :- 
  copy_term(Frm, CopyFrm),
  term_variables(CopyFrm, Vars),
  fix_variables(0, Vars),
  term_string(CopyFrm, Str).

index_form_string(Num, Frm, Str) :- 
  number_string(Num, NumStr),
  form_string(Frm, FrmStr),
  strings_concat(["[", NumStr, "] ", FrmStr, "\n"], Str).

uses(_, Var) :- 
  var(Var), !, false.

uses(Symb, [Elem | List]) :- !, 
  uses(Symb, Elem);
  uses(Symb, List).  

uses(Symb, ~ Frm) :- !, 
  uses(Symb, Frm).

uses(Symb, FrmA & FrmB) :- !,
  uses(Symb, FrmA);
  uses(Symb, FrmB).
  
uses(Symb, FrmA | FrmB) :- !,
  uses(Symb, FrmA);
  uses(Symb, FrmB).

uses(Symb, FrmA => FrmB) :- !,
  uses(Symb, FrmA);
  uses(Symb, FrmB).

uses(Symb, FrmA <=> FrmB) :- !,
  uses(Symb, FrmA);
  uses(Symb, FrmB).

uses(Symb, ! _ : Frm) :- !, 
  uses(Symb, Frm).

uses(Symb, ? _ : Frm) :- !, 
  uses(Symb, Frm).

uses(Symb, Exp) :- 
  Exp =.. [Symb | _].

uses(Symb, Exp) :- 
  Exp =.. [_ | Terms],
  uses(Symb, Terms).

uses_any([Symb | Symbs], Frm) :- 
  uses(Symb, Frm);
  uses_any(Symbs, Frm).

translate(Num, ~ TPTP, ~ Form) :- !, 
 translate(Num, TPTP, Form).

translate(Num, (! [#(Num)] : TPTP), (! Num : Form))  :- !, 
  Succ is Num + 1,
  translate(Succ, TPTP, Form).

translate(Num, (! [#(Num) | Vars] : TPTP), (! Num : Form))  :- !, 
  Succ is Num + 1,
  translate(Succ, ! Vars : TPTP, Form).

translate(Num, (? [#(Num)] : TPTP), (? Num : Form))  :- !, 
  Succ is Num + 1,
  translate(Succ, TPTP, Form).

translate(Num, (? [#(Num) | Vars] : TPTP), (? Num : Form))  :- !, 
  Succ is Num + 1,
  translate(Succ, ? Vars : TPTP, Form).

translate(_, (TPTP_A \= TPTP_B), ~ (TermA = TermB)) :- !,
  translate(TPTP_A, TermA),
  translate(TPTP_B, TermB).

translate(Num, TPTP, Form) :- 
  TPTP =.. [Conn, TPTP_A, TPTP_B],
  member(Conn, [&, '|', =>, <=>]), !,
  translate(Num, TPTP_A, FormA),
  translate(Num, TPTP_B, FormB),
  Form =.. [Conn, FormA, FormB].

translate(_, TPTP, Form) :- !,
  TPTP =.. [Rel | TPTPs], 
  maplist(translate, TPTPs, Terms),
  Form =.. [Rel | Terms].

translate(TPTP, Term) :- !,
  TPTP =.. [Fun | TPTPs], 
  maplist(translate, TPTPs, Terms),
  Term =.. [Fun | Terms].

prove_args(['-p', Source, Target | _], Source, Target).
prove_args([_ | Argv], Source, Target) :-
  prove_args(Argv, Source, Target).

verify_args(['-v', Source | _], Source).
verify_args([_ | Argv], Source) :-
  verify_args(Argv, Source).
 
help_msg :-
  write(
"=========== Usage ==========\n
Call Kes using\n 
  kes -p [source] [target]\n
to import a TSTP proof from\n 
[source] and save the compiled\n 
proof at [target]\n
  kes -v [source]\n
to verify a proof at [target]\n
=========== End ==========\n"
  ).

% main(Argv) :-
%   dynamic(theorem/2),
%   dynamic(fof/4),
%   (
%     ( prove_args(Argv, Source, Target), 
%       prove_save(Source, Target) ) ;
%     ( verify_args(Argv, Source), 
%       verify(Source) ) ;
%     help_msg
%   ).

% prove_save(Source, Target) :-
%   retractall(fof(_, _, _, _)),
%   consult(Source),
%   fof(Id,_, $false, _),
%   id_tree(Id, Tree),
%   prove((Tree, [], []), (Smt, _, Prf)),
%   punctuate(theorem(Smt, Prf), Str),
%   write_file(Target, Str).

literal(~ Atom) :- 
  propatom(Atom).

literal(Atom) :- 
  propatom(Atom).

id_form(Id, Form) :- 
  fof(Id, _, TPTP, _),
  translate(0, TPTP, Form).

eq(X, X).

ground_all(Term) :- 
  term_variables(Term, Vars),
  maplist(eq(c), Vars).

superpositional(Rul) :-
  member(
    Rul,
    [
      superposition,
      forward_demodulation,
      backward_demodulation
    ]
  ).

resolutional(Rul) :-
  member(
    Rul,
    [
      resolution,
      subsumption_resolution
      % superposition
      % forward_demodulation,
      % backward_demodulation
    ]
  ).

simple_fol(Rul) :-
  member(
    Rul,
    [
      cnf_transformation,
      ennf_transformation,
      avatar_sat_refutation,
      avatar_contradiction_clause,
      avatar_component_clause,
      flattening,
      rectify,
      skolemisation
    ]
  ).

splitting(Rul) :-
  member(
    Rul,
    [
      avatar_split_clause
    ]
  ).

linear(Par, [], Prf, Par, [], Prf). 

linear(Par, [Form | Forms], Prf, NewPar, Lits, SubPrf) :-
  linear(Par, Form, Prf, TempPar, LitsA, TempPrf),
  linear(TempPar, Forms, TempPrf, NewPar, LitsB, SubPrf),
  append(LitsA, LitsB, Lits).

linear(Par, Form, delta(@(Par, []), Form, Prf), NewPar, Lits, SubPrf) :- 
  break_delta(@(Par, []), Form, NewForm), 
  Succ is Par + 1, 
  linear(Succ, NewForm, Prf, NewPar, Lits, SubPrf).

linear(Par, Form, alpha(Form, Prf), NewPar, Lits, SubPrf) :- 
  break_alpha(Form, FormA, FormB), 
  linear(Par, FormA, Prf, ParA, LitsA, SubPrfA), 
  linear(ParA, FormB, SubPrfA, NewPar, LitsB, SubPrf),
  append(LitsA, LitsB, Lits).

linear(Par, ~ ~ Form, dne(~ ~ Form, Prf), NewPar, Lits, SubPrf) :- 
  linear(Par, Form, Prf, NewPar, Lits, SubPrf). 

linear(Par, Lit, Prf, Par, [Lit], Prf) :- 
  literal(Lit).

split(Prem, Defs, Conc, Prf) :- 
  linear(0, ~ Conc, Prf, Par, Lits, SubPrf), 
  split(Prem, Par, [], Lits, Defs, SubPrf).

split(Prem, Par, Forms, Lits, [Def | Defs], alpha(Def, Prf)) :- 
  break_alpha(Def, (Atom => Form), (Form => Atom)), 
  (
    member(Atom, Lits) -> 
    (
      Prf = beta(Atom => Form, close, SubPrf),
      split(Prem, Par, [Atom, Form | Forms], Lits, Defs, SubPrf)
    ) ;
    (
      member(~ Atom, Lits) -> 
      (
        Prf = beta(Form => Atom, PrfA, close),
        linear(Par, ~ Form, PrfA, NewPar, NewLits, PrfB),
        append([~ Atom | NewLits], Forms, NewForms),
        split(Prem, NewPar, NewForms, Lits, Defs, PrfB)
      ) ;
      false
    ) 
  ).

split(Prem, _, Lits, _, [], Prf) :- 
  close_clause(Lits, Prem, Prf).

close_goal(Lits, (Lit, Prf)) :- 
  close_lit(Lits, Lit, Prf).

decom_clause(Cla, gamma(Term, Cla, Prf), Goals) :- 
  break_gamma(Term, Cla, NewCla), 
  decom_clause(NewCla, Prf, Goals).

decom_clause((ClaA | ClaB), beta((ClaA | ClaB), PrfA, PrfB), Goals) :- 
  decom_clause(ClaA, PrfA, GoalsA),
  decom_clause(ClaB, PrfB, GoalsB),
  append(GoalsA, GoalsB, Goals).

decom_clause(Lit, Prf, [(Lit, Prf)]) :-
  literal(Lit).

break_clause(Cla, Lits) :- 
  decom_clause(Cla, _, Goals), 
  maplist(fst, Goals, Lits).

fst((X, _), X).
snd((_, Y), Y).

contains(List, Elem) :- member(Elem, List).

subset_except_one([Elem | Sub], List, Elem) :- 
  subset(Sub, List).

subset_except_one([ElemA | Sub], List, ElemB) :- 
  member(ElemA, List),
  subset_except_one(Sub, List, ElemB). 
  
find_pivots(Lits, ClaA, ClaB, LitA, LitB) :- 
  maplist(invert, Lits, CmpLits),
  break_clause(ClaA, LitsA),
  break_clause(ClaB, LitsB),
  subset_except_one(LitsA, CmpLits, LitA), 
  subset_except_one(LitsB, CmpLits, LitB).

find_pivot(FormA, FormB, FormB, FormA, Atom) :- 
  break_clause(FormA, LitsA),
  break_clause(FormB, LitsB),
  member(~ Atom, LitsA), 
  member(Atom, LitsB).

find_pivot(FormA, FormB, FormA, FormB, Atom) :- 
  break_clause(FormA, LitsA),
  break_clause(FormB, LitsB),
  member(Atom, LitsA), 
  member(~ Atom, LitsB).

resolution(ClaA, ClaB, ClaC, Prf) :- 
  find_pivot(ClaA, ClaB, ClaP, ClaN, Atom),
  linear(0, ~ ClaC, Prf, _, Lits, cut(Atom, PrfA, PrfB)), 
  close_clause([Atom | Lits], ClaN, PrfA),
  close_clause([~ Atom | Lits], ClaP, PrfB).

prove_imp_super(AtomA, TermA = TermB, AtomB, Prf) :-
  propatom(AtomA),
  propatom(AtomB),
  prove_imp_super(AtomA, TermA, TermB, AtomB, Prf).

prove_imp_super(~ AtomA, TermA = TermB, ~ AtomB, Prf) :- 
  prove_imp_super(AtomB, TermA, TermB, AtomA, Prf).

prove_imp_super(AtomA, TermL, TermR, AtomB, Prf) :- 
  AtomA =.. [Rel | TermsA],
  AtomB =.. [Rel | TermsB],
  length(TermsA, Lth),
  mk_mono_rel(Lth, Rel, Mono), 
  prove_imp_super(TermsA, TermL, TermR, TermsB, Mono, Prf). 

prove_eq_super(Term, _, _, Term, Prf) :- 
  prove_eq_refl(Term, Prf).

prove_eq_super(TermA, TermA, TermB, TermB, close). 

prove_eq_super(TermA, TermB, TermA, TermB, Prf) :-
  prove_eq_symm(TermB, close, TermA, Prf).

prove_eq_super(TermA, TermL, TermR, TermB, Prf) :-
  \+ var(TermA),
  \+ var(TermB),
  TermA =.. [Fun | TermsA],
  TermB =.. [Fun | TermsB],
  length(TermsA, Lth),
  mk_mono_fun(Lth, Fun, Mono), 
  prove_eq_super(TermsA, TermL, TermR, TermsB, Mono, Prf).

prove_eq_super([], _, _, [], _ = _, close).

prove_eq_super([TermA | TermsA], TermL, TermR, [TermB | TermsB], Mono, 
  gamma(TermA, Mono, 
    gamma(TermB, MonoA, 
      beta(MonoAB, PrfA, PrfB)))) :-
  break_gamma(TermA, Mono, MonoA),
  break_gamma(TermB, MonoA, MonoAB),
  MonoAB = (_ => NewMono),
  prove_eq_super(TermA, TermL, TermR, TermB, PrfA),
  prove_eq_super(TermsA, TermL, TermR, TermsB, NewMono, PrfB). 

prove_imp_super([], _, _, [], (AtomA => AtomB), beta(AtomA => AtomB, close, close)). 

prove_imp_super([TermA | TermsA], TermL, TermR, [TermB | TermsB], Mono, 
  gamma(TermA, Mono, 
    gamma(TermB, MonoA, 
      beta(MonoAB, PrfA, PrfB)))) :-
  break_gamma(TermA, Mono, MonoA),
  break_gamma(TermB, MonoA, MonoAB),
  MonoAB = (_ => NewMono),
  prove_eq_super(TermA, TermL, TermR, TermB, PrfA),
  prove_imp_super(TermsA, TermL, TermR, TermsB, NewMono, PrfB). 

choose_direction(Lit, Prf, Lit, Prf). 

choose_direction(TermA = TermB, Prf, TermB = TermA, NewPrf) :- 
  prove_eq_symm(TermA, close, TermB, Prf, NewPrf). 

choose_lits(Lit, TermA = TermB, Prf, NewLit, TermA = TermB, NewPrf) :- 
  choose_direction(Lit, Prf, NewLit, NewPrf).

choose_lits(TermA = TermB, Lit, Prf, NewLit, TermA = TermB, NewPrf) :- 
  choose_direction(Lit, Prf, NewLit, NewPrf).

superposition(ClaA, ClaB, ClaC, Prf) :- 
  linear(0, ~ ClaC, Prf, _, Lits, cut(CmpA, PrfA, cut(CmpB, PrfB, PrfC))), 
  find_pivots(Lits, ClaA, ClaB, LitA, LitB),
  member(LitT, Lits), 
  invert(LitA, CmpA),
  invert(LitB, CmpB),
  invert(LitT, CmpT),
  linear(_, [~ CmpB, ~ CmpA], PrfC, _, _, PrfD), % Literals available at this point : LitA, LitB, LitT
  choose_lits(LitA, LitB, PrfD, LitS, LitE, PrfE), % Choose the source literal LitS (i.e., the literal which 
                                                   % is equal to the target literal LitT modulo LitE), the
                                                   % equality literal LitE, and the direction in which LitS
                                                   % is to be used (which may vary if LitS is an equality).  
  prove_imp_super(LitS, LitE, CmpT, PrfE), % Prove that LitS plus LitE impies CmpT. Since LitT is already available 
                                           % on the branch, this means LitS and LitE are jointly contradictory.
  close_clause([CmpA | Lits], ClaA, PrfA),
  close_clause([CmpB | Lits], ClaB, PrfB).

tableaux(Forms, Lim, Par, Terms, Mode, Lems, Pth, ~ ~ Form, NewLems, dne(~ ~ Form, Prf)) :- 
  tableaux(Forms, Lim, Par, Terms, Mode, Lems, Pth, Form, NewLems, Prf).

tableaux(Forms, Lim, Par, Terms, Mode, Lems, Pth, Form, NewLems, alpha(Form, Prf)) :- 
  break_alpha(Form, FormA, FormB), 
  ( tableaux([FormB | Forms], Lim, Par, Terms, Mode, Lems, Pth, FormA, NewLems, Prf) ; 
    tableaux([FormA | Forms], Lim, Par, Terms, Mode, Lems, Pth, FormB, NewLems, Prf) ).

tableaux(Forms, Lim, Par, Terms, block, Lems, Pth, Form, NewLems, beta(Form, PrfA, PrfB)) :- 
  break_beta(Form, FormA, FormB), 
  tableaux(Forms, Lim, Par, Terms, block, Lems, Pth, FormA, TempLems, PrfA), 
  tableaux(Forms, Lim, Par, Terms, block, TempLems, Pth, FormB, NewLems, PrfB).

tableaux(Forms, Lim, Par, Terms, match, Lems, Pth, Form, NewLems, beta(Form, PrfA, PrfB)) :- 
  break_beta(Form, FormA, FormB), 
  (
    ( tableaux(Forms, Lim, Par, Terms, match, Lems, Pth, FormA, TempLems, PrfA), 
      tableaux(Forms, Lim, Par, Terms, block, TempLems, Pth, FormB, NewLems, PrfB) ) ;  
    ( tableaux(Forms, Lim, Par, Terms, match, Lems, Pth, FormB, TempLems, PrfB), 
      tableaux(Forms, Lim, Par, Terms, block, TempLems, Pth, FormA, NewLems, PrfA) ) 
  ).

tableaux(Forms, Lim, Par, Terms, Mode, Lems, Pth, FaForm, NewLems, gamma(Term, FaForm, Prf)) :- 
  break_gamma(Term, FaForm, Form), 
  tableaux([FaForm | Forms], Lim, Par, [Term | Terms], Mode, Lems, Pth, Form, NewLems, Prf).

tableaux(Forms, Lim, Par, Terms, Mode, Lems, Pth, ExForm, NewLems, delta(@(Par, Terms), ExForm, Prf)) :- 
  break_delta(@(Par, Terms), ExForm, Form), 
  Succ is Par + 1,
  tableaux(Forms, Lim, Succ, Terms, Mode, Lems, Pth, Form, NewLems, Prf).

tableaux(Forms, Lim, Par, Terms, block, Lems, Pth, Lit, NewLems, Prf) :- 
  literal(Lit), 
  (
    close_lit(Pth, Lit, Prf) -> 
    (NewLems = Lems) ;
    (
      find_lemma(Lems, Lit, Prf) -> % Lemmata check
      (NewLems = Lems) ;
      ( 
        decr_if_pos(Lim, Pred),
        not(occurs(Lit, Pth)), % Regularity check
        pluck(Forms, Form, Rem),
        tableaux(Rem, Pred, Par, Terms, match, Lems, [Lit | Pth], Form, _, Prf),
        NewLems = [(Lit, Prf) | Lems]
      )
    ) 
  ).

% If in match-mode, the newly focused literal must match with the
% previously focused literal.
tableaux(_, _, _, _, match, Lems, [Cmp | _], Lit, Lems, Prf) :- 
  literal(Lit), 
  close_lit([Cmp], Lit, Prf).

tableaux(Forms, Lim, Prf) :- 
  pluck(Forms, Form, Rem),
  tableaux(Rem, Lim, 0, [], block, [], [$true, ~ $false], Form, _, Prf).

tableaux(Forms, 10, timeout(Forms)).

tableaux(Forms, Lim, Prf) :- 
  Succ is Lim + 1,
  tableaux(Forms, Succ, Prf).

tableaux(Forms, Prf) :- 
  % add_eq_axioms(Forms, NewForms),
  tableaux(Forms, 5, Prf).

find_lemma(Lems, LitA, Prf) :-
  member((LitB, Prf), Lems), 
  LitA == LitB.

close_lit(Lits, Lit, close) :-
  member(Cmp, Lits),
  complementary(Lit, Cmp).

close_lit(Lits, (TermA = TermB), Prf) :-
  member(Cmp, Lits),
  complementary(Cmp, (TermB = TermA)),
  prove_eq_symm(TermA, close, TermB, Prf, close).

invert(~ Form, Form).

invert(Form, ~ Form) :-
  not(Form = ~ _).

complementary(~ FormA, FormB) :- !,
  unify_with_occurs_check(FormA, FormB).
  
complementary(FormA, ~ FormB) :- !,
  unify_with_occurs_check(FormA, FormB).

undup(Prem, Conc, Prf) :-
  linear(0, ~ Conc, Prf, _, Lits, SubPrf), 
  close_clause(Lits, Prem, SubPrf).

apply_ac(Prems, Conc, 
  delta(c, ~ Conc, 
    gamma(c, FormFA, 
      gamma(c, FormFAB, 
        beta(FormA => FormB, close, close)
      )
    )   
  )) :-
  break_delta(c, ~ Conc, ~ FormB),
  member(FormFAB, Prems),
  break_gamma(c, FormFAB, FormA => FormB), 
  member(FormFA, Prems),
  break_gamma(c, FormFA, FormA). 

close_clause(Lits, Cla, Prf) :- 
  decom_clause(Cla, Prf, Goals), 
  maplist(close_goal(Lits), Goals). 

elab((Prems, Conc, Rul), (Prf, Conc)) :-
  elab_eva(Prems, Conc, Rul, Prf), 
  ground_all(Prf). 

elab((Prems, Conc, Rul), admit(Prems, Conc, Rul)).

elab_eva(Prems, Conc, skolemisation, Prf) :- 
  apply_ac(Prems, Conc, Prf).

elab_eva([Prem], Conc, duplicate_literal_removal, Prf) :- 
  undup(Prem, Conc, Prf).

elab_eva([~ (Term = Term)], _, trivial_inequality_removal, Prf) :- 
   prove_eq_refl(Term, Prf).

elab_eva([Form], Form, _, close).

elab_eva([Prem | Prems], Conc, Rul, Prf) :- 
  splitting(Rul),
  split(Prem, Prems, Conc, Prf).

elab_eva([PremA, PremB], Conc, Rul, Prf) :- 
  resolutional(Rul),
  resolution(PremA, PremB, Conc, Prf).

elab_eva([ClaA, ClaB], ClaC, Rul, Prf) :- 
  superpositional(Rul),
  superposition(ClaA, ClaB, ClaC, Prf).

elab_eva(Prems, Conc, Rul, Prf) :- 
  simple_fol(Rul),
  tableaux([~ Conc | Prems], Prf).

has_eq(Exp) :-
  Exp =.. ['=' | _].

has_eq(Exp) :-
  Exp =.. [_ | Args],
  any(has_eq, Args).

stitch([(Prf, $false)], Prf).

stitch([(PrfA, Conc) | Prfs], cut(Conc, PrfB, PrfA)) :- 
  stitch(Prfs, PrfB).

extra_prems(Bch, cut(Form, PrfA, PrfB), Hyps) :-
  extra_prems([Form | Bch], PrfA, HypsA),
  extra_prems([~ Form | Bch], PrfB, HypsB),
  union(HypsA, HypsB, Hyps).

extra_prems(Bch, dne(~ ~ Form, Prf), Hyps) :-
  extra_prems([Form | Bch], Prf, TempHyps),
  ( member(~ ~ Form, Bch) -> 
    Hyps = TempHyps ;
    sort([~ ~ Form | TempHyps], Hyps) ).

extra_prems(Bch, alpha(Form, Prf), Hyps) :-
  break_alpha(Form, FormA, FormB), 
  extra_prems([FormB, FormA | Bch], Prf, TempHyps),
  ( member(Form, Bch) -> 
    Hyps = TempHyps ;
    sort([Form | TempHyps], Hyps) ).

extra_prems(Bch, beta(Form, PrfA, PrfB), Hyps) :-
  break_beta(Form, FormA, FormB), 
  extra_prems([FormA | Bch], PrfA, HypsA),
  extra_prems([FormB | Bch], PrfB, HypsB),
  union(HypsA, HypsB, TempHyps),
  ( member(Form, Bch) -> 
    Hyps = TempHyps ;
    sort([Form | TempHyps], Hyps) ).

extra_prems(Bch, gamma(Term, Form, Prf), Hyps) :-
  break_gamma(Term, Form, SubForm), 
  extra_prems([SubForm | Bch], Prf, TempHyps),
  ( member(Form, Bch) -> 
    Hyps = TempHyps ;
    sort([Form | TempHyps], Hyps) ).

extra_prems(Bch, delta(Term, Form, Prf), Hyps) :-
  break_delta(Term, Form, SubForm), 
  extra_prems([SubForm | Bch], Prf, TempHyps),
  ( member(Form, Bch) -> 
    Hyps = TempHyps ;
    sort([Form | TempHyps], Hyps) ).

extra_prems(_, close, []).

annotate_aug(Form, aug(Form, Rul)) :- 
  aug_type(Form, Rul).

extra_augs(Trunk, Prf, Augs) :- 
  extra_prems(Trunk, Prf, Prems), 
  maplist(annotate_aug, Prems, Augs).

% Def
% Skm
% DNE
% Alpha
% Beta
% Gamma
% Delta
% Cut
% Close

number_prf(Bch, hyp(Form, Prf), hyp(Form, NumPrf)) :- 
  number_prf([Form | Bch], Prf, NumPrf).

number_prf(Bch, aug(Form, Rul, Prf), aug(Form, Rul, NumPrf)) :- 
  number_prf([Form | Bch], Prf, NumPrf).

number_prf(Bch, cut(Form, PrfA, PrfB), cut(Form, NumPrfA, NumPrfB)) :- 
  number_prf([Form | Bch], PrfA, NumPrfA), !,
  number_prf([~ Form | Bch], PrfB, NumPrfB). 

number_prf(Bch, dne(~ ~ Form, Prf), dne(Num, NumPrf)) :- 
  nth0(Num, Bch, ~ ~ Form),
  number_prf([Form | Bch], Prf, NumPrf).

number_prf(Bch, alpha(Form, Prf), alpha(Num, NumPrf)) :- 
  nth0(Num, Bch, Form),
  break_alpha(Form, FormA, FormB),
  number_prf([FormB, FormA | Bch], Prf, NumPrf).

number_prf(Bch, beta(Form, PrfA, PrfB), beta(Num, NumPrfA, NumPrfB)) :- 
  nth0(Num, Bch, Form),
  break_beta(Form, FormA, FormB),
  number_prf([FormA | Bch], PrfA, NumPrfA), !,
  number_prf([FormB | Bch], PrfB, NumPrfB). 

number_prf(Bch, gamma(Term, FaForm, Prf), gamma(Term, Num, NumPrf)) :- 
  nth0(Num, Bch, FaForm),
  break_gamma(Term, FaForm, Form),
  number_prf([Form | Bch], Prf, NumPrf).

number_prf(Bch, delta(Term, ExForm, Prf), delta(Term, Num, NumPrf)) :- 
  nth0(Num, Bch, ExForm),
  break_delta(Term, ExForm, Form),
  number_prf([Form | Bch], Prf, NumPrf).

number_prf(Bch, close, close(Num)) :- 
  nth0(Num, Bch, ~ $true).

number_prf(Bch, close, close(Num)) :- 
  nth0(Num, Bch, $false).

number_prf(Bch, close, close(NumP, NumN)) :- 
  nth0(NumN, Bch, ~ AtomA),
  nth0(NumP, Bch, AtomB),
  not(AtomB = ~ _),
  unify_with_occurs_check(AtomA, AtomB), !.

hyp(Hyp) :- 
  fof(_, Type, TPTP, _),
  member(Type, [axiom, negated_conjecture]),
  translate(0, TPTP, Hyp).

aug(Form, ac(Skm)) :- 
  fof(_, _, TPTP, introduced(choice_axiom, _)),
  aoc_skolem_fun_tptp(TPTP, Skm),
  translate(0, TPTP, Form).

aug(Form, def) :- 
  fof(_, _, TPTP, introduced(avatar_definition, _)),
  translate(0, TPTP, Form).

goal(Prems, Conc, Rul) :- 
  fof(_, _, TPTP, inference(Rul, _, Ids)),
  not(Rul = negated_conjecture),
  translate(0, TPTP, Conc),
  maplist(id_form, Ids, Prems).

remove_params(@(Num, _), Const) :- 
  number_string(Num, NumStr),
  string_concat("c", NumStr, ConstStr), 
  atom_string(Const, ConstStr).

remove_params(Atom, Atom) :-
  atom(Atom).

remove_params(Exp, NewExp) :-
  Exp =.. [Head | Args], 
  maplist(remove_params, Args, NewArgs),
  NewExp =.. [Head | NewArgs].

prepend([hyp(Form) | Stock], Prf, hyp(Form, NewPrf)) :-
  prepend(Stock, Prf, NewPrf).

prepend([aug(Form, Rul) | Stock], Prf, aug(Form, Rul, NewPrf)) :-
  prepend(Stock, Prf, NewPrf).

prepend([], Prf, Prf).

hyp_form(hyp(Form), Form).
aug_form(aug(Form, _), Form).

stitch(Hyps, Augs, Prfs, Prf) :- 
  stitch(Prfs, PrfA), !,
  remove_params(PrfA, PrfB), !,
  maplist(hyp_form, Hyps, HypForms), !,
  maplist(aug_form, Augs, AugForms), !,
  append(HypForms, AugForms, Forms), !,
  extra_augs(Forms, PrfB, Augss), !,
  append([Hyps, Augs, Augss], Stock), !,
  prepend(Stock, PrfB, PrfC), !,
  number_prf([], PrfC, Prf).

prove(Source) :-
  dynamic(fof/4),
  retractall(fof(_, _, _, _)),
  consult(Source),
  findall(hyp(Form), hyp(Form), Hyps),
  findall(aug(Form, Rul), aug(Form, Rul), Augs),
  findall((Prems, Conc, Rul), goal(Prems, Conc, Rul), Goals),
  maplist(elab, Goals, Prfs), !,
  stitch(Hyps, Augs, Prfs, Prf), 
  write_file_punct("output", proof(Prf)).
  % list_br_str(Prfs, Str),
  % write_file("output", Str).

mapcut(Goal, [Elem | List]) :- 
  call(Goal, Elem), !, 
  mapcut(Goal, List). 

mapcut(_, []).

precheck_test((Prems, Conc, Rul)) :- 
  elab_eva(Prems, Conc, Rul, Prf),
  precheck([~ Conc | Prems], Prf).

precheck(Bch, dne(~ ~ Form, Prf)) :-
  precheck([Form | Bch], Prf).

precheck(Bch, alpha(Form, Prf)) :-
  break_alpha(Form, FormA, FormB),
  precheck([FormB, FormA | Bch], Prf).
  
precheck(Bch, beta(Form, PrfA, PrfB)) :-
  break_beta(Form, FormA, FormB),
  precheck([FormA | Bch], PrfA), !,
  precheck([FormB | Bch], PrfB).

precheck(Bch, gamma(Term, FaForm, Prf)) :-
  break_gamma(Term, FaForm, Form),
  precheck([Form | Bch], Prf).

precheck(Bch, delta(Const, ExForm, Prf)) :-
  break_delta(Const, ExForm, Form),
  precheck([Form | Bch], Prf).

precheck(Bch, cut(Form, PrfA, PrfB)) :- 
  precheck([Form | Bch], PrfA), !,
  precheck([~ Form | Bch], PrfB).

precheck(Bch, close) :-
  member(AtomA, Bch),
  member(~ AtomB, Bch),
  AtomA == AtomB.

precheck(Bch, close) :-
  member(~ $true, Bch).

precheck(Bch, close) :-
  member($false, Bch).