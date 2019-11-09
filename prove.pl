:- [basic].

:- op(1130, xfy, <=>). % equivalence
:- op(1110, xfy, =>).  % implication
:- op(1110, xfy, &).   % conjunction
:- op( 500, fy, ~).    % negation
:- op( 500, fy, !).    % universal quantifier
:- op( 500, fy, ?).    % existential quantifier
:- op( 500, xfy, :).

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

/* 
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
*/

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
      backward_demodulation,
      definitional_unfolding
    ]
  ).

resolutional(Rul) :-
  member(Rul, [resolution, subsumption_resolution]).

simple_fol(Rul) :-
  member(
    Rul,
    [ 
      avatar_sat_refutation,
      avatar_contradiction_clause,
      avatar_component_clause,
      flattening,
      rectify
    ]
  ).

splitting(Rul) :-
  member(Rul, [avatar_split_clause]).

% split(Prem, Defs, Conc, Prf) :- 
%   ade_n(0, ([~ Conc], Prf), Par, [(Lits, SubPrf)]), 

% split(Prem, Par, [], Lits, Defs, SubPrf).
 
% split(Prem, Par, Forms, Lits, [Def | Defs], alpha(Def, Prf)) :- 
%   break_alpha(Def, (Atom => Form), (Form => Atom)), 
%   (
%     member(Atom, Lits) -> 
%     (
%       Prf = beta(Atom => Form, close, SubPrf),
%       split(Prem, Par, [Atom, Form | Forms], Lits, Defs, SubPrf)
%     ) ;
%     (
%       member(~ Atom, Lits) -> 
%       (
%         Prf = beta(Form => Atom, PrfA, close),
%         ade_n(Par, [~ Form], PrfA, NewPar, NewLits, PrfB),
%         append([~ Atom | NewLits], Forms, NewForms),
%         split(Prem, NewPar, NewForms, Lits, Defs, PrfB)
%       ) ;
%       false
%     ) 
%   ).
% 
% split(Prem, _, Lits, _, [], Prf) :- 
%   close_clause(Lits, Prem, Prf).

% close_cont(FormsA, (FormsB, Prf)) :- 
%   close_lit(Lits, Lit, Prf).



/* Proof continuation processors */

a_1((Forms, alpha(Form, Prf)), [([FormB, FormA | Rem], Prf)]) :- 
  pluck(Forms, Form, Rem), 
  break_alpha(Form, FormA, FormB).

b_1((Forms, beta(Form, PrfA, PrfB)), [([FormA | Rem], PrfA), ([FormB | Rem], PrfB)]) :- 
  pluck(Forms, Form, Rem),
  break_beta(Form, FormA, FormB).

c_1((Forms, gamma(Term, FaForm, Prf)), [([Form | Rem], Prf)]) :- 
  pluck(Forms, FaForm, Rem),
  break_gamma(Term, FaForm, Form). 

% Caution : this predicate should NOT be used to process continuations 
% that come after any gamma rules, as the parameter for delta rule has
% no arguments and assumes the absence of any free variables.
d_1(Par, (Forms, delta(@(Par, []), ExForm, Prf)), Succ, [([Form | Rem], Prf)]) :- 
  pluck(Forms, ExForm, Rem), 
  break_delta(@(Par, []), ExForm, Form), 
  Succ is Par + 1.

e_1((Forms, dne(~ ~ Form, Prf)), [([Form | Rem], Prf)]) :- 
  pluck(Forms, ~ ~ Form, Rem).

a_n(Cont, Conts) :- 
  a_1(Cont, [NewCont]) -> 
  a_n(NewCont, Conts) ;
  (Conts = [Cont]).

b_n(Cont, Conts) :- 
  b_1(Cont, [ContA, ContB]) -> 
  (
    b_n(ContA, ContsA), 
    b_n(ContB, ContsB), 
    append(ContsA, ContsB, Conts)
  ) ;
  (Conts = [Cont]).

c_n(Cont, Conts) :- 
  c_1(Cont, [NewCont]) -> 
  c_n(NewCont, Conts) ;
  (Conts = [Cont]).

e_n(Cont, Conts) :- 
  e_1(Cont, [NewCont]) -> 
  e_n(NewCont, Conts) ;
  (Conts = [Cont]).

% Apply all applicable alpha and delta rules to 'Forms'. Since it uses d_1, 
% it should NOT be used to construct subproofs that come after any gamma rules.
ade_n(Par, Cont, NewPar, [NewCont]) :- 
  ade_1(Par, Cont, TempPar, [TempCont]) -> 
  ade_n(TempPar, TempCont, NewPar, [NewCont]) ;
  (NewPar = Par, NewCont = Cont).

ade_1(Par, Cont, NewPar, Conts) :-
  d_1(Par, Cont, NewPar, Conts).

ade_1(Par, Cont, Par, Conts) :-
  a_1(Cont, Conts) ;
  e_1(Cont, Conts).

bc_1(Cont, Conts) :-
  b_1(Cont, Conts).

bc_1(Cont, Conts) :-
  c_1(Cont, Conts).

abce_1(Cont, Conts) :-
  a_1(Cont, Conts) ;
  b_1(Cont, Conts) ;
  c_1(Cont, Conts) ;
  e_1(Cont, Conts).

abce_n(Cont, Conts) :-
  abce_1(Cont, TempConts) ->  
  ( maplist(abce_n, TempConts, Contss), 
    append(Contss, Conts) ) ; 
  ( Conts = [Cont] ).

bc_n(Cont, Conts) :-
  bc_1(Cont, TempConts) ->  
  ( maplist(bc_n, TempConts, Contss), 
    append(Contss, Conts) ) ; 
  ( Conts = [Cont] ).

clause_lits(Cla, Lits) :- 
  break_gamma(_, Cla, NewCla),
  clause_lits(NewCla, Lits).

clause_lits(Cla, Lits) :- 
  break_beta(Cla, ClaA, ClaB),
  clause_lits(ClaA, LitsA),
  clause_lits(ClaB, LitsB),
  append(LitsA, LitsB, Lits).

clause_lits(Lit, [Lit]) :- 
  literal(Lit).

% clause_lits(Cla, Lits) :- 
%   decom_clause(Cla, _, Goals), 
%   maplist(fst, Goals, Lits).

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
  clause_lits(ClaA, LitsA),
  clause_lits(ClaB, LitsB),
  subset_except_one(LitsA, CmpLits, LitA), 
  subset_except_one(LitsB, CmpLits, LitB).

find_pivot(FormA, FormB, FormB, FormA, Atom) :- 
  clause_lits(FormA, LitsA),
  clause_lits(FormB, LitsB),
  member(~ Atom, LitsA), 
  member(Atom, LitsB).

find_pivot(FormA, FormB, FormA, FormB, Atom) :- 
  clause_lits(FormA, LitsA),
  clause_lits(FormB, LitsB),
  member(Atom, LitsA), 
  member(~ Atom, LitsB).

resolution(QlaA, QlaB, QlaC, Prf) :- 
  find_pivot(QlaA, QlaB, QlaP, QlaN, Atom),
  ade_n(0, ([~ QlaC], Prf), _, [(Lits, cut(Atom, PrfA, PrfB))]), 
  lits_qla_cls([Atom | Lits], QlaN, PrfA),
  lits_qla_cls([~ Atom | Lits], QlaP, PrfB).

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

sup(ClaA, ClaB, ClaC, Prf) :- 
  ade_n(0, ([~ ClaC], Prf), _, [(Lits, cut(CmpA, PrfA, cut(CmpB, PrfB, PrfC)))]), 
  find_pivots(Lits, ClaA, ClaB, LitA, LitB),
  member(LitT, Lits), 
  invert(LitA, CmpA),
  invert(LitB, CmpB),
  invert(LitT, CmpT),
  e_n(([~ CmpB, ~ CmpA], PrfC), [(_, PrfD)]), % Literals available at this point : LitA, LitB, LitT
  choose_lits(LitA, LitB, PrfD, LitS, LitE, PrfE), % Choose the source literal LitS (i.e., the literal which 
                                                   % is equal to the target literal LitT modulo LitE), the
                                                   % equality literal LitE, and the direction in which LitS
                                                   % is to be used (which may vary if LitS is an equality).  
  prove_imp_super(LitS, LitE, CmpT, PrfE), % Prove that LitS plus LitE impies CmpT. Since LitT is already available 
                                           % on the branch, this means LitS and LitE are jointly contradictory.
  lits_qla_cls([CmpA | Lits], ClaA, PrfA),
  lits_qla_cls([CmpB | Lits], ClaB, PrfB).


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
    lits_lit_cls(Pth, Lit, Prf) -> 
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
  lits_lit_cls([Cmp], Lit, Prf).

tableaux(Forms, Lim, Prf) :- 
  pluck(Forms, Form, Rem),
  tableaux(Rem, Lim, 0, [], block, [], [$true, ~ $false], Form, _, Prf).

tableaux(Forms, 15, timeout(Forms)).

tableaux(Forms, Lim, Prf) :- 
  Succ is Lim + 1,
  tableaux(Forms, Succ, Prf).

tableaux(Forms, Prf) :- 
  % add_eq_axioms(Forms, NewForms),
  tableaux(Forms, 5, Prf).

find_lemma(Lems, LitA, Prf) :-
  member((LitB, Prf), Lems), 
  LitA == LitB.

lits_lits_tmt(LitsA, (LitsB, Prf)) :-   
  lits_lits_cls(LitsA, LitsB, Prf).  

lits_lits_cls(LitsA, LitsB, Prf) :-   
  member(LitB, LitsB),
  lits_lit_cls(LitsA, LitB, Prf).

lits_lit_tmt(Lits, ([Lit], Prf)) :-
  lits_lit_cls(Lits, Lit, Prf).

lits_lit_cls(Lits, Lit, Prf) :-
  member(Cmp, Lits),
  lit_lit_cls(Cmp, Lit, Prf).

lit_lit_cls(AtomA, ~ AtomB, Prf) :-
  propatom(AtomA),
  propatom(AtomB),
  atom_atom_cls(AtomA, AtomB, Prf).

lit_lit_cls(~ AtomA, AtomB, Prf) :-
  propatom(AtomA),
  propatom(AtomB),
  atom_atom_cls(AtomA, AtomB, Prf).

atom_atom_cls(AtomA, AtomB, close) :-
  unify_with_occurs_check(AtomA, AtomB).

atom_atom_cls((TermA = TermB), Atom, Prf) :-
  prove_eq_symm(TermA, close, TermB, Prf, close), 
  unify_with_occurs_check((TermB = TermA), Atom).
  
invert(~ Form, Form).

invert(Form, ~ Form) :-
  not(Form = ~ _).

undup(Prem, Conc, Prf) :-
  ade_n(0, ([~ Conc], Prf), _, [(Lits, SubPrf)]), 
  lits_qla_cls(Lits, Prem, SubPrf).

apply_ac([Prem | Prems], Conc, Prf) :-
  ade_n(0, ([~ Conc], Prf), _, [(Lits, SubPrf)]),
  bc_n(([Prem], SubPrf), Conts), 
  maplist(apply_ac_core(Prems, Lits), Conts).

apply_ac_core(Prems, Lits, ([Atom], Prf)) :-
  member(Prem, Prems), 
  apply_ac_core(Atom, Prem, Lits, Prf).

apply_ac_core(Atom, FaForm, Lits, gamma(Term, FaForm, Prf)) :-
  break_gamma(Term, FaForm, Form), 
  apply_ac_core(Atom, Form, Lits, Prf).
  
apply_ac_core(AtomA, AtomA => AtomB, Lits, beta(AtomA => AtomB, close, close)) :-
  member(~ AtomB, Lits).

% apply_ac(Prems, Conc, 
%   delta(c, ~ Conc, 
%     gamma(c, FormFA, 
%       gamma(c, FormFAB, 
%         beta(FormA => FormB, close, close)
%       )
%     )   
%   )) :-
%   break_delta(c, ~ Conc, ~ FormB),
%   member(FormFAB, Prems),
%   break_gamma(c, FormFAB, FormA => FormB), 
%   member(FormFA, Prems),
%   break_gamma(c, FormFA, FormA). 

find_complements(FormsA, FormsB) :- 
  member(~ Form, FormsA), 
  member(Form, FormsB). 

find_complements(FormsA, FormsB) :- 
  member(~ Form, FormsB), 
  member(Form, FormsA). 

swap(X, Y, X, Y).
swap(X, Y, Y, X).

break_alpha_par(FormA & FormB, FormA, FormB).
break_alpha_par(~ (FormA | FormB), ~ FormA, ~ FormB).
break_alpha_par(~ (FormA => FormB), ~ FormB, FormA).
break_alpha_par(FormA <=> FormB, FormB => FormA, FormA => FormB).

break_beta_par(~ (FormA & FormB), beta(~ (FormA & FormB), PrfA, PrfB), ~ FormA, PrfA, ~ FormB, PrfB).
break_beta_par(FormA | FormB, beta(FormA | FormB, PrfA, PrfB), FormA, PrfA, FormB, PrfB).
break_beta_par(FormA => FormB, beta(FormA => FormB, PrfA, PrfB), FormB, PrfB, ~ FormA, PrfA).
break_beta_par(~ (FormA <=> FormB), beta(~ (FormA <=> FormB), PrfA, PrfB),
 ~ (FormB => FormA), PrfB, ~ (FormA => FormB), PrfA). 

parallel_core(Terms, Par, FormA, FormB, 
  delta(@(Par, Terms), FormA, gamma(Term, FormB, Prf)),
  [([Term | Terms], Succ, NewFormA, NewFormB, Prf)]) :- 
  break_delta(@(Par, Terms), FormA, NewFormA),
  break_gamma(Term, FormB, NewFormB),
  Succ is Par + 1.

parallel_core(Terms, Par, ~ ~ FormA, FormB, dne(~ ~ FormA, Prf), [(Terms, Par, FormA, FormB, Prf)]).

parallel_core(Terms, Par, FormA, FormB, alpha(FormA, Prf),
  [
    (Terms, Par, FormAL, FormBL, PrfL),
    (Terms, Par, FormAR, FormBR, PrfR)
  ]) :-
  break_alpha_par(FormA, FormAL, FormAR),
  break_beta_par(FormB, Prf, FormBL, PrfL, FormBR, PrfR).

parallel((Terms, Par, FormA, FormB, Prf), NewPCs) :- 
  swap(FormA, FormB, FormL, FormR),
  parallel_core(Terms, Par, FormL, FormR, Prf, NewPCs).

ennf(PC) :- 
  parallel(PC, PCs) -> 
  maplist(ennf, PCs) ;
  ( PC = (_, _, FormA, FormB, close), 
    (FormA = ~ FormB ; FormB = ~ FormA) ). 

nnf(PC) :- 
  parallel(PC, PCs) -> 
  maplist_cut(nnf, PCs) ;
  ( PC = (_, _, FormA, FormB, Prf), 
    tableaux([FormA, FormB], Prf) ). 

cnf(Prem, Conc, Prf) :- 
  ade_n(0, ([~ Conc], Prf), _, [(Lits, SubPrf)]),
  abce_n(([Prem], SubPrf), Conts),
  maplist(lits_lits_tmt(Lits), Conts).

% Predicates of the form x_y_cls(X, Y, Prf) bind Prf to a closed proof, 
% where X and Y are available assumptions on the branch.

% Predicates of the form x_y_tmt(X, (Y, Prf)) bind Prf to a closed proof, 
% where X and Y are available assumptions on the branch, and (Y, Prf) is 
% a proof continuation.

eqr_core(Lits, Cont) :-
  b_1(Cont, [ContA, ContB]) ->
  (
    (eqr_core(Lits, ContA), lits_cla_tmt(Lits, ContB)) ; 
    (eqr_core(Lits, ContB), lits_cla_tmt(Lits, ContA))  
  ) ;
  ( Cont = ([~ (Term = Term)], Prf), 
    prove_eq_refl(Term, Prf) ).

  % eqr_core(Lits, ContA) ;






eqr(Prem, Conc, Prf) :- 
  ade_n(0, ([~ Conc], Prf), _, [(Lits, PrfA)]),
  c_n(([Prem], PrfA), [([Form], PrfB)]),
  eqr_core(Lits, ([Form], PrfB)).

lits_cla_tmt(Lits, Cont) :- 
  b_n(Cont, Conts), 
  maplist(lits_lit_tmt(Lits), Conts). 

lits_qla_cls(Lits, Qla, Prf) :- 
  lits_qla_tmt(Lits, ([Qla], Prf)).

lits_qla_tmt(Lits, Cont) :- 
  bc_n(Cont, Conts), 
  maplist(lits_lit_tmt(Lits), Conts). 

elab(goal(_, Prems, Conc, Rul), (Prf, Conc)) :-
  elab_eva(Prems, Conc, Rul, Prf), 
  ground_all(Prf). 

elab(goal(ID, Prems, Conc, Rul), failure(ID, Prems, Conc, Rul)).

elab_eva([Prem], Conc, cnf_transformation, Prf) :- 
  cnf(Prem, Conc, Prf).

elab_eva([Prem], Conc, equality_resolution, Prf) :- 
  eqr(Prem, Conc, Prf).

elab_eva(Prems, Conc, skolemisation, Prf) :- 
  apply_ac(Prems, Conc, Prf).

elab_eva([Prem], Conc, duplicate_literal_removal, Prf) :- 
  undup(Prem, Conc, Prf).

elab_eva([~ (Term = Term)], _, trivial_inequality_removal, Prf) :- 
   prove_eq_refl(Term, Prf).

elab_eva([Form], Form, _, close).

% elab_eva([Prem | Prems], Conc, Rul, Prf) :- 
%   splitting(Rul),
%   split(Prem, Prems, Conc, Prf).


elab_eva([Prem], Conc, ennf_transformation, Prf) :- 
  ennf(([], 0, Prem, ~ Conc, Prf)).

elab_eva([Prem], Conc, nnf_transformation, Prf) :- 
  nnf(([], 0, Prem, ~ Conc, Prf)).

elab_eva([PremA, PremB], Conc, Rul, Prf) :- 
  resolutional(Rul),
  resolution(PremA, PremB, Conc, Prf).

elab_eva([QlaA, QlaB], QlaC, Rul, Prf) :- 
  superpositional(Rul),
  sup(QlaA, QlaB, QlaC, Prf).

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

goal(ID, Prems, Conc, Rul) :- 
  fof(ID, _, TPTP, inference(Rul, _, IDs)),
  not(Rul = negated_conjecture),
  translate(0, TPTP, Conc),
  maplist(id_form, IDs, Prems).

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

write_prem(Num, ID) :-
  fof(ID, _, Prem, _), 
  numbervars(Prem, 0, _),
  write(fof(Num, axiom, Prem)),
  write(".\n\n").

report_failure(_, (_, _)).

report_failure(tptp, failure(ID, _, _, _)) :-
  fof(ID, _, Conc, Info), 
  numbervars(Conc, 0, _),
  Info = inference(_, _, IDs), 
  maplist_idx(write_prem, 0, IDs),
  write(fof(c, conjecture, Conc)), 
  write(".\n\n\n\n").

report_failure(graft, failure(_, Prems, Conc, Rul)) :-
  write("Failed lemma : "),
  write_break(2, Rul),
  maplist(write_break(2), Prems),  
  write("|- "),
  write_break(4, Conc).

%   numbervars(Conc, 0, _),
%   % close(Stream).
%   true.

prove(Source, Target) :-
  dynamic(fof/4),
  retractall(fof(_, _, _, _)),
  consult(Source),
  findall(hyp(Form), hyp(Form), Hyps),
  findall(aug(Form, Rul), aug(Form, Rul), Augs),
  findall(goal(ID, Prems, Conc, Rul), goal(ID, Prems, Conc, Rul), Goals),
  maplist_cut(elab, Goals, Sols), !,
  (
    member(failure(_, _, _, _), Sols) -> 
    maplist(report_failure(graft), Sols) ;
    ( stitch(Hyps, Augs, Sols, Prf), 
      write_file_punct(Target, proof(Prf)) )
  ).

/* 

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

*/