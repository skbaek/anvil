:- [misc].

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


/* Proof state display */

% theorem_string(Frms, Str) :- 
%   maplist(form_string, Frms, Strs), 
%   reverse(Strs, RevStrs),
%   strings_concat_with(", ", RevStrs, TempStr),
%   string_concat(TempStr, " |- false", Str).

% branch_string(Frms, Str) :- 
%   indexed_maplist(index_form_string, 0, Frms, Strs), 
%   reverse(["\n-------\n\n" |Strs], RevStrs),
%   strings_concat(RevStrs, Str).

% shell("vampire --proof tptp goal | tr '!=' '\\\\=' > insts"),

% branches_string(Bchs, on, Str) :- 
%   reverse(Bchs, RevBchs),
%   maplist(branch_string, RevBchs, Strs),
%   strings_concat(Strs, Str).
% 
% branches_string([Bch | Bchs], off, Str) :- 
%   length(Bchs, Lth),
%   number_string(Lth, LthStr),
%   branch_string(Bch, BchStr),
%   strings_concat(["(", LthStr, " more goals)\n\n", BchStr], Str).
  
/* Formula decomposition */

break_alpha(FrmA & FrmB, FrmA, FrmB).
break_alpha(~ (FrmA | FrmB), ~ FrmA, ~ FrmB).
break_alpha(~ (FrmA => FrmB), FrmA, ~ FrmB).
break_alpha(FrmA <=> FrmB, FrmA => FrmB, FrmB => FrmA).
alpha(Form) :- break_alpha(Form, _, _).

break_beta(~ (FrmA & FrmB), ~ FrmA, ~ FrmB).
break_beta(FrmA | FrmB, FrmA, FrmB).
break_beta(FrmA => FrmB, ~ FrmA, FrmB).
break_beta(~ (FrmA <=> FrmB), ~ (FrmA => FrmB), ~(FrmB => FrmA)).
beta(Form) :- break_beta(Form, _, _).

break_gamma(Term, ! Num : Form, NewForm) :- !, 
  substitute(Num, Term, Form, NewForm).

break_gamma(Term, ~ (? Num : Form), ~ NewForm) :- 
  substitute(Num, Term, Form, NewForm).

gamma(! _ : _).
gamma(~ (? _ : _)).

break_delta(Term, (? Var : Form), NewForm) :- !, 
  substitute(Var, Term, Form, NewForm).

break_delta(Term, ~ (! Var : Form), ~ NewForm) :- 
  substitute(Var, Term, Form, NewForm).

delta(? _ : _).
delta(~ (! _ : _)).

substitute(_, _, Var, Var) :- 
  var(Var). 

substitute(NumA, Term, Exp, NewTerm) :- 
  not(var(Exp)), 
  Exp = #(NumB),
  ( NumA = NumB -> 
    NewTerm = Term;
    NewTerm = #(NumB) ).

substitute(Num, Term, Exp, NewExp) :- 
  not(var(Exp)), 
  not(Exp = #(_)), 
  not(Exp = @(_)), 
  Exp =.. [Symb | Terms],  
  maplist(substitute(Num, Term), Terms, NewTerms),
  NewExp =.. [Symb | NewTerms].

verify([~ ~ Frm | Bch], dne(Prf)) :-
  verify([Frm, ~ ~ Frm | Bch], Prf).

verify([FrmA | Bch], alpha(Prf)) :-
  break_alpha(FrmA, FrmB, FrmC),
  verify([FrmC, FrmB, FrmA | Bch], Prf).
  
verify([FrmB, FrmA | Bch], beta(Prf)) :-
  break_beta(FrmA, FrmB, FrmC),
  verify([FrmC, FrmB, FrmA | Bch], Prf).

verify([FrmA | Bch], gamma(Term, Prf)) :-
  break_gamma(Term, FrmA, FrmB),
  verify([FrmB, FrmA | Bch], Prf).

verify([~ Frm, Frm | _], close).

verify(Bch, copy(Num, Prf)) :- 
  nth0(Num, Bch, Frm), 
  verify([Frm | Bch], Prf).

verify(Bch, cut(Frm, PrfA, PrfB)) :- 
  verify([Frm | Bch], PrfA), 
  verify([~ Frm | Bch], PrfB).

verify(Bch, tt(Prf)) :-
  verify([$true | Bch], Prf).

verify(Bch, ff(Prf)) :-
  verify([~ $false | Bch], Prf).

mk_mono_args(0, [], []).

mk_mono_args(Num, [#(NumA) | VarsA], [#(NumB) | VarsB]) :-
  NumA is (Num * 2) - 1, 
  NumB is (Num * 2) - 2, 
  Pred is Num - 1,
  mk_mono_args(Pred, VarsA, VarsB).

mk_mono_eq(Num, Fun, TermA = TermB) :- 
  mk_mono_args(Num, VarsA, VarsB),
  TermA =.. [Fun | VarsA],
  TermB =.. [Fun | VarsB].

mk_mono_imp(Num, Rel, AtomA => AtomB) :- 
  mk_mono_args(Num, VarsA, VarsB),
  AtomA =.. [Rel | VarsA],
  AtomB =.. [Rel | VarsB], !.

mk_mono_fun_filter((Fun, Num), Mono) :- 
  0 < Num,
  mk_mono_fun((Fun, Num), Mono). 

mk_mono_fun((Fun, Num), Mono) :- 
  mk_mono_eq(Num, Fun, Eq), 
  mk_mono(Num, Eq, Mono), !.

mk_mono_rel((Rel, Num), Mono) :- 
  mk_mono_imp(Num, Rel, Imp), 
  mk_mono(Num, Imp, Mono).

mk_mono_rel_filter((Rel, Num), Mono) :- 
  not((Rel = (=), Num = 2)), 
  0 < Num,
  mk_mono_rel((Rel, Num), Mono). 

mk_mono(0, Cons, Cons).

mk_mono(Num, Cons, ! NumA : ! NumB : ((#(NumA) = #(NumB)) => Mono)) :-
  NumA is (Num * 2) - 1, 
  NumB is (Num * 2) - 2, 
  decr_if_pos(Num, Pred), 
  mk_mono(Pred, Cons, Mono), !. 

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

% translate(Num, FrmA & FrmB, NewFrmA & NewFrmB) :- !,
%  translate(Num, FrmA, NewFrmA),
%  translate(Num, FrmB, NewFrmB).
%   
% translate(Num, FrmA | FrmB, NewFrmA | NewFrmB) :- !,
%  translate(Num, FrmA, NewFrmA),
%  translate(Num, FrmB, NewFrmB).
% 
% translate(FrmA => FrmB, NewFrmA => NewFrmB) :- !,
%  translate(FrmA, NewFrmA),
%  translate(FrmB, NewFrmB).
% 
% translate(FrmA <=> FrmB, NewFrmA <=> NewFrmB) :- !,
%  translate(FrmA, NewFrmA),
%  translate(FrmB, NewFrmB).



% ids_get_insts([], []).
% 
% ids_get_insts([Id | Ids], Insts) :- 
%   id_get_insts(Id, IdInsts),
%   ids_get_insts(Ids, IdsInsts),
%   subtract(IdInsts, IdsInsts, Diff),
%   append(Diff, IdsInsts, Insts).

% id_form(Id, Form) :-
%   fof(Id, _, Conc, _),
%  translate(Conc, Form).
% 
% id_tree(Id, hyp(Form)) :-
%   fof(Id, _, Conc, file(_, _)),
%  translate(Conc, Form).
% 
% id_tree(Id, def(Form, Rul)) :-
%   fof(Id, _, Conc, introduced(Rul, _)), !,
%  translate(Conc, Form).
% 
% id_tree(Id, inf(Trees, Forms, Form, Rul)) :-  
%   fof(Id, _, Conc, inference(Rul, _, Ids)), !,
%   maplist(id_tree, Ids, Trees),
%   maplist(id_form, Ids, Forms),
%  translate(Conc, Form).

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

punctuate(Term, Str) :-
  term_string(Term, TermStr),
  string_concat(TermStr, ".", Str).

% prove_save(Source, Target) :-
%   retractall(fof(_, _, _, _)),
%   consult(Source),
%   fof(Id,_, $false, _),
%   id_tree(Id, Tree),
%   prove((Tree, [], []), (Smt, _, Prf)),
%   punctuate(theorem(Smt, Prf), Str),
%   write_file(Target, Str).

unneg(~ Atom, Atom) :- !.
unneg(Atom, Atom).

propatom(Atom) :- 
  not(member(Atom, 
    [ (! _ : _), (? _ : _), (~ _), 
      (_ | _), (_ & _), (_ => _), (_ <=> _) ])).

literal(~ Atom) :- 
  propatom(Atom).

literal(Atom) :- 
  propatom(Atom).

id_conc(Id, Conc) :- 
  fof(Id, _, Conc, _).

init_goal((introduced(Rul, _), Conc), ([], Form, Rul)) :- 
 translate(0, Conc, Form).

init_goal((inference(Rul, _, PremIds), Conc), (Forms, Form, Rul)) :- 
 translate(0, Conc, Form),
  maplist(id_conc, PremIds, Prems),
  maplist(translate(0), Prems, Forms).

clausal(Rul) :-
  member(
    Rul,
    [
      resolution,
      subsumption_resolution,
      % superposition
      % forward_demodulation,
      % backward_demodulation
      none
    ]
  ).

simple_fol(Rul) :-
  member(
    Rul,
    [
      % cnf_transformation,
      avatar_sat_refutation,
      avatar_contradiction_clause,
      avatar_component_clause
      % duplicate_literal_removal
    ]
  ).

definitional(Rul) :-
  member(
    Rul,
    [
      avatar_definition
    ]
  ).

splitting(Rul) :-
  member(
    Rul,
    [
      avatar_split_clause
    ]
  ).

/*
positive(~ ~ Form) :- 
  positive(Form).

positive(Form) :- 
  break_alpha(Form, FormA, FormB), 
  ( positive(FormA) ;
    positive(FormB) ).

positive(Form) :- 
  break_beta(Form, FormA, FormB), 
  positive(FormA), 
  positive(FormB).

positive(FaForm) :- 
  break_gamma(_, FaForm, Form), 
  positive(Form). 

positive(ExForm) :- 
  break_delta(_, ExForm, Form), 
  positive(Form). 

positive(Atom) :- 
  propatom(Atom).
*/

linear(Par, Form, delta(@(Par, []), Form, Prf), NewPar, Lits, SubPrf) :- 
  break_delta(@(Par, []), Form, NewForm), 
  Succ is Par + 1, 
  linear(Succ, NewForm, Prf, NewPar, Lits, SubPrf).

linear(Par, Form, alpha(Form, Prf), NewPar, Lits, SubPrf) :- 
  break_alpha(Form, FormA, FormB), 
  linear(Par, FormA, Prf, ParA, LitsA, SubPrfA), 
  linear(ParA, FormB, SubPrfA, NewPar, LitsB, SubPrf),
  append(LitsA, LitsB, Lits).

linear(Par, ~ ~ Form, dne(Form, Prf), NewPar, Lits, SubPrf) :- 
  linear(Par, Form, Prf, NewPar, Lits, SubPrf). 

linear(Par, Lit, Prf, Par, [Lit], Prf) :- 
  literal(Lit).

gammas(Form, NewForm, gamma(Term, Form, Prf), SubPrf) :- 
  break_gamma(Term, Form, TempForm), 
  gammas(TempForm, NewForm, Prf, SubPrf).

gammas(Form, Form, Prf, Prf) :-
  not(gamma(Form)).

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

decom_clause(Cla, Prf, Goals) :- 
  break_gamma(_, Cla, NewCla), 
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

demodulation(ClaA, ClaB, ClaC, Prf) :- 
  linear(0, ~ ClaC, Prf, _, Lits, cut(CmpA, PrfA, cut(CmpB, PrfB, sorry))), 
  find_pivots(Lits, ClaA, ClaB, LitA, LitB),
  invert(LitA, CmpA),
  invert(LitB, CmpB),
  close_clause([CmpA | Lits], ClaA, PrfA),
  close_clause([CmpB | Lits], ClaB, PrfB).

/*
resolution_first(Path, (FormL | FormR), FormB, beta((FormL | FormR), PrfA, PrfB)) :- 
  resolution_first(Path, FormL, FormB, PrfA), 
  resolution_rest(Path, FormR, PrfB).

resolution_first(Path, (FormL | FormR), FormB, beta((FormL | FormR), PrfA, PrfB)) :- 
  resolution_first(Path, FormR, FormB, PrfB), 
  resolution_rest(Path, FormL, PrfA).

resolution_first(Path, FormA, FormB, gamma(Term, FormA, Prf)) :- 
  break_gamma(Term, FormA, NewFormA), 
  resolution_first(Path, NewFormA, FormB, Prf).

resolution_first(Path, Lit, Form, Prf) :- 
  literal(Lit),
  resolution_second(Path, Lit, Form, Prf).

resolution_second(Path, Lit, (FormL | FormR), beta((FormL | FormR), PrfL, PrfR)) :- 
  resolution_second(Path, Lit, FormL, PrfL),
  resolution_rest(Path, FormR, PrfR).

resolution_second(Path, Lit, (FormL | FormR), beta((FormL | FormR), PrfL, PrfR)) :- 
  resolution_second(Path, Lit, FormR, PrfR),
  resolution_rest(Path, FormL, PrfL).

resolution_second(Path, Lit, Form, gamma(Term, Form, Prf)) :- 
  break_gamma(Term, Form, NewForm), 
  resolution_second(Path, Lit, NewForm, Prf).
  
resolution_second(_, LitA, LitB, close) :- 
  literal(LitB),
  complementary(LitA, LitB).

resolution_rest(Path, (FormA | FormB), beta((FormA | FormB), PrfA, PrfB)) :- 
  resolution_rest(Path, FormA, PrfA),
  resolution_rest(Path, FormB, PrfB).

resolution_rest(Path, Lit, close) :-
  literal(Lit),
  has_complement(Lit, Path).
*/

tableaux(Forms, Lim, Par, Terms, Mode, Lems, Pth, ~ ~ Form, NewLems, dne(Form, Prf)) :- 
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
  add_eq_axioms(Forms, NewForms),
  tableaux(NewForms, 5, Prf).

find_lemma(Lems, LitA, Prf) :-
  member((LitB, Prf), Lems), 
  LitA == LitB.

rels_funs([], [], []).

rels_funs([Form | Forms], Rels, Funs) :- 
  rels_funs(Form, RelsA, FunsA),
  rels_funs(Forms, RelsB, FunsB),
  union(RelsA, RelsB, Rels),
  union(FunsA, FunsB, Funs).

rels_funs(! _ : Form, Rels, Funs) :- 
  rels_funs(Form, Rels, Funs).

rels_funs(? _ : Form, Rels, Funs) :- 
  rels_funs(Form, Rels, Funs).

rels_funs(~ Form, Rels, Funs) :- 
  rels_funs(Form, Rels, Funs).

rels_funs(FormA & FormB, Rels, Funs) :- 
  rels_funs(FormA, RelsA, FunsA),
  rels_funs(FormB, RelsB, FunsB),
  union(RelsA, RelsB, Rels),
  union(FunsA, FunsB, Funs).

rels_funs(FormA | FormB, Rels, Funs) :- 
  rels_funs(FormA, RelsA, FunsA),
  rels_funs(FormB, RelsB, FunsB),
  union(RelsA, RelsB, Rels),
  union(FunsA, FunsB, Funs).

rels_funs(FormA => FormB, Rels, Funs) :- 
  rels_funs(FormA, RelsA, FunsA),
  rels_funs(FormB, RelsB, FunsB),
  union(RelsA, RelsB, Rels),
  union(FunsA, FunsB, Funs).

rels_funs(FormA <=> FormB, Rels, Funs) :- 
  rels_funs(FormA, RelsA, FunsA),
  rels_funs(FormB, RelsB, FunsB),
  union(RelsA, RelsB, Rels),
  union(FunsA, FunsB, Funs).

rels_funs(Atom, [(Rel, Num)], Funs) :-
  propatom(Atom), 
  Atom =.. [Rel | Terms], 
  length(Terms, Num),
  maplist(funs, Terms, Funss), 
  union(Funss, Funs).

funs(#(_), []). 

funs(Term, [(Term, 0)]) :-
  atom(Term).

funs(Term, [(Fun, Num) | Funs]) :-
  not(Term = #(_)),
  not(atom(Term)),
  Term =.. [Fun | Terms],
  length(Terms, Num),
  maplist(funs, Terms, Funss), 
  union(Funss, Funs).

add_eq_axioms(Forms, NewForms) :-
  rels_funs(Forms, Rels, Funs), 
  (
    member(((=), 2), Rels) ->
    (
      collect(mk_mono_fun_filter, Funs, MonoFuns),
      collect(mk_mono_rel_filter, Rels, MonoRels),
       append(
         [ 
           Forms,
           MonoFuns,
           MonoRels,
           [
             (! 0 : (#(0) = #(0))),
             (! 0 : ! 1 : ((#(0) = #(1)) => (#(1) = #(0)))), 
             (! 0 : ! 1 : ! 2 : ((#(0) = #(1)) => ((#(1) = #(2)) => (#(0) = #(2)))))
           ] 
         ],
         NewForms) 
    ) ; 
    NewForms = Forms
  ). 

close_lit(Lits, Lit, close) :-
  member(Cmp, Lits),
  complementary(Lit, Cmp).

close_lit(Lits, (TermA = TermB), Prf) :-
  member(Cmp, Lits),
  complementary(Cmp, (TermB = TermA)),
  prove_symm(TermA, TermB, Prf, close).

invert(~ Form, Form).

invert(Form, ~ Form) :-
  not(Form = ~ _).

complementary(~ FormA, FormB) :- !,
  unify_with_occurs_check(FormA, FormB).
  
complementary(FormA, ~ FormB) :- !,
  unify_with_occurs_check(FormA, FormB).

prove_symm(TermA, TermB, 
  gamma(TermA, ! 0: ! 1: ((#(0) = #(1)) => (#(1) = #(0))),
    gamma(TermB, ! 1: ((TermA = #(1)) => (#(1) = TermA)),
      beta((TermA = TermB) => (TermB = TermA), close, Prf))), 
  Prf).

undup(Prem, Conc, Prf) :-
  linear(0, ~ Conc, Prf, _, Lits, SubPrf), 
  close_clause(Lits, Prem, SubPrf).

close_clause(Lits, Cla, Prf) :- 
  decom_clause(Cla, Prf, Goals), 
  maplist(close_goal(Lits), Goals). 

elab(([ClaA, ClaB], ClaC, backward_demodulation), val(Prf, ClaC)) :- 
  demodulation(ClaA, ClaB, ClaC, Prf).

elab(([Prem], Conc, duplicate_literal_removal), val(Prf, Conc)) :- 
  undup(Prem, Conc, Prf).

elab(([Prem | Prems], Conc, Rul), val(Prf, Conc)) :- 
  splitting(Rul),
  split(Prem, Prems, Conc, Prf).

elab(([PremA, PremB], Conc, Rul), val(Prf, Conc)) :- 
  clausal(Rul),
  resolution(PremA, PremB, Conc, Prf).

elab((Prems, Conc, Rul), val(Prf, Conc)) :- 
  simple_fol(Rul),
  tableaux([~ Conc | Prems], Prf).

elab((Prems, Conc, Rul), sat(Prems, Conc, Rul)) :- 
  definitional(Rul).

elab((Prems, Conc, Rul), admit(Prems, Conc, Rul)).

has_eq(Exp) :-
  Exp =.. ['=' | _].

has_eq(Exp) :-
  Exp =.. [_ | Args],
  any(has_eq, Args).

prove(Source) :-
  dynamic(fof/4),
  retractall(fof(_, _, _, _)),
  consult(Source),
  findall((Just, Conc), fof(_, _, Conc, Just), Steps),
  collect(init_goal, Steps, Goals),
  maplist(elab, Goals, Prfs),
  list_string(Prfs, Str),
  % maplist(check([]), Prfs),
  % write("CHECK SUCCESS!!!").
  write_file("output", Str).

verify(Source) :-
  retractall(theorem(_, _)),
  consult(Source),
  theorem(Smt, Prf),
  verify(Smt, Prf),
  write("Proof verified : "),
  maplist(form_string, Smt, Strs),
  strings_concat_with(", ", Strs, Str),
  write(Str).