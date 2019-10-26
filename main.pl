#!/usr/bin/env swipl

:- initialization(main, main).

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

insts_string([], _, "No insts\n\n").

insts_string(Insts, on, Str) :-
  maplist(inst_string, Insts, Strs), 
  strings_concat(Strs, TempStr),
  string_concat(TempStr, "\n", Str).
  
insts_string([Inst | Insts], off, Str) :-
  inst_string(Inst, InstStr), 
  length(Insts, Lth),
  number_string(Lth, LthStr),
  strings_concat([InstStr, "\n(", LthStr, " more insts)\n\n"], Str).

inst_string(defin(Conc, Rul), Str) :- 
  term_string(Conc, ConcStr),
  term_string(Rul, RulStr),
  strings_concat(["?Γ |= ", ConcStr, " [", RulStr, "]\n"], Str).

inst_string(lemma(Prems, Conc, Rul), Str) :- 
  maplist(term_string, Prems, PremStrs),
  strings_concat_with(", ", PremStrs, PremsStr),
  term_string(Conc, ConcStr),
  term_string(Rul, RulStr),
  strings_concat([PremsStr, " |- ", ConcStr, " [", RulStr, "]\n"], Str).

inst_string(Inst, Str) :- 
  term_string(Inst, InstStr),
  string_concat(InstStr, "\n", Str).

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

decode_disp(all, on, on).
decode_disp(goals, on, off).
decode_disp(insts, off, on).
decode_disp(none, off, off).

% write_state(State) :-
%   get_disp(State, Disp),
%   decode_disp(Disp, ShowBchs, ShowInsts),
%   get_branches(State, Bchs),
%   branches_string(Bchs, ShowBchs, BchsStr),
%   get_insts(State, Insts),
%   insts_string(Insts, ShowInsts, InstsStr),
%   shell("clear"),
%   write(BchsStr), 
%   write(InstsStr).
% 
% write_state(_, _, _) :-
%   write("Ill-formed state.").
  
/* Formula decomposition */

break_alpha(FrmA & FrmB, FrmA, FrmB).
break_alpha(~ (FrmA | FrmB), ~ FrmA, ~ FrmB).
break_alpha(~ (FrmA => FrmB), FrmA, ~ FrmB).

break_beta(~ (FrmA & FrmB), FrmA, ~ FrmB).
break_beta(~ (FrmA & FrmB), FrmB, ~ FrmA).
break_beta(FrmA | FrmB, ~ FrmA, FrmB).
break_beta(FrmA | FrmB, ~ FrmB, FrmA).
break_beta(FrmA => FrmB, FrmA, FrmB).
break_beta(FrmA => FrmB, ~ FrmB, ~ FrmA).

fa_inst(Trm, (! [X] : Form), NewForm) :- !, 
  copy_term((! [X] : Form), (! [Y] : NewForm)), 
  Y = Trm.

break_gamma(Trm, (! [X] : Frm), NewFrm) :- !, 
  copy_term((! [X] : Frm), (! [Y] : NewFrm)), 
  Y = Trm.

break_gamma(Trm, (! [X | Xs] : Frm), (! Ys : NewFrm)) :- !, 
  copy_term((! [X | Xs] : Frm), (! [Y | Ys] : NewFrm)), 
  Y = Trm.

break_gamma(Trm, ~ (? [X] : Frm), ~ NewFrm) :- !, 
  copy_term((? [X] : Frm), (? [Y] : NewFrm)), 
  Y = Trm.

break_gamma(Trm, ~ (? [X | Xs] : Frm), ~ (? Ys : NewFrm)) :- !, 
  copy_term((? [X | Xs] : Frm), (? [Y | Ys] : NewFrm)), 
  Y = Trm.

/* 
branch_nth0(State, Num, Frm) :-
  get_branch(State, Bch),
  nth0(Num, Bch, Frm).
  
branch_member(State,Frm) :-
  get_branch(State, Bch),
  member(Frm, Bch).

branch_where(State, Frm, Num) :-
  get_branch(State, Bch),
  variant_nth0(Num, Bch, Frm).

branch_has(State, Frm) :-
  get_branch(State, Bch),
  variant_member(Frm, Bch).

branch_length(State, Num) :-
  get_branch(State, Bch),
  length(Bch, Num).

*/

% check_msg(_, _, over, over).
% 
% check_msg(Bch, Prf, into, Mode) :- 
%   shell("clear"),
%   branch_string(Bch, BchStr),
%   term_string(Prf, PrfStr),
%   strings_concat([BchStr, "Proof = ", PrfStr, "\n"], Str),
%   write(Str),
%   prompt(Mode).

verify([~ ~ Frm | Bch], dne(Prf)) :-
  verify([Frm, ~ ~ Frm | Bch], Prf).

verify([FrmA | Bch], alpha(Prf)) :-
  break_alpha(FrmA, FrmB, FrmC),
  verify([FrmC, FrmB, FrmA | Bch], Prf).
  
verify([FrmB, FrmA | Bch], beta(Prf)) :-
  break_beta(FrmA, FrmB, FrmC),
  verify([FrmC, FrmB, FrmA | Bch], Prf).

verify([FrmA | Bch], gamma(Trm, Prf)) :-
  break_gamma(Trm, FrmA, FrmB),
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


mk_pair(X, Y, (X, Y)).

mk_fun_mono(0, VarsA, [], VarsB, [], Fun, (TrmA = TrmB)) :- !,
  TrmA =.. [Fun | VarsA],
  TrmB =.. [Fun | VarsB].

mk_fun_mono(Num, VarsA, [X | ExtA], VarsB, [Y | ExtB], Fun, ! [X, Y] : ((X = Y) => Frm)) :- !,
  PredNum is Num - 1, 
  mk_fun_mono(PredNum, VarsA, ExtA, VarsB, ExtB, Fun, Frm).

mk_fun_mono(Num, Fun, Frm) :- 
  mk_fun_mono(Num, SrcVars, SrcVars, TgtVars, TgtVars, Fun, Frm).

mk_rel_mono(0, SrcVars, [], TgtVars, [], Pred, (SrcAtm => TgtAtm)) :- !,
  SrcAtm =.. [Pred | SrcVars],
  TgtAtm =.. [Pred | TgtVars].

mk_rel_mono(Num, SrcVars, [X | SrcExt], TgtVars, [Y | TgtExt], 
  Pred, ! [X, Y] : ((X = Y) => Frm)) :- !,
  PredNum is Num - 1, 
  mk_rel_mono(PredNum, SrcVars, SrcExt, TgtVars, TgtExt, Pred, Frm).

mk_rel_mono(Num, Pred, Frm) :- 
  mk_rel_mono(Num, SrcVars, SrcVars, TgtVars, TgtVars, Pred, Frm).

lits_align(~SrcAtm, ~TgtAtm, TgtAtm, SrcAtm) :- !.

lits_align(SrcAtm, TgtAtm, SrcAtm, TgtAtm). 

% hypothesis(Frm) :- 
%   fof(_, Type, Frm), 
%   member(Type, [axiom, negated_conjecture]).
%   
% conclusion(Frm) :- 
%   fof(_, Type, Frm), 
%   member(Type, [conjecture]).

% read_theorem(Filename, Frms) :- 
%   retractall(fof(_, _, _)),
%   consult(Filename), 
%   findall(Frm, hypothesis(Frm), Hyps),
%   findall(~ Frm, conclusion(Frm), Concs),
%   append(Hyps, Concs, Frms).
% 
% set_theorem([Filename], Frms) :- 
%   !, read_theorem(Filename, Frms).
% 
% set_theorem(_, [~ Goal]) :- 
%   write("Enter goal : "),
%   read(user_input, Goal).

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
  Exp =.. [_ | Trms],
  uses(Symb, Trms).

uses_any([Symb | Symbs], Frm) :- 
  uses(Symb, Frm);
  uses_any(Symbs, Frm).

desugar(~ Frm, ~ NewFrm) :- !, 
  desugar(Frm, NewFrm).

desugar(FrmA & FrmB, NewFrmA & NewFrmB) :- !,
  desugar(FrmA, NewFrmA),
  desugar(FrmB, NewFrmB).
  
desugar(FrmA | FrmB, NewFrmA | NewFrmB) :- !,
  desugar(FrmA, NewFrmA),
  desugar(FrmB, NewFrmB).

desugar(FrmA => FrmB, NewFrmA => NewFrmB) :- !,
  desugar(FrmA, NewFrmA),
  desugar(FrmB, NewFrmB).

desugar(FrmA <=> FrmB, NewFrmA <=> NewFrmB) :- !,
  desugar(FrmA, NewFrmA),
  desugar(FrmB, NewFrmB).

desugar((! Vars : Frm), (! Vars : NewFrm))  :- !, 
  desugar(Frm, NewFrm).

desugar((? Vars : Frm), (? Vars : NewFrm))  :- !, 
  desugar(Frm, NewFrm).

desugar((TrmA \= TrmB), ~ (TrmA = TrmB)) :- !.

desugar(Atm, Atm).

% ids_get_insts([], []).
% 
% ids_get_insts([Id | Ids], Insts) :- 
%   id_get_insts(Id, IdInsts),
%   ids_get_insts(Ids, IdsInsts),
%   subtract(IdInsts, IdsInsts, Diff),
%   append(Diff, IdsInsts, Insts).

id_form(Id, Form) :-
  fof(Id, _, Conc, _),
  desugar(Conc, Form).

id_tree(Id, hyp(Form)) :-
  fof(Id, _, Conc, file(_, _)),
  desugar(Conc, Form).

id_tree(Id, def(Form, Rul)) :-
  fof(Id, _, Conc, introduced(Rul, _)), !,
  desugar(Conc, Form).

id_tree(Id, inf(Trees, Forms, Form, Rul)) :-  
  fof(Id, _, Conc, inference(Rul, _, Ids)), !,
  maplist(id_tree, Ids, Trees),
  maplist(id_form, Ids, Forms),
  desugar(Conc, Form).

% Tree : hyp(Conc) | def()

% Input  : (Tree, Branch, Symbs)
% Output : (Branch, Symbs, Prf)

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

main(Argv) :-
  dynamic(theorem/2),
  dynamic(fof/4),
  (
    ( prove_args(Argv, Source, Target), 
      prove_save(Source, Target) ) ;
    ( verify_args(Argv, Source), 
      verify(Source) ) ;
    help_msg
  ).

punctuate(Term, Str) :-
  term_string(Term, TermStr),
  string_concat(TermStr, ".", Str).

prove_save(Source, Target) :-
  retractall(fof(_, _, _, _)),
  consult(Source),
  fof(Id,_, $false, _),
  id_tree(Id, Tree),
  prove((Tree, [], []), (Smt, _, Prf)),
  punctuate(theorem(Smt, Prf), Str),
  write_file(Target, Str).

is_hyp((file(_, _), _)).

id_conc(Id, Conc) :- 
  fof(Id, _, Conc, _).

init_goal((inference(Rul, _, PremIds), Conc), deduce(Prems, Conc, Rul)) :- 
  maplist(id_conc, PremIds, Prems).

prove(deduce(Prems, Conc, Rul), Prf) :- 
  member(Rul, [definition_unfolding]), 
  lits_sub_terms(Prems, Terms),
  init_ecs(Terms, InitECs), 
  collect(mk_eqhyp, Prems, EqHyps),
  cc(EqHyps, InitECs, ECs),
  first(prove_by_ecs(ECs, Conc), Prems, Prf). 

prove_debug(Source) :-
  dynamic(fof/4),
  retractall(fof(_, _, _, _)),
  consult(Source),
  findall((Just, Conc), fof(_, _, Conc, Just), Lines),
  exclude(is_hyp, Lines, Steps),
  maplist(init_goal, Steps, Goals),
  write(Goals).


verify(Source) :-
  retractall(theorem(_, _)),
  consult(Source),
  theorem(Smt, Prf),
  verify(Smt, Prf),
  write("Proof verified : "),
  maplist(form_string, Smt, Strs),
  strings_concat_with(", ", Strs, Str),
  write(Str).

extend_branch(Bch, Form, Bch, Num) :-
  where(Form, Bch, Num), !.

extend_branch(Bch, Form, NewBch, Num) :-
  append(Bch, [Form], NewBch),
  length(Bch, Num).
  

/* Main loop */

closure(Bch, copy(Num, ff(close))) :- 
  where($false, Bch, Num).
  
closure(Bch, tt(copy(Num, close))) :- 
  where(~ $true, Bch, Num).

closure(Bch, copy(NumA, (copy(NumB, close)))) :- 
  where(Form, Bch, NumA), 
  where(~ Form, Bch, PredNumB), 
  NumB is PredNumB + 1.

prove((_, Bch, Symbs), (Bch, Symbs, Prf)) :-  
  closure(Bch, Prf).

prove((_, Bch, Symbs), (NewBch, Symbs, copy(NumC, gamma(Trm, copy(NumB, close))))) :-  
  where(~ (Trm = Trm), Bch, NumA), 
  NumB is NumA + 2, 
  extend_branch(Bch, (! [X] : (X = X)), NewBch, NumC).

prove(
  (inf([hyp(ConcA) | Trees], Prems, ConcB, Rul), Bch, Symbs), 
  (NewBch, NewSymbs, Prf)
) :-  
  (
    member(ConcA, Bch) ->
    TempBch = Bch ; 
    append(Bch, [ConcA], TempBch)
  ),
  prove(
    (inf(Trees, Prems, ConcB, Rul), TempBch, Symbs),
    (NewBch, NewSymbs, Prf)
  ).

prove(
  (inf([def(Atom <=> Form, _) | Trees], Prems, Conc, Rul), Bch, Symbs), 
  (NewBch, NewSymbs, def(Atom, Form, Prf))
) :-  
  atom(Atom),
  not(uses(Atom, Bch)),
  prove(
    (inf(Trees, Prems, Conc, Rul), [(Atom <=> Form) | Bch], [Atom | Symbs]), 
    ([(Atom <=> Form) | NewBch], NewSymbs, Prf)
  ).

prove(
  (inf([Tree | Trees], Prems, Conc, Rul), Bch, Symbs), 
  (NewBch, NewSymbs, cut(Prem, PrfA, PrfB))
) :- 
  Tree = inf(_, _, _, _), 
  length(Trees, Lth),
  htn0(Lth, Prems, Prem), 
  prove(
    (Tree, [~ Prem | Bch], Symbs),
    ([~ Prem | TempBch], TempSymbs, PrfB)
  ),
  prove(
    (inf(Trees, Prems, Conc, Rul), [Prem | TempBch], TempSymbs),
    ([Prem | NewBch], NewSymbs, PrfA) 
  ).


% prove(State) :- 
%   get_insts(State, [lemma([Src | _], Tgt, definition_unfolding)]),
%   lits_align(Src, Tgt, Ante, Cons),
%   Ante =.. [Pred | AnteArg], 
%   Cons =.. [Pred | ConsArg], 
%   maplist(mk_pair, AnteArg, ConsArg, Pairs),
%   length(Pairs, Lth),
%   mk_rel_mono(Lth, Pred, Mono), 
%   posit_insts(State, Mono, TempInsts),
%   append(TempInsts, [mono(Pairs), copy_form(Src), beta], NewInsts), 
%   set_insts_auto(State, NewInsts, NewState),
%   prove(NewState).
% prove(State) :- 
%   get_insts(State, [defin(Atom <=> Frm, _) | Insts]),
%   set_insts_auto(State, [def(Atom, Frm) | Insts], NewState),
%   prove(NewState).

% prove(
%   (inf([], Prems, Conc, Rul), Bch, Symbs), 
%   (NewBch, Symbs, cut(Atom, PrfA, PrfB))
% ) :-  
%   % If Rul is one of equational rules
%   member(Rul, [definition_unfolding]),
%   contra_cc([~ Conc | Prems], Atom, PosPrf, NegPrf), 
%   prove_eq([Atom | Bch], NegPrf, [Atom | TempBch], PrfA),
%   prove_eq([~ Atom | TempBch], PosPrf, [~ Atom | NewBch], PrfB).

% prove_rel_mono(Bch, [Eqn | Eqns], Src, NewBch, 
%   gamma(TrmA, gamma(TrmB, cut((TrmA = TrmB), beta(PrfA), PrfB))),
%   lhs(Eqn, TrmA),
%   rhs(Eqn, TrmB),
%   prove_eq(Bch, Eqn, TempBch, PrfB), 
%   prove_rel_mono(TempBch, Eqns, Src, NewBch, PrfA). 

% prove_rel_mono(Bch, [Eqn | Eqns], Src, NewBch, 
%   gamma(TrmA, gamma(TrmB, cut((TrmA = TrmB), beta(PrfA), PrfB))),
  



% prove_rel_mono(Bch, Rel, [Eqn | Eqns], Src, NewBch, copy(Num, Prf)) :- 
%   length(Eqns, Lth),
%   mk_rel_mono(Lth, Rel, Form), 
%   extend_branch(Bch, Form, NewBch, Num),
% 
    






% prove(
%   (inf([], Prems, Conc, _), Bch, Symbs), 
%   (NewBch, Symbs, copy(Lth, Prf))
% ) :-  
%   length(Bch, Lth),
%   mk_imp(Prems, Conc, Imp), 
%   append(Bch, [Imp], NewBch),
%   mk_triv_prf([Imp | NewBch], Imp, Prf).

mk_imp([], Conc, Conc). 

mk_imp([Prem | Prems], Conc, (Prem => Imp)) :-  
  mk_imp(Prems, Conc, Imp). 

mk_triv_prf(_, $false, ff(close)).

% Bch is the current branch, with Cons at the tip.
mk_triv_prf(Bch, Cons, copy(Num, close)) :- 
  nth0(Num, Bch, ~ Cons).

% Bch is the current branch, with (Ante => Cons) at the tip.
mk_triv_prf(Bch, (Ante => Cons), copy(Num, beta(Prf))) :- 
  nth0(Num, Bch, Ante),
  mk_triv_prf([Cons, Ante | Bch], Cons, Prf).

unneg(~ Atom, Atom) :- !.
unneg(Atom, Atom).

all_sub_terms(Term, Terms) :-
  findall(SubTerm, sub_term(SubTerm, Term), SubTerms),
  sort(SubTerms, Terms).

atom_sub_terms(Atom, Terms) :-
  Atom =.. [_ | Args],
  maplist(all_sub_terms, Args, Termss),
  union(Termss, Terms).

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

lhs(eqhyp(LHS, _), LHS).
lhs(eqsymm(LHS, _, _), LHS).
lhs(eqtrans(LHS, _, _, _), LHS).
lhs(eqmono(LHS, _, _), LHS).

rhs(eqhyp(_, RHS), RHS).
rhs(eqsymm(_, _, RHS), RHS).
rhs(eqtrans(_, _, _, RHS), RHS).
rhs(eqmono(_, _, RHS), RHS).

% Propagate the effects of equating TrmA and TrmB
propagate(Eqn, ECs, NewECs) :- 
  lhs(Eqn, LHS),
  rhs(Eqn, RHS),
  pluck(member_ec(LHS), ECs, ECL, ECs1),
  pluck(member_ec(RHS), ECs1, ECR, ECs2),
  ECL = (TreeL, SupsL),
  ECR = (TreeR, SupsR),
  union(SupsL, SupsR, Sups),
  list_prod(SupsL, SupsR, SupPairs), 
  ECs3 = [(bridge(TreeL, Eqn, TreeR), Sups) | ECs2], 
  collect(calc_eqv(ECs3), SupPairs, NewEqns), 
  foldl(propagate, NewEqns, ECs3, NewECs).
  
calc_eqv(ECs, (TrmA, TrmB), eqmono(TrmA, Eqns, TrmB)) :- 
  TrmA =.. [Pred | ArgsA],
  TrmB =.. [Pred | ArgsB],
  maplist(calc_eqn(ECs), ArgsA, ArgsB, Eqns).

calc_eqn(ECs, TrmA, TrmB, Eqn) :- 
  first(calc_eqn_in_ec(TrmA, TrmB), ECs, Eqn).

calc_eqn_in_ec(TrmA, TrmB, (Tree, _), Eqn) :- 
  calc_eqn_in_tree(TrmA, TrmB, Tree, Eqn).

calc_eqn_in_tree(Trm, Trm, elem(Trm), eqrefl(Trm)). 

calc_eqn_in_tree(TrmA, TrmB, bridge(TreeL, Eqn, TreeR), NewEqn) :- 
  ( member_tree(TrmA, TreeL), 
    member_tree(TrmB, TreeL), 
    calc_eqn_in_tree(TrmA, TrmB, TreeL, NewEqn) ) ; 
  ( member_tree(TrmA, TreeR), 
    member_tree(TrmB, TreeR), 
    calc_eqn_in_tree(TrmA, TrmB, TreeR, NewEqn) ) ; 
  ( lhs(Eqn, TrmL), 
    rhs(Eqn, TrmR), 
    calc_eqn_in_tree(TrmA, TrmL, TreeL, EqnL), 
    calc_eqn_in_tree(TrmR, TrmB, TreeR, EqnR), 
    NewEqn = eqtrans(TrmA, EqnL, eqtrans(TrmL, Eqn, EqnR, TrmB), TrmB) ) ;
  ( lhs(Eqn, TrmL), 
    rhs(Eqn, TrmR), 
    calc_eqn_in_tree(TrmB, TrmL, TreeL, EqnL), 
    calc_eqn_in_tree(TrmR, TrmA, TreeR, EqnR), 
    NewEqn = eqtrans(TrmB, EqnL, eqtrans(TrmL, Eqn, EqnR, TrmA), TrmA) ).

cc(EqHyps, ECs, NewECs) :- 
  foldl(propagate, EqHyps, ECs, NewECs).

direct_sub_term(SubTerm, Term) :-
  Term =.. [_ | Args],
  member(SubTerm, Args).

init_ec(Terms, Term, (elem(Term), Sups)) :- 
  include(direct_sub_term(Term), Terms, Sups).

init_ecs(Terms, ECs) :- 
  maplist(init_ec(Terms), Terms, ECs).

mk_eqhyp((TrmA = TrmB), eqhyp(TrmA, TrmB)).

ne_self_prf((~ (Trm = Trm), Prf), (Trm, Prf)).

find_contra(NormLits, (Trm = Trm), refleq, ReflNePrf) :- 
  first(ne_self_prf, NormLits, (Trm, ReflNePrf)).

find_contra(NormLits, Atom, PosPrf, NegPrf) :- 
  member((~ Atom, NegPrf), NormLits), 
  member((Atom, PosPrf), NormLits).

representative(elem(Term), Term).

representative(bridge(Tree, _, _), Term) :-
  representative(Tree, Term).

normalize_term_in(Term, (Tree, _), (Eqn, NormTerm)) :- 
  representative(Tree, NormTerm), 
  calc_eqn_in_tree(Term, NormTerm, Tree, Eqn).

normalize_term(ECs, Term, Eqn, NormTerm) :- 
  first(normalize_term_in(Term), ECs, (Eqn, NormTerm)).


prove_by_ecs(ECs, ~Tgt, ~ Src, 
  not_intro(not_elim(open(~ Src), Prf, $false), ~ Tgt)) :-
  !, prove_by_ecs(ECs, Src, Tgt, TempPrf), 
  close_hyp(Tgt, TempPrf, Prf).

prove_by_ecs(ECs, Tgt, Src, Prf) :- 
  Tgt =.. [Rel | TgtArgs], 
  Src =.. [Rel | SrcArgs], 
  length(TgtArgs, Lth),
  mk_rel_mono(Lth, Rel, Mono), 
  prove_by_mono(ECs, open(Mono), SrcArgs, TgtArgs, Prf).

prove_by_mono(ECs, MonoPrf, [TrmA | TrmsA], [TrmB | TrmsB], Prf) :-
  conc(MonoPrf, Mono), % ! [X, Y] : ((X = Y) => Mono)), 
  fa_inst(TrmA, Mono, MonoA),
  fa_inst(TrmB, MonoA, MonoAB),
  MonoAB = (_ => NewMono),
  equate_by_ecs(ECs, TrmA, TrmB, EqPrf), 
  prove_by_mono(ECs, 
    imp_elim(fa_elim(TrmB, fa_elim(TrmA, MonoPrf, MonoA), MonoAB), EqPrf, NewMono), 
    TrmsA, TrmsB, Prf). 


















/*

prove(State) :-
  get_goal(State, (Bch, [copy(Num) | Insts], copy(Num, Prf))),
  branch_nth0(State, Num, Frm),
  set_goal(State, ([Frm | Bch], Insts, Prf), NewState),
  prove(NewState).

prove(State) :-
  get_goal(State, (Twig, [alpha | Insts], alpha(Prf))),
  get_branch(State, [Frm | _]),
  break_alpha(Frm, FrmA, FrmB),
  set_goal(State, ([FrmB, FrmA | Twig], Insts, Prf), NewState),
  prove(NewState).

prove(State) :-
  get_goal(State, (Twig, [beta | Insts], beta(Prf))), 
  get_branch(State, [FrmB, FrmA | _]),
  break_beta(FrmA, FrmB, FrmC),
  set_goal(State, ([FrmC | Twig], Insts, Prf), NewState),
  prove(NewState).

prove(State) :-
  get_goal(State, (Twig, [gamma(Trm) | Insts], gamma(Trm, Prf))),
  get_branch(State, [Frm | _]),
  break_gamma(Trm, Frm, NewFrm),
  set_goal(State, ([NewFrm | Twig], Insts, Prf), NewState),
  prove(NewState).

prove(State) :- 
  get_goals(State, [(_, [close | _], close) | Goals]),
  get_branch(State, [~ Frm, Frm | _]),
  set_goals(State, Goals, NewState),
  prove(NewState).

prove(State) :- 
  get_goal(State, (Twig, [dne | Insts], dne(Prf))), 
  get_branch(State, [~ ~ Frm | _]),
  set_goal(State, ([Frm | Twig], Insts, Prf), NewState), 
  prove(NewState).

prove(State) :- 
  get_goal(State, (Twig, [tt | Insts], tt(Prf))), 
  set_goal(State, ([$true | Twig], Insts, Prf), NewState), 
  prove(NewState).

prove(State) :- 
  get_goal(State, (Twig, [ff | Insts], ff(Prf))), 
  set_goal(State, ([~ $false | Twig], Insts, Prf), NewState), 
  prove(NewState).

prove(State) :- 
  get_goals(State, [(Twig, [cut(Frm) | _], cut(Frm, PrfA, PrfB)) | Goals]),
  set_goals(State, [([Frm | Twig], [], PrfA), ([~ Frm | Twig], [], PrfB) | Goals], NewState),
  prove(NewState).

% Retroactively extend the theorem being proven.
prove(State) :- 
  get_insts(State, [ext(Frm) | Insts]),
  get_symbs(State, Symbs),
  not(uses_any(Symbs, Frm)),
  get_ext(State, [Frm | NewExt]),
  set_insts(State, Insts, TempState),
  set_ext(TempState, NewExt, NewState),
  prove(NewState).


prove(State) :-
  get_insts(State, [copy_form(Frm) | Insts]),
  branch_where(State, Frm, Num), 
  ( Num = 0 ->
    set_insts_auto(State, Insts, NewState) ;
    set_insts_auto(State, [copy(Num) | Insts], NewState)
  ),
  prove(NewState).

prove(State) :- 
  get_insts(State, []),
  branch_member(State, Frm),
  branch_has(State, ~ Frm),
  set_insts_auto(State, [copy_form(Frm), copy_form(~ Frm), close], NewState),
  prove(NewState).



% If there are more than one lemmas to be proven, cut to 
% spawn a subgoal and continue with the main line of the proof.
prove(State) :-
  get_goals(State, [(Twig, [lemma(Prems, Conc, Rul) | Insts], cut(Conc, PrfA, PrfB)) | Goals]),
  Insts = [_ | _],
  auto_verify(State, Auto),
  set( 
    State, 
    [ 
      ([Conc | Twig], Insts, PrfA), 
      ([~ Conc | Twig], [lemma(Prems, Conc, Rul)], PrfB) | 
      Goals
    ], 
    same, 
    same, 
    Auto, 
    same, 
    NewState
  ),
  prove(NewState).

% If conclusion of lemma is a reflexive equality, prove it immediately.
prove(State) :- 
  get_insts(State, [lemma(_, (Trm = Trm), _)]),
  posit_insts(State, (! [X] : (X = X)), TempInsts),
  append(TempInsts, [gamma(Trm)], NewInsts),
  set_insts_auto(State, NewInsts, NewState),
  prove(NewState).

% Apply symmetry to reverse an existing equation.
prove(State) :- 
  get_insts(State, [lemma(_, (TrmA = TrmB), _)]),
  branch_has(State, (TrmB = TrmA)),
  posit_insts(State, (! [X, Y] : ((X = Y) => (Y = X))), TempInsts),
  append(
    TempInsts, 
    [
      gamma(TrmB), 
      gamma(TrmA), 
      copy_form(TrmB = TrmA),
      beta
    ],
    NewInsts
  ),
  set_insts_auto(State, NewInsts, NewState),
  prove(NewState).

% Apply symmetry to reverse an existing inequation.
prove(State) :- 
  get_insts(State, [lemma(_, ~ (TrmA = TrmB), _)]),
  branch_has(State, ~ (TrmB = TrmA)),
  posit_insts(State, (! [X, Y] : ((X = Y) => (Y = X))), TempInsts),
  append(
    TempInsts,
    [
      gamma(TrmA), 
      gamma(TrmB), 
      copy_form(~ (TrmB = TrmA)),
      beta
    ], 
    NewInsts
  ),
  set_insts_auto(State, NewInsts, NewState),
  prove(NewState).

% If the directive uses a premise that does not exist on the branch,
% that premise must be obtainable from an existing hypothesis via an 
% simple, implicit processing step.
prove(State) :- 
  get_insts(State, [lemma(Prems, Conc, Rul)]), 
  member(Prem, Prems), 
  not(branch_has(State, Prem)), 
  set_insts_auto(State, [lemma([], Prem, implicit), lemma(Prems, Conc, Rul)], NewState),
  prove(NewState).

% If an hypothesis of lemma is a negated reflexive equality, close immediately.
prove(State) :-
  get_insts(State, [lemma([~ (Trm = Trm) | _], _, _)]), 
  posit_insts(State, (! [X] : (X = X)), TempInsts),
  append(
    TempInsts, 
    [
      gamma(Trm), 
      copy_form(~ (Trm = Trm)), 
      close
    ], 
    NewInsts
  ),
  set_insts_auto(State, NewInsts, NewState),
  prove(NewState).


prove(State) :- 
  get_insts(State, [lemma(_, (TrmA = TrmB), congr)]), 
  TrmA =.. [Fun | ArgA], 
  TrmB =.. [Fun | ArgB], 
  maplist(mk_pair, ArgA, ArgB, Pairs),
  length(Pairs, Lth),
  mk_fun_mono(Lth, Fun, Mono), 
  posit_insts(State, Mono, TempInsts),
  append(TempInsts, [mono(Pairs)], NewInsts), 
  set_insts_auto(State, NewInsts, NewState),
  prove(NewState).

prove(State) :- 
  get_insts(State, [mono([(TrmA, TrmB) | Pairs]) | Insts]),
  set_insts_auto(
    State,
    [ 
      gamma(TrmA), 
      gamma(TrmB), 
      lemma([], (TrmA = TrmB), congr),
      beta,
      mono(Pairs) |
      Insts
    ],
    NewState
  ),
  prove(NewState).

prove(State) :- 
  get_insts(State, [mono([]) | Insts]),
  set_insts_auto(State, Insts, NewState),
  prove(NewState).

% If all goals are closed, finish.
prove(State) :- 
  get_goals(State, []),
  get_ext(State, []), 
  write("\n\nQED.\n\n").

  

id_theorem_string((Id, Thm), Str) :- 
  atom_string(Id, IdStr), 
  theorem_string(Thm, ThmStr),
  strings_concat([IdStr, " : ", ThmStr], Str).
 
%loop(write(Filename)) :- 
%  findall(theorem(Id, Smt, Prf), theorem(Id, Smt, Prf), Thms),
%  open(Filename, write, Stream),
%  maplist(write_punct(Stream), Thms),
%  close(Stream),
%  loop.



read_input(Inp) :-
  read_term(user_input, Inp, [syntax_errors(fail)]).


*/