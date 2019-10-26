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

check(_, open(_)).

check(Hyps, closed(Form)) :- 
  member(Form, Hyps).

check(Hyps, fa_elim(Term, Prf, Form)) :- 
  conc(Prf, FaForm), 
  fa_inst(Term, FaForm, FormTerm), 
  Form =@= FormTerm, 
  check(Hyps, Prf).

check(Hyps, imp_elim(PrfA, PrfB, FormB)) :- 
  conc(PrfA, FormA => FormB), 
  conc(PrfB, FormA), 
  check(Hyps, PrfA),
  check(Hyps, PrfB).

check(Hyps, not_elim(PrfA, PrfB, $false)) :- 
  conc(PrfA, ~ Form), 
  conc(PrfB, Form), 
  check(Hyps, PrfA),
  check(Hyps, PrfB).

check(Hyps, and_elim_left(Prf, Conc)) :- 
  conc(Prf, Conc & _), 
  check(Hyps, Prf).

check(Hyps, and_elim_right(Prf, Conc)) :- 
  conc(Prf, _ & Conc), 
  check(Hyps, Prf).

check(Hyps, raa(Prf, Conc)) :- 
  conc(Prf, $false), 
  check([~ Conc | Hyps], Prf).




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

fa_inst(Trm, (! [X | Xs] : Frm), (! Ys : NewFrm)) :- !, 
  copy_term((! [X | Xs] : Frm), (! [Y | Ys] : NewFrm)), 
  Y = Trm.

break_gamma(Trm, ~ (? [X] : Frm), ~ NewFrm) :- !, 
  copy_term((? [X] : Frm), (? [Y] : NewFrm)), 
  Y = Trm.

break_gamma(Trm, ~ (? [X | Xs] : Frm), ~ (? Ys : NewFrm)) :- !, 
  copy_term((? [X | Xs] : Frm), (? [Y | Ys] : NewFrm)), 
  Y = Trm.

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

% id_form(Id, Form) :-
%   fof(Id, _, Conc, _),
%   desugar(Conc, Form).
% 
% id_tree(Id, hyp(Form)) :-
%   fof(Id, _, Conc, file(_, _)),
%   desugar(Conc, Form).
% 
% id_tree(Id, def(Form, Rul)) :-
%   fof(Id, _, Conc, introduced(Rul, _)), !,
%   desugar(Conc, Form).
% 
% id_tree(Id, inf(Trees, Forms, Form, Rul)) :-  
%   fof(Id, _, Conc, inference(Rul, _, Ids)), !,
%   maplist(id_tree, Ids, Trees),
%   maplist(id_form, Ids, Forms),
%   desugar(Conc, Form).

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

% mk_imp([], Conc, Conc). 
% 
% mk_imp([Prem | Prems], Conc, (Prem => Imp)) :-  
%   mk_imp(Prems, Conc, Imp). 

unneg(~ Atom, Atom) :- !.
unneg(Atom, Atom).

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

lhs(EqPrf, LHS) :-
  conc(EqPrf, (LHS = _)).

rhs(EqPrf, RHS) :-
  conc(EqPrf, (_ = RHS)).

% Propagate the effects of equating TrmA and TrmB
propagate(Eqn, ECs, NewECs) :- 
  lhs(Eqn, LHS),
  rhs(Eqn, RHS),
  pick(member_ec(LHS), ECs, ECL, ECs1),
  pick(member_ec(RHS), ECs1, ECR, ECs2),
  ECL = (TreeL, SupsL),
  ECR = (TreeR, SupsR),
  union(SupsL, SupsR, Sups),
  list_prod(SupsL, SupsR, SupPairs), 
  ECs3 = [(bridge(TreeL, Eqn, TreeR), Sups) | ECs2], 
  collect(prove_eq_ecs(ECs3), SupPairs, NewEqns), 
  foldl(propagate, NewEqns, ECs3, NewECs).
  
prove_eq_ecs(ECs, (TrmA, TrmB), Prf) :- 
  TrmA =.. [Fun | TrmsA],
  TrmB =.. [Fun | TrmsB],
  length(TrmsA, Lth),
  mk_fun_mono(Lth, Fun, Mono), 
  prove_mono_cons(ECs, open(Mono), TrmsA, TrmsB, Prf).

prove_eq_ecs(ECs, TrmA, TrmB, Eqn) :- 
  first(prove_eq_ec(TrmA, TrmB), ECs, Eqn).

prove_eq_ec(TrmA, TrmB, (Tree, _), Eqn) :- 
  prove_eq_et(TrmA, TrmB, Tree, Eqn).

prove_eq_trans([_, _], [Prf], Prf). 

prove_eq_trans([TrmA, TrmB | Trms], [PrfAB | Prfs], 
  imp_elim(
    imp_elim(
      fa_elim(
        TrmC,
        fa_elim(
          TrmB,
          fa_elim(
            TrmA, 
            open(! [X, Y, Z] : ((X = Y) => ((Y = Z) => (X = Z)))), 
            (! [Y, Z] : ((TrmA = Y) => ((Y = Z) => (TrmA = Z))))
          ), 
          (! [Z] : ((TrmA = TrmB) => ((TrmB = Z) => (TrmA = Z))))
        ),
        ((TrmA = TrmB) => ((TrmB = TrmC) => (TrmA = TrmC)))
      ),
      PrfAB,
      ((TrmB = TrmC) => (TrmA = TrmC))
    ),
    PrfBC, 
    (TrmA = TrmC)
  )
) :-
  prove_eq_trans([TrmB | Trms], Prfs, PrfBC), 
  rhs(PrfBC, TrmC).

prove_eq_et(Trm, Trm, elem(Trm), 
  fa_elim(Trm, open(! [X] : (X = X)), (Trm = Trm))). 

prove_eq_et(TrmA, TrmB, bridge(TreeL, PrfLR, TreeR), PrfAB) :- 
  ( member_tree(TrmA, TreeL), 
    member_tree(TrmB, TreeL), 
    prove_eq_et(TrmA, TrmB, TreeL, PrfAB) ) ; 
  ( member_tree(TrmA, TreeR), 
    member_tree(TrmB, TreeR), 
    prove_eq_et(TrmA, TrmB, TreeR, PrfAB) ) ; 
  ( lhs(Eqn, TrmL), 
    rhs(Eqn, TrmR), 
    prove_eq_et(TrmA, TrmL, TreeL, PrfL), 
    prove_eq_et(TrmR, TrmB, TreeR, PrfR), 
    prove_eq_trans([TrmA, TrmL, TrmR, TrmB], [PrfL, PrfLR, PrfR], PrfAB) ) ;
  ( lhs(Eqn, TrmL), 
    rhs(Eqn, TrmR), 
    prove_eq_et(TrmB, TrmL, TreeL, PrfL), 
    prove_eq_et(TrmR, TrmA, TreeR, PrfR), 
    prove_eq_trans([TrmB, TrmL, TrmR, TrmA], [PrfL, PrfLR, PrfR], PrfAB) ).

cc(EqHyps, ECs, NewECs) :- 
  foldl(propagate, EqHyps, ECs, NewECs).

direct_sub_term(SubTerm, Term) :-
  Term =.. [_ | Args],
  member(SubTerm, Args).

init_ec(Terms, Term, (elem(Term), Sups)) :- 
  include(direct_sub_term(Term), Terms, Sups).

init_ecs(Terms, ECs) :- 
  maplist(init_ec(Terms), Terms, ECs).

mk_eqhyp((TrmA = TrmB), open(TrmA = TrmB)).

% ne_self_prf((~ (Trm = Trm), Prf), (Trm, Prf)).
% 
% find_contra(NormLits, (Trm = Trm), refleq, ReflNePrf) :- 
%   first(ne_self_prf, NormLits, (Trm, ReflNePrf)).
% 
% find_contra(NormLits, Atom, PosPrf, NegPrf) :- 
%   member((~ Atom, NegPrf), NormLits), 
%   member((Atom, PosPrf), NormLits).
% 
% representative(elem(Term), Term).
% 
% representative(bridge(Tree, _, _), Term) :-
%   representative(Tree, Term).
% 
% normalize_term_in(Term, (Tree, _), (Eqn, NormTerm)) :- 
%   representative(Tree, NormTerm), 
%   prove_eq_et(Term, NormTerm, Tree, Eqn).
% 
% normalize_term(ECs, Term, Eqn, NormTerm) :- 
%   first(normalize_term_in(Term), ECs, (Eqn, NormTerm)).


eq_mod_ec(TrmA, TrmB, EC) :- 
  member_ec(TrmA, EC),
  member_ec(TrmB, EC).

eq_mod_ecs(ECs, TrmA, TrmB) :- 
  any(eq_mod_ec(TrmA, TrmB), ECs).

iff_mod_ecs(ECs, AtomA, AtomB) :- 
  AtomA =.. [Rel | TermsA],
  AtomB =.. [Rel | TermsB],
  maplist(eq_mod_ecs(ECs), TermsA, TermsB).

prove_by_ecs(ECs, Lits, not_elim(open(~ (TrmA = TrmB)), Prf, $false)) :- 
  occurs((~ (TrmA = TrmB)), Lits),
  eq_mod_ecs(ECs, TrmA, TrmB),
  prove_eq_ecs(ECs, TrmA, TrmB, Prf).

prove_by_ecs(ECs, Lits, not_elim(open(~ AtomB), imp_elim(Prf, open(AtomA), AtomB), $false)) :- 
  occurs(AtomA, Lits),
  occurs((~ AtomB), Lits),
  iff_mod_ecs(ECs, AtomA, AtomB), 
  AtomA =.. [Rel | TermsA], 
  AtomB =.. [Rel | TermsB], 
  length(TermsA, Lth),
  mk_rel_mono(Lth, Rel, Mono), 
  prove_mono_cons(ECs, open(Mono), TermsA, TermsB, Prf).

prove_mono_cons(ECs, MonoPrf, [TrmA | TrmsA], [TrmB | TrmsB], Prf) :-
  conc(MonoPrf, Mono), % ! [X, Y] : ((X = Y) => Mono)), 
  fa_inst(TrmA, Mono, MonoA),
  fa_inst(TrmB, MonoA, MonoAB),
  MonoAB = (_ => NewMono),
  prove_eq_ecs(ECs, TrmA, TrmB, EqPrf), 
  prove_mono_cons(ECs, 
    imp_elim(fa_elim(TrmB, fa_elim(TrmA, MonoPrf, MonoA), MonoAB), EqPrf, NewMono), 
    TrmsA, TrmsB, Prf). 

prove_mono_cons(_, Prf, [], [], Prf).

% not 
% imp 
% fa_elim

conc(open(Conc), Conc).
conc(closed(Conc), Conc).
conc(not_elim(_, _, Conc), Conc).
conc(not_intro(_, Conc), Conc).
conc(imp_elim(_, _, Conc), Conc).
conc(imp_intro(_, Conc), Conc).
conc(fa_elim(_, _, Conc), Conc).
conc(fa_intro(_, Conc), Conc).

map_hyp(Goal, closed(Form), Prf) :-
  call(Goal, closed(Form), Prf).

map_hyp(Goal, open(Form), Prf) :-
  call(Goal, open(Form), Prf).

map_hyp(Goal, not_elim(PrfA, PrfB, Conc), not_elim(NewPrfA, NewPrfB, Conc)) :- 
  map_hyp(Goal, PrfA, NewPrfA),
  map_hyp(Goal, PrfB, NewPrfB).

map_hyp(Form, not_intro(Prf, Conc), not_intro(NewPrf, Conc)) :- 
  map_hyp(Form, Prf, NewPrf).

map_hyp(Form, imp_elim(PrfA, PrfB, Conc), imp_elim(NewPrfA, NewPrfB, Conc)) :- 
  map_hyp(Form, PrfA, NewPrfA),
  map_hyp(Form, PrfB, NewPrfB).

map_hyp(Form, imp_intro(Prf, Conc), imp_intro(NewPrf, Conc)) :- 
  map_hyp(Form, Prf, NewPrf).

map_hyp(Form, fa_elim(Trm, Prf, Conc), fa_elim(Trm, NewPrf, Conc)) :- 
  map_hyp(Form, Prf, NewPrf).

map_hyp(Form, fa_intro(Prf, Conc), fa_intro(NewPrf, Conc)) :- 
  map_hyp(Form, Prf, NewPrf).

is_hyp((file(_, _), _)).

id_conc(Id, Conc) :- 
  fof(Id, _, Conc, _).

init_goal((inference(Rul, _, PremIds), Conc), deduce(NewPrems, NewConc, Rul)) :- 
  desugar(Conc, NewConc),
  maplist(id_conc, PremIds, Prems),
  maplist(desugar, Prems, NewPrems).

propositional(Rul) :-
  member(Rul, [cnf_transformation]).

equational(Rul) :-
  member(Rul, [definition_unfolding, trivial_inequality_removal]).

infer_from(_, closed(Form), closed(Form)).
infer_from((FrmA & FrmB), open(FrmA), and_elim_left(open(FrmA & FrmB), FrmA)).
infer_from((FrmA & FrmB), open(FrmB), and_elim_right(open(FrmA & FrmB), FrmB)).

prove_nd(Fs, not_elim(open(~ F), open(F), $false)) :- 
  occurs(~ F, Fs),
  occurs(F, Fs).

prove_nd(Forms, Prf) :- 
  pluck(Forms, (FrmP & FrmQ), Rem), 
  prove_nd([FrmP, FrmQ | Rem], TempPrf),
  map_hyp(infer_from(FrmP & FrmQ), TempPrf, Prf).

% prove_nd(Forms, Prf) :- 
%   pluck(Forms, (FrmP | FrmQ), Rem), 
%   prove_nd([FrmP, FrmQ | Rem], TempPrf),
%   map_hyp(infer_from(FrmP & FrmQ), TempPrf, Prf).
% 
% prove_nd(Forms, Prf) :- 
%   pluck(Forms, (FrmP => FrmQ), Rem), 
%   prove_nd([FrmP, FrmQ | Rem], TempPrf),
%   map_hyp(infer_from(FrmP & FrmQ), TempPrf, Prf).

close_if_eq(_, closed(Form), closed(Form)).
close_if_eq(Form, open(Form), closed(Form)) :- !.
close_if_eq(_, open(Form), open(Form)).

close_hyp(Form, Prf, NewPrf) :-
  map_hyp(close_if_eq(Form), Prf, NewPrf).

prove(deduce(Prems, Conc, Rul), raa(Prf, Conc)) :- 
  propositional(Rul),
  prove_nd([~ Conc | Prems], TempPrf),
  close_hyp(~ Conc, TempPrf, Prf).

prove(deduce(Prems, Conc, Rul), Prf) :- 
  equational(Rul),
  Lits = [~ Conc | Prems], 
  lits_sub_terms(Lits, Terms),
  init_ecs(Terms, InitECs), 
  collect(mk_eqhyp, Prems, EqHyps),
  cc(EqHyps, InitECs, ECs),
  prove_by_ecs(ECs, Lits, FalsePrf),  
  ( ( Conc = $false, Prf = FalsePrf ) ; 
    ( close_hyp(~ Conc, FalsePrf, TempPrf), 
      Prf = raa(TempPrf, Conc) ) ).

prove(deduce(Prems, Conc, Rul), admit(Prems, Conc, Rul)). 

prove_debug(Source) :-
  dynamic(fof/4),
  retractall(fof(_, _, _, _)),
  consult(Source),
  findall((Just, Conc), fof(_, _, Conc, Just), Lines),
  exclude(is_hyp, Lines, Steps),
  maplist(init_goal, Steps, Goals),
  maplist(prove, Goals, Prfs),
  maplist(check([]), Prfs),
  write("CHECK SUCCESS!!!").

verify(Source) :-
  retractall(theorem(_, _)),
  consult(Source),
  theorem(Smt, Prf),
  verify(Smt, Prf),
  write("Proof verified : "),
  maplist(form_string, Smt, Strs),
  strings_concat_with(", ", Strs, Str),
  write(Str).