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
alpha(Form) :- break_alpha(Form, _, _).

break_beta(~ (FrmA & FrmB), ~ FrmA, ~ FrmB).
break_beta(FrmA | FrmB, FrmA, FrmB).
break_beta(FrmA => FrmB, ~ FrmA, FrmB).

beta(Form) :- break_beta(Form, _, _).

break_gamma(Term, ! Num : Form, NewForm) :- !, 
  substitute(Num, Term, Form, NewForm).

break_gamma(Term, ~ (? Num : Form), ~ NewForm) :- 
  substitute(Num, Term, Form, NewForm).

gamma(! _ : _).
gamma(~ (? _ : _)).

break_delta(Par, (? Var : Form), NewForm) :- !, 
  substitute(Var, &(Par), Form, NewForm).

break_delta(Par, ~ (! Var : Form), ~ NewForm) :- 
  substitute(Var, &(Par), Form, NewForm).

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
  not(Exp = &(_)), 
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

mk_fun_mono(0, VarsA, [], VarsB, [], Fun, (TermA = TermB)) :- 
  TermA =.. [Fun | VarsA],
  TermB =.. [Fun | VarsB].

mk_fun_mono(Num, VarsA, [X | ExtA], VarsB, [Y | ExtB], Fun, ! [X, Y] : ((X = Y) => Frm)) :- 
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

% Propagate the effects of equating TermA and TermB
propagate((TermA, Prf, TermB), ECs, NewECs) :- 
  pick(member_ec(TermA), ECs, ECL, ECs1),
  pick(member_ec(TermB), ECs1, ECR, ECs2),
  ECL = (TreeL, SupsL),
  ECR = (TreeR, SupsR),
  union(SupsL, SupsR, Sups),
  list_prod(SupsL, SupsR, SupPairs), 
  ECs3 = [(bridge(TreeL, (TermA, Prf, TermB), TreeR), Sups) | ECs2], 
  collect(mono_ecs_eqprf(ECs3), SupPairs, EqPrfs), 
  foldl(propagate, EqPrfs, ECs3, NewECs).
  
mono_ecs_eqprf(ECs, (TermA, TermB), (TermA, Prf, TermB)) :- 
  mono_ecs_prf(ECs, TermA, TermB, Prf). 

% Prove TermA = TermB by monotonicity + equivalences classes
mono_ecs_prf(ECs, TermA, TermB, EqPrf) :- 
  TermA =.. [Fun | TermsA],
  TermB =.. [Fun | TermsB],
  length(TermsA, Lth),
  mk_fun_mono(Lth, Fun, Mono), 
  mono_ecs_prf_core(ECs, Mono, TermsA, TermsB, EqPrf).

mono_ecs_prf_core(_, (_ = _), [], [], close).

mono_ecs_prf_core(ECs, Mono, [TermA | TermsA], [TermB | TermsB], 
  gamma(TermA, Mono, 
    gamma(TermB, MonoA, 
      cut(TermA = TermB, 
        beta(MonoAB, (TermA = TermB), PrfA), 
        PrfB)))) :-
  break_gamma(TermA, Mono, MonoA),
  break_gamma(TermB, MonoA, MonoAB),
  MonoAB = (_ => NewMono),
  mono_ecs_prf_core(ECs, NewMono, TermsA, TermsB, PrfA), 
  ecs_prf(ECs, TermA, TermB, PrfB).

ecs_prf(ECs, TermA, TermB, Prf) :- 
  first(ec_prf(TermA, TermB), ECs, Prf).

ec_prf(TermA, TermB, (Tree, _), Eqn) :- 
  et_prf(TermA, TermB, Tree, Eqn).

et_prf(Term, Term, elem(Term), gamma(Term, (! [X] : (X = X)), close)).

et_prf(TermA, TermB, bridge(TreeL, (TermL, PrfLR, TermR), TreeR), PrfAB) :- 
  ( member_tree(TermA, TreeL), 
    member_tree(TermB, TreeL), 
    et_prf(TermA, TermB, TreeL, PrfAB) ) ; 
  ( member_tree(TermA, TreeR), 
    member_tree(TermB, TreeR), 
    et_prf(TermA, TermB, TreeR, PrfAB) ) ; 
  ( et_prf(TermA, TermL, TreeL, PrfL), 
    et_prf(TermR, TermB, TreeR, PrfR), 
    prove_eq_trans([TermA, TermL, TermR, TermB], [PrfL, PrfLR, PrfR], PrfAB) ) ;
  ( et_prf(TermB, TermL, TreeL, PrfL), 
    et_prf(TermR, TermA, TreeR, PrfR), 
    prove_eq_trans([TermB, TermL, TermR, TermA], [PrfL, PrfLR, PrfR], PrfAB) ).

prove_eq_trans([_, _], [Prf], Prf). 

prove_eq_trans([TermA, TermB | Terms], [PrfAB | Prfs], 
  gamma(TermA, (! [X, Y, Z] : ((X = Y) => ((Y = Z) => (X = Z)))), 
    gamma(TermB, (! [Y, Z] : ((TermA = Y) => ((Y = Z) => (TermA = Z)))),
      gamma(TermC, (! [Z] : ((TermA = TermB) => ((TermB = Z) => (TermA = Z)))),
        cut(TermA = TermB, 
          beta((TermA = TermB) => ((TermB = TermC) => (TermA = TermC)), 
            (TermA = TermB), 
            cut(TermB = TermC, 
              beta((TermB = TermC) => (TermA = TermC), 
                TermB = TermC, 
                close), 
              PrfBC)), 
          PrfAB))))) :-
  last(Terms, TermC),
  prove_eq_trans([TermB | Terms], Prfs, PrfBC).

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

% ne_self_prf((~ (Term = Term), Prf), (Term, Prf)).
% 
% find_contra(NormLits, (Term = Term), refleq, ReflNePrf) :- 
%   first(ne_self_prf, NormLits, (Term, ReflNePrf)).
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
%   et_prf(Term, NormTerm, Tree, Eqn).
% 
% normalize_term(ECs, Term, Eqn, NormTerm) :- 
%   first(normalize_term_in(Term), ECs, (Eqn, NormTerm)).


eq_mod_ec(TermA, TermB, EC) :- 
  member_ec(TermA, EC),
  member_ec(TermB, EC).

eq_mod_ecs(ECs, TermA, TermB) :- 
  any(eq_mod_ec(TermA, TermB), ECs).

iff_mod_ecs(ECs, AtomA, AtomB) :- 
  AtomA =.. [Rel | TermsA],
  AtomB =.. [Rel | TermsB],
  maplist(eq_mod_ecs(ECs), TermsA, TermsB).

ecs_lits_prf(ECs, Lits, Prf) :- 
  occurs((~ (TermA = TermB)), Lits),
  eq_mod_ecs(ECs, TermA, TermB),
  ecs_prf(ECs, TermA, TermB, Prf).

propatom(Atom) :- 
  not(member(Atom, 
    [ (! _ : _), (? _ : _), (~ _), 
      (_ | _), (_ & _), (_ => _), (_ <=> _) ])).

literal(~ Atom) :- 
  propatom(Atom).

literal(Atom) :- 
  propatom(Atom).

conc(open(Conc), Conc).
conc(closed(Conc), Conc).

conc(not_elim(_, _), $false).
conc(not_intro(_, Conc), Conc).

conc(or_elim(_, _, _, Conc), Conc).
conc(or_intro(_, Conc), Conc).

conc(and_elim(_, _, Conc), Conc).
conc(and_intro(_, _, Conc), Conc).

conc(imp_elim(_, _, Conc), Conc).
conc(imp_intro(_, Conc), Conc).

conc(fa_elim(_, _, Conc), Conc).
conc(fa_intro(_, Conc), Conc).

map_hyp(Goal, closed(Form), Prf) :-
  call(Goal, closed(Form), Prf).

map_hyp(Goal, open(Form), Prf) :-
  call(Goal, open(Form), Prf).

map_hyp(Goal, 
  or_elim(PrfA, PrfB, PrfC, Conc), 
  or_elim(NewPrfA, NewPrfB, NewPrfC, Conc)) :- 
  map_hyp(Goal, PrfA, NewPrfA),
  map_hyp(Goal, PrfB, NewPrfB),
  map_hyp(Goal, PrfC, NewPrfC).

map_hyp(Goal, 
  or_intro(Prf, Conc), 
  or_intro(NewPrf, Conc)) :- 
  map_hyp(Goal, Prf, NewPrf).

map_hyp(Goal, and_elim(Dir, Prf, Conc), and_elim(Dir, NewPrf, Conc)) :- 
  map_hyp(Goal, Prf, NewPrf).

map_hyp(Goal, and_intro(PrfA, PrfB, Conc), and_intro(NewPrfA, NewPrfB, Conc)) :- 
  map_hyp(Goal, PrfA, NewPrfA),
  map_hyp(Goal, PrfB, NewPrfB).

map_hyp(Goal, not_elim(PrfA, PrfB), not_elim(NewPrfA, NewPrfB)) :- 
  map_hyp(Goal, PrfA, NewPrfA),
  map_hyp(Goal, PrfB, NewPrfB).

map_hyp(Goal, not_intro(Prf, Conc), not_intro(NewPrf, Conc)) :- 
  map_hyp(Goal, Prf, NewPrf).

map_hyp(Goal, imp_elim(PrfA, PrfB, Conc), imp_elim(NewPrfA, NewPrfB, Conc)) :- 
  map_hyp(Goal, PrfA, NewPrfA),
  map_hyp(Goal, PrfB, NewPrfB).

map_hyp(Goal, imp_intro(Prf, Conc), imp_intro(NewPrf, Conc)) :- 
  map_hyp(Goal, Prf, NewPrf).

map_hyp(Goal, fa_elim(Term, Prf, Conc), fa_elim(Term, NewPrf, Conc)) :- 
  map_hyp(Goal, Prf, NewPrf).

map_hyp(Goal, fa_intro(Prf, Conc), fa_intro(NewPrf, Conc)) :- 
  map_hyp(Goal, Prf, NewPrf).

map_hyp(Goal, raa(Prf, Conc), raa(NewPrf, Conc)) :- 
  map_hyp(Goal, Prf, NewPrf).

% is_hyp((file(_, _), _)).

id_conc(Id, Conc) :- 
  fof(Id, _, Conc, _).

init_goal((introduced(Rul, _), Conc), ([], Form, Rul)) :- 
 translate(0, Conc, Form).

init_goal((inference(Rul, _, PremIds), Conc), (Forms, Form, Rul)) :- 
 translate(0, Conc, Form),
  maplist(id_conc, PremIds, Prems),
  maplist(translate(0), Prems, Forms).

logical(Rul) :-
  member(
    Rul,
    [
      resolution,
      cnf_transformation,
      subsumption_resolution,
      avatar_sat_refutation,
      avatar_contradiction_clause
    ]
  ).

equational(Rul) :-
  member(Rul, [definition_unfolding, trivial_inequality_removal]).

/* 

% linear(+Num, +Forms, -Proof, -NewNum, -NewForms -SubPrf) :
% Given a fresh parameter number 'Num' and formulas 'Forms', 
% binds 'Proof' to a partially instantiated proof in which all
% applicable linear rules have been applied, 'NewNum' to the 
% new fresh parameter number, 'NewForms' to the new set of 
% working formulas, and 'SubPrf' to the remaining proof after 
% linear rule applications.

linear(Num, Forms, dne(~ ~ Form, Prf), NewNum, NewForms, NewPrf) :-
  pluck(Forms, ~ ~ Form, Rem), !, 
  linear(Num, [Form | Rem], Prf, NewNum, NewForms, NewPrf).

linear(Num, Forms, alpha(Form, Prf), NewNum, NewForms, NewPrf) :- 
  pick(alpha, Forms, Form, Rem), 
  break_alpha(Form, FormA, FormB), !,
  linear(Num, [FormA, FormB | Rem], Prf, NewNum, NewForms, NewPrf).

linear(Num, Forms, delta(&(Num), ExForm, Prf), NewNum, NewForms, NewPrf) :- 
  pick(delta, Forms, ExForm, Rem), 
  break_delta(&(Num), ExForm, Form), 
  Succ is Num + 1, 
  linear(Succ, [Form | Rem], Prf, NewNum, NewForms, NewPrf).

linear(Num, Forms, beta(Form, close, Prf), NewNum, NewForms, NewPrf) :-
  pick(beta, Forms, Form, Rem), 
  break_beta(Form, FormA, FormB), 
  has_complement(FormA, Forms), !,
  linear(Num, [FormB | Rem], Prf, NewNum, NewForms, NewPrf).

linear(Num, Forms, beta(Form, Prf, close), NewNum, NewForms, NewPrf) :-
  pick(beta, Forms, Form, Rem), 
  break_beta(Form, FormA, FormB), 
  has_complement(FormB, Forms), 
  linear(Num, [FormA | Rem], Prf, NewNum, NewForms, NewPrf).

linear(Num, Forms, Prf, Num, Forms, Prf).

tableaux(_, _, Forms, ff(close)) :- 
  member($false, Forms), !.

tableaux(_, _, Forms, tt(close)) :- 
  member(~ $true, Forms), !.

tableaux(_, _, Forms, close) :-
  include(literal, Forms, Lits),
  find_complements(Lits).

tableaux(FaNum, ExNum, Forms, Prf) :-
  linear(ExNum, Forms, Prf, NewExNum, NewForms, NewPrf), 
  tableaux(FaNum, NewExNum, NewForms, NewPrf).

tableaux(FaNum, ExNum, Forms, cut(FormA, beta(FormAB, FormA, PrfA), PrfB)) :-
  pick(beta, Forms, FormAB, Rem), 
  beta_minor(FormAB, FormA), !,
  break_beta(FormAB, FormA, FormB),
  tableaux(FaNum, ExNum, [FormB | Rem], PrfA),
  tableaux(FaNum, ExNum, [~ FormA | Rem], PrfB).

tableaux(FaNum, ExNum, Forms, gamma(Term, FaForm, Prf)) :- 
  pick(gamma, Forms, FaForm, Rem),
  0 < FaNum, !, 
  FaPred is FaNum - 1,  
  break_gamma(Term, FaForm, Form), 
  append([Form | Rem], [FaForm], NewForms), 
  tableaux(FaPred, ExNum, NewForms, Prf).

tableaux(FaNum, Forms, Prf) :- 
  tableaux(FaNum, 0, Forms, Prf).

% If a query 'tableaux(FaNum, Forms, Prf)' failed, it means that 
%the proof search attempted to instantiate gamma subformulas more 
% than 'FaNum' times. In that case, Increment 'FaNum' and try again.
tableaux(FaNum, Forms, Prf) :- 
  FaSucc is FaNum + 1,
  tableaux(FaSucc, Forms, Prf).

tableaux(Forms, Prf) :- 
  tableaux(0, Forms, Prf).

*/

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

contab(Forms, Lim, Par, Mode, Pth, ~ ~ Form, dne(Form, Prf)) :- 
  contab(Forms, Lim, Par, Mode, Pth, Form, Prf).

contab(Forms, Lim, Par, start, Pth, Form, alpha(Form, Prf)) :- 
  break_alpha(Form, FormA, FormB), 
  ( ( positive(FormA), contab([FormB | Forms], Lim, Par, start, Pth, FormA, Prf) ) ; 
    ( positive(FormB), contab([FormA | Forms], Lim, Par, start, Pth, FormB, Prf) ) ).

contab(Forms, Lim, Par, Mode, Pth, Form, alpha(Form, Prf)) :- 
  member(Mode, [block, match(_)]),
  break_alpha(Form, FormA, FormB), 
  ( contab([FormB | Forms], Lim, Par, Mode, Pth, FormA, Prf) ; 
    contab([FormA | Forms], Lim, Par, Mode, Pth, FormB, Prf) ).

contab(Forms, Lim, Par, Mode, Pth, Form, beta(Form, PrfA, PrfB)) :- 
  member(Mode, [start, block]),
  break_beta(Form, FormA, FormB), 
  contab(Forms, Lim, Par, Mode, Pth, FormA, PrfA),
  contab(Forms, Lim, Par, Mode, Pth, FormB, PrfB). 

contab(Forms, Lim, Par, match(Lit), Pth, Form, beta(Form, PrfA, PrfB)) :- 
  break_beta(Form, FormA, FormB), 
  (
    ( contab(Forms, Lim, Par, match(Lit), Pth, FormA, PrfA),
      contab(Forms, Lim, Par, block, Pth, FormB, PrfB) ) ;  
    ( contab(Forms, Lim, Par, match(Lit), Pth, FormB, PrfB),
      contab(Forms, Lim, Par, block, Pth, FormA, PrfA) ) 
  ).

contab(Forms, Lim, Par, Mode, Pth, FaForm, gamma(Term, FaForm, Prf)) :- 
  break_gamma(Term, FaForm, Form), 
  contab([FaForm | Forms], Lim, Par, Mode, Pth, Form, Prf).

contab(Forms, Lim, Par, Mode, Pth, ExForm, delta(Par, ExForm, Prf)) :- 
  break_delta(Par, ExForm, Form), 
  Succ is Par + 1,
  contab(Forms, Lim, Succ, Mode, Pth, Form, Prf).

contab(Forms, Lim, Par, Mode, Pth, Lit, Prf) :- 
  literal(Lit), 
  member(Mode, [start, block]), 
  (
    (has_complement(Lit, Pth), Prf = close) ; 
    ( 
      decr_if_pos(Lim, Pred),
      pluck(Forms, Form, Rem),
      contab(Rem, Pred, Par, match(Lit), [Lit | Pth], Form, Prf)  
    )
  ).

contab(_, _, _, match(Cmp), _, Lit, close) :- 
  literal(Lit), 
  complementary(Lit, Cmp).

contab(Forms, Lim, Prf) :- 
  add_eq_axioms(Forms, NewForms),
  pluck(NewForms, Form, Rem),
  positive(Form),
  contab(Rem, Lim, 0, start, [$true, ~ $false], Form, Prf).

contab(Forms, 10, timeout(Forms)).

contab(Forms, Lim, Prf) :- 
  Succ is Lim + 1,
  contab(Forms, Succ, Prf).

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

funs(Term, [Term]) :-
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
    member('=', Rels) ->
    (
      maplist(mk_mono_fun, Funs, MonoFuns),
      maplist(mk_mono_rel, Rels, MonoRels),
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

has_complement(Lit, Pth) :-
  member(Cmp, Pth),
  complementary(Lit, Cmp).

complementary(~ FormA, FormB) :- !,
  unify_with_occurs_check(FormA, FormB).
  
complementary(FormA, ~ FormB) :- !,
  unify_with_occurs_check(FormA, FormB).

% find_complements([Lit | Lits]) :- 
%   complementary(Lit, Cmpl), 
%   member(Cmpl, Lits).
% 
% find_complements([_ | Lits]) :- 
%   find_complements(Lits).

elab((Prems, Conc, Rul), lemma(Prf, Conc)) :- 
  logical(Rul),
  contab([~ Conc | Prems], 0, Prf), !.

% elab((Prems, Conc, Rul), lemma(Prf, Conc)) :- 
%   equational(Rul),
%   Lits = [~ Conc | Prems], 
%   lits_sub_terms(Lits, Terms),
%   init_ecs(Terms, InitECs), 
%   collect(mk_eqhyp, Prems, EqHyps),
%   cc(EqHyps, InitECs, ECs),
%   ecs_lits_prf(ECs, Lits, Prf), !.

elab((Prems, Conc, Rul), admit(Prems, Conc, Rul)) :- !. 

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