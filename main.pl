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
      avatar_contradiction_clause,
      avatar_component_clause
    ]
  ).

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

contab(Forms, Lim, Par, Terms, Mode, Lems, Pth, ~ ~ Form, NewLems, dne(Form, Prf)) :- 
  contab(Forms, Lim, Par, Terms, Mode, Lems, Pth, Form, NewLems, Prf).

contab(Forms, Lim, Par, Terms, start, Lems, Pth, Form, NewLems, alpha(Form, Prf)) :- 
  break_alpha(Form, FormA, FormB), 
  ( ( positive(FormA), contab([FormB | Forms], Lim, Par, Terms, start, Lems, Pth, FormA, NewLems, Prf) ) ; 
    ( positive(FormB), contab([FormA | Forms], Lim, Par, Terms, start, Lems, Pth, FormB, NewLems, Prf) ) ).

contab(Forms, Lim, Par, Terms, Mode, Lems, Pth, Form, NewLems, alpha(Form, Prf)) :- 
  member(Mode, [block, match]),
  break_alpha(Form, FormA, FormB), 
  ( contab([FormB | Forms], Lim, Par, Terms, Mode, Lems, Pth, FormA, NewLems, Prf) ; 
    contab([FormA | Forms], Lim, Par, Terms, Mode, Lems, Pth, FormB, NewLems, Prf) ).

contab(Forms, Lim, Par, Terms, Mode, Lems, Pth, Form, NewLems, beta(Form, PrfA, PrfB)) :- 
  member(Mode, [start, block]),
  break_beta(Form, FormA, FormB), 
  contab(Forms, Lim, Par, Terms, Mode, Lems, Pth, FormA, TempLems, PrfA),
  contab(Forms, Lim, Par, Terms, Mode, TempLems, Pth, FormB, NewLems, PrfB).

contab(Forms, Lim, Par, Terms, match, Lems, Pth, Form, NewLems, beta(Form, PrfA, PrfB)) :- 
  break_beta(Form, FormA, FormB), 
  (
    ( contab(Forms, Lim, Par, Terms, match, Lems, Pth, FormA, TempLems, PrfA),
      contab(Forms, Lim, Par, Terms, block, TempLems, Pth, FormB, NewLems, PrfB) ) ;  
    ( contab(Forms, Lim, Par, Terms, match, Lems, Pth, FormB, TempLems, PrfB),
      contab(Forms, Lim, Par, Terms, block, TempLems, Pth, FormA, NewLems, PrfA) ) 
  ).

contab(Forms, Lim, Par, Terms, Mode, Lems, Pth, FaForm, NewLems, gamma(Term, FaForm, Prf)) :- 
  break_gamma(Term, FaForm, Form), 
  contab([FaForm | Forms], Lim, Par, [Term | Terms], Mode, Lems, Pth, Form, NewLems, Prf).

contab(Forms, Lim, Par, Terms, Mode, Lems, Pth, ExForm, NewLems, delta(Par, ExForm, Prf)) :- 
  break_delta(@(Par, Terms), ExForm, Form), 
  Succ is Par + 1,
  contab(Forms, Lim, Succ, Terms, Mode, Lems, Pth, Form, NewLems, Prf).

contab(Forms, Lim, Par, Terms, Mode, Lems, Pth, Lit, NewLems, Prf) :- 
  literal(Lit), 
  member(Mode, [start, block]), 
  (
    has_complement(Lit, Pth) -> 
    (NewLems = Lems, Prf = close) ;
    (
      find_lemma(Lems, Lit, Prf) -> 
      (NewLems = Lems) ;
      ( 
        decr_if_pos(Lim, Pred),
        not(occurs(Lit, Pth)), % Regularity check
        pluck(Forms, Form, Rem),
        contab(Rem, Pred, Par, Terms, match, Lems, [Lit | Pth], Form, _, Prf),
        NewLems = [(Lit, Prf) | Lems]
      )
    ) 
  ).

contab(_, _, _, _, match, Lems, [Cmp | _], Lit, Lems, close) :- 
  literal(Lit), 
  complementary(Lit, Cmp).

contab(Forms, Lim, Prf) :- 
  pluck(Forms, Form, Rem),
  positive(Form),
  contab(Rem, Lim, 0, [], start, [], [$true, ~ $false], Form, _, Prf).

contab(Forms, 10, timeout(Forms)).

contab(Forms, Lim, Prf) :- 
  Succ is Lim + 1,
  contab(Forms, Succ, Prf).

contab(Forms, Prf) :- 
  add_eq_axioms(Forms, NewForms),
  contab(NewForms, 5, Prf).

fst((X, _), X). 

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
  contab([~ Conc | Prems], Prf), !.

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