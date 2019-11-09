:- op(1130, xfy, <=>). % equivalence
:- op(1110, xfy, =>).  % implication
:- op(1110, xfy, &).   % conjunction
:- op( 500, fy, ~).    % negation
:- op( 500, fy, !).    % universal quantifier
:- op( 500, fy, ?).    % existential quantifier
:- op( 500, xfy, :).

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
  Exp =.. [Symb | Terms],  
  maplist(substitute(Num, Term), Terms, NewTerms),
  NewExp =.. [Symb | NewTerms].

union([], []).

union([List | Lists], Set) :- 
  union(Lists, TempSet),
  union(List, TempSet, Set).

mark(Num) :-
  number_string(Num, NumStr),
  strings_concat(["Tracing ", NumStr, "\n"], Msg),
  write(Msg).

repeat(0, _).

repeat(Num, Goal) :- 
  0 < Num, 
  Pred is Num - 1, 
  call(Goal),
  repeat(Pred, Goal).

write_break(Num, Term) :-
  write(Term),
  repeat(Num, write("\n")).

strings_concat([], "").

strings_concat([Str | Strs], NewStr) :- 
  strings_concat(Strs, TempStr), 
  string_concat(Str, TempStr, NewStr). 

strings_concat_with(_, [], "").

strings_concat_with(_, [Str], Str).

strings_concat_with(Div, [Str | Strs], Result) :-
  strings_concat_with(Div, Strs, TempStr),
  strings_concat([Str, Div, TempStr], Result).
 
% Similar to member/2, but avoids instantion.
occurs(ElemA, [ElemB | _]) :- 
  ElemA == ElemB.

occurs(Elem, [_ | List]) :-
  occurs(Elem, List).

write_file(Target, Term) :-
  open(Target, write, Stream),
  write(Stream, Term),
  close(Stream).

pick(Goal, [Elem | Rem], Elem, Rem) :- 
  call(Goal, Elem), !.

pick(Goal, [ElemA | List], ElemB, [ElemA | Rem]) :- 
  pick(Goal, List, ElemB, Rem).

find(Goal, List, Elem) :- 
  pick(Goal, List, Elem, _).

pluck([Elem | Rem], Elem, Rem).

pluck([ElemA | List], ElemB, [ElemA | Rem]) :- 
  pluck(List, ElemB, Rem).

list_prod([ElemA | ListA], [ElemB | ListB], List, [(ElemA, ElemB) | Prod]) :-
  list_prod([ElemA | ListA], ListB, List, Prod).

list_prod([_ | ListA], [], List, Prod) :- 
  list_prod(ListA, List, List, Prod).

list_prod([], _, _, []).

list_prod(ListA, ListB, Prod) :-
  list_prod(ListA, ListB, ListB, Prod).

first(Goal, [Elem | _], Result) :-
  call(Goal, Elem, Result), !.

first(Goal, [_ | List], Result) :-
  first(Goal, List, Result).

collect(_, [], []).

collect(Goal, [Elem | List], Results) :-
  call(Goal, Elem, Result) -> 
  ( collect(Goal, List, TempResults),
    Results = [Result | TempResults] ) ; 
  collect(Goal, List, Results).

any(Goal, [Elem | _]) :-
  call(Goal, Elem).

any(Goal, [_ | List]) :-
  any(Goal, List).

list_br_str(List, Str) :-
  maplist(term_string, List, Strs), 
  strings_concat_with("\n\n", Strs, Str).
  
list_str(List, Str) :-
  maplist(term_string, List, Strs), 
  strings_concat_with(", ", Strs, Str).

last([Elem], Elem). 

last([_ | List], Elem) :- last(List, Elem). 

decr_if_pos(Num, Pred) :-
  0 < Num,
  Pred is Num - 1.

prove_eq_refl(Term, gamma(Term, ! 0: (#(0) = #(0)), Prf), Prf).

prove_eq_refl(Term, Prf) :- 
  prove_eq_refl(Term, Prf, close).

prove_eq_symm(TermA, PrfAB, TermB, 
  gamma(TermA, ! 0: ! 1: ((#(0) = #(1)) => (#(1) = #(0))),
    gamma(TermB, ! 1: ((TermA = #(1)) => (#(1) = TermA)),
      beta((TermA = TermB) => (TermB = TermA), PrfAB, Prf))), 
  Prf).

prove_eq_symm(TermA, PrfAB, TermB, PrfBA) :- 
  prove_eq_symm(TermA, PrfAB, TermB, PrfBA, close).

prove_eq_trans(TermA, PrfAB, TermB, PrfBC, TermC,  
  gamma(TermA, (! 0: ! 1: ! 2 : ((#(0) = #(1)) => ((#(1) = #(2)) => (#(0) = #(2))))), 
    gamma(TermB, (! 1: ! 2: ((TermA = #(1)) => ((#(1) = #(2)) => (TermA = #(2))))),
      gamma(TermC, (! 2: ((TermA = TermB) => ((TermB = #(2)) => (TermA = #(2))))),
        beta((TermA = TermB) => ((TermB = TermC) => (TermA = TermC)), PrfAB,
          beta((TermB = TermC) => (TermA = TermC), PrfBC, Prf))))), Prf).

unneg(~ Atom, Atom) :- !.
unneg(Atom, Atom).

write_file_punct(Filename, Term) :- 
  term_string(Term, TermStr),
  string_concat(TermStr, ".", Str),
  write_file(Filename, Str).

propatom(Atom) :- 
  not(member(Atom, 
    [ (! _ : _), (? _ : _), (~ _), 
      (_ | _), (_ & _), (_ => _), (_ <=> _) ])).

aug_type(! 0: (#(0) = #(0)), refl_eq).

aug_type((! 0: ! 1: ((#(0) = #(1)) => (#(1) = #(0)))), symm_eq).

aug_type((! 0: ! 1: ! 2: ((#(0) = #(1)) => ((#(1) = #(2)) => (#(0) = #(2))))), trans_eq).

aug_type(Form, mono_fun) :- 
  is_mono_fun(Form).

aug_type(Form, mono_rel) :- 
  is_mono_rel(Form).

mono_args_args_cons(! NumA : ! NumB : (#(NumA) = #(NumB) => Form), [#(NumA) | ArgsA], [#(NumB) | ArgsB], Cons) :- 
  mono_args_args_cons(Form, ArgsA, ArgsB, Cons).

mono_args_args_cons(Form, [], [], Form).

is_mono_rel(Form) :- 
  mono_args_args_cons(Form, ArgsA, ArgsB, AtomA => AtomB), !, 
  AtomA =.. [Rel | ArgsA],
  AtomB =.. [Rel | ArgsB].

is_mono_fun(Form) :- 
  mono_args_args_cons(Form, ArgsA, ArgsB, TermA = TermB), !, 
  TermA =.. [Fun | ArgsA],
  TermB =.. [Fun | ArgsB].

analyze_forall_tptp(! VarsA : Form, Vars, Body) :-
  analyze_forall_tptp(Form, VarsB, Body),
  append(VarsA, VarsB, Vars).

analyze_forall_tptp(Form, [], Form).

% aoc_skolem_fun_tptp(+Form, -Skm).
aoc_skolem_fun_tptp(Form, Skm) :-
  analyze_forall_tptp(Form, VarsA, (? [VarA] : FormA) => FormB), 
  unifiable(FormA, FormB, [VarB = Term]), 
  VarA == VarB, 
  Term =.. [Skm | VarsB], 
  VarsA == VarsB, !.

analyze_forall(! Num : Form, [Num | Nums], Body) :-
  analyze_forall(Form, Nums, Body).

analyze_forall(Form, [], Form).

mk_var(Num, #(Num)).

% aoc_skolem_fun(+Form, +Skm).
aoc_skolem_fun(Form, Skm) :-
  analyze_forall(Form, Nums, (? Num : FormA) => FormB), 
  maplist(mk_var, Nums, Vars), 
  SkmTrm =.. [Skm | Vars], 
  substitute(Num, SkmTrm, FormA, FormB).

maplist_cut(Goal, [Elem | List]) :- 
  call(Goal, Elem), !, 
  maplist_cut(Goal, List). 

maplist_cut(_, []).

maplist_cut(Goal, [ElemA | ListA], [ElemB | ListB]) :- 
  call(Goal, ElemA, ElemB), !, 
  maplist_cut(Goal, ListA, ListB). 

maplist_cut(_, [], []).

maplist_idx(Goal, Num, [Elem | List]) :- 
  call(Goal, Num, Elem), 
  Succ is Num + 1,
  maplist_idx(Goal, Succ, List).

maplist_idx(_, _, []).


/* Monotonicity */

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

mk_mono_fun(Num, Fun, Mono) :- 
  mk_mono_eq(Num, Fun, Eq), 
  mk_mono(Num, Eq, Mono), !.

mk_mono_rel(Num, Rel, Mono) :- 
  mk_mono_imp(Num, Rel, Imp), 
  mk_mono(Num, Imp, Mono).

mk_mono(0, Cons, Cons).

mk_mono(Num, Cons, ! NumA : ! NumB : ((#(NumA) = #(NumB)) => Mono)) :-
  NumA is (Num * 2) - 1, 
  NumB is (Num * 2) - 2, 
  decr_if_pos(Num, Pred), 
  mk_mono(Pred, Cons, Mono), !.

space_write(Num, Term) :- 
  repeat(Num, write("|  ")),
  write(Term).

subformulas(Lvl, Form) :- 
  space_write(Lvl, Form), 
  Next is Lvl + 1, 
  ( 
    ( break_alpha(Form, FormA, FormB), 
      write(" [alpha]\n"),
      subformulas(Next, FormA),
      subformulas(Next, FormB) ) ;
    ( break_beta(Form, FormA, FormB), 
      write(" [beta]\n"),
      subformulas(Next, FormA),
      subformulas(Next, FormB) ) ;
    ( break_gamma(@(Lvl), Form, NewForm), 
      write(" [gamma]\n"),
      subformulas(Next, NewForm) ) ;
    ( break_delta(@(Lvl), Form, NewForm), 
      write(" [delta]\n"),
      subformulas(Next, NewForm) ) ;
    ( Form = ~ ~ NewForm, 
      write(" [dne]\n"),
      subformulas(Next, NewForm) ) ;
    write(" [lit]\n")
  ).
