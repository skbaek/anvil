:- [basic].

proof(_).

form_funs_props(! _ : Form, Funs, Props) :- 
  form_funs_props(Form, Funs, Props).

form_funs_props(? _ : Form, Funs, Props) :- 
  form_funs_props(Form, Funs, Props).

form_funs_props(~ Form, Funs, Props) :- 
  form_funs_props(Form, Funs, Props).

form_funs_props(FormA & FormB, Funs, Props) :- 
  form_funs_props(FormA, FunsA, PropsA),
  form_funs_props(FormB, FunsB, PropsB),
  ord_union(FunsA, FunsB, Funs),
  ord_union(PropsA, PropsB, Props).

form_funs_props(FormA | FormB, Funs, Props) :- 
  form_funs_props(FormA, FunsA, PropsA),
  form_funs_props(FormB, FunsB, PropsB),
  ord_union(FunsA, FunsB, Funs),
  ord_union(PropsA, PropsB, Props).

form_funs_props(FormA => FormB, Funs, Props) :- 
  form_funs_props(FormA, FunsA, PropsA),
  form_funs_props(FormB, FunsB, PropsB),
  ord_union(FunsA, FunsB, Funs),
  ord_union(PropsA, PropsB, Props).

form_funs_props(FormA <=> FormB, Funs, Props) :- 
  form_funs_props(FormA, FunsA, PropsA),
  form_funs_props(FormB, FunsB, PropsB),
  ord_union(FunsA, FunsB, Funs),
  ord_union(PropsA, PropsB, Props).

form_funs_props(Atom, [], [Atom]) :-
  atom(Atom).

form_funs_props(Atom, Funs, []) :-
  \+ atom(Atom),
  propatom(Atom), 
  Atom =.. [_ | Terms], 
  maplist(term_funs, Terms, Funss), 
  ord_union(Funss, Funs).

term_funs(#(_), []). 

term_funs(Term, [(Term, 0)]) :-
  atom(Term).

term_funs(Term, Funs) :-
  Term \= #(_),
  \+ atom(Term),
  Term =.. [Fun | Terms],
  length(Terms, Num),
  maplist(term_funs, Terms, Funss), 
  ord_union([[(Fun, Num)] | Funss], Funs).

nullary((_, 0)).

term_consts(Term, Consts) :- 
  term_funs(Term, Funs),
  include(nullary, Funs, Consts).

form_consts(Form, Consts) :- 
  form_funs_props(Form, Funs, _),
  include(nullary, Funs, Consts).

funs_props_update(Form, Funs, Props, NewFuns, NewProps) :- 
  form_funs_props(Form, FormFuns, FormProps), 
  ord_union(Funs, FormFuns, NewFuns),
  ord_union(Props, FormProps, NewProps).

check_hyps(Bch, Funs, Props, hyp(Form, Prf)) :-
  funs_props_update(Form, Funs, Props, NewFuns, NewProps), 
  check_hyps([Form | Bch], NewFuns, NewProps, Prf).

check_hyps(Bch, Funs, Props, Prf) :-
  check_augs(Bch, Funs, Props, Prf).

check_augs(Bch, Funs, Props, aug(Prop <=> Form, def, Prf)) :-
  \+ member(Prop, Props), 
  funs_props_update(Form, Funs, Props, NewFuns, TempProps), 
  ord_add_element(TempProps, Prop, NewProps),
  check_augs([(Prop <=> Form) | Bch], NewFuns, NewProps, Prf).

check_augs(Bch, Funs, Props, aug(Form, ac(Skm), Prf)) :-
  aoc_skolem_fun(Form, Skm), 
  \+ member((Skm, 1), Funs), 
  funs_props_update(Form, Funs, Props, NewFuns, NewProps), 
  check_augs([Form | Bch], NewFuns, NewProps, Prf).

check_augs(Bch, Funs, Props, aug(Form, Type, Prf)) :- 
  aug_type(Form, Type), 
  funs_props_update(Form, Funs, Props, NewFuns, NewProps), 
  check_augs([Form | Bch], NewFuns, NewProps, Prf).

check_augs(Bch, Funs, _, Prf) :- 
  Prf \= aug(_, _, _),
  include(nullary, Funs, Consts), 
  check(Bch, Consts, Prf).

check(Bch, Consts, dne(Num, Prf)) :-
  nth0(Num, Bch, ~ ~ Form),
  check([Form | Bch], Consts, Prf).

check(Bch, Consts, alpha(Num, Prf)) :-
  nth0(Num, Bch, Form),
  break_alpha(Form, FormA, FormB),
  check([FormB, FormA | Bch], Consts, Prf).
  
check(Bch, Consts, beta(Num, PrfA, PrfB)) :-
  nth0(Num, Bch, Form),
  break_beta(Form, FormA, FormB),
  check([FormA | Bch], Consts, PrfA),
  check([FormB | Bch], Consts, PrfB).

check(Bch, Consts, gamma(Term, Num, Prf)) :-
  \+ member(#(_), Term), % Only ground term substitutions are permitted
  nth0(Num, Bch, FaForm),
  break_gamma(Term, FaForm, Form),
  term_consts(Term, TermConsts),
  ord_union(Consts, TermConsts, NewConsts),
  check([Form | Bch], NewConsts, Prf).

check(Bch, Consts, delta(Const, Num, Prf)) :-
  nth0(Num, Bch, ExForm),
  break_delta(Const, ExForm, Form),
  atom(Const), 
  \+ member(Const, Consts), % Delta rule parameter must be fresh
  ord_add_element(Consts, Const, NewConsts),
  check([Form | Bch], NewConsts, Prf).

check(Bch, Consts, cut(Form, PrfA, PrfB)) :- 
  form_consts(Form, FormConsts),
  ord_union(Consts, FormConsts, NewConsts),
  check([Form | Bch], NewConsts, PrfA), 
  check([~ Form | Bch], NewConsts, PrfB).

check(Bch, _, close(NumP, NumN)) :-
  nth0(NumP, Bch, FormP),
  nth0(NumN, Bch, ~ FormN),
  FormP == FormN.

check(Bch, _, close(Num)) :-
  nth0(Num, Bch, ~ $true).

check(Bch, _, close(Num)) :-
  nth0(Num, Bch, $false).

get_hyps_augs(hyp(Form, Prf), [Form | Forms], Augs) :- 
  get_hyps_augs(Prf, Forms, Augs).

get_hyps_augs(Prf, [], Augs) :-
  get_augs(Prf, Augs).

get_augs(aug(Form, Rul, Prf), [(Form, Rul) | Augs]) :- 
  get_augs(Prf, Augs).

get_augs(_, []).

print_hyp(Form) :- 
  write(Form), 
  write(" (hypothesis)\n"). 
  
print_aug((Form, Rul)) :- 
  write(Form), 
  write(" ("), 
  write(Rul), 
  write(")\n"). 

print_header(Prf) :- 
  get_hyps_augs(Prf, Hyps, Augs), 
  maplist(print_hyp, Hyps),
  maplist(print_aug, Augs),
  write("|- false.").

check(Source) :-
  dynamic(proof/1),
  retractall(proof(_)),
  consult(Source),
  proof(Prf),
  check_hyps([], [], [], Prf),
  print_header(Prf).