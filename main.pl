#!/usr/bin/env swipl



/* Anvil theorem prover */



:- initialization(main, main).

:- [misc].

:- op(1130, xfy, <=>). % equivalence
:- op(1110, xfy, =>).  % implication
:- op(1110, xfy, &).   % conjunction
:- op( 500, fy, ~).    % negation
:- op( 500, fy, !).    % universal quantifier
:- op( 500, fy, ?).    % existential quantifier
:- op( 500, xfy, :).

theorem(_, _, _).
fof(_, _, _).
fof(_, _, _, _).

% number_label(Num, Lab) :-
%   number_string(Num, NumStr), 
%   string_concat("f", NumStr, Str),
%   atom_string(Lab, Str).
 
write_axiom(Stm, Num, Frm) :- 
  % number_label(Num, Lab), 
  write(Stm, tff(Num, axiom, Frm)),
  write(Stm, ".\n\n").

write_punct(Stm, X) :-
  write(Stm, X),
  write(Stm, ".\n\n").

ids_get_insts([], []).

ids_get_insts([Id | Ids], Insts) :- 
  id_get_insts(Id, IdInsts),
  ids_get_insts(Ids, IdsInsts),
  subtract(IdInsts, IdsInsts, Diff),
  append(Diff, IdsInsts, Insts).

id_conc(Id, Conc) :-
  fof(Id, _, Frm, _),
  desugar(Frm, Conc).

id_get_insts(Id, []) :-
  fof(Id, _, _, file(_, _)), !.

id_get_insts(Id, [defin(Conc, Rul)]) :-
  fof(Id, _, Frm, introduced(Rul, _)), !,
  desugar(Frm, Conc).

id_get_insts(Id, [lemma(Prems, Conc, Rul) | Insts]) :-
  fof(Id, _, Frm, inference(Rul, _, Ids)), !,
  maplist(id_conc, Ids, Prems),
  ids_get_insts(Ids, Insts),
  desugar(Frm, Conc).

vampire(Frms, Insts) :-
  retractall(fof(_, _, _, _)),
  open("goal", write, Strm),
  indexed_maplist(write_axiom(Strm), 0, Frms),
  close(Strm),
  shell("vampire --proof tptp goal | tr '!=' '\\\\=' > insts"),
  consult("insts"), 
  fof(Id,_, $false, _),
  id_get_insts(Id, RevInsts),
  reverse(RevInsts, Insts).

indexed_maplist(_, _, []).

indexed_maplist(Goal, Num, [Elem | List]) :-
  call(Goal, Num, Elem),
  SuccNum is Num + 1,
  indexed_maplist(Goal, SuccNum, List).

indexed_maplist(_, _, [], []).

indexed_maplist(Goal, Num, [ElemA | ListA], [ElemB | ListB]) :-
  call(Goal, Num, ElemA, ElemB),
  SuccNum is Num + 1,
  indexed_maplist(Goal, SuccNum, ListA, ListB).

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

set(X, Y, X) :- Y == same, !.
set(_, X, X).

/* State data access */

% ([(Bch, Insts, Prf) | Goals], Ext, Symbs, Auto, Disp)

set((OldGoals, OldExt, OldSymbs, OldAuto, OldDisp), 
     InpGoals, InpExt, InpSymbs, InpAuto, InpDisp, 
    (NewGoals, NewExt, NewSymbs, NewAuto, NewDisp)) :-
  set(OldGoals, InpGoals, NewGoals),
  set(OldExt, InpExt, NewExt),
  set(OldSymbs, InpSymbs, NewSymbs),
  set(OldAuto, InpAuto, NewAuto),
  set(OldDisp, InpDisp, NewDisp).

set_goals(State, Goals, NewState) :-
  set(State, Goals, same, same, same, same, NewState).

set_ext(State, Ext, NewState) :-
  set(State, same, Ext, same, same, same, NewState).

set_symbs(State, Symbs, NewState) :-
  set(State, same, same, Symbs, same, same, NewState).

set_auto(State, Auto, NewState) :-
  set(State, same, same, same, Auto, same, NewState).

set_disp(State, Disp, NewState) :-
  set(State, same, same, same, same, Disp, NewState).

set_goal(State, Goal, NewState) :-
  get_goals(State, [_ | Goals]),
  set_goals(State, [Goal | Goals], NewState).

get_goals((Goals, _, _, _, _), Goals).
get_ext((_, Ext, _, _, _), Ext).
get_symbs((_, _, Symbs, _, _), Symbs).
get_auto((_, _, _, Auto, _), Auto).
get_disp((_, _, _, _, Disp), Disp).

get_goal(([Goal | _], _, _, _), Goal).

get_insts(State, Insts) :- 
  get_goal(State, (_, Insts, _)).

get_inst(State, Inst) :- 
  get_goal(State, (_, [Inst | _], _)).

set_insts(State, Insts, NewState) :- 
  get_goal(State, (Bch, _, Prf)),
  set_goal(State, (Bch, Insts, Prf), NewState).

set_insts_auto(State, Insts, NewState) :- 
  auto_check(State, Auto), 
  set_insts(State, Insts, TempState),
  set_auto(TempState, Auto, NewState).

get_branch(State, Bch) :-
  get_goal(State, (Frms, _, _)),
  groundfix(Frms, Bch).

groundfix(Var, []) :- var(Var), !.

groundfix([Elem | List], [Elem | Gfx]) :- 
  groundfix(List, Gfx).

inspect(Var) :- var(Var), write("Var found, done : "), write(Var), !.

inspect([Elem | List]) :- 
  write("Keep looking : "), 
  write(Elem),
  inspect(List).

auto_check(State, full) :-
  get_auto(State, full).

auto_check(State, burst(Num)) :-
  get_auto(State, burst(SuccNum)), 
  1 < SuccNum, 
  Num is SuccNum - 1.

auto_check(State, manual) :-
  get_auto(State, burst(1)).


/* Proof state display */

theorem_string(Frms, Str) :- 
  maplist(form_string, Frms, Strs), 
  reverse(Strs, RevStrs),
  strings_concat_with(", ", RevStrs, TempStr),
  string_concat(TempStr, " |- false", Str).

branch_string(Frms, Str) :- 
  indexed_maplist(index_form_string, 0, Frms, Strs), 
  reverse(["\n-------\n\n" |Strs], RevStrs),
  strings_concat(RevStrs, Str).

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

triple_fst((X, _, _), X).

get_branches_aux((Frms, _, _), Bch) :- 
  groundfix(Frms, Bch).

get_branches(State, Bchs) :- 
  get_goals(State, Goals),
  maplist(get_branches_aux, Goals, Bchs).

branches_string(Bchs, on, Str) :- 
  reverse(Bchs, RevBchs),
  maplist(branch_string, RevBchs, Strs),
  strings_concat(Strs, Str).

branches_string([Bch | Bchs], off, Str) :- 
  length(Bchs, Lth),
  number_string(Lth, LthStr),
  branch_string(Bch, BchStr),
  strings_concat(["(", LthStr, " more goals)\n\n", BchStr], Str).

decode_disp(all, on, on).
decode_disp(goals, on, off).
decode_disp(insts, off, on).
decode_disp(none, off, off).

write_state(State) :-
  get_disp(State, Disp),
  decode_disp(Disp, ShowBchs, ShowInsts),
  get_branches(State, Bchs),
  branches_string(Bchs, ShowBchs, BchsStr),
  get_insts(State, Insts),
  insts_string(Insts, ShowInsts, InstsStr),
  shell("clear"),
  write(BchsStr), 
  write(InstsStr).

write_state(_, _, _) :-
  write("Ill-formed state.").
  
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

prompt(Mode) :-
  write("\n\nNext step (into/over) "),
  read_input(Inp),
  (
    member(Inp, [over, into]) -> 
    Mode = Inp ;
    (write("Invalid input.\n\n"), prompt(Mode))
  ). 

check_msg(_, _, over, over).

check_msg(Bch, Prf, into, Mode) :- 
  shell("clear"),
  branch_string(Bch, BchStr),
  term_string(Prf, PrfStr),
  strings_concat([BchStr, "Proof = ", PrfStr, "\n"], Str),
  write(Str),
  prompt(Mode).

check([~ ~ Frm | Bch], dne(Prf), Mode) :-
  check_msg([~ ~ Frm | Bch], dne, Mode, NewMode),
  check([Frm, ~ ~ Frm | Bch], Prf, NewMode).

check([FrmA | Bch], alpha(Prf), Mode) :-
  break_alpha(FrmA, FrmB, FrmC),
  check_msg([FrmA | Bch], alpha, Mode, NewMode),
  check([FrmC, FrmB, FrmA | Bch], Prf, NewMode).
  
check([FrmB, FrmA | Bch], beta(Prf), Mode) :-
  break_beta(FrmA, FrmB, FrmC),
  check_msg([FrmB, FrmA | Bch], beta, Mode, NewMode),
  check([FrmC, FrmB, FrmA | Bch], Prf, NewMode).

check([FrmA | Bch], gamma(Trm, Prf), Mode) :-
  break_gamma(Trm, FrmA, FrmB),
  check_msg([FrmA | Bch], gamma(Trm), Mode, NewMode),
  check([FrmB, FrmA | Bch], Prf, NewMode).

check([~ Frm, Frm | _], close, _).

check(Bch, copy(Num, Prf), Mode) :-
  nth0(Num, Bch, Frm), 
  check_msg(Bch, copy(Num), Mode, NewMode),
  check([Frm | Bch], Prf, NewMode).

check(Bch, cut(Frm, PrfA, PrfB), Mode) :- 
  check_msg(Bch, cut(Frm), Mode, ModeA),
  check([Frm | Bch], PrfA, ModeA),
  check_msg(Bch, cut(~ Frm), Mode, ModeB),
  check([~ Frm | Bch], PrfB, ModeB).

check(Bch, tt(Prf), Mode) :- 
  check_msg(Bch, tt, Mode, NewMode),
  check([$true | Bch], Prf, NewMode).

check(Bch, ff(Prf), Mode) :- 
  check_msg(Bch, ff, Mode, NewMode),
  check([~ $false | Bch], Prf, NewMode).


/* Main loop */

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

prove(State) :- 
  get_insts(State, [next, _ | Insts]),
  set_insts(State, Insts, NewState),
  prove(NewState).

prove(State) :-
  get_insts(State, [Inst | Insts]),
  update_auto(Inst, NewAuto),
  set_insts(State, Insts, TempState),
  set_auto(TempState, NewAuto, NewState),
  prove(NewState).

prove(State) :-
  get_insts(State, [Disp | Insts]),
  member(Disp, [none, goals, insts, all]),
  set_insts(State, Insts, TempState),
  set_disp(TempState, Disp, NewState),
  prove(NewState).

prove(State) :-
  get_insts(State, [load | _]),
  get_branch(State, Frms),
  vampire(Frms, Insts),
  set_insts(State, Insts, NewState),
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
  get_goal(State, (Bch, [def(Atom, Frm) | Insts], def(Atom, Frm, Prf))),
  atom(Atom),
  get_branch(State, Bch),
  not(uses(Atom, Bch)),
  get_symbs(State, Symbs),
  set_goal(State, ([(Atom <=> Frm) | Bch], Insts, Prf), TempState),
  set_symbs(TempState, [Atom | Symbs], NewState),
  prove(NewState).


/** Automatic execution **/ 

/* Non-cutting rules */ 

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

% If conclusion of lemma is already available, 
% copy it to the tip and proceed to next instruction.
prove(State) :- 
  get_insts(State, [lemma(_, Conc, _) | Insts]),
  branch_has(State, Conc),
  set_insts_auto(State, [copy_form(Conc) | Insts], NewState),
  prove(NewState).

prove(State) :- 
  get_insts(State, [defin(Atom <=> Frm, _) | Insts]),
  set_insts_auto(State, [def(Atom, Frm) | Insts], NewState),
  prove(NewState).

/* Cutting rules */ 

% If there are more than one lemmas to be proven, cut to 
% spawn a subgoal and continue with the main line of the proof.
prove(State) :-
  get_goals(State, [(Twig, [lemma(Prems, Conc, Rul) | Insts], cut(Conc, PrfA, PrfB)) | Goals]),
  Insts = [_ | _],
  auto_check(State, Auto),
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
  get_insts(State, [lemma([Src | _], Tgt, definition_unfolding)]),
  lits_align(Src, Tgt, Ante, Cons),
  Ante =.. [Pred | AnteArg], 
  Cons =.. [Pred | ConsArg], 
  maplist(mk_pair, AnteArg, ConsArg, Pairs),
  length(Pairs, Lth),
  mk_pred_mono(Lth, Pred, Mono), 
  posit_insts(State, Mono, TempInsts),
  append(TempInsts, [mono(Pairs), copy_form(Src), beta], NewInsts), 
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

% If there there is no executable head instruction,
% prompt the user for new instruction.
prove(State) :- 
  write_state(State),
  (
    read_input(Inst) -> 
    (
      get_insts(State, Insts),
      set_insts(State, [Inst | Insts], TempState),
      set_auto(TempState, manual, NewState),
      prove(NewState)
    ) ; 
    (
      write_break("Invalid instruction."),
      prove(State)
    )
  ).

mk_pair(X, Y, (X, Y)).

get_show_opt(State, on, on, NewState) :- 
  get_insts(State, [show_all | Insts]), !,
  set_insts(State, Insts, NewState).

get_show_opt(State, on, off, NewState) :- 
  get_insts(State, [show_goals | Insts]), !,
  set_insts(State, Insts, NewState).

get_show_opt(State, off, on, NewState) :- 
  get_insts(State, [show_insts | Insts]), !,
  set_insts(State, Insts, NewState).

get_show_opt(State, off, off, State).

% If the requrested formula is already at the tip, there is nothing to do.
posit_insts(State, Frm, []) :- 
  get_branch(State, [Frm | _]), !.

posit_insts(State, Frm, [copy(Num)]) :- 
  branch_where(State, Frm, Num), !.
  
posit_insts(State, Frm, [ext(Frm), copy(Num)]) :- 
  branch_length(State, Num).

mk_fun_mono(0, VarsA, [], VarsB, [], Fun, (TrmA = TrmB)) :- !,
  TrmA =.. [Fun | VarsA],
  TrmB =.. [Fun | VarsB].

mk_fun_mono(Num, VarsA, [X | ExtA], VarsB, [Y | ExtB], Fun, ! [X, Y] : ((X = Y) => Frm)) :- !,
  PredNum is Num - 1, 
  mk_fun_mono(PredNum, VarsA, ExtA, VarsB, ExtB, Fun, Frm).

mk_fun_mono(Num, Fun, Frm) :- 
  mk_fun_mono(Num, SrcVars, SrcVars, TgtVars, TgtVars, Fun, Frm).

mk_pred_mono(0, SrcVars, [], TgtVars, [], Pred, (SrcAtm => TgtAtm)) :- !,
  SrcAtm =.. [Pred | SrcVars],
  TgtAtm =.. [Pred | TgtVars].

mk_pred_mono(Num, SrcVars, [X | SrcExt], TgtVars, [Y | TgtExt], 
  Pred, ! [X, Y] : ((X = Y) => Frm)) :- !,
  PredNum is Num - 1, 
  mk_pred_mono(PredNum, SrcVars, SrcExt, TgtVars, TgtExt, Pred, Frm).

mk_pred_mono(Num, Pred, Frm) :- 
  mk_pred_mono(Num, SrcVars, SrcVars, TgtVars, TgtVars, Pred, Frm).

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

update_auto(full, full).
update_auto(semi, burst(1)).
update_auto(burst(Num), burst(Num)) :- 
  integer(Num), 0 < Num.


main(_) :-
  dynamic(fof/3),
  dynamic(fof/4),
  dynamic(theorem/3),
  loop.

loop :-
  write("Anvil "),
  read_input(Cmd),
  loop(Cmd).

loop :- 
  write_break("Invalid command."),
  loop.

id_theorem_string((Id, Thm), Str) :- 
  atom_string(Id, IdStr), 
  theorem_string(Thm, ThmStr),
  strings_concat([IdStr, " : ", ThmStr], Str).

loop(skip) :- loop.

loop(prove(Id)) :- 
  retract(theorem(Id, Smt, _)),
  append(Smt, Ext, SmtExt),
  prove(([(SmtExt, [], Prf)], Ext, [], manual, none)),
  assert(theorem(Id, SmtExt, Prf)),
  loop.

loop(check(Id)) :- 
  theorem(Id, Smt, Prf), 
  check(Smt, Prf, into),
  write("Proof verified.\n"),
  loop.
  
loop(show) :- 
  findall((Id, Thm), theorem(Id, Thm, _), IdThms),
  maplist(id_theorem_string, IdThms, Strs),
  strings_concat_with("\n", Strs, Str),
  write_break(Str),
  loop.

loop(read(Filename)) :- 
  retractall(theorem(_, _, _)), 
  consult(Filename),
  loop.

loop(write(Filename)) :- 
  findall(theorem(Id, Smt, Prf), theorem(Id, Smt, Prf), Thms),
  open(Filename, write, Stream),
  maplist(write_punct(Stream), Thms),
  close(Stream),
  loop.


loop(exit) :- write("\n"). 

read_input(Inp) :-
  read_term(user_input, Inp, [syntax_errors(fail)]).

