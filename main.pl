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

number_label(Num, Lab) :-
  number_string(Num, NumStr), 
  string_concat("f", NumStr, Str),
  atom_string(Lab, Str).

write_axiom(Stm, Num, Frm) :- 
  number_label(Num, Lab), 
  write(Stm, tff(Lab, axiom, Frm)),
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

id_get_insts(Id, [define(Conc, Rul)]) :-
  fof(Id, _, Frm, introduced(Rul, _)), !,
  desugar(Frm, Conc).

id_get_insts(Id, [lemma(Prems, Conc, Rul) | Insts]) :-
  fof(Id, _, Frm, inference(Rul, _, Ids)), !,
  maplist(id_conc, Ids, Prems),
  ids_get_insts(Ids, Insts),
  desugar(Frm, Conc).

vampire(Frms, Insts) :-
  retractall(fof(_, _, _, _)),
  open("goal", write, Stm),
  indexed_maplist(write_axiom(Stm), 0, Frms),
  close(Stm),
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

formula_string(Num, Frm, Str) :- 
  number_string(Num, NumStr),
  term_string(Frm, FrmStr),
  strings_concat(["[", NumStr, "] ", FrmStr, "\n"], Str).

set(X, same, X) :- !.
set(_, X, X).

/* State data access */

% ([(Branch, Insts, Prf) | Goals], Trunk, Symbs, Mode)

set((OldGoals, OldTrunk, OldSymbs, OldMode), 
     InpGoals, InpTrunk, InpSymbs, InpMode, 
    (NewGoals, NewTrunk, NewSymbs, NewMode)) :-
  set(OldGoals, InpGoals, NewGoals),
  set(OldTrunk, InpTrunk, NewTrunk),
  set(OldSymbs, InpSymbs, NewSymbs),
  set(OldMode, InpMode, NewMode).

set_goals(State, Goals, NewState) :-
  set(State, Goals, same, same, same, NewState).

set_trunk(State, Trunk, NewState) :-
  set(State, same, Trunk, same, same, NewState).

set_symbs(State, Symbs, NewState) :-
  set(State, same, same, Symbs, same, NewState).

set_mode(State, Mode, NewState) :-
  set(State, same, same, same, Mode, NewState).

set_goal(State, Goal, NewState) :-
  get_goals(State, [_ | Goals]),
  set_goals(State, [Goal | Goals], NewState).

get_goals((Goals, _, _, _), Goals).
get_trunk((_, Trunk, _, _), Trunk).
get_symbs((_, _, Symbs, _), Symbs).
get_mode((_, _, _, Mode), Mode).

get_goal(([Goal | _], _, _, _), Goal).

get_branch(State, Bch) :- 
  get_goal(State, (Bch, _, _)).

get_insts(State, Insts) :- 
  get_goal(State, (_, Insts, _)).

get_inst(State, Inst) :- 
  get_goal(State, (_, [Inst | _], _)).

set_insts(State, Insts, NewState) :- 
  get_goal(State, (Bch, _, Prf)),
  set_goal(State, (Bch, Insts, Prf), NewState).

set_insts_auto(State, Insts, NewState) :- 
  auto_check(State, Mode), 
  set_insts(State, Insts, TempState),
  set_mode(TempState, Mode, NewState).

get_wood(State, Wood) :-
  get_branch(State, Bch),
  get_trunk(State, Trunk),
  append(Bch, Trunk, Wood).

auto_check(State, full) :-
  get_mode(State, full).

auto_check(State, burst(Num)) :-
  get_mode(State, burst(SuccNum)), 
  1 < SuccNum, 
  Num is SuccNum - 1.

auto_check(State, manual) :-
  get_mode(State, burst(1)).


/* Proof state display */

forms_string(Frms, Str) :- 
  indexed_maplist(formula_string, 0, Frms, RevStrs), 
  reverse(RevStrs, Strs),
  strings_concat(Strs, Str).

insts_string([], "No insts").

insts_string([Inst | Insts], Str) :-
  inst_string(Inst, InstStr), 
  length(Insts, Lth),
  number_string(Lth, LthStr),
  strings_concat([InstStr, " | (", LthStr, " more insts)"], Str).

inst_string(define(Conc, Rul), Str) :- 
  term_string(Conc, ConcStr),
  term_string(Rul, RulStr),
  strings_concat(["Γ |/- ⊥ ===> Γ, ", ConcStr, " |/- ⊥ [", RulStr, "]"], Str).

inst_string(lemma(Prems, Conc, Rul), Str) :- 
  maplist(term_string, Prems, PremStrs),
  strings_concat_with(", ", PremStrs, PremsStr),
  term_string(Conc, ConcStr),
  term_string(Rul, RulStr),
  strings_concat([PremsStr, " |- ", ConcStr, " [", RulStr, "]"], Str).

inst_string(Inst, Str) :- 
  term_string(Inst, Str).

triple_fst((X, _, _), X).

write_state(State) :-
  get_goals(State, [_ | Goals]),
  length(Goals, Lth),
  number_string(Lth, LthStr),
  get_wood(State, Wood),
  get_insts(State, Insts),
  forms_string(Wood, WoodStr),
  insts_string(Insts, InstsStr),
  strings_concat(
    [
      "(", LthStr, " more goals)\n\n",
      "-------\n\n",
      WoodStr, "\n",
      "-------\n\n",
      InstsStr, "\n\n"
    ], 
    Str   
  ),
  % shell("clear"),
  write(Str).

write_state(_) :-
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

wood_nth0(State, Num, Frm) :-
  get_wood(State, Wood),
  nth0(Num, Wood, Frm).
  
wood_member(State,Frm) :-
  get_wood(State, Wood),
  member(Frm, Wood).

wood_where(State, Frm, Num) :-
  get_wood(State, Wood),
  variant_nth0(Num, Wood, Frm).

wood_has(State, Frm) :-
  get_wood(State, Wood),
  variant_member(Frm, Wood).

wood_length(State, Num) :-
  get_wood(State, Wood),
  length(Wood, Num).




/* Main loop */

prove(State) :-
  get_goal(State, (Bch, [copy(Num) | Insts], copy(Num, Prf))),
  wood_nth0(State, Num, Frm),
  set_goal(State, ([Frm | Bch], Insts, Prf), NewState),
  prove(NewState).

prove(State) :-
  get_insts(State, [copy_form(Frm) | Insts]),
  wood_where(State, Frm, 0), 
  set_insts(State, Insts, NewState),
  prove(NewState).

prove(State) :-
  get_goal(State, (Bch, [copy_form(Frm) | Insts], copy(Num, Prf))),
  wood_where(State, Frm, Num),
  not(Num = 0),
  set_goal(State, ([Frm | Bch], Insts, Prf), NewState),
  prove(NewState).


prove(State) :-
  get_goal(State, (Bch, [alpha | Insts], alpha(Prf))),
  get_wood(State, [Frm | _]),
  break_alpha(Frm, FrmA, FrmB),
  set_goal(State, ([FrmB, FrmA | Bch], Insts, Prf), NewState),
  prove(NewState).

prove(State) :-
  get_goal(State, (Bch, [beta | Insts], beta(Prf))), 
  get_wood(State, [FrmB, FrmA | _]),
  break_beta(FrmA, FrmB, FrmC),
  set_goal(State, ([FrmC | Bch], Insts, Prf), NewState),
  prove(NewState).

prove(State) :-
  get_goal(State, (Bch, [gamma(Trm) | Insts], gamma(Trm, Prf))),
  get_wood(State, [Frm | _]),
  break_gamma(Trm, Frm, NewFrm),
  set_goal(State, ([NewFrm | Bch], Insts, Prf), NewState),
  prove(NewState).

prove(State) :- 
  get_goals(State, [(_, [close | _], close) | Goals]),
  get_wood(State, [~ Frm, Frm | _]),
  set_goals(State, Goals, NewState),
  prove(NewState).

prove(State) :- 
  get_goal(State, (Bch, [dne | Insts], dne(Prf))), 
  get_wood(State, [~ ~ Frm | _]),
  set_goal(State, ([Frm | Bch], Insts, Prf), NewState), 
  prove(NewState).

prove(State) :- 
  get_goal(State, (Bch, [tt | Insts], tt(Prf))), 
  set_goal(State, ([$true | Bch], Insts, Prf), NewState), 
  prove(NewState).

prove(State) :- 
  get_goal(State, (Bch, [ff | Insts], ff(Prf))), 
  set_goal(State, ([$false | Bch], Insts, Prf), NewState), 
  prove(NewState).

prove(State) :- 
  get_goals(State, [(Bch, [cut(Frm) | _], cut(Frm, PrfA, PrfB)) | Goals]),
  set_goals(State, [([Frm | Bch], [], PrfA), ([~ Frm | Bch], [], PrfB) | Goals], NewState),
  prove(NewState).

prove(State) :- 
  get_insts(State, [next, _ | Insts]),
  set_insts(State, Insts, NewState),
  prove(NewState).

prove(State) :-
  get_insts(State, [Mode | Insts]),
  encode_mode(Mode, NewMode),
  set_insts(State, Insts, TempState),
  set_mode(TempState, NewMode, NewState),
  prove(NewState).

prove(State) :-
  get_insts(State, [load | _]),
  get_wood(State, Frms),
  vampire(Frms, Insts),
  set_insts(State, Insts, NewState),
  prove(NewState).

% prove(State) :- 
%   get_insts(State, [show_insts | Insts]), 
%   maplist(inst_string, Insts, Strs),
%   maplist(write_break, Strs),
%   set_insts(State, Insts, NewState),
%   prove(NewState).

% Retroactively extend the theorem being proven.
prove(State) :- 
  get_insts(State, [ext(Frm) | Insts]),
  get_symbs(State, Symbs),
  not(uses_any(Symbs, Frm)),
  get_trunk(State, Trunk),
  append(Trunk, [Frm], NewTrunk),
  set_insts(State, Insts, TempState),
  set_trunk(TempState, NewTrunk, NewState),
  prove(NewState).

prove(State) :-
  get_goal(State, (Bch, [def(Atom, Frm) | Insts], def(Atom, Frm, Prf))),
  atom(Atom),
  get_wood(State, Wood),
  not(uses(Atom, Wood)),
  get_symbs(State, Symbs),
  set(State, ([(Atom <=> Frm) | Bch], Insts, Prf), same, [Atom | Symbs], same, NewState),
  prove(NewState).

prove(State) :-
  get_goals(State, [(_, [skip | _], skip) | Goals]),
  set_goals(State, Goals, NewState),
  prove(NewState).


/** Automatic execution **/ 

/* Non-cutting rules */ 

prove(State) :- 
  get_insts(State, []),
  wood_member(State, Frm),
  wood_has(State, ~ Frm),
  set_insts_auto(State, [copy_form(Frm), copy_form(~ Frm), close], NewState),
  prove(NewState).

% If conclusion of lemma is already available, 
% copy it to the tip and proceed to next instruction.
prove(State) :- 
  get_insts(State, [lemma(_, Conc, _) | Insts]),
  wood_has(State, Conc),
  set_insts_auto(State, [copy_form(Conc) | Insts], NewState),
  prove(NewState).

/* Cutting rules */ 

% If there are more than one lemmas to be proven, cut to 
% spawn a subgoal and continue with the main line of the proof.
prove(State) :-
  get_goals(State, [(Bch, [lemma(Prems, Conc, Rul) | Insts], cut(Conc, PrfA, PrfB)) | Goals]),
  Insts = [_ | _],
  auto_check(State, Mode),
  set( 
    State, 
    [ 
      ([Conc | Bch], Insts, PrfA), 
      ([~ Conc | Bch], [lemma(Prems, Conc, Rul)], PrfB) | 
      Goals
    ], 
    same, same, Mode, NewState
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
  wood_has(State, (TrmB = TrmA)),
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
  wood_has(State, ~ (TrmB = TrmA)),
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
  not(wood_has(State, Prem)), 
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
  write("QED.").

% If there there is no executable head instruction,
% prompt the user for new instruction.
prove(State) :- 
  write_state(State), 
  read(user_input, Inst),
  get_insts(State, Insts),
  set_insts(State, [Inst | Insts], TempState),
  set_mode(TempState, manual, NewState),
  prove(NewState).

mk_pair(X, Y, (X, Y)).

check_auto(full, full).

check_auto(semi, manual).

% If the requrested formula is already at the tip, there is nothing to do.
posit_insts(State, Frm, []) :- 
  get_wood(State, [Frm | _]), !.

posit_insts(State, Frm, [copy(Num)]) :- 
  wood_where(State, Frm, Num), !.
  
posit_insts(State, Frm, [ext(Frm), copy(Num)]) :- 
  wood_length(State, Num).

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

encode_mode(full, full).
encode_mode(semi, burst(1)).
encode_mode(burst(Num), burst(Num)) :-
  integer(Num), 0 < Num.

main(_) :-
  dynamic(theorem/3),
  loop.

loop :-
  write("Anvil>>"),
  read(user_input, Cmd),
  loop(Cmd).

loop(read(Filename)) :- 
  retractall(theorem(_, _, _)), 
  consult(Filename),
  findall(Thm, theorem(_, Thm, _), Thms),
  write(Thms),
  loop.

 % % dynamic(fof/3),
 % % dynamic(fof/4),
 % set_theorem(Argv, Frms),
 % loop(([([], [], Prf)], Frms, [], manual)),
 % write(Prf).
