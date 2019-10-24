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

theorem(_, _, _).
fof(_, _, _).
fof(_, _, _, _).

main(_) :-
  dynamic(fof/3),
  dynamic(fof/4),
  dynamic(theorem/3),
  loop.