#!/usr/bin/env swipl

:- initialization(main, main).

main(Argv) :-
  write(Argv),
  (
  member('-p', Argv) ->
  write("YES") ;
  write("NO")
).
