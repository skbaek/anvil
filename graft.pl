#!/usr/bin/env swipl

:- initialization(main, main).

:- [prove, check].

prove_args(['--prove', Source, Target | _], Source, Target).
prove_args([_ | Argv], Source, Target) :-
  prove_args(Argv, Source, Target).

check_args(['--check', Source | _], Source).
check_args([_ | Argv], Source) :-
  check_args(Argv, Source).
 
help_msg :-
  write(
"=========== Usage ==========\n
Call Graft using\n 
  graft --prove [source] [target]\n
to import a TSTP proof from [source],
compile it to .grft format, and save the 
result at [target]\n
  graft --check [source]\n
to check a compiled proof at [target]\n
=========== End ==========\n"
  ).

main(Argv) :-
  dynamic(fof/4), (
    ( prove_args(Argv, Source, Target), 
      prove(Source, Target) ) ;
    ( check_args(Argv, Source), 
      check(Source) ) ;
    help_msg
  ).