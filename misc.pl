union([], []).

union([List | Lists], Set) :- 
  union(Lists, TempSet),
  union(List, TempSet, Set).

mark(Num) :-
  number_string(Num, NumStr),
  strings_concat(["Tracing ", NumStr, "\n"], Msg),
  write(Msg).

write_break(Trm) :-
  write(Trm),
  write("\n").

strings_concat([], "").

strings_concat([Str | Strs], NewStr) :- 
  strings_concat(Strs, TempStr), 
  string_concat(Str, TempStr, NewStr). 

strings_concat_with(_, [], "").

strings_concat_with(_, [Str], Str).

strings_concat_with(Div, [Str | Strs], Rst) :-
  strings_concat_with(Div, Strs, TempStr),
  strings_concat([Str, Div, TempStr], Rst).

variant_nth0(0, [ElemA | _], ElemB) :- 
  ElemA =@= ElemB.

variant_nth0(Num, [_ | List], Elem) :- 
  variant_nth0(PredNum, List, Elem),
  Num is PredNum + 1.

variant_member(ElemA, [ElemB | _]) :- 
  ElemA =@= ElemB.

variant_member(Elem, [_ | List]) :-
  variant_member(Elem, List).

% groundfix(Var, []) :- var(Var), !.
% 
% groundfix([Elem | List], [Elem | Gfx]) :- 
%   groundfix(List, Gfx).