
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

/* Difflist operations */ 

% precons(Elem, (List, Ext), ([Elem | List], Ext)).
% 
% postcons(Elem, (List, [Elem | Ext]), (List, Ext)).
% 
% prepend(ListA, (ListB, Ext), (ListAB, Ext)) :-
%   append(ListA, ListB, ListAB).
% 
% postpend(ListA, (ListB, Ext), (ListB, NewExt)) :-
%   append(ListA, NewExt, Ext).

% Extract the ground prefix of a difflist.
gnd_prefix(List, []) :- 
  var(List), !.

gnd_prefix([Elem | List], [Elem | Pfx]) :- 
  gnd_prefix(List, Pfx).

gnd_nth0(_, Var, _) :-
  var(Var), !, false.

gnd_nth0(0, [Elem | _], Elem).

gnd_nth0(Num, [_ | List], Elem) :-
  gnd_nth0(PredNum, List, Elem), 
  Num is PredNum + 1.

gnd_member(_, Var) :-
  var(Var), !, false.

gnd_member(Elem, [Elem | _]).

gnd_member(Elem, [_ | List]) :-
  gnd_member(Elem, List).

gnd_length(Var, 0) :-
  var(Var), !. 

gnd_length([_ | List], Num) :- 
  gnd_length(List, PredNum), 
  Num is PredNum + 1.
