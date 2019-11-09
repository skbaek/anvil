
bar(0).
quz(0).

qux(X) :- bar(X).
qux(X) :- quz(X).

foo(Num) :- 
  qux(Num) -> 
  (write("Fail"), false) ;
  true.
  