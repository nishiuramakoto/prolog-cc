% -*- mode:prolog; -*-
% Find all solutions of an 11 by 11 board.
% The \+ with the fail is a trick to make it find all solutions.
big(bear).
big(elephant).
small(cat).
brown(bear).
black(cat).
gray(elephant).
dark(Z) :- black(Z).
dark(Z) :- brown(Z).

goal(X) :- dark(X),big(X).
