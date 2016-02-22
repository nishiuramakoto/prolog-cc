% Find all solutions of an 11 by 11 board.
% The \+ with the fail is a trick to make it find all solutions.
goal(X) :- 2 > 1, ! , X = Y.
goal(X) :- 3 > 1, X = 3.
