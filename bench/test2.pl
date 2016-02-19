% -*- mode:prolog; -*-

conc([], L2, L2).
conc([X|L1],L2,[X|L3]) :- conc(L1,L2,L3).

% flatten(List,FlatList)
flatten([],[]).
flatten([X|Tail],FlatList) :- flatten(X,L1), flatten(Tail,L2), conc(L1,L2,FlatList).
flatten(X,[X]) :- X=a.
