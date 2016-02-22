
/* */
solution([]).

solution([co(X,Y)|Others]) :-
     solution(Others),
     member(Y,[1,2,3,4,5,6]),
     noattack(co(X,Y),Others).

%% solution([X/Y|Others]) :-
%%     solution(Others),
%%     member(Y,[1,2,3,4,5,6]),
%%     noattack(X/Y,Others).

noattack(_,[]).

noattack(co(X,Y),[co(X1,Y1)|Others]) :-
    Y =\=  Y1,
    Y1-Y =\= X1-X,
    Y1-Y =\= X-X1,
    noattack(co(X,Y),Others).

%% noattack(X/Y,[X1/Y1|Others]) :-
%%     Y =\= Y1,
%%     Y1-Y =\= X1-X,
%%     Y1-Y =\= X-X1,
%%     noattack(X/Y,Others).

member(Item,[Item|_Rest]).

member(Item,[_First|Rest]) :-
    member(Item,Rest).


template([co(1,Y1),co(2,Y2),co(3,Y3),co(4,Y4),co(5,Y5),co(6,Y6)]).
%% template([1/Y1,2/Y2,3/Y3,4/Y4,5/Y5,6/Y6]).

goal(S) :- template(S) , solution(S).
