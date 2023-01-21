:- module msc.

:- interface.

:- import_module io.
:- import_module list.
:- import_module int.

:- func mapi(func(T1,int)=T2, list(T1)) = list(T2).
:- func mapi2d(func(T1,int,int)=T2, list(list(T1))) = list(list(T2)).
:- func mapi3d(func(T1,int,int,int)=T2, list(list(list(T1)))) = list(list(list(T2))).

:- func map2d(func(T1)=T2, list(list(T1))) = list(list(T2)).
:- func map3d(func(T1)=T2, list(list(list(T1)))) = list(list(list(T2))).

:- func map2d_corresponding(func(T1,T2)=T3, list(list(T1)), list(list(T2))) = list(list(T3)).
:- func map3d_corresponding(func(T1,T2)=T3, list(list(list(T1))), list(list(list(T2)))) =
   list(list(list(T3))).

:- func dim2(list(list(T))) = {int,int}.
:- func dim3(list(list(list(T)))) = {int,int,int}.

:- func condense3(list(list(list(T)))) = list(T).
:- func chunk3(list(T), int,int) = list(list(list(T))).

:- func map2(func(T1,T2) = T3, list(T1), list(T2)) = list(T3).

:- implementation.

mapi(F,L) = list.reverse(mapi_helper(F,L,0,[])).
:- func mapi_helper(func(T1,int)=T2, list(T1), int, list(T2)) = list(T2).
mapi_helper(F, List, I, Agg) = Y :-
    if List = [Head|Tail] then
        Y=mapi_helper(F, Tail, int.(I+1), [F(Head,I)|Agg])
    else Y = Agg.

mapi2d(F, ListOfLists) = mapi(func(Row,I) = mapi(func(X,J) = F(X,I,J), Row), ListOfLists).

mapi3d(F, Lists) = mapi(func(Slice,I) =
			mapi(func(Row,J) =
			     mapi(func(X,K) = F(X,I,J,K),
				  Row),
			     Slice),
			Lists).

map2d(F, List) = map(func(Row) = map(F, Row), List).

map3d(F, List) = map(func(Slice) = map(func(Row) = map(F, Row), Slice), List).

map2d_corresponding(F, List1, List2) =
list.map_corresponding(func(Row1,Row2) = list.map_corresponding(F, Row1,Row2), List1, List2).

map3d_corresponding(F, List1, List2) = list.map_corresponding(func(Slice1,Slice2) =
					    list.map_corresponding(func(Row1,Row2) =
						 list.map_corresponding(F, Row1,Row2),
						 Slice1, Slice2),
					    List1, List2).

dim2(L) = Y :-
    is_empty(L) -> Y = {0,0}
    ;
    Y = {length(L), length(det_head(L))}.

dim3(L) = Y :-
    is_empty(L) -> Y = {0,0,0}
    ;
    Y = {length(L), length(det_head(L)), length(det_head(det_head(L)))}.

chunk3(List, Nrows, Ncols) = Y :-
Y1 = list.chunk(List, Ncols),
	  Y = list.chunk(Y1,Nrows).

condense3(Lists) = Y :-
    Lists2 = list.map(condense, Lists),
    Y = list.foldr(func(Item,Agg) = list.append(Item,Agg), Lists2, []).

map2(F,List1,List2) = list.map_corresponding(F,List1,List2).

:- pred test(io::di, io::uo) is det.
test(!IO) :-
    Y=mapi3d(func(X,I,J,K) = {I,J,K,int.(X+I+J+K)}, [[[1,2,3],[4,5,6]]]),
    print_line(Y,!IO),
    Y2 = dim2([[],[2]]),
    print_line(Y2,!IO),
    Y3=map3d(func(X) = int.(X+1), [[[1,2,3],[4,5,6]]]),
    print_line(Y3,!IO),
    Y4 = [[[1,1],[2,2],[3,3]],[[11,10],[12,20],[13,30]]],
    {_,R,C} = dim3(Y4),
    Y5=condense3(Y4),
    print_line(Y5,!IO),
    Y6=chunk3(Y5,R,C),
    print_line(Y6,!IO).
