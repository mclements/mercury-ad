:- module ad.
:- interface.
:- import_module io.
:- import_module list.
:- import_module float.

:- pred main(io::di, io::uo) is det.

:- type ad_number --->
   dual_number(int,       % epsilon (used for order of derivative)
	       ad_number, % value
	       ad_number) % derivative
   ;
   tape(int,              % variable order (new)
	int,              % epsilon (used for order of derivative)
	ad_number,        % value
	list(ad_number),  % factors
	list(ad_number),  % tape
	int,              % fanout 
	ad_number)        % sensitivity
   ;
   base(float).

:- func make_dual_number(int,ad_number,ad_number) = ad_number.
:- func make_tape(int, int, ad_number, list(ad_number),
		  list(ad_number)) = ad_number.

:- func (ad_number::in) + (ad_number::in) = (ad_number::out) is det.
:- func (ad_number::in) - (ad_number::in) = (ad_number::out) is det.
:- func (ad_number::in) * (ad_number::in) = (ad_number::out) is det.
:- func (ad_number::in) / (ad_number::in) = (ad_number::out) is det.
:- pred (ad_number::in) < (ad_number::in) is semidet.
:- pred (ad_number::in) =< (ad_number::in) is semidet.
:- pred (ad_number::in) > (ad_number::in) is semidet.
:- pred (ad_number::in) >= (ad_number::in) is semidet.
:- pred (ad_number::in) == (ad_number::in) is semidet.
:- func exp(ad_number) = ad_number is det.
:- func sqrt(ad_number) = ad_number is det.

:- pred derivative_F((func(ad_number) = ad_number)::in, ad_number::in, ad_number::out,
		     int::in, int::out) is det.
:- pred derivative_F((func(ad_number) = ad_number)::in, ad_number::in, ad_number::out) is det.
:- pred gradient_F((func(list(ad_number)) = ad_number)::in,
		   list(ad_number)::in, list(ad_number)::out) is det.
:- pred gradient_F((func(list(ad_number)) = ad_number)::in,
		   list(ad_number)::in, list(ad_number)::out,
		  int::in, int::out) is det.
:- pred gradient_R((func(list(ad_number)) = ad_number)::in,
		   list(ad_number)::in, list(ad_number)::out,
		   int::in, int::out) is det.
:- pred gradient_R((func(list(ad_number)) = ad_number)::in,
		   list(ad_number)::in, list(ad_number)::out) is det.

:- pred gradient_ascent_F((func(list(ad_number)) = ad_number)::in,
			   list(ad_number)::in,
			   int::in,
			   float::in,
			   {list(ad_number), ad_number, list(ad_number)}::out) is det.
:- pred gradient_ascent_R((func(list(ad_number)) = ad_number)::in,
			   list(ad_number)::in,
			   int::in,
			   float::in,
			   {list(ad_number), ad_number, list(ad_number)}::out) is det.
:- pred multivariate_argmin_F((func(list(ad_number)) = ad_number)::in,
			      list(ad_number)::in,
			      list(ad_number)::out) is det.
:- pred multivariate_argmin_R((func(list(ad_number)) = ad_number)::in,
			      list(ad_number)::in,
			      list(ad_number)::out) is det.
:- pred multivariate_argmax_F((func(list(ad_number)) = ad_number)::in,
			      list(ad_number)::in,
			      list(ad_number)::out) is det.
:- pred multivariate_argmax_R((func(list(ad_number)) = ad_number)::in,
			      list(ad_number)::in,
			      list(ad_number)::out) is det.
:- pred multivariate_max_F((func(list(ad_number)) = ad_number)::in,
			   list(ad_number)::in,
			   ad_number::out) is det.
:- pred multivariate_max_R((func(list(ad_number)) = ad_number)::in,
			   list(ad_number)::in,
			   ad_number::out) is det.

:- func sqr(ad_number) = ad_number.
:- func map_n(func(int) = ad_number, int) = list(ad_number).
:- func vplus(list(ad_number), list(ad_number)) = list(ad_number).
:- func vminus(list(ad_number), list(ad_number)) = list(ad_number).
:- func ktimesv(ad_number, list(ad_number)) = list(ad_number).
:- func magnitude_squared(list(ad_number)) = ad_number.
:- func magnitude(list(ad_number)) = ad_number.
:- func distance_squared(list(ad_number),list(ad_number)) = ad_number.
:- func distance(list(ad_number),list(ad_number)) = ad_number.

:- implementation.
:- import_module bool.
:- import_module math.
:- import_module map.
:- import_module int.

main(!IO) :- 
    examples(!IO).

%% :- mutable(epsilon, int, 0, ground, [untrailed,attach_to_io_state]).

make_dual_number(E, X, Xprime) = Y :-
    if Xprime = base(0.0)
    then Y = X 
    else Y = dual_number(E, X, Xprime).

make_tape(N,E,X,Factors,Tapes) =
    tape(N, E, X, Factors, Tapes, 0, base(0.0)).

X + Y = lift_real_cross_real_to_real(func(A,B) = A+B,
				     func(_,_) = base(1.0),
				     func(_,_) = base(1.0), X, Y).
X - Y = lift_real_cross_real_to_real(func(A,B) = A-B,
				     func(_,_) = base(1.0),
				     func(_,_) = base(-1.0), X, Y).
X * Y = lift_real_cross_real_to_real(func(A,B) = A*B,
				     func(_,B) = B,
				     func(A,_) = A, X, Y).
X / Y = lift_real_cross_real_to_real(func(A,B) = A/B,
				     func(_,B) = base(1.0)/B,
				     func(A,B) = base(0.0)-A/(B*B), X, Y).

X < Y :- lift_real_cross_real_to_bool(pred(A::in,B::in) is semidet :- A < B, X, Y).
X =< Y :- lift_real_cross_real_to_bool(pred(A::in,B::in) is semidet :- A =< B, X, Y).
X == Y :- lift_real_cross_real_to_bool((pred(A::in,B::in) is semidet :- A =< B, B =< A), X, Y).
X > Y :- lift_real_cross_real_to_bool(pred(A::in,B::in) is semidet :- A > B, X, Y).
X >= Y :- lift_real_cross_real_to_bool(pred(A::in,B::in) is semidet :- A >= B, X, Y).

exp(X) = lift_real_to_real(math.exp, exp, X).
sqrt(X) = lift_real_to_real(math.sqrt,
			    func(B) = base(1.0)/(sqrt(B)+sqrt(B)),
			    X).
%% TODO: add further functions and operators

:- func lift_real_to_real(func(float) = float, func(ad_number) = ad_number, ad_number) =
   ad_number.
lift_real_to_real(F,Dfdx,P) = Y :-
    Self = (func(A) = lift_real_to_real(F,Dfdx,A)),
    (P = base(X), Y = base(F(X))
    ;
    P = dual_number(E,X,Xprime), Y = make_dual_number(E, Self(X), Dfdx(X)*Xprime)
    ;
    P = tape(N, E, X, _, _, _, _), Y = make_tape(N, E, Self(X), [Dfdx(X)], [P])).

:- func lift_real_cross_real_to_real(func(float,float) = float,
				     func(ad_number, ad_number) = ad_number,
				     func(ad_number, ad_number) = ad_number,
				     ad_number, ad_number) = ad_number.
lift_real_cross_real_to_real(F,Dfdx1,Dfdx2,P1,P2) = Y :-
    Self = (func(A,B) = lift_real_cross_real_to_real(F,Dfdx1,Dfdx2,A,B)),
    (P1 = dual_number(E1,X1,X1prime),
     (P2 = dual_number(E2,X2,X2prime),
      (if E1<E2
	     then
	     Y=make_dual_number(E2, Self(P1,X2),Dfdx2(P1,X2)*X2prime)
	       else
	       (if E2<E1 then
		      Y=make_dual_number(E1, Self(X1,P2),Dfdx1(X1,P2)*X1prime)
			else
			Y = make_dual_number(E1, Self(X1,X2),Dfdx1(X1,X2)*X1prime+Dfdx2(X1,X2)*X2prime)))
     ;
     P2=tape(N2,E2,X2,_,_,_,_),
     (if E1<E2
	    then 
	    Y=make_tape(N2,E2,Self(P1,X2),[Dfdx2(P1,X2)], [P2])
	      else
	      Y=make_dual_number(E1,Self(X1,P2),Dfdx1(X1,P2)*X1prime))
     ;
     P2=base(_),
     Y=make_dual_number(E1,Self(X1,P2),Dfdx1(X1,P2)*X1prime))
    ;
    %%
    P1=tape(N1,E1,X1,_,_,_,_),
    (P2=dual_number(E2,X2,X2prime),
     (if E1<E2 then
	    Y = make_dual_number(E2,Self(P1,X2), Dfdx2(P1,X2)*X2prime)
		else
		Y = make_tape(N1,E1,Self(X1,P2), [Dfdx1(X1,P2)], [P1]))
    ;
    P2 = tape(N2,E2, X2, _,_,_,_),
    (if E1<E2 then
	   Y= make_tape(N2,E2, Self(P1,X2), [Dfdx2(P1,X2)], [P2])
	      else
	      (if E2<E1 then
		     Y= make_tape(N1, E1, Self(X1,P2), [Dfdx1(X1,P2)], [P1]) else
			Y=make_tape(N1, E1, Self(X1,X2), [Dfdx1(X1,X2),Dfdx2(X1,X2)], [P1,P2])))
    ;
    P2=base(_),
    Y=make_tape(N1,E1, Self(X1,P2), [Dfdx1(X1,P2)], [P1]))
    ;
    %%
    P1=base(X1),
    (P2 = dual_number(E2,X2,X2prime),
     Y = make_dual_number(E2, Self(P1,X2), Dfdx2(P1,X2)*X2prime)
    ;
    P2=tape(N2,E2,X2,_,_,_,_),
    Y=make_tape(N2,E2, Self(P1,X2), [Dfdx2(P1,X2)], [P2])
    ;
    P2=base(X2),
    Y=base(F(X1,X2)))).

:- pred lift_real_cross_real_to_bool(pred(float,float)::in(pred(in,in) is semidet),
				     ad_number::in, ad_number::in) is semidet.

lift_real_cross_real_to_bool(F, P1, P2) :-
    P1 = dual_number(_, X1, _),
    ((P2 = dual_number(_, X2, _) ; P2 = tape(_, _, X2, _, _, _, _)),
      lift_real_cross_real_to_bool(F, X1, X2)
     ;
     P2 = base(_),
     lift_real_cross_real_to_bool(F, X1, P2))
    ;
    %%
    P1 = tape(_, _, X1, _, _, _, _),
    ((P2 = dual_number(_,X2,_) ; P2 = tape(_,_,X2,_,_,_,_)),
     lift_real_cross_real_to_bool(F, X1, X2)
    ;
    P2 = base(_),
    lift_real_cross_real_to_bool(F, X1, P2))
    ;
    %%
    P1 = base(X1),
    ((P2=dual_number(_,X2, _) ; P2 = tape(_, _, X2, _, _, _, _)),
     lift_real_cross_real_to_bool(F, P1, X2)
    ;
    P2 = base(X2),
    call(F,X1,X2)).

derivative_F(F,X,Y) :- derivative_F(F,X,Y,0,_).
derivative_F(F,X,Y,!Epsilon) :-
	!:Epsilon = int.(!.Epsilon + 1),
	Fprime = F(make_dual_number(!.Epsilon, X, base(1.0))),
	(if Fprime = dual_number(E1, _, Yprime) then
		     (if int.(E1 < !.Epsilon) then Y = base(0.0) else Y=Yprime)
		     else Y = base(0.0)),
	!:Epsilon = int.(!.Epsilon - 1).

:- pred examples(io::di, io::uo) is det.
examples(!IO) :-
    derivative_F(func(X) = exp(base(2.0)*X), base(1.0), GradF),
    print_line("Expected: ", !IO), print_line(base(math.exp(2.0)*2.0), !IO),
    print_line(GradF, !IO),
    gradient_R(func(List) = Y :-
		   (if List=[A,B] then Y=exp(base(2.0)*A)+B else Y = base(0.0)),
		   [base(1.0),base(3.0)], Grad0),
    print_line("Expected: ", !IO), print_line([base(math.exp(2.0)*2.0),base(1.0)], !IO),
    print_line(Grad0, !IO),
    gradient_R(func(List) = Y :-
		   (if List=[A,B] then Y=B+A*A*A else Y = base(0.0)),
		   [base(1.1),base(2.3)], Grad),
    print_line("Expected: ", !IO), print_line([base(3.0*1.1*1.1),base(1.0)], !IO),
    print_line(Grad, !IO),
    gradient_R(func(List) = Y :-
		   (if List=[A,B] then Y=exp(B+A*A*A) else Y = base(0.0)),
		   [base(1.1),base(2.3)], Grad2),
    print_line("Expected: ", !IO),
    print_line([base(math.exp(2.3+1.1*1.1*1.1)*(3.0*1.1*1.1)),
		base(math.exp(2.3+1.1*1.1*1.1))], !IO),
    print_line(Grad2, !IO),
    gradient_F(func(List) = Y :-
		   (if List=[A,B] then Y=exp(B+A*A*A) else Y = base(0.0)),
		   [base(1.1),base(2.3)], Grad3),
    print_line("Expected: ", !IO),
    print_line([base(math.exp(2.3+1.1*1.1*1.1)*(3.0*1.1*1.1)),
		base(math.exp(2.3+1.1*1.1*1.1))], !IO),
    print_line(Grad3, !IO),
    multivariate_argmin_F(func(AB) = Y :-
			      if AB = [A,B]
				      then Y = A*A+(B-base(1.0))*(B-base(1.0))
								  else Y=base(0.0),
			  [base(1.0),base(2.0)],Y4),
    print_line("Expected: ", !IO),
    print_line([base(0.0),base(1.0)], !IO),
    print_line(Y4,!IO),
    multivariate_argmin_R(func(AB) = Y :-
			      if AB = [A,B]
				      then Y = A*A+(B-base(1.0))*(B-base(1.0))
								  else Y=base(0.0),
			  [base(1.0),base(2.0)],Y5),
    print_line("Expected: ", !IO),
    print_line([base(0.0),base(1.0)], !IO),
    print_line(Y5,!IO).
			  
 
:- func determine_fanout(ad_number) = ad_number.
determine_fanout(In) = Y :-
    if In = tape(N, E, X, Factors, Tapes, Fanout, Sensitivity) then
    NewFanout = int.(Fanout + 1),
    (if NewFanout = 1
     then
     NewTapes = list.map(func(Tape) = determine_fanout(Tape), Tapes),
     Y = tape(N, E, X, Factors, NewTapes, NewFanout, Sensitivity)
	 else
     Y = tape(N, E, X, Factors, Tapes, NewFanout, Sensitivity))
    else Y = In. %% base(_) and dual_number(_,_,_)

:- func reverse_phase(ad_number, ad_number) = ad_number.
reverse_phase(Sensitivity1, In) = Y :-
    if In = tape(N, E, X, Factors, Tapes, Fanout, Sensitivity) then
    NewSensitivity = Sensitivity+Sensitivity1,
    NewFanout = int.(Fanout - 1),
    (if NewFanout = 0
     then
     NewTapes = list.map_corresponding(func(Factor,Tape) =
		       reverse_phase(NewSensitivity*Factor, Tape), Factors, Tapes),
     Y = tape(N, E, X, Factors, NewTapes, NewFanout, NewSensitivity)
     else
     Y = tape(N, E, X, Factors, Tapes, NewFanout, NewSensitivity))
    else Y = In. %% base(_) and dual_number(_,_,_)

:- pred extract_gradients(ad_number::in,
			  map(int,ad_number)::in,
			  map(int,ad_number)::out) is det.
extract_gradients(In,!Map) :-
    In = tape(N,_,_,_,[],_, Sensitivity) ->
	(if contains(!.Map, N)
	 then map.det_update(N,Sensitivity+lookup(!.Map,N),!Map)
         else map.det_insert(N,Sensitivity,!Map))
    ;
    In = tape(_,_,_,_, Tapes, _, _) ->
    list.foldl(extract_gradients, Tapes, !Map)
    ;
    !:Map = !.Map.

gradient_R(F,X,Y) :- gradient_R(F,X,Y,0,_).
gradient_R(F,X,Y,!Epsilon) :-
	!:Epsilon = int.(!.Epsilon + 1),
	Indexes = 1..length(X),
	Epsilon0 = !.Epsilon,
	NewX = list.map_corresponding(func(Xi,J) = make_tape(J, Epsilon0, Xi, [], []), X, Indexes),
	Y1 = F(NewX),
	(if Y1 = tape(_, E1, _, _, _, _, _),
	 (if int.(E1 < !.Epsilon) then Tape = Y1
	  else
	  Y1a = determine_fanout(Y1),
	  Tape = reverse_phase(base(1.0),Y1a))
	then
	extract_gradients(Tape, map.init, Map1),
	Y = map.values(Map1)
	%% Y = [Tape] % for debugging
	else Y = []), %% base(_) and dual_number(_,_,_)
	!:Epsilon = int.(!.Epsilon - 1).

:- func write_real(ad_number) = float.
write_real(In) = Y :-
    In = dual_number(_,X,_) -> Y = write_real(X)
    ;
    In = tape(_,_,X,_,_,_,_) -> Y = write_real(X)
    ;
    In = base(X) -> Y = X
    ;
    Y = 0.0. 

sqr(X) = X*X.
map_n(F,N) = list.map(func(I) = F(I), 1..N).
vplus(A,B) = list.map_corresponding(func(Ai,Bi) = Ai+Bi, A, B).
vminus(A,B) = list.map_corresponding(func(Ai,Bi) = Ai-Bi, A, B).
ktimesv(K,V) = list.map(func(Vi) = Vi*K, V).
magnitude_squared(V) = list.foldl(func(Vi,A) = A+Vi*Vi, V, base(0.0)).
magnitude(V) = sqrt(magnitude_squared(V)).
distance_squared(V1,V2) = magnitude_squared(vminus(V1,V2)).
distance(V1,V2) = sqrt(distance_squared(V1,V2)).

:- module ad.lists.
:- interface.
:- func (list(ad_number)::in) + (list(ad_number)::in) = (list(ad_number)::out) is det.
:- func (list(ad_number)::in) - (list(ad_number)::in) = (list(ad_number)::out) is det.
:- implementation.
X + Y = list.map_corresponding(func(Xi,Yi) = Xi+Yi, X, Y).
X - Y = list.map_corresponding(func(Xi,Yi) = Xi-Yi, X, Y).
:- end_module ad.lists.

:- func replace_ith1(list(T),int,T) = list(T).
replace_ith1(In, I, Xi) = Y :-
    In = [Xh|Xt] ->
    (if I = 1 then Y=[Xi|Xt] else Y = [Xh|replace_ith1(Xt, int.(I-1), Xi)])
    ;
    Y = [].

gradient_F(F,X,Y) :-gradient_F(F,X,Y,0,_).
gradient_F(F,X,Y,!Epsilon) :-
    some [Eps] (
	Eps = !.Epsilon,
    list.map_foldl(pred(I::in,Yi::out, _::in, E1::out) is det :-
		       derivative_F(func(Xi) = F(replace_ith1(X, I, Xi)),
				    det_index1(X,I), Yi, Eps, E1),
		       1..list.length(X), Y, !Epsilon)).

gradient_ascent_F(F, X0, N, Eta, Y) :-
    gradient_F(F, X0, D0),
    (if N = 0
	    then Y = {X0, F(X0), D0}
     else gradient_ascent_F(F, 
	     vplus(X0, ktimesv(base(Eta), D0)), int.(N-1), Eta, Y)).

gradient_ascent_R(F, X0, N, Eta, Y) :-
    gradient_F(F, X0, D0),
    (if N = 0
	    then Y = {X0, F(X0), D0}
     else gradient_ascent_R(F, 
	     vplus(X0, ktimesv(base(Eta), D0)), int.(N-1), Eta, Y)).

multivariate_argmin_F(F,X,Y) :-
    multivariate_argmin_F_loop(X, F, base(1e-5), base(1e-8), 0, Y).

:- pred multivariate_argmin_F_loop(list(ad_number)::in,
				   (func(list(ad_number)) = ad_number)::in,
				   ad_number::in,
				   ad_number::in,
				   int::in,
				   list(ad_number)::out) is det.
multivariate_argmin_F_loop(X, F, Eta, Gtol, I, Y) :-
    FX = F(X),
    gradient_F(F,X,GX),
    (if magnitude(GX) =< Gtol
     then Y=X
     else (if I=10
		then multivariate_argmin_F_loop(X,F,base(2.0)*Eta, Gtol, 0, Y)
		else Xdash = vminus(X, ktimesv(Eta, GX)),
		    (if distance(X,Xdash) =< Gtol
		       then Y=X
		       else FXdash = F(Xdash),
			    (if FXdash<FX
			       then multivariate_argmin_F_loop(Xdash,F, Eta, Gtol, int.(I+1), Y) 
			       else multivariate_argmin_F_loop(X,F,Eta/base(2.0), Gtol, 0, Y))))).

multivariate_argmin_R(F,X,Y) :-
    multivariate_argmin_R_loop(X, F, base(1e-5), base(1e-8), 0, Y).

:- pred multivariate_argmin_R_loop(list(ad_number)::in,
				   (func(list(ad_number)) = ad_number)::in,
				   %% pred(list(ad_number), list(ad_number),IO0,IO1)::in(pred(in,in,out,di,uo) is det),
				   ad_number::in,
				   ad_number::in,
				   int::in,
				   list(ad_number)::out) is det.
multivariate_argmin_R_loop(X, F, Eta, Gtol, I, Y) :-
    FX = F(X),
    gradient_R(F,X,GX),
    (if magnitude(GX) =< Gtol
     then Y=X
     else (if I=10
		then multivariate_argmin_R_loop(X,F,base(2.0)*Eta, Gtol, 0, Y)
		else Xdash = vminus(X, ktimesv(Eta, GX)),
		    (if distance(X,Xdash)=< Gtol
		       then Y=X
		       else FXdash = F(Xdash),
			    (if FXdash<FX
			       then multivariate_argmin_R_loop(Xdash,F, Eta, Gtol, int.(I+1), Y) 
			       else multivariate_argmin_R_loop(X,F,Eta/base(2.0), Gtol, 0, Y))))).

multivariate_argmax_F(F,X,Y) :-
    multivariate_argmin_F(func(X1) = base(0.0) - F(X1), X, Y).
multivariate_max_F(F,X, Y) :-
    multivariate_argmax_F(F,X, Theta),
    Y = F(Theta).
multivariate_argmax_R(F,X,Y) :-
    multivariate_argmin_R(func(X1) = base(0.0) - F(X1), X, Y).
multivariate_max_R(F,X, Y) :-
    multivariate_argmax_R(F,X, Theta),
    Y = F(Theta).
