%--------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et
%--------------------------------------------------%
% Copyright (C) 2023 Mark Clements.
% This file is distributed under the terms specified in LICENSE.
%--------------------------------------------------%
%
% File: ad.m.
% Authors: mclements
% Stability: low.
%
% This module defines backward and forward automatic
% differentiation
%
%--------------------------------------------------%

:- module ad.
:- interface.
:- import_module list.
:- import_module float.

    %% main representation type
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

    %% vector of ad_numbers
:- type v_ad_number == list(ad_number).
    %% matrix of ad_numbers
:- type m_ad_number == list(list(ad_number)).
    %% vector of floats
:- type v_float == list(float).
    %% matrix of floats
:- type m_float == list(list(float)).

    %% make_dual(Tag, Value, Derivative) constructs a dual_number
:- func make_dual_number(int,ad_number,ad_number) = ad_number.
    %% make_dual(Tag, Epsilon, Value, Factors, Tapes) constructs a tape
:- func make_tape(int, int, ad_number, v_ad_number,
		  v_ad_number) = ad_number.

%% defined functions and predicates for differentiation
:- func (ad_number::in) + (ad_number::in) = (ad_number::out) is det.
:- func (ad_number::in) - (ad_number::in) = (ad_number::out) is det.
:- func (ad_number::in) * (ad_number::in) = (ad_number::out) is det.
:- func (ad_number::in) / (ad_number::in) = (ad_number::out) is det.
:- func pow(ad_number, ad_number) = ad_number.
:- pred (ad_number::in) < (ad_number::in) is semidet.
:- pred (ad_number::in) =< (ad_number::in) is semidet.
:- pred (ad_number::in) > (ad_number::in) is semidet.
:- pred (ad_number::in) >= (ad_number::in) is semidet.
:- pred (ad_number::in) == (ad_number::in) is semidet. % equality
:- func exp(ad_number) = ad_number is det.
:- func ln(ad_number) = ad_number is det.
:- func log2(ad_number) = ad_number is det.
:- func log10(ad_number) = ad_number is det.
:- func log(ad_number,ad_number) = ad_number is det.
:- func sqrt(ad_number) = ad_number is det.
:- func sin(ad_number) = ad_number is det.
:- func cos(ad_number) = ad_number is det.
:- func tan(ad_number) = ad_number is det.
:- func asin(ad_number) = ad_number is det.
:- func acos(ad_number) = ad_number is det.
:- func atan(ad_number) = ad_number is det.
:- func atan2(ad_number,ad_number) = ad_number is det.
:- func sinh(ad_number) = ad_number is det.
:- func cosh(ad_number) = ad_number is det.
:- func tanh(ad_number) = ad_number is det.
:- func abs(ad_number) = ad_number is det.
%% TODO: add further functions and operators

    %% derivative_F(F,Theta,Derivative,!Epsilon) takes a function F and initial values Theta,
    %% and returns the Derivarive, with input and output for Epsilon (accounting on the derivatives).
    %% Uses forward differentiation.
:- pred derivative_F((func(ad_number) = ad_number)::in, ad_number::in, ad_number::out,
		     int::in, int::out) is det.
    %% derivative_F(F,Theta,Derivative) takes a function F and initial values Theta,
    %% and returns the Derivative, assuming the default derivative count.
    %% Uses forward differentiation.
:- pred derivative_F((func(ad_number) = ad_number)::in, ad_number::in, ad_number::out) is det.

    %% gradient_F(F,Theta,Gradient,!Epsilon) takes a function F and initial values Theta,
    %% and returns the Gradient, with input and output for Epsilon (accounting on the derivatives)
    %% Uses forward differentiation.
:- pred gradient_F((func(v_ad_number) = ad_number)::in,
		   v_ad_number::in, v_ad_number::out) is det.
    %% gradient_F(F,Theta,Gradient) takes a function F and initial values Theta,
    %% and returns the Gradient, assuming the default derivative count.
    %% Uses forward differentiation.
:- pred gradient_F((func(v_ad_number) = ad_number)::in,
		   v_ad_number::in, v_ad_number::out,
		  int::in, int::out) is det.

    %% gradient_F(F,Theta,Gradient) takes a function F and initial values Theta,
    %% and returns the Gradient, assuming the default derivative count.
    %% Uses backward differentiation.
:- pred gradient_R((func(v_ad_number) = ad_number)::in,
		   v_ad_number::in, v_ad_number::out,
		   int::in, int::out) is det.
    %% gradient_R(F,Theta,Gradient) takes a function F and initial values Theta,
    %% and returns the Gradient, assuming the default derivative count.
    %% Uses backward differentiation.
:- pred gradient_R((func(v_ad_number) = ad_number)::in,
		   v_ad_number::in, v_ad_number::out) is det.

    %% gradient_ascent_F(F,Theta,Iterations,Eta,{Final,Objective,Derivatives})
    %% takes a function F, initial values Theta, number of Iterations and change Epsilon,
    %% a calculates the *maximum*, returning the Final parameters, the Objective and the Derivatives.
    %% Uses forward differentiation.
:- pred gradient_ascent_F((func(v_ad_number) = ad_number)::in,
			   v_ad_number::in,
			   int::in,
			   float::in,
			   {v_ad_number, ad_number, v_ad_number}::out) is det.
    %% gradient_ascent_R(F,Theta,Iterations,Eta,{Final,Objective,Derivatives})
    %% takes a function F, initial values Theta, number of Iterations and change Epsilon,
    %% a calculates the *maximum*, returning the Final parameters, the Objective and the Derivatives.
    %% Uses backward differentiation.
:- pred gradient_ascent_R((func(v_ad_number) = ad_number)::in,
			   v_ad_number::in,
			   int::in,
			   float::in,
			   {v_ad_number, ad_number, v_ad_number}::out) is det.

    %% multivariate_argmin_F(F,Theta,Final})
    %% takes a function F and initial values Theta
    %% and calculates the Final values for the *minimum*.
    %% Uses forward differentiation.
:- pred multivariate_argmin_F((func(v_ad_number) = ad_number)::in,
			      v_ad_number::in,
			      v_ad_number::out) is det.
    %% multivariate_argmin_F(F,Theta,Final})
    %% takes a function F and initial values Theta
    %% and calculates the Final values for the *minimum*.
    %% Uses backward differentiation.
:- pred multivariate_argmin_R((func(v_ad_number) = ad_number)::in,
			      v_ad_number::in,
			      v_ad_number::out) is det.

    %% multivariate_argmax_F(F,Theta,Final})
    %% takes a function F and initial values Theta
    %% and calculates the Final values for the *maximum*.
    %% Uses forward differentiation.
:- pred multivariate_argmax_F((func(v_ad_number) = ad_number)::in,
			      v_ad_number::in,
			      v_ad_number::out) is det.
    %% multivariate_argmax_R(F,Theta,Final})
    %% takes a function F and initial values Theta
    %% and calculates the Final values for the *maximum*.
    %% Uses backward differentiation.
:- pred multivariate_argmax_R((func(v_ad_number) = ad_number)::in,
			      v_ad_number::in,
			      v_ad_number::out) is det.

    %% multivariate_max_F(F,Theta,Value})
    %% takes a function F and initial values Theta
    %% and calculates the *maximum* Value.
    %% Uses forward differentiation.
:- pred multivariate_max_F((func(v_ad_number) = ad_number)::in,
			   v_ad_number::in,
			   ad_number::out) is det.
    %% multivariate_max_R(F,Theta,Value})
    %% takes a function F and initial values Theta
    %% and calculates the *maximum* Value.
    %% Uses backward differentiation.
:- pred multivariate_max_R((func(v_ad_number) = ad_number)::in,
			   v_ad_number::in,
			   ad_number::out) is det.

%% Some common utilities
    %% sqr(X) = X*X
:- func sqr(ad_number) = ad_number.
    %% map_n(F,N) = list.map(F, 1..N).
:- func map_n(func(int) = ad_number, int) = v_ad_number.
    %% vplus(X,Y) = X + Y
:- func vplus(v_ad_number, v_ad_number) = v_ad_number.
    %% vminus(X,Y) = X - Y
:- func vminus(v_ad_number, v_ad_number) = v_ad_number.
    %% ktimesv(K,V) = K*V
:- func ktimesv(ad_number, v_ad_number) = v_ad_number.
    %% magnitude_squared(V) = sum_i(V[i]*V[i])
:- func magnitude_squared(v_ad_number) = ad_number.
    %% magnitude(V) = sqrt(sum_i(V[i]*V[i]))
:- func magnitude(v_ad_number) = ad_number.
    %% distance_squared(X,Y) = magnitude_sqrt(X-Y)
:- func distance_squared(v_ad_number,v_ad_number) = ad_number.
    %% distance(X,Y) = magnitude(X-Y)
:- func distance(v_ad_number,v_ad_number) = ad_number.
    %% fdiff(F,X,Eps) gives the first derivative for F at X using a
    %% symmetric finite difference using Eps
:- func fdiff(func(float)=float,float,float) = float.
    %% fdiff(F,X) = fdiff(F,X,1.0e-5)
:- func fdiff(func(float)=float,float) = float.

%% submodule for operations and functions on v_ad_number
:- module ad.v.
:- interface.
    %% Addition
:- func (v_ad_number::in) + (v_ad_number::in) = (v_ad_number::out) is det.
    %% Subtraction
:- func (v_ad_number::in) - (v_ad_number::in) = (v_ad_number::out) is det.
    %% multiplication by a scalar
:- func (ad_number::in) * (v_ad_number::in) = (v_ad_number::out) is det.
    %% convert from a vector of floats
:- func from_list(v_float) = v_ad_number.
    %% convert of a vector of floats
:- func to_list(v_ad_number) = v_float is det.
:- end_module ad.v.

%% submodule for operations and functions on m_ad_number
:- module ad.m.
:- interface.
    %% Addition
:- func (m_ad_number::in) + (m_ad_number::in) = (m_ad_number::out) is det.
    %% Subtraction
:- func (m_ad_number::in) - (m_ad_number::in) = (m_ad_number::out) is det.
    %% convert from a matrix of floats
:- func from_lists(m_float) = m_ad_number.
    %% convert of a matrix of floats
:- func to_lists(m_ad_number) = m_float is det.
:- end_module ad.m.

    %% fanout(Tape) is the fanout operation for backward differentiation 
:- func determine_fanout(ad_number) = ad_number.
    %% reverse_phase(Sensitivity,Tape) is the reverse pahse for backward differentiation
:- func reverse_phase(ad_number, ad_number) = ad_number.
    %% extract_gradients(Tape) extracts the gradients as a vector
:- func extract_gradients(ad_number) = v_ad_number.
    %% to_float(Ad_number) return a float representation
:- func to_float(ad_number) = float.

:- implementation.
:- import_module bool.
:- import_module math.
:- import_module int.
:- import_module map.

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
pow(X,Y) = lift_real_cross_real_to_real(func(A,B) = pow(A,B),
					func(A,B) = B*pow(A,B-base(1.0)),
					func(A,B) = ln(A)*pow(A,B), X, Y).
atan2(Y,X) = lift_real_cross_real_to_real(math.atan2,
					  func(B,A) = A/(A*A+B*B),
					  func(B,A) = base(0.0)-B/(A*A+B*B), Y, X).
log(X,Base) = lift_real_cross_real_to_real(math.log,
				           func(A,B) = base(1.0)/(A*ln(B)),
					   func(A,B) = base(0.0)-ln(A)/(B*ln(B)*ln(B)), X, Base).

X < Y :- lift_real_cross_real_to_bool(pred(A::in,B::in) is semidet :- A < B, X, Y).
X =< Y :- lift_real_cross_real_to_bool(pred(A::in,B::in) is semidet :- A =< B, X, Y).
X == Y :- lift_real_cross_real_to_bool((pred(A::in,B::in) is semidet :- A =< B, B =< A), X, Y).
X > Y :- lift_real_cross_real_to_bool(pred(A::in,B::in) is semidet :- A > B, X, Y).
X >= Y :- lift_real_cross_real_to_bool(pred(A::in,B::in) is semidet :- A >= B, X, Y).

exp(X) = lift_real_to_real(math.exp, exp, X).
ln(X) = lift_real_to_real(math.ln, func(A) = base(1.0)/A, X).
log2(X) = lift_real_to_real(math.log2, func(A) = base(1.0)/A/base(math.ln(2.0)), X).
log10(X) = lift_real_to_real(math.log10, func(A) = base(1.0)/A/base(math.ln(10.0)), X).
sqrt(X) = lift_real_to_real(math.sqrt,
			    func(B) = base(1.0)/(sqrt(B)+sqrt(B)),
			    X).
sin(X) = lift_real_to_real(math.sin, cos, X).
cos(X) = lift_real_to_real(math.cos, func(A) = base(0.0)-sin(A), X).
tan(X) = lift_real_to_real(math.tan, func(A) = base(1.0)+tan(A)*tan(A), X).
asin(X) = lift_real_to_real(math.asin, func(A) = base(1.0)/sqrt(base(1.0)-A*A), X).
acos(X) = lift_real_to_real(math.acos, func(A) = base(0.0) - base(1.0)/sqrt(base(1.0)-A*A), X).
atan(X) = lift_real_to_real(math.atan, func(A) = base(1.0)/(base(1.0)+A*A), X).
sinh(X) = lift_real_to_real(math.sinh, cosh, X).
cosh(X) = lift_real_to_real(math.cosh, sinh, X).
tanh(X) = lift_real_to_real(math.tanh, func(A) = base(1.0)-tanh(A)*tanh(A), X).
abs(X) = lift_real_to_real(float.abs,
			   func(A) = B :- if A>=base(0.0) then B=base(1.0) else B=base(-1.0), X).
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

:- pred extract_gradients_helper(ad_number::in, map(int,ad_number)::in, map(int,ad_number)::out) is det.
extract_gradients_helper(In,!Map) :-
    In = tape(N,_,_,_,[],_, Sensitivity) ->
	(if contains(!.Map, N)
	 then map.det_update(N,Sensitivity+lookup(!.Map,N),!Map)
         else map.det_insert(N,Sensitivity,!Map))
    ;
    In = tape(_,_,_,_, Tapes, _, _) ->
    list.foldl(extract_gradients_helper, Tapes, !Map)
    ;
    !:Map = !.Map.

extract_gradients(In) = Result :-
    extract_gradients_helper(In, map.init, Map1),
    Result = map.values(Map1).

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
	Y = extract_gradients(Tape)
	%% Y = [Tape] % for debugging
	else Y = []), %% base(_) and dual_number(_,_,_)
	!:Epsilon = int.(!.Epsilon - 1).

to_float(In) = Y :-
    In = dual_number(_,X,_) -> Y = to_float(X)
    ;
    In = tape(_,_,X,_,_,_,_) -> Y = to_float(X)
    ;
    In = base(X) -> Y = X
    ;
    Y = 0.0. 

sqr(X) = X*X.
map_n(F,N) = list.map(F, 1..N).
vplus(A,B) = ad.v.(A+B).
vminus(A,B) = ad.v.(A-B).
ktimesv(K,V) = ad.v.(K*V).
magnitude_squared(V) = list.foldl(func(Vi,A) = A+Vi*Vi, V, base(0.0)).
magnitude(V) = sqrt(magnitude_squared(V)).
distance_squared(V1,V2) = magnitude_squared(vminus(V1,V2)).
distance(V1,V2) = sqrt(distance_squared(V1,V2)).
fdiff(F,X,Eps) = (F(X+Eps)-F(X-Eps))/2.0/Eps.
fdiff(F,X) = fdiff(F,X,1.0e-5).

:- module ad.v.
:- implementation.
X + Y = list.map_corresponding(func(Xi,Yi) = Xi+Yi, X, Y).
X - Y = list.map_corresponding(func(Xi,Yi) = Xi-Yi, X, Y).
X * Y = list.map(func(Yi) = X*Yi, Y).
from_list(List) = list.map(func(Item) = base(Item),List).
to_list(List) = list.map((func(Item) = Y :- Item=base(X) -> Y=X; Y=0.0),List).
:- end_module ad.v.

:- module ad.m.
:- implementation.
X + Y = list.map_corresponding(func(Xi,Yi) = ad.v.(Xi+Yi), X, Y).
X - Y = list.map_corresponding(func(Xi,Yi) = ad.v.(Xi-Yi), X, Y).
from_lists(Lists) = list.map(ad.v.from_list,Lists).
to_lists(Lists) = list.map(ad.v.to_list,Lists).
:- end_module ad.m.

:- import_module ad.v.
:- import_module ad.m.

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

:- pred multivariate_argmin_F_loop(v_ad_number::in,
				   (func(v_ad_number) = ad_number)::in,
				   ad_number::in,
				   ad_number::in,
				   int::in,
				   v_ad_number::out) is det.
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

:- pred multivariate_argmin_R_loop(v_ad_number::in,
				   (func(v_ad_number) = ad_number)::in,
				   ad_number::in,
				   ad_number::in,
				   int::in,
				   v_ad_number::out) is det.
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
