:- module ad.
:- interface.
:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module list.
:- import_module float.
:- import_module bool.
:- import_module math.
:- import_module store.

main(!IO) :- 
    example1(!IO),
    example2(!IO).

:- type ad_number --->
   dual_number(ad_number, ad_number, ad_number)
   ;
   tape(ad_number,
	ad_number,
	list(ad_number),
	list(ad_number),
	ad_number, % ref
	ad_number) % ref
   ;
   base(float).

:- mutable(epsilon, ad_number, base(0.0), ground, [untrailed,attach_to_io_state]).

:- func make_dual_number(ad_number,ad_number,ad_number) = ad_number.
make_dual_number(E, X, Xprime) = Y :-
    if Xprime == base(0.0)
    then Y = X 
    else Y = dual_number(E, X, Xprime).

:- func make_tape(ad_number, ad_number, list(ad_number), list(ad_number)) = ad_number.
make_tape(E,X,Factors,Tapes) =
    tape(E, X, Factors, Tapes, base(0.0), base(0.0)).

:- func (ad_number::in) + (ad_number::in) = (ad_number::out) is det.
X + Y = lift_real_cross_real_to_real(func(A,B) = A+B,
				     func(_,_) = base(1.0),
				     func(_,_) = base(1.0), X, Y).
:- func (ad_number::in) - (ad_number::in) = (ad_number::out) is det.
X - Y = lift_real_cross_real_to_real(func(A,B) = A-B,
				     func(_,_) = base(1.0),
				     func(_,_) = base(-1.0), X, Y).
:- func (ad_number::in) * (ad_number::in) = (ad_number::out) is det.
X * Y = lift_real_cross_real_to_real(func(A,B) = A*B,
				     func(_,B) = B,
				     func(A,_) = A, X, Y).
:- func (ad_number::in) / (ad_number::in) = (ad_number::out) is det.
X / Y = lift_real_cross_real_to_real(func(A,B) = A/B,
				     func(_,B) = base(1.0)/B,
				     func(A,B) = base(0.0)-A/(B*B), X, Y).

:- pred (ad_number::in) < (ad_number::in) is semidet.
X < Y :- lift_real_cross_real_to_bool(pred(A::in,B::in) is semidet :- A < B, X, Y).
:- pred (ad_number::in) =< (ad_number::in) is semidet.
X =< Y :- lift_real_cross_real_to_bool(pred(A::in,B::in) is semidet :- A =< B, X, Y).

:- pred (ad_number::in) == (ad_number::in) is semidet.
X == Y :- lift_real_cross_real_to_bool((pred(A::in,B::in) is semidet :- A =< B, B =< A), X, Y).


:- func exp(ad_number) = ad_number is det.
exp(X) = lift_real_to_real(math.exp, exp, X).
:- func sqrt(ad_number) = ad_number is det.
sqrt(X) = lift_real_to_real(math.sqrt,
			    func(B) = base(1.0)/(sqrt(B)+sqrt(B)),
			    X).

:- func lift_real_to_real(func(float) = float, func(ad_number) = ad_number, ad_number) =
   ad_number.
lift_real_to_real(F,Dfdx,P) = Y :-
    Self = (func(A) = lift_real_to_real(F,Dfdx,A)),
    (P = base(X), Y = base(F(X))
    ;
    P = dual_number(E,X,Xprime), Y = make_dual_number(E, Self(X), Dfdx(X)*Xprime)
    ;
    P = tape(E, X, _, _, _, _), Y = make_tape(E, Self(X), [Dfdx(X)], [P])).

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
     P2=tape(E2,X2,_,_,_,_),
     (if E1<E2
	    then 
	    Y=make_tape(E2,Self(P1,X2),[Dfdx2(P1,X2)], [P2])
	      else
	      Y=make_dual_number(E1,Self(X1,P2),Dfdx1(X1,P2)*X1prime))
     ;
     P2=base(_),
     Y=make_dual_number(E1,Self(X1,P2),Dfdx1(X1,P2)*X1prime))
    ;
    %%
    P1=tape(E1,X1,_,_,_,_),
    (P2=dual_number(E2,X2,X2prime),
     (if E1<E2 then
	    Y = make_dual_number(E2,Self(P1,X2), Dfdx2(P1,X2)*X2prime)
		else
		Y = make_tape(E1,Self(X1,P2), [Dfdx1(X1,P2)], [P1]))
    ;
    P2 = tape(E2, X2, _,_,_,_),
    (if E1<E2 then
	   Y= make_tape(E2, Self(P1,X2), [Dfdx2(P1,X2)], [P2])
	      else
	      (if E2<E1 then
		     Y= make_tape(E1, Self(X1,P2), [Dfdx1(X1,P2)], [P1]) else
			Y=make_tape(E1, Self(X1,X2), [Dfdx1(X1,X2),Dfdx2(X1,X2)], [P1,P2])))
    ;
    P2=base(_),
    Y=make_tape(E1, Self(X1,P2), [Dfdx1(X1,P2)], [P1]))
    ;
    %%
    P1=base(X1),
    (P2 = dual_number(E2,X2,X2prime),
     Y = make_dual_number(E2, Self(P1,X2), Dfdx2(P1,X2)*X2prime)
    ;
    P2=tape(E2,X2,_,_,_,_),
    Y=make_tape(E2, Self(P1,X2), [Dfdx2(P1,X2)], [P2])
    ;
    P2=base(X2),
    Y=base(F(X1,X2)))).

:- pred lift_real_cross_real_to_bool(pred(float,float)::in(pred(in,in) is semidet),
				     ad_number::in, ad_number::in) is semidet.

lift_real_cross_real_to_bool(F, P1, P2) :-
    P1 = dual_number(_, X1, _),
    ((P2 = dual_number(_, X2, _) ; P2 = tape(_, X2, _, _, _, _)),
      lift_real_cross_real_to_bool(F, X1, X2)
     ;
     P2 = base(_),
     lift_real_cross_real_to_bool(F, X1, P2))
    ;
    %%
    P1 = tape(_, X1, _, _, _, _),
    ((P2 = dual_number(_,X2,_) ; P2 = tape(_,X2,_,_,_,_)),
     lift_real_cross_real_to_bool(F, X1, X2)
    ;
    P2 = base(_),
    lift_real_cross_real_to_bool(F, X1, P2))
    ;
    %%
    P1 = base(X1),
    ((P2=dual_number(_,X2, _) ; P2 = tape(_, X2, _, _, _, _)),
     lift_real_cross_real_to_bool(F, P1, X2)
    ;
    P2 = base(X2),
    call(F,X1,X2)).

:- pred derivative_F((func(ad_number) = ad_number)::in, ad_number::in, ad_number::out, io::di, io::uo) is det.
derivative_F(F,X,Y,!IO) :-
    some [!Epsilon] (
	get_epsilon(!:Epsilon, !IO),
	!:Epsilon = !.Epsilon + base(1.0),
	set_epsilon(!.Epsilon, !IO),
	Fprime = F(make_dual_number(!.Epsilon, X, base(1.0))),
	(if Fprime = dual_number(E1, _, Yprime) then
		     get_epsilon(!:Epsilon, !IO),
		     (if E1 < !.Epsilon then Y = base(0.0) else Y=Yprime)
		     else Y = base(0.0)),
	!:Epsilon = !.Epsilon - base(1.0),
	set_epsilon(!.Epsilon, !IO)).

:- pred example1(io::di, io::uo) is det.
example1(!IO) :-
    derivative_F(func(X) = exp(base(2.0)*X), base(1.0), Y, !IO),
    print_line(Y, !IO),
    print("Expected: ", !IO),
    print_line(math.exp(2.0)*2.0, !IO).

:- func determine_fanout(ad_number) = ad_number.
determine_fanout(In) = Y :-
    if In = tape(E, X, Factors, Tapes, Fanout, Sensitivity) then
    NewFanout = Fanout + base(1.0),
    (if NewFanout == base(1.0)
     then
     NewTapes = list.map(func(Tape) = determine_fanout(Tape), Tapes),
     Y = tape(E, X, Factors, NewTapes, NewFanout, Sensitivity)
	 else
     Y = tape(E, X, Factors, Tapes, NewFanout, Sensitivity))
    else Y = In. %% base(_) and dual_number(_,_,_)

:- func reverse_phase(ad_number, ad_number) = ad_number.
reverse_phase(Sensitivity1, In) = Y :-
    if In = tape(E, X, Factors, Tapes, Fanout, Sensitivity) then
    NewSensitivity = Sensitivity+Sensitivity1,
    NewFanout = Fanout - base(1.0),
    (if NewFanout == base(0.0)
     then
     NewTapes = list.map_corresponding(func(Factor,Tape) =
		       reverse_phase(NewSensitivity*Factor, Tape), Factors, Tapes),
     Y = tape(E, X, Factors, NewTapes, NewFanout, NewSensitivity)
     else
     Y = tape(E, X, Factors, Tapes, NewFanout, NewSensitivity))
    else Y = In. %% base(_) and dual_number(_,_,_)

:- func extract_gradients(ad_number) = ad_number.

extract_gradients(In) = Y :-
    (In = tape(_,_,[], [], _, Sensitivity) -> Y = Sensitivity
    ;
    In = tape(_,_,_, Tapes, _, _) ->
    Y = list.foldl(func(Item,Aggr) = Yi is det :-
		       (Sensitivity1 = extract_gradients(Item),
		       Yi=Aggr+Sensitivity1), Tapes, base(0.0))
    ;
    Y=In).

:- pred gradient_R((func(list(ad_number)) = ad_number)::in, list(ad_number)::in, list(ad_number)::out,
		   io::di, io::uo) is det.

gradient_R(F,X,Y,!IO) :-
    some [!Epsilon] (
	get_epsilon(!:Epsilon, !IO),
	!:Epsilon = !.Epsilon + base(1.0),
	set_epsilon(!.Epsilon, !IO),
	Epsilon0 = !.Epsilon,	      
	NewX = list.map(func(Xi) = make_tape(Epsilon0, Xi, [], []), X),
	Y1 = F(NewX),
        get_epsilon(!:Epsilon, !IO), %% Is this needed?
	Epsilon1 = !.Epsilon,	      
	(if Y1 = tape(E1, _, _, _, _, _),
	 (if E1 < Epsilon1 then Tapes2 = [Y1]
	  else
	  Y1a = determine_fanout(Y1),
	  reverse_phase(base(1.0),Y1a) = tape(_,_,_,Tapes2,_,_))
	then
	Y = list.map(extract_gradients, Tapes2)
	%% Y = Tapes2
	else Y = []), %% base(_) and dual_number(_,_,_)
	!:Epsilon = !.Epsilon - base(1.0),
	set_epsilon(!.Epsilon, !IO)).

%% let rec determine_fanout (Tape (_, _, _, tapes, fanout, _)) =
%%     (fanout := !fanout+.(Base 1.0);
%%      if !fanout<=(Base 1.0) && (Base 1.0)<=(!fanout)
%%      (* for-each *)
%%      then (map determine_fanout tapes; ())
%%      else ())

%% let rec reverse_phase sensitivity1 (Tape (_, _, factors, tapes, fanout, sensitivity)) =
%%   (sensitivity := !sensitivity+.sensitivity1;
%%    fanout := !fanout-.(Base 1.0);
%%    if !fanout<=(Base 0.0) && (Base 0.0)<=(!fanout)
%%        (* for-each *)
%%    then ((map2
%% 	    (fun factor tape -> reverse_phase (!sensitivity*.factor) tape)
%% 	    factors tapes);
%% 	 ())
%%    else ())
		      
%% let gradient_R f x =
%%     (epsilon := !epsilon+.(Base 1.0);
%%      let x = map (fun xi -> (tape (!epsilon) xi [] [])) x in
%%      let y = f x in
%%      (match f x with (Dual_number _) -> ()
%%      | Tape (e1, _, _, _, _, _) ->
%% 	 if e1<(!epsilon)
%% 	 then ()
%% 	 else (determine_fanout y; reverse_phase (Base 1.0) y)
%%      | Base _ -> ());
%%      epsilon := !epsilon-.(Base 1.0);
%%      map (fun (Tape (_, _, _, _, _, sensitivity)) -> !sensitivity) x)

:- pred example2(io::di, io::uo) is det.
example2(!IO) :-
    gradient_R(func(List) = Y :-
		   (if List=[A,B] then Y=B+A*A*A else Y = base(0.0)),
		   [base(1.1),base(2.3)], Grad, !IO),
    print_line(Grad, !IO), %% Oops: it is order-dependent:(
    print("Expected: ", !IO), print_line([3.0*1.1*1.1,1.0], !IO).

    %% gradient_R(func(List) = Y :-
    %% 		   (if List=[A,B,C] then Y=base(1.2)*A*A*A+base(1.5)*B*B+C*base(1.1) else Y=base(0.0)),
    %% 		   [base(1.0),base(2.0),base(3.0)], Grad, !IO),
    %% print_line(Grad, !IO),
    %% print_line("Expected: [base(3.6),base(6.0),base(1.1)]", !IO).

%% let rec write_real p =
%%   match p with (Dual_number (_, x, _)) -> ((write_real x); p)
%%   | (Tape (_, x, _, _, _, _)) -> ((write_real x); p)
%%   | (Base x) -> ((Printf.printf "%.18g\n" x); p)

%% let sqr x = x*.x

%% let map_n f n =
%%   let rec loop i = if i=n then [] else (f i)::(loop (i+1)) in loop 0

%% let vplus u v = map2 ( +. ) u v

%% let vminus u v = map2 ( -. ) u v

%% let ktimesv k = map (fun x -> k*.x)

%% let magnitude_squared x = fold_left ( +. ) (Base 0.0) (map sqr x)

%% let magnitude x = sqrt (magnitude_squared x)

%% let distance_squared u v = magnitude_squared (vminus v u)

%% let distance u v = sqrt (distance_squared u v)

%% let rec replace_ith (xh::xt) i xi =
%%     if i<=(Base 0.0) && (Base 0.0)<=i
%%     then xi::xt
%%     else xh::(replace_ith xt (i-.(Base 1.0)) xi)

%% let gradient_F f x =
%%   map_n
%%     (fun i -> derivative_F (fun xi -> f (replace_ith x (Base (float i)) xi)) (nth x i))
%%     (length x)

%% let rec gradient_ascent_F f x0 n eta =
%%     if n<=(Base 0.0) && (Base 0.0)<=n
%%     then (x0, (f x0), (gradient_F f x0))
%%     else gradient_ascent_F
%% 	     f (vplus x0 (ktimesv eta (gradient_F f x0))) (n-.(Base 1.0)) eta

%% let rec gradient_ascent_R f x0 n eta =
%%     if n<=(Base 0.0) && (Base 0.0)<=n
%%     then (x0, (f x0), (gradient_R f x0))
%%     else gradient_ascent_R
%% 	     f (vplus x0 (ktimesv eta (gradient_R f x0))) (n-.(Base 1.0)) eta

%% let multivariate_argmin_F f x =
%%     let g = gradient_F f in
%%     let rec loop x fx gx eta i =
%% 	       if (magnitude gx)<=(Base 1e-5)
%% 	       then x
%% 	       else if i<=(Base 10.0) && (Base 10.0)<=i
%% 	       then loop x fx gx ((Base 2.0)*.eta) (Base 0.0)
%% 	       else let x' = vminus x (ktimesv eta gx)
%% 		    in if (distance x x')<=(Base 1e-5)
%% 		       then x
%% 		       else let fx' = (f x')
%% 			    in if fx'<fx
%% 			       then loop x' fx' (g x') eta (i+.(Base 1.0))
%% 			       else loop x fx gx (eta/.(Base 2.0)) (Base 0.0)
%%        in loop x (f x) (g x) (Base 1e-5) (Base 0.0)

%% let rec multivariate_argmax_F f x =
%%     multivariate_argmin_F (fun x -> (Base 0.0)-.(f x)) x

%% let rec multivariate_max_F f x = f (multivariate_argmax_F f x)

%% let multivariate_argmin_R f x =
%%     let g = gradient_R f
%%     in let rec loop x fx gx eta i =
%% 	       if (magnitude gx)<=(Base 1e-5)
%% 	       then x
%% 	       else if i<=(Base 10.0) && (Base 10.0)<=i
%% 	       then loop x fx gx ((Base 2.0)*.eta) (Base 0.0)
%% 	       else let x' = vminus x (ktimesv eta gx)
%% 		    in if (distance x x')<=(Base 1e-5)
%% 		       then x
%% 		       else let fx' = (f x')
%% 			    in if fx'<fx
%% 			       then loop x' fx' (g x') eta (i+.(Base 1.0))
%% 			       else loop x fx gx (eta/.(Base 2.0)) (Base 0.0)
%%        in loop x (f x) (g x) (Base 1e-5) (Base 0.0)

%% let rec multivariate_argmax_R f x =
%%   multivariate_argmin_R (fun x -> (Base 0.0)-.(f x)) x

%% let multivariate_max_R f x = f (multivariate_argmax_R f x)