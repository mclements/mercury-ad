:- module test_ad.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- use_module math.
:- import_module ad.
:- import_module ad.v.
:- import_module list.
:- import_module float.

main(!IO) :-
    derivative_F(func(X) = exp(base(2.0)*X), base(1.0), GradF),
    print_line("Expected: ", !IO), print_line(base(math.exp(2.0)*2.0), !IO),
    print_line(GradF, !IO),
    gradient_R(func(List) = Y :-
		   (if List=[A,B] then Y=exp(base(2.0)*A)+B else Y = base(0.0)),
		   from_list([1.0,3.0]), Grad0),
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
    print_line(Y5,!IO),
    multivariate_argmin_R(rosenbrock,
			  [base(-3.0),base(4.0)],Y6),
    print_line("Expected: ", !IO),
    print_line([base(1.0),base(1.0)], !IO),
    print_line(Y6,!IO),
    multivariate_argmin_F(rosenbrock,
			  [base(-3.0),base(4.0)],Y7),
    print_line("Expected: ", !IO),
    print_line([base(1.0),base(1.0)], !IO),
    print_line(Y7,!IO),
    gradient_F(func(List) = Y :-
		   (if List=[A,B] then Y=atan2(A,B) else Y = base(0.0)),
		   [base(0.5),base(0.6)], Y8),
    print_line("Expected: ", !IO),
    Y8_Y = base(fdiff(func(Yi)=math.atan2(Yi,0.6),0.5)),
    Y8_X = base(fdiff(func(Xi)=math.atan2(0.5,Xi),0.6)),
    print_line([Y8_Y, Y8_X], !IO),
    print_line(Y8,!IO).

:- func rosenbrock(v_ad_number) = ad_number.
rosenbrock(In) = Result :-
    In = [X,Y] ->
    A = base(1.0),
    B = base(100.0),
    Result = (A-X)*(A-X)+B*(Y-X*X)*(Y-X*X)
    ;
    Result = base(0.0).
