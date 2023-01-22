:- module mlp_R.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module ad.
:- import_module ad.v.
:- import_module ad.m.
:- import_module list.
:- import_module int.
:- import_module map.

main(!IO) :-
    Fit = vanilla(error_on_dataset(xor_data),
		  xor_ws0,
		  10000, % 1_000_000
		  base(0.3)),
    Y = ad.to_float(Fit),
    io.print_line(Y, !IO).

:- func xor_ws0 = list(m_ad_number).
xor_ws0 = [from_lists([[0.0, -0.284227, 1.16054],
 		       [0.0, 0.617194, 1.30467]]),
 	   from_lists([[0.0, -0.084395, 0.648461]])].

:- func xor_data = list({v_ad_number,v_ad_number}).
xor_data = [{[base(0.0), base(0.0)], [base(0.0)]},
		{[base(0.0), base(1.0)], [base(1.0)]},
		{[base(1.0), base(0.0)], [base(1.0)]},
		{[base(1.0), base(1.0)], [base(0.0)]}].

:- func sum_activities(v_ad_number, v_ad_number) = ad_number is det. 
sum_activities(Activities, Bias_Ws) = Y :-
    if Bias_Ws = [Bias|Ws] then
	Y = list.foldl(func(L,A) =L+A+Bias,
		       list.map_corresponding(func(A,B) = A*B, Ws, Activities),
		       base(0.0))
    else
        Y = base(0.0).

:- func sum_layer(v_ad_number, m_ad_number) = v_ad_number is det.
sum_layer(Activities, Ws_layer) = 
  list.map(func(Bias_Ws) = sum_activities(Activities, Bias_Ws),
	   Ws_layer).

:- func sigmoid(ad_number) = ad_number is det.
sigmoid(X) = base(1.0)/(base(1.0)+exp(base(0.0)-X)).

:- func forward_pass(list(m_ad_number),v_ad_number) = v_ad_number is det.
forward_pass(A,In1) = Y :-
    A = [Ws_layer|Ws_layers] ->
	Y = forward_pass(Ws_layers, list.map(sigmoid, sum_layer(In1, Ws_layer)))
    ;
    Y = In1.

:- func error_on_dataset(list({v_ad_number,v_ad_number}), list(m_ad_number))=ad_number.
error_on_dataset(Dataset,Ws_layers) = Y :-
  Y = list.foldl(func(A,B) = A+B,
		 list.map((func({In1,Target}) = 
			   base(0.5)*ad.magnitude_squared(ad.vminus(forward_pass(Ws_layers, In1), Target))),
			  Dataset),
		 base(0.0)).

:- func s_kstar(list(m_ad_number), ad_number, list(m_ad_number)) = list(m_ad_number).
s_kstar(W,K,Y) = 
list.map_corresponding((func(Wi, Yi) =
      list.map_corresponding((func(Wij, Yij) =
	    list.map_corresponding((func(Wijk,Yijk) = Wijk-K*Yijk),
		 Wij, Yij)),
	   Wi, Yi)),
     W, Y).

:- pred weight_gradient((func(list(m_ad_number))=ad_number)::(in(func(in)=out is det)),
			list(m_ad_number)::in, list(m_ad_number)::out, int::in, int::out).
weight_gradient(F,W,Y,!Epsilon) :-
    !:Epsilon = int.(!.Epsilon+1),
    Epsilon1 = !.Epsilon,
    {_,Nrows,Ncols} = dim3(W),
    W2 = mapi3d(func(Wijk,I,J,K) =
		ad.make_tape(int.(Nrows*Ncols*I+Ncols*J+K), Epsilon1, Wijk, [], []), W),
    Y1 = F(W2),
    (if Y1 = tape(_,E1,_,_,_,_,_),
     (if int.(E1 < !.Epsilon) then Tape = Y1
      else
        Y1a = ad.determine_fanout(Y1),
        Tape = ad.reverse_phase(base(1.0),Y1a))
     then
      List = ad.extract_gradients(Tape),
      Y = chunk3(List, Nrows, Ncols)
     else Y = [[[]]]),
     !:Epsilon = int.(!.Epsilon - 1).

:- func vanilla(func(list(m_ad_number)) = ad_number, list(m_ad_number), int, ad_number) =
   ad_number.
vanilla(F,W0,N,Eta) = Result :-
    if N=0 then Result = F(W0)
    else
      weight_gradient(F,W0,Y,0,_),
      Result = vanilla(F,s_kstar(W0,Eta,Y), int.(N-1), Eta).

%%%% Some utilities

:- func mapi(func(T1,int)=T2, list(T1)) = list(T2).
mapi(F,L) = list.reverse(mapi_helper(F,L,0,[])).
:- func mapi_helper(func(T1,int)=T2, list(T1), int, list(T2)) = list(T2).
mapi_helper(F, List, I, Agg) = Y :-
    if List = [Head|Tail] then
        Y=mapi_helper(F, Tail, int.(I+1), [F(Head,I)|Agg])
    else Y = Agg.

:- func mapi3d(func(T1,int,int,int)=T2, list(list(list(T1)))) = list(list(list(T2))).
mapi3d(F, Lists) = mapi(func(Slice,I) =
			mapi(func(Row,J) =
			     mapi(func(X,K) = F(X,I,J,K),
				  Row),
			     Slice),
			Lists).

:- func dim3(list(list(list(T)))) = {int,int,int}.
dim3(L) = Y :-
    is_empty(L) -> Y = {0,0,0}
    ;
    Y = {length(L), length(det_head(L)), length(det_head(det_head(L)))}.

:- func chunk3(list(T), int,int) = list(list(list(T))).
chunk3(List, Nrows, Ncols) = Y :-
    Y1 = list.chunk(List, Ncols),
    Y = list.chunk(Y1,Nrows).
