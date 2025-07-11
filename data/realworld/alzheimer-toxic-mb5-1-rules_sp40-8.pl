less_toxic(A,B):- ring_subst_5(A,F),ring_subst_6(B,E),great_polar(D,C),polar(F,D).
less_toxic(A,B):- alk_groups(B,D),ring_subst_4(A,C),n_val(A,D),ring_subst_5(B,E).
less_toxic(A,B):- ring_subst_6(B,E),pi_acceptor(E,D),x_subst(A,C,E),size(E,F).
less_toxic(A,B):- x_subst(B,C,F),ring_subst_5(A,F),ring_subst_5(A,D),polarisable(F,E).
less_toxic(A,B):- ring_subst_6(A,E),ring_subst_6(A,D),x_subst(B,F,C),alk_groups(A,F).
less_toxic(A,B):- x_subst(B,F,D),x_subst(B,F,E),ring_subst_4(A,E),ring_subst_4(B,C).
less_toxic(A,B):- alk_groups(A,D),r_subst_3(B,E),ring_subst_6(B,C),ring_subst_5(B,C).
less_toxic(A,B):- r_subst_1(B,C),flex(D,F),ring_subst_5(A,D),ring_substitutions(B,E).
less_toxic(A,B):- alk_groups(B,D),r_subst_2(A,C),x_subst(A,D,F),ring_subst_4(B,E).
less_toxic(A,B):- ring_subst_3(A,F),x_subst(B,C,D),alk_groups(B,E),ring_substitutions(A,E).
less_toxic(A,B):- ring_subst_6(B,F),ring_subst_3(B,C),x_subst(A,E,F),ring_subst_2(B,D).
less_toxic(A,B):- r_subst_1(A,E),alk_groups(A,D),ring_substitutions(B,D),r_subst_1(B,C).
less_toxic(A,B):- x_subst(A,C,D),sigma(D,E),ring_subst_4(B,D),n_val(B,C).
less_toxic(A,B):- ring_subst_2(B,C),n_val(B,F),x_subst(A,F,D),ring_subst_5(A,E).
less_toxic(A,B):- ring_subst_6(B,F),ring_subst_5(B,D),n_val(A,C),polarisable(D,E).
less_toxic(A,B):- x_subst(A,D,F),r_subst_3(B,C),ring_subst_5(A,E).
less_toxic(A,B):- ring_subst_5(A,C),ring_subst_2(B,C),ring_substitutions(B,E),pi_acceptor(C,D).
less_toxic(A,B):- polarisable(E,C),h_acceptor(E,F),ring_subst_4(B,E),ring_subst_2(A,D).
less_toxic(A,B):- ring_subst_5(A,C),ring_subst_4(B,D),r_subst_3(B,F),r_subst_2(B,E).
less_toxic(A,B):- ring_subst_3(A,F),r_subst_2(B,D),alk_groups(B,C),h_acceptor(F,E).
less_toxic(A,B):- ring_subst_6(A,F),ring_subst_4(B,D),ring_subst_2(B,E),ring_subst_4(B,C).
less_toxic(A,B):- x_subst(A,F,E),n_val(B,D),x_subst(A,C,E),n_val(B,C).
less_toxic(A,B):- size(E,C),ring_subst_4(B,E),r_subst_2(A,D),size(E,F).
less_toxic(A,B):- ring_subst_6(A,C),r_subst_3(A,E),pi_doner(C,D),ring_subst_6(B,C).
less_toxic(A,B):- gt(C,F),x_subst(B,F,E),n_val(A,C),ring_substitutions(B,D).
less_toxic(A,B):- ring_subst_4(B,F),ring_subst_6(A,C),ring_subst_2(B,E),x_subst(A,D,C).
less_toxic(A,B):- x_subst(A,C,D),h_doner(D,F),ring_subst_4(B,D),polarisable(D,E).
less_toxic(A,B):- ring_subst_3(A,F),ring_subst_3(A,E),r_subst_3(B,C),h_doner(F,D).
less_toxic(A,B):- flex(E,F),ring_subst_3(A,E),polarisable(E,D),ring_subst_5(B,C).
less_toxic(A,B):- ring_subst_2(B,C),polarisable(C,D),ring_subst_6(B,E),ring_subst_6(A,E).
less_toxic(A,B):- ring_subst_4(A,C),x_subst(B,D,E),ring_subst_5(B,F),ring_subst_5(A,E).
less_toxic(A,B):- ring_subst_5(A,F),alk_groups(B,E),pi_doner(F,C),r_subst_2(A,D).
less_toxic(A,B):- r_subst_3(B,D),polarisable(E,C),polar(E,F),ring_subst_6(A,E).
less_toxic(A,B):- alk_groups(B,D),polarisable(C,F),x_subst(A,E,C),ring_subst_3(B,C).
less_toxic(A,B):- r_subst_1(B,C),ring_subst_5(B,D),ring_subst_6(A,E),ring_subst_5(A,E).
less_toxic(A,B):- r_subst_2(B,C),ring_subst_3(A,E),ring_subst_3(A,F),ring_subst_3(B,D).
less_toxic(A,B):- ring_subst_6(B,E),gt(F,D),n_val(A,F),r_subst_3(B,C).
less_toxic(A,B):- ring_subst_4(B,F),ring_subst_6(A,D),ring_subst_3(A,C),flex(F,E).
less_toxic(A,B):- ring_subst_5(A,F),x_subst(B,C,D),size(D,E),ring_subst_6(A,F).
less_toxic(A,B):- r_subst_1(B,C),ring_substitutions(A,D),ring_subst_2(B,E),size(E,F).
