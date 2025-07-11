less_toxic(A,B):- x_subst(A,F,E),r_subst_3(A,D),ring_subst_5(B,C).
less_toxic(A,B):- x_subst(B,D,E),polarisable(E,C),ring_subst_4(A,E),size(E,F).
less_toxic(A,B):- r_subst_1(B,C),ring_subst_4(B,D),ring_subst_2(A,E),n_val(A,F).
less_toxic(A,B):- ring_subst_4(B,F),ring_subst_2(A,C),r_subst_2(B,D),sigma(F,E).
less_toxic(A,B):- ring_subst_6(B,D),r_subst_1(A,F),ring_subst_2(B,E),flex(E,C).
less_toxic(A,B):- x_subst(B,D,E),ring_subst_5(A,E),x_subst(A,D,C),alk_groups(B,F).
less_toxic(A,B):- r_subst_3(A,C),ring_subst_5(B,E),flex(E,D),size(E,F).
less_toxic(A,B):- ring_subst_6(A,C),ring_subst_2(B,C),r_subst_1(B,D),r_subst_1(A,D).
less_toxic(A,B):- ring_subst_2(A,E),ring_subst_3(A,C),ring_subst_3(A,F),x_subst(B,D,C).
less_toxic(A,B):- r_subst_1(B,C),ring_subst_4(B,E),x_subst(A,D,F),ring_subst_3(A,F).
less_toxic(A,B):- ring_subst_4(A,D),ring_subst_3(B,C),ring_subst_3(A,C),ring_subst_2(B,D).
less_toxic(A,B):- h_doner(C,F),ring_subst_6(A,D),x_subst(A,E,D),ring_subst_5(B,C).
less_toxic(A,B):- r_subst_2(B,C),ring_subst_5(A,F),ring_substitutions(B,E),polar(F,D).
less_toxic(A,B):- r_subst_3(A,C),ring_substitutions(B,E),x_subst(A,E,D),ring_subst_3(B,D).
less_toxic(A,B):- size(D,F),r_subst_2(A,C),ring_subst_4(B,D),ring_subst_4(A,E).
less_toxic(A,B):- ring_subst_2(B,C),x_subst(A,E,C),h_doner(C,F),polar(C,D).
less_toxic(A,B):- x_subst(A,C,F),x_subst(A,C,D),x_subst(B,C,D),x_subst(A,E,F).
less_toxic(A,B):- ring_subst_5(B,D),x_subst(A,C,D),x_subst(A,E,D),alk_groups(A,C).
less_toxic(A,B):- ring_subst_6(A,C),ring_subst_5(A,F),alk_groups(A,E),ring_subst_3(B,D).
less_toxic(A,B):- r_subst_1(B,C),r_subst_1(A,F),alk_groups(A,E),gt(E,D).
less_toxic(A,B):- r_subst_3(B,D),ring_subst_6(A,C),sigma(C,E),alk_groups(B,F).
less_toxic(A,B):- gt(C,E),r_subst_3(A,C),ring_substitutions(A,E),r_subst_1(B,D).
less_toxic(A,B):- x_subst(A,D,E),gt(C,D),ring_subst_3(B,E),n_val(A,C).
less_toxic(A,B):- ring_substitutions(B,E),r_subst_3(A,C),x_subst(B,D,F),alk_groups(A,C).
less_toxic(A,B):- r_subst_3(B,D),ring_subst_3(B,E),pi_doner(E,F),ring_subst_6(A,C).
less_toxic(A,B):- gt(E,C),alk_groups(B,C),ring_subst_2(A,D),n_val(A,E).
less_toxic(A,B):- ring_subst_3(A,F),ring_substitutions(B,C),x_subst(B,C,E),ring_subst_2(A,D).
less_toxic(A,B):- ring_subst_5(B,F),ring_subst_2(B,F),x_subst(B,C,D),alk_groups(A,E).
less_toxic(A,B):- ring_subst_5(A,C),ring_subst_3(B,C),ring_subst_4(B,E),ring_subst_2(B,D).
less_toxic(A,B):- r_subst_2(B,C),ring_subst_3(A,E),n_val(A,F),r_subst_2(A,D).
less_toxic(A,B):- r_subst_1(A,F),x_subst(A,C,E),n_val(A,C),ring_substitutions(B,D).
less_toxic(A,B):- ring_substitutions(B,E),x_subst(A,E,D),x_subst(B,F,C).
less_toxic(A,B):- x_subst(B,D,E),r_subst_2(B,F),ring_subst_3(A,C),x_subst(A,D,C).
less_toxic(A,B):- ring_subst_6(A,C),ring_subst_5(A,F),h_acceptor(E,D),ring_subst_6(B,E).
less_toxic(A,B):- ring_subst_5(A,F),pi_acceptor(C,E),x_subst(B,D,F),ring_subst_5(B,C).
less_toxic(A,B):- ring_subst_4(A,C),ring_subst_2(B,C),x_subst(B,D,F),r_subst_3(A,E).
less_toxic(A,B):- ring_subst_5(A,F),ring_subst_5(B,D),ring_subst_4(B,E),h_acceptor(F,C).
less_toxic(A,B):- ring_subst_5(B,D),polar(C,E),n_val(A,F),ring_subst_5(B,C).
less_toxic(A,B):- ring_subst_6(B,F),x_subst(B,C,D),alk_groups(A,E),ring_substitutions(B,C).
less_toxic(A,B):- polar(C,E),n_val(B,D),r_subst_3(A,D),ring_subst_6(B,C).
less_toxic(A,B):- x_subst(A,F,E),x_subst(A,F,C),ring_subst_5(A,D),ring_subst_2(B,D).
less_toxic(A,B):- alk_groups(A,D),r_subst_3(A,C),r_subst_3(B,E),x_subst(A,D,F).
less_toxic(A,B):- ring_subst_5(B,F),r_subst_1(B,C),ring_subst_5(A,D),ring_subst_4(A,E).
less_toxic(A,B):- r_subst_2(A,C),ring_subst_4(B,E),n_val(A,F),r_subst_2(A,D).
less_toxic(A,B):- x_subst(A,C,D),x_subst(B,C,E),x_subst(A,F,D),ring_subst_2(A,D).
less_toxic(A,B):- ring_subst_6(B,C),r_subst_1(A,D),polarisable(C,E),ring_subst_5(B,C).
less_toxic(A,B):- x_subst(B,E,F),ring_subst_4(B,F),h_doner(D,C),ring_subst_3(A,D).
less_toxic(A,B):- n_val(B,D),x_subst(B,C,E),x_subst(A,C,E),ring_subst_5(B,E).
less_toxic(A,B):- n_val(A,D),ring_subst_5(B,E),x_subst(B,D,C),sigma(C,F).
less_toxic(A,B):- ring_subst_3(A,E),flex(E,C),ring_subst_3(B,F),pi_acceptor(F,D).
less_toxic(A,B):- ring_subst_5(A,C),ring_subst_6(A,D),x_subst(B,F,E),ring_subst_2(A,D).
less_toxic(A,B):- ring_substitutions(A,F),x_subst(B,F,D),x_subst(B,C,D),x_subst(B,C,E).
less_toxic(A,B):- ring_subst_2(A,E),polar(C,F),x_subst(B,D,C),ring_subst_6(B,C).
less_toxic(A,B):- ring_subst_6(B,C),size(C,E),ring_subst_3(B,D),r_subst_3(A,F).
less_toxic(A,B):- ring_subst_5(A,F),pi_acceptor(F,E),alk_groups(B,C),pi_acceptor(F,D).
less_toxic(A,B):- gt(E,F),ring_subst_2(B,C),ring_subst_4(A,D),x_subst(B,E,D).
less_toxic(A,B):- x_subst(A,F,E),h_acceptor(E,D),x_subst(B,F,E),alk_groups(A,C).
less_toxic(A,B):- ring_subst_3(A,E),ring_subst_2(B,C),size(E,D),x_subst(B,F,C).
less_toxic(A,B):- ring_subst_5(A,C),r_subst_2(B,F),r_subst_3(B,E),ring_subst_2(B,D).
less_toxic(A,B):- r_subst_1(A,E),r_subst_1(B,C),ring_subst_5(B,D),size(D,F).
less_toxic(A,B):- r_subst_2(A,E),r_subst_3(B,D),ring_subst_2(B,C),ring_subst_4(B,F).
less_toxic(A,B):- x_subst(A,C,D),ring_subst_5(A,D),n_val(B,F),sigma(D,E).
less_toxic(A,B):- size(D,E),size(D,C),x_subst(A,F,D),alk_groups(B,F).
less_toxic(A,B):- ring_subst_5(B,D),ring_subst_2(A,C),x_subst(A,E,C),ring_subst_5(A,D).
less_toxic(A,B):- ring_subst_2(B,F),alk_groups(A,E),x_subst(A,D,C),ring_substitutions(B,D).
less_toxic(A,B):- ring_subst_2(B,C),r_subst_2(B,F),alk_groups(A,E),r_subst_2(A,D).
less_toxic(A,B):- r_subst_1(B,C),ring_subst_5(B,D),ring_subst_5(A,D).
less_toxic(A,B):- x_subst(B,F,D),r_subst_2(A,C),ring_subst_2(B,E),r_subst_2(B,C).
less_toxic(A,B):- ring_subst_3(A,E),x_subst(B,C,D),r_subst_3(A,C),x_subst(A,C,E).
less_toxic(A,B):- ring_subst_5(A,C),n_val(B,E),x_subst(B,D,C),r_subst_3(A,F).
less_toxic(A,B):- x_subst(B,C,D),r_subst_1(A,F),ring_subst_4(A,E),ring_subst_3(A,D).
less_toxic(A,B):- ring_subst_6(B,F),n_val(B,E),flex(F,D),alk_groups(A,C).
less_toxic(A,B):- x_subst(A,F,E),polarisable(E,C),x_subst(A,F,D),alk_groups(B,F).
less_toxic(A,B):- x_subst(B,C,F),ring_subst_5(A,F),n_val(B,E),h_acceptor(F,D).
less_toxic(A,B):- ring_subst_4(B,F),n_val(A,D),polar(E,C),ring_subst_6(B,E).
less_toxic(A,B):- ring_subst_3(A,E),ring_subst_3(B,C),ring_subst_4(B,E),polarisable(C,D).
less_toxic(A,B):- ring_subst_6(B,D),ring_subst_5(A,E),n_val(A,C),ring_subst_3(B,D).
less_toxic(A,B):- alk_groups(A,D),ring_subst_2(B,C),ring_subst_2(B,E),sigma(C,F).
less_toxic(A,B):- ring_subst_3(B,E),n_val(A,D),polarisable(E,C),size(E,F).
less_toxic(A,B):- x_subst(B,E,F),h_doner(C,D),ring_substitutions(A,E),ring_subst_6(B,C).
