less_toxic(A,B):- ring_subst_3(B,E),r_subst_3(A,C),ring_subst_2(A,D),alk_groups(B,F).
less_toxic(A,B):- x_subst(B,F,E),r_subst_3(A,D),x_subst(A,D,C),ring_subst_4(A,E).
less_toxic(A,B):- ring_substitutions(A,F),x_subst(A,D,E),ring_subst_4(A,C),ring_subst_5(B,C).
less_toxic(A,B):- r_subst_2(A,E),sigma(C,D),r_subst_3(B,F),ring_subst_4(B,C).
less_toxic(A,B):- size(F,E),ring_subst_3(B,C),ring_subst_3(A,F),size(F,D).
less_toxic(A,B):- ring_subst_6(A,E),size(E,D),ring_substitutions(A,C),alk_groups(B,F).
less_toxic(A,B):- ring_subst_6(A,D),ring_subst_3(B,C),ring_subst_5(A,D),ring_subst_6(B,C).
less_toxic(A,B):- x_subst(B,C,F),ring_subst_2(B,F),gt(E,C),x_subst(A,E,D).
less_toxic(A,B):- ring_subst_2(B,C),ring_subst_3(A,C),ring_subst_2(B,E),x_subst(A,F,D).
less_toxic(A,B):- x_subst(A,F,E),sigma(C,D),ring_subst_6(B,E),ring_subst_5(B,C).
less_toxic(A,B):- x_subst(B,F,E),gt(C,D),ring_substitutions(A,C),ring_subst_4(A,E).
less_toxic(A,B):- ring_subst_2(A,C),r_subst_2(B,F),ring_subst_2(B,E),ring_subst_2(B,D).
less_toxic(A,B):- alk_groups(B,D),ring_subst_4(A,C),n_val(A,D),ring_substitutions(B,E).
less_toxic(A,B):- x_subst(B,C,D),ring_subst_6(A,D),ring_subst_3(A,D),r_subst_2(B,E).
less_toxic(A,B):- x_subst(A,F,E),sigma(C,D),x_subst(B,F,C).
less_toxic(A,B):- ring_substitutions(B,C),ring_subst_4(B,E),r_subst_2(A,D),polarisable(E,F).
less_toxic(A,B):- x_subst(B,F,D),alk_groups(B,C),x_subst(A,E,D),gt(E,F).
less_toxic(A,B):- x_subst(B,E,F),r_subst_1(B,C),alk_groups(A,E),pi_acceptor(F,D).
less_toxic(A,B):- ring_subst_2(A,F),x_subst(A,D,E),sigma(F,C),x_subst(B,D,E).
less_toxic(A,B):- ring_subst_5(A,F),flex(F,C),r_subst_1(B,D),sigma(F,E).
less_toxic(A,B):- x_subst(A,C,F),ring_subst_6(A,D),x_subst(B,E,D),ring_subst_2(B,D).
less_toxic(A,B):- x_subst(B,D,E),n_val(B,F),ring_subst_5(B,E),x_subst(A,D,C).
less_toxic(A,B):- size(D,F),ring_subst_4(A,D),ring_subst_4(A,E),ring_subst_6(B,C).
less_toxic(A,B):- size(D,C),ring_subst_6(B,D),alk_groups(B,F),ring_subst_4(A,E).
less_toxic(A,B):- ring_subst_6(A,F),ring_substitutions(A,D),r_subst_3(B,E),r_subst_3(B,C).
less_toxic(A,B):- x_subst(A,F,E),r_subst_3(B,D),ring_subst_2(A,E),ring_subst_5(B,C).
less_toxic(A,B):- alk_groups(A,E),h_acceptor(C,F),x_subst(B,D,C),ring_subst_4(B,C).
less_toxic(A,B):- x_subst(B,D,E),n_val(A,D),ring_subst_3(A,C),x_subst(B,D,C).
less_toxic(A,B):- pi_doner(E,C),sigma(E,D),ring_subst_6(B,E),ring_subst_4(A,E).
less_toxic(A,B):- n_val(B,D),r_subst_1(B,F),n_val(A,C),ring_subst_4(B,E).
less_toxic(A,B):- ring_subst_3(A,F),n_val(A,C),x_subst(A,E,D),ring_subst_3(B,D).
less_toxic(A,B):- ring_subst_6(B,F),ring_subst_2(A,C),n_val(A,D),r_subst_3(B,E).
less_toxic(A,B):- ring_subst_3(B,E),x_subst(A,C,D),ring_subst_3(B,F),ring_subst_3(A,D).
less_toxic(A,B):- n_val(B,E),x_subst(A,C,D),gt(E,C).
less_toxic(A,B):- r_subst_1(A,E),x_subst(B,C,D),r_subst_3(A,C),ring_subst_4(B,F).
less_toxic(A,B):- ring_subst_4(B,F),polarisable(F,C),ring_subst_2(A,D),n_val(A,E).
less_toxic(A,B):- r_subst_1(A,E),r_subst_2(B,D),ring_subst_5(A,C),r_subst_3(B,F).
less_toxic(A,B):- r_subst_1(B,C),ring_subst_5(A,F),ring_subst_2(A,D),n_val(A,E).
less_toxic(A,B):- x_subst(A,C,F),ring_subst_5(B,D),ring_subst_6(A,D),x_subst(A,E,F).
less_toxic(A,B):- sigma(D,C),ring_subst_3(A,D),alk_groups(A,E),ring_subst_2(B,D).
less_toxic(A,B):- r_subst_2(A,E),ring_subst_4(B,F),polarisable(F,C),size(F,D).
less_toxic(A,B):- gt(F,E),x_subst(A,C,D),ring_substitutions(B,C),r_subst_3(A,F).
less_toxic(A,B):- r_subst_2(A,F),ring_subst_5(A,E),ring_subst_5(B,E),x_subst(A,D,C).
less_toxic(A,B):- ring_subst_4(A,C),x_subst(B,F,D),gt(F,E),r_subst_3(A,E).
less_toxic(A,B):- ring_subst_6(A,C),ring_subst_5(B,D),r_subst_2(A,F),ring_subst_4(A,E).
less_toxic(A,B):- ring_substitutions(A,F),ring_subst_5(A,D),ring_subst_4(A,E),ring_subst_4(B,C).
less_toxic(A,B):- ring_subst_6(A,C),r_subst_1(B,F),polarisable(D,E),ring_subst_2(B,D).
less_toxic(A,B):- ring_subst_6(B,E),size(E,F),r_subst_1(A,D),ring_subst_4(B,C).
less_toxic(A,B):- n_val(A,C),ring_subst_5(A,D),x_subst(B,E,D),h_acceptor(D,F).
less_toxic(A,B):- ring_substitutions(B,E),ring_subst_3(A,F),polar(D,C),ring_subst_3(A,D).
less_toxic(A,B):- r_subst_2(A,E),ring_subst_4(A,C),ring_subst_6(A,D),ring_subst_5(B,C).
less_toxic(A,B):- ring_subst_6(B,F),ring_subst_2(B,C),r_subst_1(A,D),flex(F,E).
less_toxic(A,B):- r_subst_3(B,D),r_subst_3(A,C),n_val(A,F),r_subst_2(B,E).
less_toxic(A,B):- alk_groups(B,D),ring_subst_6(B,F),gt(D,C),ring_subst_6(A,E).
less_toxic(A,B):- x_subst(A,F,E),ring_subst_4(B,C),x_subst(B,F,C),ring_subst_2(B,D).
less_toxic(A,B):- x_subst(B,E,F),ring_subst_3(B,C),alk_groups(A,E),x_subst(B,D,C).
less_toxic(A,B):- ring_subst_2(A,C),ring_subst_6(B,D),ring_subst_2(B,E),h_acceptor(C,F).
less_toxic(A,B):- alk_groups(A,D),r_subst_1(A,F),ring_subst_2(B,E),ring_subst_3(A,C).
less_toxic(A,B):- ring_subst_6(B,E),n_val(A,F),r_subst_2(A,D),size(E,C).
less_toxic(A,B):- x_subst(A,F,E),ring_subst_6(B,E),pi_acceptor(E,C),r_subst_3(A,D).
less_toxic(A,B):- ring_subst_5(A,C),n_val(B,E),r_subst_2(A,F),ring_subst_2(B,D).
less_toxic(A,B):- r_subst_2(B,F),r_subst_1(B,D),ring_subst_6(A,E),ring_subst_6(B,C).
less_toxic(A,B):- ring_subst_4(A,C),flex(E,F),sigma(E,D),ring_subst_5(B,E).
less_toxic(A,B):- sigma(C,D),x_subst(A,E,C),ring_subst_3(A,C),ring_substitutions(B,E).
less_toxic(A,B):- r_subst_2(A,E),ring_subst_4(B,F),x_subst(B,D,F),alk_groups(A,C).
less_toxic(A,B):- ring_substitutions(A,F),x_subst(B,D,E),n_val(A,D),ring_subst_6(B,C).
less_toxic(A,B):- x_subst(B,C,F),x_subst(B,D,E),x_subst(A,D,F),n_val(B,C).
less_toxic(A,B):- r_subst_2(B,C),ring_subst_3(A,E),sigma(E,F),ring_subst_6(B,D).
less_toxic(A,B):- r_subst_2(A,E),ring_subst_4(A,F),pi_acceptor(D,C),ring_subst_2(B,D).
less_toxic(A,B):- ring_subst_5(B,F),gt(C,E),x_subst(A,C,D),alk_groups(B,C).
less_toxic(A,B):- ring_substitutions(B,F),n_val(A,D),ring_subst_2(A,E),n_val(A,C).
less_toxic(A,B):- h_acceptor(E,F),ring_subst_5(B,E),ring_subst_2(A,D),ring_subst_4(B,C).
less_toxic(A,B):- x_subst(A,D,F),ring_subst_3(A,F),pi_doner(F,C),ring_subst_5(B,E).
less_toxic(A,B):- ring_subst_3(B,E),r_subst_3(B,C),ring_substitutions(A,D),x_subst(B,C,E).
less_toxic(A,B):- size(D,C),ring_subst_2(B,E),x_subst(A,F,D),alk_groups(B,F).
less_toxic(A,B):- alk_groups(B,D),r_subst_1(B,C),r_subst_1(A,C),n_val(B,E).
less_toxic(A,B):- size(C,F),ring_subst_2(B,C),ring_subst_4(A,D),ring_subst_5(A,E).
less_toxic(A,B):- ring_subst_6(B,E),polarisable(F,C),ring_subst_3(A,F),flex(E,D).
less_toxic(A,B):- polar(D,E),r_subst_1(A,F),n_val(A,C),ring_subst_3(B,D).
less_toxic(A,B):- ring_subst_6(B,E),x_subst(A,C,D),r_subst_1(B,F),ring_subst_5(B,E).
less_toxic(A,B):- pi_acceptor(E,C),x_subst(A,D,E),ring_substitutions(B,F),ring_subst_3(B,E).
less_toxic(A,B):- r_subst_3(B,D),h_acceptor(F,C),ring_subst_4(B,F),ring_subst_4(A,E).
less_toxic(A,B):- ring_subst_5(B,F),ring_substitutions(A,D),ring_subst_2(B,E),polar(F,C).
less_toxic(A,B):- pi_doner(E,F),ring_subst_2(A,E),r_subst_1(B,D),ring_substitutions(A,C).
less_toxic(A,B):- polarisable(D,E),ring_subst_4(A,D),r_subst_3(B,C),ring_subst_3(B,D).
less_toxic(A,B):- polar(E,F),ring_subst_5(B,D),ring_subst_2(A,E),pi_acceptor(E,C).
less_toxic(A,B):- ring_subst_6(A,D),ring_subst_6(B,C),x_subst(B,F,C),r_subst_1(B,E).
less_toxic(A,B):- ring_subst_2(A,F),x_subst(A,C,D),ring_subst_3(A,F),ring_subst_5(B,E).
less_toxic(A,B):- r_subst_1(B,C),ring_subst_2(B,D),polarisable(D,E),r_subst_3(A,F).
less_toxic(A,B):- x_subst(B,C,D),x_subst(A,C,E),sigma(D,F),ring_subst_3(A,D).
less_toxic(A,B):- r_subst_2(B,C),h_doner(D,E),ring_subst_2(A,D),ring_subst_2(B,D).
less_toxic(A,B):- h_acceptor(D,F),ring_subst_3(A,E),alk_groups(B,C),ring_subst_3(B,D).
less_toxic(A,B):- ring_subst_5(A,C),ring_subst_6(B,D),h_doner(E,F),ring_subst_4(A,E).
less_toxic(A,B):- ring_subst_5(A,F),ring_subst_3(B,C),ring_subst_6(B,E),polarisable(C,D).
less_toxic(A,B):- ring_subst_6(A,C),x_subst(B,D,E),x_subst(B,D,F),ring_subst_4(B,C).
less_toxic(A,B):- ring_subst_6(A,E),x_subst(B,C,D),ring_subst_6(B,D),alk_groups(A,C).
less_toxic(A,B):- x_subst(B,D,E),ring_subst_3(A,E),ring_substitutions(A,D),r_subst_3(B,C).
less_toxic(A,B):- ring_subst_3(A,E),n_val(B,D),pi_acceptor(E,F),sigma(E,C).
less_toxic(A,B):- ring_substitutions(A,F),h_doner(E,D),ring_subst_2(B,E),ring_subst_6(B,C).
less_toxic(A,B):- alk_groups(B,D),x_subst(A,D,E),r_subst_1(A,F),polar(E,C).
less_toxic(A,B):- x_subst(A,F,E),ring_subst_6(A,D),ring_subst_3(B,C),ring_subst_2(B,E).
less_toxic(A,B):- ring_subst_4(A,D),n_val(A,F),sigma(D,E),ring_subst_5(B,C).
less_toxic(A,B):- ring_subst_6(A,C),ring_subst_5(A,D),ring_subst_2(B,E),n_val(A,F).
less_toxic(A,B):- pi_doner(C,E),ring_subst_3(B,C),ring_subst_3(A,F),polar(C,D).
less_toxic(A,B):- ring_substitutions(B,D),ring_subst_2(B,E),n_val(A,C),alk_groups(A,F).
less_toxic(A,B):- ring_subst_4(B,F),r_subst_1(B,C),x_subst(A,E,F),ring_subst_2(A,D).
less_toxic(A,B):- x_subst(B,D,E),ring_subst_2(A,C),ring_subst_5(A,E),h_acceptor(C,F).
less_toxic(A,B):- alk_groups(A,D),n_val(A,D),size(C,E),ring_subst_6(B,C).
less_toxic(A,B):- ring_subst_5(A,F),pi_acceptor(E,D),ring_subst_2(B,E),x_subst(A,C,E).
less_toxic(A,B):- sigma(D,C),ring_subst_5(B,D),n_val(A,E),ring_subst_2(B,D).
less_toxic(A,B):- ring_substitutions(B,C),ring_subst_6(A,D),polar(D,F),x_subst(A,C,E).
less_toxic(A,B):- ring_subst_3(A,E),n_val(B,D),gt(D,C),ring_subst_6(A,E).
less_toxic(A,B):- ring_subst_2(B,F),ring_subst_3(B,F),x_subst(A,C,E),ring_substitutions(B,D).
less_toxic(A,B):- r_subst_1(B,F),n_val(A,D),n_val(A,C),ring_subst_5(A,E).
less_toxic(A,B):- r_subst_3(B,E),ring_subst_3(A,C),ring_subst_5(A,D),alk_groups(B,F).
less_toxic(A,B):- ring_subst_6(B,F),pi_doner(F,E),polar(F,C),r_subst_2(A,D).
less_toxic(A,B):- x_subst(A,C,F),x_subst(B,D,E),n_val(A,C),n_val(B,C).
less_toxic(A,B):- ring_subst_6(A,C),n_val(A,D),r_subst_3(A,D),ring_subst_5(B,C).
less_toxic(A,B):- x_subst(B,E,C),r_subst_3(B,E),n_val(A,D),h_doner(C,F).
less_toxic(A,B):- ring_subst_5(B,D),ring_subst_5(A,F),x_subst(A,E,C),ring_subst_5(A,D).
