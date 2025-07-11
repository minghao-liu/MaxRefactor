less_toxic(A,B):- x_subst(A,D,E),polar(E,F),r_subst_3(A,D),r_subst_2(B,C).
less_toxic(A,B):- r_subst_3(B,D),ring_subst_3(B,E),r_subst_3(A,C),ring_subst_6(B,F).
less_toxic(A,B):- pi_acceptor(D,E),flex(C,F),ring_subst_3(A,C),ring_subst_2(B,D).
less_toxic(A,B):- ring_subst_4(A,D),ring_subst_5(B,C),alk_groups(B,E),ring_subst_2(B,D).
less_toxic(A,B):- ring_substitutions(A,F),x_subst(A,D,E),ring_subst_6(B,E),n_val(B,C).
less_toxic(A,B):- alk_groups(B,D),x_subst(B,D,E),x_subst(A,F,C),gt(F,D).
less_toxic(A,B):- ring_substitutions(B,E),r_subst_3(A,C),r_subst_2(B,D),n_val(A,E).
less_toxic(A,B):- ring_subst_5(A,F),ring_subst_6(A,D),ring_subst_3(A,C),ring_subst_6(B,E).
less_toxic(A,B):- polar(E,F),ring_subst_6(A,D),ring_subst_4(B,E),ring_subst_4(B,C).
less_toxic(A,B):- r_subst_2(B,F),n_val(A,D),x_subst(A,C,E),ring_subst_5(A,E).
less_toxic(A,B):- r_subst_1(B,C),n_val(B,D),n_val(B,F),ring_subst_6(A,E).
less_toxic(A,B):- ring_subst_5(A,C),ring_subst_2(B,E),r_subst_3(B,F),ring_substitutions(B,D).
less_toxic(A,B):- x_subst(B,E,C),ring_substitutions(A,D),n_val(A,E).
less_toxic(A,B):- ring_subst_5(A,C),ring_subst_5(B,E),r_subst_3(B,F),ring_substitutions(B,D).
less_toxic(A,B):- x_subst(B,E,F),r_subst_3(A,C),x_subst(A,D,F),r_subst_3(A,E).
less_toxic(A,B):- ring_substitutions(B,E),ring_subst_2(B,F),r_subst_3(A,E),x_subst(B,D,C).
less_toxic(A,B):- alk_groups(A,D),n_val(A,D),flex(E,C),x_subst(B,F,E).
less_toxic(A,B):- ring_subst_4(A,E),x_subst(B,F,E),x_subst(B,D,C),alk_groups(A,F).
less_toxic(A,B):- ring_subst_4(B,F),x_subst(B,C,D),polar(F,E),ring_subst_2(A,D).
less_toxic(A,B):- ring_subst_6(A,F),r_subst_3(A,D),ring_subst_4(B,E),x_subst(A,C,E).
less_toxic(A,B):- ring_subst_2(A,F),x_subst(A,D,E),x_subst(B,D,F),h_acceptor(F,C).
less_toxic(A,B):- r_subst_3(B,D),pi_acceptor(C,E),r_subst_3(A,D),ring_subst_5(A,C).
less_toxic(A,B):- ring_subst_2(B,C),x_subst(A,E,C),r_subst_1(A,F),pi_acceptor(C,D).
less_toxic(A,B):- ring_subst_2(B,C),ring_subst_6(A,D),h_acceptor(C,E),alk_groups(B,F).
less_toxic(A,B):- ring_subst_5(B,F),ring_subst_6(A,D),ring_substitutions(A,E),alk_groups(A,C).
less_toxic(A,B):- x_subst(B,D,E),ring_subst_4(B,E),alk_groups(A,C),r_subst_3(B,F).
less_toxic(A,B):- ring_subst_2(A,C),ring_subst_6(B,D),ring_subst_4(A,E),ring_subst_5(B,C).
less_toxic(A,B):- ring_subst_5(A,C),ring_subst_3(B,C),x_subst(A,D,C),ring_subst_5(B,C).
less_toxic(A,B):- ring_subst_2(A,C),pi_acceptor(D,F),x_subst(A,E,D),ring_subst_2(B,D).
less_toxic(A,B):- ring_subst_5(A,D),r_subst_3(A,E),alk_groups(B,C),n_val(A,C).
less_toxic(A,B):- ring_subst_4(A,F),x_subst(B,C,D),r_subst_3(A,E),ring_subst_2(B,D).
less_toxic(A,B):- n_val(A,D),r_subst_3(A,D),alk_groups(A,C),ring_subst_5(B,E).
less_toxic(A,B):- r_subst_1(A,E),ring_subst_5(B,D),alk_groups(B,F),ring_subst_5(B,C).
less_toxic(A,B):- x_subst(B,C,F),gt(E,C),n_val(A,D),x_subst(B,E,F).
less_toxic(A,B):- pi_doner(E,D),ring_subst_4(B,E),polar(F,C),ring_subst_3(A,F).
less_toxic(A,B):- pi_doner(D,F),ring_substitutions(B,C),ring_subst_2(B,E),ring_subst_2(A,D).
less_toxic(A,B):- r_subst_1(B,C),polarisable(F,D),ring_subst_2(B,F),r_subst_3(A,E).
less_toxic(A,B):- size(D,F),x_subst(A,C,D),n_val(A,C),r_subst_1(B,E).
less_toxic(A,B):- ring_subst_5(B,F),ring_subst_2(A,C),ring_subst_5(A,F),x_subst(A,E,D).
less_toxic(A,B):- x_subst(A,D,E),polar(E,C),ring_subst_5(B,E).
less_toxic(A,B):- r_subst_3(B,D),ring_subst_6(A,E),flex(C,F),x_subst(A,D,C).
less_toxic(A,B):- ring_subst_5(B,F),r_subst_1(B,C),polarisable(E,D),ring_subst_6(A,E).
less_toxic(A,B):- ring_subst_2(B,C),x_subst(A,F,C),alk_groups(A,E),h_acceptor(C,D).
less_toxic(A,B):- x_subst(A,F,E),ring_substitutions(A,D),ring_subst_4(B,C),r_subst_3(A,F).
less_toxic(A,B):- alk_groups(B,D),r_subst_1(A,E),x_subst(A,F,C),ring_subst_5(A,C).
less_toxic(A,B):- x_subst(A,C,D),alk_groups(B,E),n_val(B,C),r_subst_3(A,F).
less_toxic(A,B):- ring_subst_5(B,F),ring_subst_2(A,C),size(E,D),ring_subst_4(A,E).
less_toxic(A,B):- r_subst_3(A,C),r_subst_3(A,E),x_subst(B,E,D),ring_subst_3(A,D).
less_toxic(A,B):- ring_subst_3(B,E),size(F,C),ring_subst_4(A,F),ring_subst_2(B,D).
less_toxic(A,B):- ring_subst_5(B,F),ring_subst_6(A,D),pi_doner(D,E),sigma(F,C).
less_toxic(A,B):- n_val(B,C),ring_subst_4(A,D),x_subst(B,C,E),ring_subst_4(A,E).
less_toxic(A,B):- ring_subst_5(B,F),ring_subst_6(A,D),pi_acceptor(D,E),h_doner(D,C).
less_toxic(A,B):- ring_subst_6(A,E),ring_subst_6(A,D),ring_subst_3(B,C),ring_subst_3(B,D).
less_toxic(A,B):- x_subst(B,C,F),r_subst_1(A,E),h_doner(F,D),ring_subst_4(B,F).
less_toxic(A,B):- ring_subst_6(A,C),ring_subst_3(B,E),n_val(A,F),polar(C,D).
less_toxic(A,B):- x_subst(B,D,E),ring_substitutions(B,F),n_val(B,D),x_subst(A,D,C).
less_toxic(A,B):- h_doner(F,E),ring_subst_4(A,F),ring_subst_5(B,D),r_subst_3(B,C).
less_toxic(A,B):- ring_substitutions(A,F),alk_groups(B,E),r_subst_1(A,D),ring_subst_6(B,C).
less_toxic(A,B):- x_subst(A,C,D),alk_groups(A,E),r_subst_3(B,C).
less_toxic(A,B):- alk_groups(B,D),r_subst_3(A,E),n_val(B,F),x_subst(B,F,C).
less_toxic(A,B):- x_subst(B,C,D),ring_subst_4(A,D),x_subst(B,F,E),gt(F,C).
less_toxic(A,B):- alk_groups(B,D),ring_subst_6(A,C),sigma(F,E),ring_subst_3(A,F).
less_toxic(A,B):- ring_subst_5(A,F),n_val(B,D),alk_groups(A,E),n_val(B,C).
less_toxic(A,B):- ring_subst_2(A,C),r_subst_3(A,D),x_subst(A,D,C),ring_subst_6(B,C).
less_toxic(A,B):- ring_substitutions(B,F),ring_subst_3(A,C),ring_subst_2(B,E),polar(C,D).
less_toxic(A,B):- ring_subst_4(A,C),ring_subst_4(B,E),h_acceptor(D,F),ring_subst_2(B,D).
less_toxic(A,B):- ring_subst_4(B,F),sigma(F,D),size(F,C),ring_subst_6(A,E).
less_toxic(A,B):- flex(C,E),r_subst_1(A,F),pi_acceptor(C,D),ring_subst_6(B,C).
less_toxic(A,B):- x_subst(B,C,F),h_acceptor(F,D),n_val(A,C),r_subst_1(B,E).
less_toxic(A,B):- alk_groups(A,D),ring_subst_2(B,F),ring_subst_2(B,E),r_subst_3(B,C).
less_toxic(A,B):- x_subst(A,E,F),r_subst_3(A,E),polar(D,C),ring_subst_2(B,D).
less_toxic(A,B):- x_subst(A,E,C),alk_groups(B,E),gt(E,D),ring_substitutions(B,D).
less_toxic(A,B):- ring_subst_5(B,D),n_val(A,C),ring_subst_6(B,D),ring_subst_3(A,D).
less_toxic(A,B):- ring_subst_4(A,F),ring_subst_3(A,E),polarisable(F,D),n_val(B,C).
less_toxic(A,B):- n_val(B,E),ring_subst_4(B,D),n_val(A,C),r_subst_3(A,F).
less_toxic(A,B):- x_subst(A,F,E),x_subst(A,D,E),ring_subst_2(B,C),ring_subst_2(A,C).
less_toxic(A,B):- x_subst(B,D,E),ring_subst_2(B,C),ring_subst_2(A,E),ring_subst_6(A,F).
less_toxic(A,B):- ring_subst_3(A,E),x_subst(B,D,F),ring_subst_5(B,E),alk_groups(A,C).
less_toxic(A,B):- r_subst_3(A,C),ring_subst_3(B,F),ring_substitutions(B,E),h_doner(F,D).
less_toxic(A,B):- n_val(B,E),ring_subst_5(A,F),r_subst_3(A,C),x_subst(B,E,D).
less_toxic(A,B):- r_subst_3(B,D),alk_groups(A,D),n_val(A,C),r_subst_1(B,E).
less_toxic(A,B):- h_doner(D,E),ring_subst_2(B,C),ring_subst_4(A,D),ring_subst_6(B,C).
less_toxic(A,B):- x_subst(B,C,F),pi_acceptor(F,E),ring_subst_3(A,D).
less_toxic(A,B):- x_subst(B,C,F),ring_subst_5(A,F),gt(E,C),x_subst(A,E,D).
less_toxic(A,B):- r_subst_2(A,E),r_subst_1(A,C),ring_subst_6(A,D),r_subst_2(B,F).
less_toxic(A,B):- ring_subst_2(B,C),x_subst(A,E,D),sigma(D,F),sigma(C,F).
less_toxic(A,B):- x_subst(B,D,E),gt(D,F),size(E,C),ring_subst_6(A,E).
less_toxic(A,B):- gt(E,C),r_subst_3(B,E),ring_subst_5(A,D).
less_toxic(A,B):- ring_substitutions(B,F),r_subst_3(A,C),ring_subst_4(A,D),polar(D,E).
less_toxic(A,B):- ring_subst_6(A,D),r_subst_3(B,E),polar(F,C),ring_subst_3(A,F).
less_toxic(A,B):- ring_subst_5(B,D),gt(E,C),polar(D,F),n_val(A,E).
less_toxic(A,B):- n_val(B,E),ring_subst_6(B,D),n_val(A,F),ring_subst_6(B,C).
less_toxic(A,B):- x_subst(B,F,D),ring_subst_4(A,D),x_subst(B,C,E),r_subst_3(B,F).
less_toxic(A,B):- r_subst_1(B,F),r_subst_3(A,C),ring_subst_5(B,E),ring_subst_2(B,D).
less_toxic(A,B):- r_subst_2(B,C),ring_subst_6(A,D),pi_acceptor(D,E).
less_toxic(A,B):- alk_groups(B,D),r_subst_1(A,F),ring_subst_6(B,C),r_subst_1(B,E).
less_toxic(A,B):- x_subst(B,C,D),r_subst_2(A,F),alk_groups(A,E),ring_substitutions(B,C).
less_toxic(A,B):- ring_substitutions(A,F),x_subst(B,C,D),r_subst_3(A,C),pi_doner(D,E).
less_toxic(A,B):- ring_subst_5(A,C),ring_subst_6(B,C),size(C,D),r_subst_1(B,E).
less_toxic(A,B):- r_subst_2(A,E),r_subst_3(B,C),alk_groups(B,F),ring_subst_3(A,D).
less_toxic(A,B):- ring_subst_4(B,F),r_subst_2(B,C),ring_subst_5(A,D),h_acceptor(F,E).
less_toxic(A,B):- ring_subst_4(A,C),ring_subst_2(B,C),ring_subst_4(A,D),pi_doner(D,E).
less_toxic(A,B):- ring_subst_2(A,C),x_subst(A,E,C),x_subst(B,D,F),gt(E,D).
less_toxic(A,B):- ring_substitutions(A,F),ring_subst_4(A,C),x_subst(B,E,D),alk_groups(B,F).
less_toxic(A,B):- ring_substitutions(B,F),ring_subst_3(B,C),n_val(B,D),ring_subst_4(A,E).
less_toxic(A,B):- alk_groups(B,D),ring_subst_2(A,C),gt(F,E),r_subst_3(B,F).
less_toxic(A,B):- ring_subst_3(A,D),r_subst_3(B,C),sigma(D,F),r_subst_1(B,E).
less_toxic(A,B):- polar(E,D),r_subst_1(B,C),ring_subst_2(A,E),polarisable(E,F).
less_toxic(A,B):- alk_groups(A,D),n_val(B,F),ring_subst_2(B,E),ring_subst_2(A,C).
less_toxic(A,B):- ring_subst_4(B,F),ring_subst_2(A,C),ring_subst_3(A,E),polarisable(E,D).
less_toxic(A,B):- ring_subst_3(A,E),flex(E,C),n_val(A,F),ring_subst_6(B,D).
less_toxic(A,B):- ring_subst_4(B,F),alk_groups(A,D),size(F,C),n_val(A,E).
less_toxic(A,B):- ring_subst_5(A,F),flex(F,C),ring_subst_2(A,E),r_subst_2(B,D).
less_toxic(A,B):- alk_groups(B,D),ring_subst_6(B,E),x_subst(A,D,C),alk_groups(A,F).
less_toxic(A,B):- n_val(B,D),alk_groups(B,E),gt(D,C),ring_subst_3(A,F).
less_toxic(A,B):- ring_subst_4(A,D),x_subst(A,C,D),ring_substitutions(A,E),alk_groups(B,C).
less_toxic(A,B):- ring_subst_6(A,C),x_subst(A,D,E),sigma(C,F),ring_subst_4(B,C).
less_toxic(A,B):- sigma(E,F),x_subst(A,C,D),ring_subst_4(B,E),ring_subst_3(A,D).
less_toxic(A,B):- ring_subst_2(B,C),ring_subst_3(A,C),pi_doner(E,D),ring_subst_4(A,E).
less_toxic(A,B):- ring_subst_5(A,F),r_subst_3(B,C),x_subst(A,E,D),n_val(A,E).
less_toxic(A,B):- gt(E,F),ring_subst_5(A,D),x_subst(A,E,D),x_subst(B,F,C).
less_toxic(A,B):- ring_subst_2(A,F),x_subst(B,C,D),h_acceptor(D,E).
less_toxic(A,B):- ring_substitutions(A,D),n_val(A,D),r_subst_2(A,F),x_subst(B,C,E).
less_toxic(A,B):- x_subst(B,E,F),n_val(B,D),ring_subst_6(A,C).
less_toxic(A,B):- n_val(B,E),r_subst_1(A,F),ring_subst_3(B,D),ring_subst_6(B,C).
less_toxic(A,B):- ring_subst_2(A,C),x_subst(A,E,C),ring_subst_3(B,C),n_val(B,D).
less_toxic(A,B):- ring_subst_6(B,F),polarisable(E,D),polarisable(F,C),ring_subst_4(A,E).
less_toxic(A,B):- ring_subst_6(A,C),ring_subst_5(B,D),h_doner(C,F),ring_subst_4(A,E).
less_toxic(A,B):- ring_subst_2(A,F),ring_subst_2(B,C),ring_subst_5(A,E),ring_subst_2(B,D).
less_toxic(A,B):- ring_subst_2(A,C),ring_subst_6(A,D),ring_subst_6(A,F),r_subst_2(B,E).
less_toxic(A,B):- ring_subst_3(B,E),ring_subst_2(B,C),flex(C,D),ring_subst_5(A,E).
less_toxic(A,B):- ring_subst_4(A,F),size(D,C),alk_groups(B,E),ring_subst_2(B,D).
less_toxic(A,B):- r_subst_3(B,D),x_subst(A,D,E),r_subst_3(B,C),polarisable(E,F).
less_toxic(A,B):- ring_substitutions(B,F),n_val(A,C),x_subst(A,E,D),alk_groups(A,F).
less_toxic(A,B):- x_subst(B,D,E),r_subst_2(A,F),polarisable(E,C),ring_subst_4(A,E).
less_toxic(A,B):- ring_subst_4(B,F),ring_subst_4(B,C),x_subst(A,D,F),alk_groups(A,E).
less_toxic(A,B):- ring_subst_4(A,C),ring_subst_5(B,D),r_subst_3(B,F),r_subst_1(B,E).
less_toxic(A,B):- ring_subst_2(B,F),h_doner(F,C),x_subst(A,E,F),ring_subst_2(B,D).
less_toxic(A,B):- ring_subst_4(A,F),x_subst(A,E,C),alk_groups(B,E),sigma(C,D).
less_toxic(A,B):- pi_acceptor(D,C),h_acceptor(D,E),r_subst_1(A,F),ring_subst_2(B,D).
less_toxic(A,B):- r_subst_2(B,C),polarisable(F,D),ring_subst_3(A,F),ring_subst_5(A,E).
less_toxic(A,B):- polar(E,C),ring_subst_2(A,D),r_subst_3(B,F),ring_subst_5(B,E).
less_toxic(A,B):- x_subst(A,F,E),x_subst(A,D,E),ring_subst_5(A,C),ring_subst_4(B,C).
less_toxic(A,B):- x_subst(A,F,E),ring_substitutions(B,F),ring_subst_2(A,D),pi_acceptor(D,C).
less_toxic(A,B):- ring_subst_4(A,C),ring_subst_2(A,C),ring_subst_2(B,E),r_subst_2(A,D).
less_toxic(A,B):- x_subst(A,C,D),ring_subst_4(A,D),ring_subst_5(B,E),n_val(B,C).
less_toxic(A,B):- x_subst(B,C,F),x_subst(A,D,E),gt(C,D),r_subst_3(B,D).
less_toxic(A,B):- ring_subst_6(B,F),pi_doner(F,E),size(F,C),r_subst_3(A,D).
less_toxic(A,B):- r_subst_2(B,C),n_val(A,D),x_subst(B,F,E),ring_substitutions(B,D).
less_toxic(A,B):- ring_subst_5(A,F),ring_subst_6(A,D),h_doner(F,C),r_subst_2(B,E).
