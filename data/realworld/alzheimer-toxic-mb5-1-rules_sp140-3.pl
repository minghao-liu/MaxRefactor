less_toxic(A,B):- ring_subst_6(A,D),x_subst(B,C,D),ring_subst_5(A,D),alk_groups(A,C).
less_toxic(A,B):- ring_subst_2(A,C),r_subst_2(B,D).
less_toxic(A,B):- ring_subst_2(B,C),ring_substitutions(A,E),ring_subst_3(A,F),pi_doner(F,D).
less_toxic(A,B):- x_subst(A,C,D),gt(C,F),gt(F,C),ring_subst_4(B,E).
less_toxic(A,B):- gt(E,F),polarisable(D,C),ring_substitutions(A,E),ring_subst_3(B,D).
less_toxic(A,B):- ring_subst_2(A,C),ring_subst_6(B,C),r_subst_2(B,D),r_subst_1(B,E).
less_toxic(A,B):- x_subst(B,E,F),x_subst(A,E,C),n_val(B,D).
less_toxic(A,B):- ring_subst_3(A,E),great_sigma(F,D),sigma(E,F),ring_subst_6(B,C).
less_toxic(A,B):- alk_groups(B,D),r_subst_1(A,F),ring_substitutions(A,E),ring_subst_3(B,C).
less_toxic(A,B):- ring_subst_6(B,E),flex(E,C),ring_subst_3(A,F),ring_subst_2(A,D).
less_toxic(A,B):- x_subst(B,E,F),flex(F,C),alk_groups(B,D),ring_subst_2(A,F).
less_toxic(A,B):- x_subst(B,C,D),r_subst_3(A,C),x_subst(B,F,E),ring_subst_6(B,D).
less_toxic(A,B):- n_val(B,C),n_val(A,D),alk_groups(B,F),gt(D,E).
less_toxic(A,B):- ring_subst_4(B,E),r_subst_3(A,D),ring_subst_4(A,E),ring_subst_6(B,C).
less_toxic(A,B):- ring_substitutions(B,F),ring_subst_6(A,D),ring_subst_3(B,E),h_doner(D,C).
less_toxic(A,B):- x_subst(A,E,C),ring_subst_4(A,D),x_subst(B,E,D),h_doner(C,F).
less_toxic(A,B):- polarisable(C,F),x_subst(A,E,C),alk_groups(A,E),ring_subst_2(B,D).
less_toxic(A,B):- x_subst(B,D,E),n_val(A,C),x_subst(B,F,E),r_subst_3(A,D).
less_toxic(A,B):- ring_subst_5(A,F),ring_subst_5(A,D),h_doner(D,C),r_subst_1(B,E).
less_toxic(A,B):- ring_subst_5(B,D),ring_subst_3(B,E),ring_subst_3(A,E),sigma(D,C).
less_toxic(A,B):- r_subst_1(A,C),ring_subst_6(A,D),ring_subst_4(B,D),pi_doner(D,E).
less_toxic(A,B):- ring_subst_6(A,E),ring_subst_4(B,C),x_subst(A,D,C),r_subst_3(A,F).
less_toxic(A,B):- ring_subst_4(B,F),ring_substitutions(B,C),x_subst(A,E,F),x_subst(A,E,D).
less_toxic(A,B):- x_subst(A,F,E),x_subst(B,F,D),n_val(B,F),r_subst_3(B,C).
less_toxic(A,B):- n_val(B,C),ring_subst_3(B,E),alk_groups(A,C),ring_subst_2(B,D).
less_toxic(A,B):- h_doner(F,E),ring_subst_5(A,F),ring_subst_2(B,C),ring_subst_4(B,D).
less_toxic(A,B):- x_subst(B,C,F),pi_doner(F,E),ring_subst_2(A,D),ring_subst_2(A,F).
less_toxic(A,B):- ring_subst_6(A,C),ring_subst_2(B,E),ring_subst_6(B,E),ring_substitutions(B,D).
less_toxic(A,B):- alk_groups(B,D),r_subst_2(B,C),r_subst_3(A,E),n_val(A,F).
less_toxic(A,B):- ring_subst_4(B,F),r_subst_2(A,C),ring_subst_5(A,E),pi_doner(F,D).
less_toxic(A,B):- ring_subst_2(B,F),x_subst(B,C,D),ring_subst_4(A,D),x_subst(A,E,F).
less_toxic(A,B):- ring_subst_5(A,C),sigma(C,F),size(D,E),ring_subst_2(B,D).
less_toxic(A,B):- r_subst_3(B,D),ring_subst_3(B,F),x_subst(A,C,E),ring_substitutions(B,D).
less_toxic(A,B):- alk_groups(B,F),x_subst(B,E,C),x_subst(A,D,C),ring_subst_5(B,C).
less_toxic(A,B):- sigma(E,C),ring_subst_3(A,F),ring_subst_4(A,E),ring_subst_2(B,D).
less_toxic(A,B):- ring_subst_2(A,C),size(C,F),polarisable(D,E),ring_subst_2(B,D).
less_toxic(A,B):- x_subst(B,E,F),x_subst(B,C,D),r_subst_3(B,E),ring_subst_3(A,D).
less_toxic(A,B):- x_subst(A,C,F),size(E,D),ring_subst_2(B,E),ring_subst_6(A,E).
less_toxic(A,B):- alk_groups(B,D),r_subst_3(A,D),alk_groups(B,C),n_val(A,E).
less_toxic(A,B):- h_acceptor(D,C),ring_subst_3(A,E),n_val(A,F),ring_subst_6(B,D).
less_toxic(A,B):- ring_subst_5(B,F),ring_substitutions(A,E),polar(F,C),ring_subst_2(B,D).
less_toxic(A,B):- ring_subst_5(B,F),gt(E,C),r_subst_3(A,E),gt(C,D).
less_toxic(A,B):- x_subst(A,C,F),ring_subst_2(B,E),r_subst_2(A,D),n_val(B,C).
less_toxic(A,B):- ring_subst_6(B,D),flex(E,C),n_val(A,F),ring_subst_6(A,E).
less_toxic(A,B):- polar(C,F),ring_subst_5(B,E),ring_subst_2(A,D),ring_subst_6(B,C).
less_toxic(A,B):- ring_subst_3(B,E),n_val(A,C),ring_subst_2(A,D),polarisable(E,F).
less_toxic(A,B):- ring_substitutions(A,F),x_subst(A,E,C),r_subst_3(B,E),gt(F,D).
less_toxic(A,B):- alk_groups(B,D),flex(E,C),ring_subst_2(B,E),ring_substitutions(A,F).
less_toxic(A,B):- x_subst(B,D,E),r_subst_3(A,D),x_subst(B,D,C),ring_substitutions(B,D).
less_toxic(A,B):- ring_substitutions(B,E),r_subst_3(A,D),ring_subst_4(B,C).
less_toxic(A,B):- polarisable(E,C),ring_substitutions(A,D),ring_subst_5(B,E),alk_groups(B,F).
less_toxic(A,B):- alk_groups(A,E),n_val(B,F),x_subst(B,D,C),ring_substitutions(B,D).
less_toxic(A,B):- ring_subst_6(A,C),x_subst(B,D,E),ring_subst_3(B,F),ring_subst_4(B,E).
less_toxic(A,B):- ring_subst_3(B,E),h_acceptor(E,F),h_doner(E,C),ring_subst_3(A,D).
less_toxic(A,B):- r_subst_1(B,F),polar(E,C),ring_subst_3(B,D),ring_subst_4(A,E).
less_toxic(A,B):- ring_subst_2(B,C),h_acceptor(E,D),ring_subst_4(A,E),h_acceptor(C,F).
less_toxic(A,B):- alk_groups(A,D),n_val(B,F),x_subst(B,D,C),r_subst_1(B,E).
less_toxic(A,B):- ring_subst_4(A,D),x_subst(B,E,D),ring_subst_6(B,C),ring_subst_2(B,D).
less_toxic(A,B):- ring_subst_4(A,C),ring_subst_5(A,D),x_subst(B,F,E),ring_subst_2(B,D).
less_toxic(A,B):- x_subst(A,F,E),h_acceptor(E,D),ring_subst_5(B,E),great_h_acc(D,C).
less_toxic(A,B):- x_subst(A,C,D),ring_subst_2(B,E),ring_subst_4(B,E),r_subst_3(B,F).
less_toxic(A,B):- ring_subst_2(A,F),ring_subst_2(B,C),r_subst_3(B,E),x_subst(A,D,C).
less_toxic(A,B):- n_val(A,D),alk_groups(B,C),ring_subst_4(A,E),ring_subst_5(B,E).
less_toxic(A,B):- ring_substitutions(B,C),ring_subst_4(A,D),ring_subst_6(B,E),size(E,F).
less_toxic(A,B):- ring_subst_5(A,F),ring_subst_6(B,C),pi_acceptor(D,E),ring_subst_3(A,D).
less_toxic(A,B):- ring_subst_3(A,E),polar(C,F),x_subst(B,D,C),ring_subst_5(B,C).
less_toxic(A,B):- pi_doner(E,C),size(E,D),ring_subst_5(A,E),alk_groups(B,F).
less_toxic(A,B):- alk_groups(B,D),ring_subst_4(A,C),x_subst(A,F,C),n_val(B,E).
less_toxic(A,B):- flex(F,C),ring_subst_3(A,D),x_subst(A,E,F),ring_subst_2(B,D).
less_toxic(A,B):- pi_doner(E,C),pi_acceptor(E,D),ring_subst_3(A,F),ring_subst_5(B,E).
less_toxic(A,B):- n_val(B,E),flex(D,C),alk_groups(A,E),ring_subst_2(B,D).
less_toxic(A,B):- r_subst_1(A,F),n_val(A,E),ring_subst_6(B,C),ring_substitutions(B,D).
less_toxic(A,B):- ring_substitutions(B,C),gt(E,C),alk_groups(A,E),r_subst_2(A,D).
less_toxic(A,B):- ring_subst_6(B,F),ring_subst_3(A,E),ring_subst_6(A,D),x_subst(B,C,E).
less_toxic(A,B):- pi_doner(C,F),ring_substitutions(A,E),r_subst_3(A,D),x_subst(B,D,C).
less_toxic(A,B):- flex(E,F),ring_subst_2(B,C),flex(C,D),ring_subst_6(A,E).
less_toxic(A,B):- ring_subst_4(A,D),h_doner(E,F),x_subst(B,C,E),alk_groups(A,C).
less_toxic(A,B):- ring_substitutions(A,F),h_doner(C,D),gt(F,E),ring_subst_4(B,C).
less_toxic(A,B):- ring_subst_2(A,E),x_subst(B,D,F),n_val(B,C).
less_toxic(A,B):- x_subst(B,F,D),ring_subst_2(B,C),ring_subst_3(A,E),ring_subst_3(B,D).
less_toxic(A,B):- r_subst_2(B,F),ring_subst_3(A,C),flex(C,D),ring_subst_4(A,E).
less_toxic(A,B):- ring_subst_4(A,D),ring_subst_3(B,C),polarisable(C,E),alk_groups(B,F).
less_toxic(A,B):- r_subst_2(B,C),ring_subst_6(A,D),n_val(A,E),ring_subst_3(A,D).
less_toxic(A,B):- r_subst_3(A,E),r_subst_1(A,D),r_subst_3(B,F),ring_subst_6(B,C).
less_toxic(A,B):- x_subst(B,F,D),gt(E,C),r_subst_3(A,E),alk_groups(B,F).
less_toxic(A,B):- x_subst(A,E,C),x_subst(A,E,F),r_subst_3(A,E),ring_subst_2(B,D).
less_toxic(A,B):- ring_substitutions(B,F),x_subst(A,E,C),r_subst_2(B,D),n_val(A,E).
less_toxic(A,B):- ring_subst_4(B,D),r_subst_1(A,F),ring_subst_2(B,E),h_acceptor(E,C).
less_toxic(A,B):- ring_subst_3(A,E),ring_subst_4(B,E),r_subst_3(B,C),ring_subst_6(B,D).
less_toxic(A,B):- n_val(B,E),ring_subst_2(A,C),n_val(A,D),gt(D,F).
less_toxic(A,B):- ring_subst_4(B,D),ring_subst_6(B,C),ring_subst_2(A,D),r_subst_2(B,E).
less_toxic(A,B):- x_subst(A,C,F),ring_subst_3(A,E),n_val(B,D),gt(D,C).
less_toxic(A,B):- ring_subst_5(A,C),ring_subst_3(A,E),flex(E,D),alk_groups(B,F).
less_toxic(A,B):- ring_subst_6(B,F),ring_subst_6(A,D),ring_subst_3(B,C),size(F,E).
less_toxic(A,B):- ring_subst_4(B,F),sigma(E,D),ring_subst_3(B,C),ring_subst_5(A,E).
less_toxic(A,B):- n_val(B,E),n_val(A,F),h_doner(D,C),ring_subst_2(B,D).
less_toxic(A,B):- ring_subst_4(A,C),h_doner(E,F),ring_subst_4(B,E),polar(C,D).
less_toxic(A,B):- x_subst(B,C,F),r_subst_1(A,D),alk_groups(B,C),x_subst(A,C,E).
less_toxic(A,B):- ring_subst_4(B,F),r_subst_1(B,D),n_val(A,E),polar(F,C).
less_toxic(A,B):- sigma(D,C),ring_subst_3(B,E),ring_subst_2(A,D),ring_subst_4(A,E).
less_toxic(A,B):- x_subst(B,F,C),ring_subst_6(A,E),x_subst(B,D,C),alk_groups(B,F).
less_toxic(A,B):- n_val(A,C),r_subst_3(B,C).
less_toxic(A,B):- ring_subst_2(A,C),size(C,D),ring_subst_2(B,E),h_acceptor(C,F).
less_toxic(A,B):- ring_subst_4(B,F),x_subst(A,D,E),h_acceptor(E,C).
less_toxic(A,B):- x_subst(B,E,F),ring_subst_4(B,F),size(F,C),r_subst_1(A,D).
less_toxic(A,B):- x_subst(B,D,C),ring_subst_6(B,E),x_subst(A,D,C),polarisable(E,F).
less_toxic(A,B):- r_subst_3(A,C),x_subst(B,F,E),gt(F,D),r_subst_3(B,F).
less_toxic(A,B):- ring_subst_6(A,C),h_doner(C,D),r_subst_3(B,F),ring_subst_4(A,E).
less_toxic(A,B):- ring_subst_6(A,F),ring_subst_5(A,E),r_subst_3(B,C),ring_subst_3(B,D).
less_toxic(A,B):- pi_acceptor(C,F),ring_substitutions(B,E),alk_groups(A,E),x_subst(B,D,C).
less_toxic(A,B):- ring_subst_2(B,F),pi_doner(F,E),x_subst(A,D,F),ring_subst_4(B,C).
less_toxic(A,B):- r_subst_1(A,E),ring_subst_2(A,C),ring_subst_2(B,C),h_acceptor(C,D).
less_toxic(A,B):- r_subst_3(B,C),ring_subst_4(A,D),ring_subst_2(B,E),alk_groups(B,C).
less_toxic(A,B):- x_subst(A,D,E),r_subst_3(A,C),ring_subst_5(A,F),x_subst(B,D,F).
less_toxic(A,B):- x_subst(A,F,E),ring_subst_4(A,C),polar(E,D),ring_subst_2(B,E).
less_toxic(A,B):- ring_subst_2(A,F),ring_subst_5(B,D),ring_subst_4(A,E),sigma(E,C).
less_toxic(A,B):- ring_subst_6(B,D),ring_subst_3(A,C),n_val(A,F),h_acceptor(C,E).
less_toxic(A,B):- ring_subst_2(B,C),x_subst(B,E,C),ring_subst_2(A,D),n_val(A,E).
less_toxic(A,B):- ring_subst_5(A,C),ring_subst_5(A,F),ring_subst_4(B,D),n_val(B,E).
less_toxic(A,B):- ring_subst_6(A,C),gt(E,F),r_subst_3(B,E),x_subst(B,E,D).
less_toxic(A,B):- ring_substitutions(B,E),r_subst_1(A,D),ring_subst_4(B,C).
less_toxic(A,B):- gt(C,E),x_subst(B,C,D),ring_subst_2(A,D),r_subst_3(B,F).
less_toxic(A,B):- ring_subst_6(A,C),x_subst(A,F,C),ring_subst_2(B,E),r_subst_3(A,D).
less_toxic(A,B):- gt(F,E),ring_substitutions(B,F),x_subst(A,C,D),ring_subst_2(A,D).
less_toxic(A,B):- gt(C,F),ring_subst_6(A,D),ring_subst_4(B,E),alk_groups(B,C).
less_toxic(A,B):- n_val(A,E),x_subst(A,E,D),ring_subst_5(B,C).
less_toxic(A,B):- ring_subst_3(B,E),ring_subst_5(A,F),ring_subst_2(B,E),x_subst(A,D,C).
less_toxic(A,B):- r_subst_3(B,D),pi_doner(E,C),ring_subst_3(A,E),h_doner(E,F).
less_toxic(A,B):- flex(E,F),ring_subst_3(A,E),n_val(B,D),x_subst(B,C,E).
less_toxic(A,B):- ring_subst_5(A,D),n_val(A,F),x_subst(B,C,E),ring_subst_4(A,E).
less_toxic(A,B):- ring_subst_6(A,C),ring_subst_2(B,C),size(C,D),ring_subst_4(B,E).
less_toxic(A,B):- gt(C,F),x_subst(B,C,D),h_acceptor(D,E),n_val(A,C).
less_toxic(A,B):- ring_substitutions(A,D),gt(D,C),x_subst(A,C,E),ring_substitutions(B,D).
less_toxic(A,B):- ring_subst_4(A,F),r_subst_3(B,C),ring_subst_5(A,E),ring_subst_2(B,D).
less_toxic(A,B):- ring_subst_4(B,F),ring_substitutions(A,D),sigma(F,E),alk_groups(A,C).
less_toxic(A,B):- h_doner(E,F),ring_subst_6(B,E),polar(D,C),ring_subst_3(A,D).
less_toxic(A,B):- r_subst_2(B,C),pi_acceptor(E,F),ring_subst_4(A,E),ring_subst_3(A,D).
less_toxic(A,B):- x_subst(B,E,C),n_val(A,F),gt(E,D),ring_subst_6(B,C).
less_toxic(A,B):- alk_groups(B,D),alk_groups(B,E),alk_groups(A,E),gt(D,C).
less_toxic(A,B):- ring_subst_4(A,C),ring_subst_2(B,D),flex(D,F),r_subst_1(B,E).
