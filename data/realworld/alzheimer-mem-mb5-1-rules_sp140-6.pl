great_rsd(A,B):- ring_subst_2(B,D),ring_subst_2(A,D),x_subst(B,C,F),ring_subst_5(A,E).
great_rsd(A,B):- alk_groups(A,E),x_subst(A,D,C),n_val(B,E),x_subst(B,E,C).
great_rsd(A,B):- ring_subst_3(B,E),x_subst(B,F,C),r_subst_2(A,D),ring_subst_2(B,C).
great_rsd(A,B):- alk_groups(B,F),size(D,C),r_subst_3(A,E),ring_subst_5(A,D).
great_rsd(A,B):- ring_subst_3(B,E),x_subst(B,C,E),x_subst(A,D,E),r_subst_3(A,F).
great_rsd(A,B):- n_val(B,F),r_subst_1(A,C),ring_subst_4(A,E),x_subst(A,F,D).
great_rsd(A,B):- h_acceptor(F,E),h_doner(F,D),r_subst_3(B,C),ring_subst_5(A,F).
great_rsd(A,B):- x_subst(A,C,F),alk_groups(A,D),n_val(B,E).
great_rsd(A,B):- polar(E,D),x_subst(B,C,F),ring_subst_4(A,E),polar(F,D).
great_rsd(A,B):- ring_subst_5(A,C),n_val(A,D),x_subst(A,E,F),alk_groups(B,E).
great_rsd(A,B):- ring_subst_6(A,F),r_subst_1(A,D),h_doner(C,E),ring_subst_3(B,C).
great_rsd(A,B):- r_subst_3(A,D),x_subst(B,D,C),alk_groups(A,F),ring_subst_2(B,E).
great_rsd(A,B):- ring_subst_4(B,C),ring_subst_6(A,D),ring_subst_3(A,E),ring_subst_2(B,C).
great_rsd(A,B):- polarisable(E,C),r_subst_3(A,D),ring_subst_5(B,E),ring_subst_2(B,E).
great_rsd(A,B):- n_val(A,D),gt(D,C),x_subst(B,C,E),ring_substitutions(A,C).
great_rsd(A,B):- pi_doner(C,E),ring_subst_2(B,F),sigma(C,D),ring_subst_6(A,C).
great_rsd(A,B):- r_subst_2(A,C),ring_subst_2(B,F),sigma(F,D),size(F,E).
great_rsd(A,B):- n_val(B,F),x_subst(A,C,E),r_subst_3(A,C),gt(F,D).
great_rsd(A,B):- n_val(A,C),n_val(B,D),gt(C,E),ring_substitutions(A,C).
great_rsd(A,B):- ring_subst_3(A,C),ring_subst_2(A,D),ring_subst_2(A,E),ring_subst_3(B,C).
great_rsd(A,B):- r_subst_1(B,D),x_subst(A,C,E),ring_subst_3(A,E),ring_subst_4(B,E).
great_rsd(A,B):- h_acceptor(C,E),r_subst_3(A,D),ring_subst_4(A,C),alk_groups(B,D).
great_rsd(A,B):- ring_substitutions(A,D),x_subst(A,D,C),x_subst(B,F,C),size(C,E).
great_rsd(A,B):- ring_substitutions(B,C),ring_subst_2(B,D),r_subst_3(A,E),x_subst(A,C,D).
great_rsd(A,B):- ring_subst_4(A,D),x_subst(A,E,D),ring_substitutions(B,E),x_subst(A,E,C).
great_rsd(A,B):- ring_subst_5(B,F),x_subst(A,C,F),r_subst_1(A,E),alk_groups(B,D).
great_rsd(A,B):- size(F,D),ring_subst_6(A,F),ring_subst_2(B,E),flex(F,C).
great_rsd(A,B):- h_doner(F,C),flex(F,D),ring_subst_2(B,F),ring_subst_2(A,E).
great_rsd(A,B):- x_subst(B,D,F),ring_subst_2(A,C),x_subst(A,D,C),polarisable(C,E).
great_rsd(A,B):- ring_subst_2(B,E),ring_subst_6(B,C),x_subst(A,F,D),ring_subst_5(B,D).
great_rsd(A,B):- ring_subst_4(A,D),gt(F,E),r_subst_2(B,C),n_val(B,F).
great_rsd(A,B):- ring_subst_5(B,E),n_val(A,D),flex(E,F),pi_acceptor(E,C).
great_rsd(A,B):- h_acceptor(F,D),ring_subst_6(B,C),x_subst(A,E,F),ring_subst_4(B,F).
great_rsd(A,B):- n_val(A,C),pi_acceptor(D,E),ring_subst_2(B,D),ring_subst_5(A,D).
great_rsd(A,B):- gt(F,E),ring_subst_3(A,D),ring_subst_4(B,C),x_subst(B,F,D).
great_rsd(A,B):- x_subst(A,F,E),ring_subst_2(B,D),ring_subst_4(B,C),ring_subst_4(A,D).
great_rsd(A,B):- r_subst_1(B,D),alk_groups(A,F),ring_subst_6(A,C),ring_subst_3(A,E).
great_rsd(A,B):- ring_subst_5(A,E),n_val(A,D),ring_subst_4(B,F),pi_acceptor(E,C).
great_rsd(A,B):- ring_substitutions(A,E),ring_subst_2(B,D),r_subst_3(B,C),r_subst_3(A,C).
great_rsd(A,B):- ring_subst_4(B,D),r_subst_3(A,E),x_subst(A,E,F),x_subst(A,C,D).
great_rsd(A,B):- ring_subst_4(A,D),r_subst_1(A,C),ring_subst_4(A,E),n_val(B,F).
great_rsd(A,B):- r_subst_3(B,F),flex(D,E),x_subst(A,C,D),r_subst_3(A,F).
great_rsd(A,B):- ring_substitutions(A,E),sigma(C,F),sigma(C,D),ring_subst_3(B,C).
great_rsd(A,B):- x_subst(B,C,D),ring_substitutions(A,F),x_subst(B,C,E),x_subst(A,C,D).
great_rsd(A,B):- ring_subst_2(A,C),h_doner(E,F),ring_subst_3(B,E),ring_subst_6(A,D).
great_rsd(A,B):- ring_subst_6(A,C),sigma(C,D),x_subst(B,E,C),r_subst_2(B,F).
great_rsd(A,B):- x_subst(A,C,E),r_subst_3(A,D),ring_subst_2(B,E),r_subst_2(B,F).
great_rsd(A,B):- ring_subst_4(B,D),ring_subst_5(B,E),x_subst(A,C,F),ring_subst_4(A,E).
great_rsd(A,B):- x_subst(B,E,D),ring_subst_4(B,F),ring_subst_5(A,F),n_val(B,C).
great_rsd(A,B):- ring_subst_2(A,D),ring_subst_6(A,C),ring_subst_6(B,D),ring_subst_6(A,D).
great_rsd(A,B):- x_subst(B,D,E),alk_groups(B,D),x_subst(A,D,E),pi_doner(E,C).
great_rsd(A,B):- n_val(A,C),x_subst(B,E,D),gt(E,F),x_subst(B,F,D).
great_rsd(A,B):- x_subst(B,E,D),n_val(A,E),x_subst(A,C,D),r_subst_1(B,F).
great_rsd(A,B):- ring_subst_6(B,E),r_subst_1(A,C),ring_subst_5(B,F),h_acceptor(E,D).
great_rsd(A,B):- h_doner(F,C),ring_subst_4(B,F),ring_subst_4(A,E),pi_doner(F,D).
great_rsd(A,B):- ring_substitutions(B,C),ring_subst_6(B,E),pi_doner(E,F),r_subst_1(A,D).
great_rsd(A,B):- alk_groups(B,C),ring_substitutions(B,E),gt(E,D),r_subst_3(A,D).
great_rsd(A,B):- ring_subst_3(B,D),polarisable(D,F),ring_subst_2(A,E),ring_subst_2(B,C).
great_rsd(A,B):- sigma(F,D),ring_subst_3(A,F),sigma(E,C),ring_subst_3(B,E).
great_rsd(A,B):- size(D,C),ring_subst_3(B,E),ring_subst_3(A,E),ring_subst_5(A,D).
great_rsd(A,B):- n_val(B,E),ring_subst_4(A,C),ring_subst_5(A,F),polarisable(F,D).
great_rsd(A,B):- polar(E,C),ring_subst_3(A,E),r_subst_2(A,D),r_subst_3(B,F).
great_rsd(A,B):- ring_substitutions(A,D),alk_groups(A,C),ring_subst_6(B,F),ring_subst_2(B,E).
great_rsd(A,B):- ring_subst_4(A,D),r_subst_3(B,E),r_subst_3(B,C),r_subst_2(B,F).
great_rsd(A,B):- ring_subst_4(A,D),ring_subst_5(B,E),h_doner(D,C),size(E,F).
great_rsd(A,B):- x_subst(B,C,E),ring_subst_4(B,F),x_subst(A,D,E),n_val(B,C).
great_rsd(A,B):- ring_subst_3(A,E),alk_groups(B,D),x_subst(B,C,E),ring_subst_2(A,E).
great_rsd(A,B):- n_val(A,C),ring_substitutions(A,E),gt(C,D),alk_groups(B,E).
great_rsd(A,B):- pi_acceptor(D,F),ring_subst_2(B,D),r_subst_1(A,E),r_subst_1(B,C).
great_rsd(A,B):- alk_groups(A,E),n_val(B,D),r_subst_3(B,D),ring_subst_2(B,C).
great_rsd(A,B):- ring_subst_2(A,C),ring_subst_3(B,E),size(E,F),polarisable(E,D).
great_rsd(A,B):- ring_subst_3(B,E),r_subst_3(B,C),x_subst(A,C,D),r_subst_1(A,F).
great_rsd(A,B):- flex(D,E),ring_subst_2(B,F),ring_subst_4(B,C),ring_subst_5(A,D).
great_rsd(A,B):- ring_subst_3(B,F),x_subst(A,C,E),alk_groups(A,C),ring_substitutions(B,D).
great_rsd(A,B):- sigma(F,E),x_subst(A,C,F),ring_substitutions(B,D),r_subst_3(A,C).
great_rsd(A,B):- gt(D,E),alk_groups(A,D),n_val(A,E),ring_subst_3(B,C).
great_rsd(A,B):- pi_doner(D,C),r_subst_1(A,F),ring_subst_6(A,D),alk_groups(B,E).
great_rsd(A,B):- x_subst(B,F,E),x_subst(A,F,C),ring_subst_4(A,E),polar(C,D).
great_rsd(A,B):- h_acceptor(F,C),ring_subst_2(B,D),polar(D,E),ring_subst_6(A,F).
great_rsd(A,B):- polarisable(E,C),h_acceptor(E,F),ring_subst_4(A,E),ring_subst_5(B,D).
great_rsd(A,B):- r_subst_2(B,D),h_acceptor(C,E),alk_groups(B,F),ring_subst_4(A,C).
great_rsd(A,B):- sigma(E,F),ring_subst_4(B,C),alk_groups(A,D),ring_subst_3(A,E).
great_rsd(A,B):- alk_groups(A,E),ring_subst_4(A,D),ring_subst_4(B,F),ring_subst_3(A,C).
great_rsd(A,B):- pi_acceptor(F,C),ring_subst_4(B,F),ring_subst_3(A,E),polarisable(F,D).
great_rsd(A,B):- ring_subst_4(A,D),x_subst(A,E,D),ring_subst_2(B,D),sigma(D,C).
great_rsd(A,B):- gt(D,C),alk_groups(B,D),x_subst(B,C,E),ring_subst_5(A,F).
great_rsd(A,B):- ring_subst_2(B,D),ring_subst_4(A,E),x_subst(A,C,D).
great_rsd(A,B):- n_val(A,C),sigma(D,F),r_subst_3(B,E),ring_subst_6(B,D).
great_rsd(A,B):- pi_acceptor(C,F),polarisable(C,E),ring_subst_5(A,D),ring_subst_2(B,C).
great_rsd(A,B):- alk_groups(B,C),ring_subst_3(A,F),alk_groups(A,D),gt(D,E).
great_rsd(A,B):- r_subst_3(A,D),r_subst_1(B,F),x_subst(B,E,C),alk_groups(B,E).
great_rsd(A,B):- x_subst(A,F,E),ring_subst_4(A,D),ring_subst_5(A,D),ring_subst_3(B,C).
great_rsd(A,B):- ring_substitutions(A,C),ring_subst_3(A,F),h_doner(F,D),alk_groups(B,E).
great_rsd(A,B):- ring_substitutions(A,E),ring_subst_6(A,F),polarisable(C,D),ring_subst_2(B,C).
great_rsd(A,B):- ring_subst_2(A,C),polarisable(F,E),ring_subst_2(A,D),ring_subst_2(B,F).
great_rsd(A,B):- polar(E,C),h_doner(E,F),x_subst(A,D,E),ring_subst_3(B,E).
great_rsd(A,B):- pi_acceptor(E,D),r_subst_1(A,C),ring_subst_4(B,F),ring_subst_6(A,E).
great_rsd(A,B):- ring_substitutions(A,D),x_subst(B,F,C),ring_subst_6(A,E),x_subst(B,D,E).
great_rsd(A,B):- x_subst(A,F,E),alk_groups(A,C),ring_subst_4(A,D),r_subst_3(B,F).
great_rsd(A,B):- x_subst(B,F,C),ring_subst_3(A,D),r_subst_1(A,E).
great_rsd(A,B):- ring_subst_4(A,D),ring_subst_6(B,E),r_subst_3(B,C),ring_subst_5(A,F).
great_rsd(A,B):- ring_subst_3(A,F),ring_subst_6(A,C),ring_substitutions(B,D),x_subst(B,E,C).
great_rsd(A,B):- h_doner(C,F),x_subst(A,D,C),x_subst(B,D,C),ring_subst_3(A,E).
great_rsd(A,B):- r_subst_3(A,D),ring_subst_6(A,E),gt(D,C),ring_substitutions(B,D).
great_rsd(A,B):- ring_subst_3(A,F),ring_subst_2(B,D),pi_acceptor(D,C),h_doner(F,E).
great_rsd(A,B):- pi_acceptor(C,E),flex(C,F),alk_groups(A,D),ring_subst_3(B,C).
great_rsd(A,B):- ring_subst_2(B,D),ring_subst_6(B,C),n_val(A,E),r_subst_1(B,F).
great_rsd(A,B):- n_val(A,D),alk_groups(B,D),r_subst_1(A,E),ring_substitutions(A,C).
great_rsd(A,B):- ring_subst_2(A,C),ring_subst_5(A,C),alk_groups(B,D),n_val(B,E).
great_rsd(A,B):- h_doner(E,C),ring_subst_4(A,E),x_subst(B,D,E),ring_subst_3(B,E).
great_rsd(A,B):- ring_subst_3(A,F),ring_subst_2(A,D),r_subst_2(A,E),ring_subst_3(B,C).
great_rsd(A,B):- ring_subst_5(A,C),ring_subst_5(B,F),x_subst(A,E,F),ring_subst_5(A,D).
great_rsd(A,B):- sigma(F,E),n_val(A,D),ring_subst_6(B,F),n_val(A,C).
great_rsd(A,B):- ring_subst_5(B,F),ring_subst_3(B,D),ring_subst_4(A,C),r_subst_2(A,E).
great_rsd(A,B):- size(F,C),ring_subst_5(B,F),alk_groups(A,D),ring_subst_4(B,E).
great_rsd(A,B):- ring_substitutions(A,D),alk_groups(B,F),x_subst(A,E,C),gt(D,E).
great_rsd(A,B):- x_subst(A,D,C),r_subst_3(B,E),ring_subst_5(B,C),sigma(C,F).
great_rsd(A,B):- r_subst_3(A,D),ring_subst_4(B,C),ring_subst_4(B,E),ring_subst_6(A,C).
great_rsd(A,B):- x_subst(A,D,C),polarisable(E,F),ring_subst_4(B,C),ring_subst_3(B,E).
great_rsd(A,B):- ring_subst_5(A,C),ring_subst_3(A,D),x_subst(A,E,F),ring_subst_2(B,C).
great_rsd(A,B):- r_subst_3(B,E),polarisable(D,F),x_subst(A,C,D),n_val(B,C).
great_rsd(A,B):- h_acceptor(C,F),x_subst(A,D,C),ring_subst_5(B,C),ring_subst_3(B,E).
great_rsd(A,B):- ring_subst_4(A,D),x_subst(B,C,D),polarisable(F,E),ring_subst_5(B,F).
great_rsd(A,B):- sigma(C,E),ring_subst_6(B,C),n_val(A,D),r_subst_2(A,F).
great_rsd(A,B):- ring_subst_4(A,C),gt(E,F),r_subst_3(B,E),x_subst(A,F,D).
great_rsd(A,B):- r_subst_2(A,C),ring_subst_2(A,D),ring_subst_5(B,F),ring_subst_5(A,E).
great_rsd(A,B):- pi_doner(C,E),ring_subst_2(A,D),ring_subst_4(B,F),ring_subst_6(A,C).
great_rsd(A,B):- n_val(A,C),ring_subst_5(B,E),x_subst(A,F,D),ring_subst_3(B,E).
great_rsd(A,B):- x_subst(A,F,E),n_val(A,D),ring_substitutions(A,F),ring_substitutions(B,C).
great_rsd(A,B):- polarisable(F,C),ring_subst_2(A,D),ring_subst_5(B,F),n_val(A,E).
great_rsd(A,B):- x_subst(B,D,F),ring_subst_5(A,E),ring_subst_6(B,C),ring_subst_6(B,F).
great_rsd(A,B):- pi_doner(F,E),ring_subst_3(A,D),ring_subst_4(B,F),r_subst_3(B,C).
great_rsd(A,B):- r_subst_3(B,D),r_subst_3(A,D),x_subst(A,D,C),x_subst(A,D,E).
great_rsd(A,B):- ring_subst_6(B,E),alk_groups(B,C),n_val(A,C),ring_subst_6(B,D).
great_rsd(A,B):- h_acceptor(C,F),size(E,D),ring_subst_6(B,C),ring_subst_3(A,E).
great_rsd(A,B):- ring_subst_3(A,C),ring_subst_4(B,D),ring_subst_4(B,C),ring_subst_2(B,C).
great_rsd(A,B):- x_subst(A,F,E),h_doner(C,D),r_subst_3(B,F),ring_subst_2(B,C).
great_rsd(A,B):- x_subst(A,D,F),ring_subst_3(A,C),ring_subst_5(B,F),ring_subst_2(A,E).
great_rsd(A,B):- x_subst(B,E,D),n_val(A,F),n_val(B,E),x_subst(A,C,D).
great_rsd(A,B):- ring_subst_5(A,C),r_subst_2(A,E),ring_subst_4(B,F),polarisable(C,D).
