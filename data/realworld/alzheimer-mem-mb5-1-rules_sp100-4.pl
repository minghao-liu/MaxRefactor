great_rsd(A,B):- n_val(B,E),ring_subst_5(A,D),x_subst(B,E,C),ring_subst_2(B,C).
great_rsd(A,B):- x_subst(A,F,E),ring_subst_2(A,C),sigma(E,D),ring_substitutions(B,F).
great_rsd(A,B):- x_subst(A,F,C),alk_groups(A,D),x_subst(A,D,E),ring_subst_3(B,C).
great_rsd(A,B):- ring_substitutions(B,C),r_subst_3(A,D),x_subst(A,D,E),ring_substitutions(B,F).
great_rsd(A,B):- x_subst(A,F,E),gt(F,D),alk_groups(A,F),r_subst_3(B,C).
great_rsd(A,B):- x_subst(A,D,F),ring_subst_6(B,E),r_subst_1(B,C).
great_rsd(A,B):- sigma(C,F),r_subst_1(A,D),n_val(A,E),ring_subst_3(B,C).
great_rsd(A,B):- ring_subst_6(B,D),ring_subst_6(A,C),ring_subst_4(B,E),pi_doner(D,F).
great_rsd(A,B):- ring_subst_2(A,F),ring_subst_5(B,E),flex(F,D),h_doner(E,C).
great_rsd(A,B):- alk_groups(B,C),flex(D,E),x_subst(A,C,D),ring_subst_5(A,D).
great_rsd(A,B):- alk_groups(A,E),x_subst(B,D,C),gt(D,F),n_val(B,D).
great_rsd(A,B):- r_subst_3(A,D),alk_groups(B,D),x_subst(B,D,E),size(E,C).
great_rsd(A,B):- x_subst(A,C,E),ring_subst_4(A,F),ring_subst_6(B,F),size(E,D).
great_rsd(A,B):- h_doner(F,C),ring_subst_5(B,E),x_subst(A,D,E),ring_subst_5(A,F).
great_rsd(A,B):- x_subst(B,E,D),ring_subst_2(B,D),ring_subst_4(B,C),x_subst(A,F,D).
great_rsd(A,B):- ring_subst_3(B,F),ring_subst_3(A,F),x_subst(B,C,D),ring_subst_2(A,E).
great_rsd(A,B):- x_subst(B,F,E),ring_subst_2(A,C),h_doner(C,D),ring_subst_3(B,C).
great_rsd(A,B):- flex(D,C),ring_subst_4(B,D),ring_subst_5(A,E),flex(E,F).
great_rsd(A,B):- x_subst(A,F,E),x_subst(A,D,C),ring_substitutions(B,D),ring_subst_2(A,E).
great_rsd(A,B):- ring_substitutions(B,C),ring_subst_4(A,E),alk_groups(B,D),r_subst_3(B,C).
great_rsd(A,B):- pi_doner(E,F),ring_subst_4(B,D),ring_subst_5(B,C),ring_subst_2(A,E).
great_rsd(A,B):- r_subst_3(B,D),alk_groups(B,F),r_subst_3(B,E),x_subst(A,E,C).
great_rsd(A,B):- gt(D,F),ring_subst_6(B,C),alk_groups(A,D),n_val(A,E).
great_rsd(A,B):- h_acceptor(E,F),x_subst(B,D,C),ring_subst_4(A,C),ring_subst_6(A,E).
great_rsd(A,B):- n_val(B,F),ring_subst_5(B,E),ring_subst_4(B,C),x_subst(A,D,E).
great_rsd(A,B):- alk_groups(B,F),ring_subst_2(A,D),ring_subst_3(A,E),ring_subst_6(B,C).
great_rsd(A,B):- ring_subst_4(A,D),r_subst_1(B,E),ring_subst_6(A,F),ring_subst_2(B,C).
great_rsd(A,B):- polarisable(E,D),h_acceptor(E,F),r_subst_1(A,C),ring_subst_3(B,E).
great_rsd(A,B):- r_subst_1(B,D),n_val(A,C),r_subst_1(A,D),ring_subst_2(A,E).
great_rsd(A,B):- ring_subst_3(B,F),sigma(E,C),r_subst_2(A,D),ring_subst_3(A,E).
great_rsd(A,B):- ring_subst_4(A,D),ring_subst_6(B,D),flex(D,F),x_subst(A,E,C).
great_rsd(A,B):- polar(E,D),sigma(E,F),x_subst(B,C,E),ring_subst_3(A,E).
great_rsd(A,B):- x_subst(B,C,D),x_subst(A,E,F),ring_subst_2(B,F).
great_rsd(A,B):- ring_subst_3(B,D),x_subst(A,F,C),r_subst_2(A,E),ring_subst_2(B,C).
great_rsd(A,B):- n_val(A,E),ring_subst_5(A,D),x_subst(A,C,D),r_subst_1(B,F).
great_rsd(A,B):- r_subst_2(A,E),ring_subst_6(A,D),polarisable(D,C),ring_substitutions(B,F).
great_rsd(A,B):- polarisable(C,E),sigma(C,F),ring_subst_4(B,C),ring_subst_6(A,D).
great_rsd(A,B):- ring_subst_2(A,F),ring_subst_3(B,D),ring_subst_6(B,C),r_subst_1(A,E).
great_rsd(A,B):- sigma(F,C),n_val(A,D),ring_subst_2(B,F),ring_subst_2(B,E).
great_rsd(A,B):- h_doner(F,D),ring_subst_2(B,F),r_subst_2(B,C),ring_subst_3(A,E).
great_rsd(A,B):- h_doner(F,C),ring_subst_4(B,F),h_acceptor(F,D),ring_subst_3(A,E).
great_rsd(A,B):- gt(C,F),r_subst_3(A,E),r_subst_3(B,C),ring_subst_5(A,D).
great_rsd(A,B):- x_subst(A,F,E),n_val(B,F),r_subst_3(B,C),x_subst(A,C,D).
great_rsd(A,B):- ring_subst_6(A,E),ring_subst_6(A,F),ring_subst_6(A,C),ring_substitutions(B,D).
great_rsd(A,B):- ring_substitutions(A,D),n_val(B,D),r_subst_3(B,E),gt(E,C).
great_rsd(A,B):- x_subst(B,D,F),ring_subst_3(A,F),h_acceptor(F,C),n_val(A,E).
great_rsd(A,B):- alk_groups(A,E),ring_subst_6(B,C),n_val(A,D),ring_subst_2(B,C).
great_rsd(A,B):- ring_subst_4(A,D),ring_subst_5(B,E),ring_subst_5(A,C),ring_subst_2(B,E).
great_rsd(A,B):- ring_subst_4(A,D),ring_subst_5(A,E),ring_subst_4(B,F),size(E,C).
great_rsd(A,B):- size(E,D),ring_subst_5(A,E),x_subst(B,C,E),ring_subst_5(A,F).
great_rsd(A,B):- n_val(A,F),x_subst(A,D,C),alk_groups(B,D),ring_subst_5(A,E).
great_rsd(A,B):- ring_subst_3(B,F),ring_substitutions(A,E),flex(F,D),x_subst(A,C,F).
great_rsd(A,B):- x_subst(A,C,F),ring_subst_3(B,E),ring_subst_3(A,E),ring_subst_5(A,D).
great_rsd(A,B):- r_subst_1(B,D),ring_subst_2(B,E),alk_groups(A,F),r_subst_2(B,C).
great_rsd(A,B):- x_subst(A,D,C),ring_subst_5(B,C),x_subst(A,F,C),ring_subst_5(A,E).
great_rsd(A,B):- ring_subst_5(B,D),r_subst_1(B,E),r_subst_3(A,C),ring_subst_6(B,D).
great_rsd(A,B):- ring_substitutions(B,C),ring_subst_4(A,D),ring_subst_4(A,E),x_subst(A,C,D).
great_rsd(A,B):- ring_subst_4(A,D),ring_subst_3(A,E),ring_subst_3(B,E),r_subst_3(A,C).
great_rsd(A,B):- pi_acceptor(D,C),ring_subst_3(A,D),ring_subst_5(B,F),polar(D,E).
great_rsd(A,B):- ring_subst_4(B,D),ring_subst_2(A,D),r_subst_3(A,C),ring_subst_5(A,D).
great_rsd(A,B):- ring_subst_3(B,F),ring_subst_4(B,F),h_doner(D,E),x_subst(A,C,D).
great_rsd(A,B):- size(E,D),ring_subst_6(B,C),ring_subst_3(A,E),ring_substitutions(A,F).
great_rsd(A,B):- ring_subst_4(B,D),ring_subst_6(A,E),ring_subst_3(A,D),ring_subst_2(B,C).
great_rsd(A,B):- ring_substitutions(B,C),ring_subst_2(B,D),n_val(A,E),r_subst_2(B,F).
great_rsd(A,B):- pi_doner(D,E),ring_subst_2(A,D),r_subst_3(B,F),ring_subst_2(B,C).
great_rsd(A,B):- ring_subst_2(A,F),ring_subst_6(B,C),r_subst_1(B,E),pi_acceptor(F,D).
great_rsd(A,B):- n_val(B,D),ring_subst_5(B,C),pi_acceptor(E,F),ring_subst_2(A,E).
great_rsd(A,B):- alk_groups(A,E),h_acceptor(F,D),ring_subst_4(B,F),size(F,C).
great_rsd(A,B):- r_subst_3(A,D),pi_acceptor(E,F),ring_subst_5(A,C),ring_subst_4(B,E).
great_rsd(A,B):- pi_acceptor(E,C),ring_substitutions(A,D),x_subst(B,D,E),r_subst_3(B,F).
great_rsd(A,B):- polar(D,F),ring_subst_3(A,D),ring_subst_5(A,C),ring_subst_2(B,E).
great_rsd(A,B):- ring_subst_3(B,D),x_subst(B,C,D),ring_subst_5(A,E),r_subst_2(A,F).
great_rsd(A,B):- alk_groups(A,E),ring_subst_6(B,D),polar(D,F),r_subst_3(A,C).
great_rsd(A,B):- r_subst_3(A,D),n_val(A,D),ring_subst_5(B,F),x_subst(B,E,C).
great_rsd(A,B):- r_subst_3(B,D),pi_acceptor(E,F),gt(D,C),ring_subst_2(A,E).
great_rsd(A,B):- x_subst(A,D,C),x_subst(B,E,F),ring_subst_4(B,F),alk_groups(B,D).
great_rsd(A,B):- ring_subst_3(B,D),ring_subst_4(A,E),pi_doner(D,F),ring_subst_3(B,C).
great_rsd(A,B):- ring_subst_3(A,F),x_subst(B,C,D),ring_subst_3(A,D),polarisable(F,E).
great_rsd(A,B):- ring_subst_4(A,D),size(D,C),x_subst(B,E,F),ring_subst_2(B,F).
great_rsd(A,B):- alk_groups(B,C),ring_substitutions(A,D),ring_subst_3(B,E),ring_subst_4(B,F).
great_rsd(A,B):- ring_subst_2(A,C),ring_subst_3(A,F),ring_subst_3(B,D),h_acceptor(F,E).
great_rsd(A,B):- size(C,F),ring_subst_6(A,C),ring_subst_3(B,E),ring_subst_6(A,D).
great_rsd(A,B):- n_val(B,D),ring_subst_6(A,C),ring_substitutions(B,D),ring_subst_3(B,C).
great_rsd(A,B):- ring_subst_6(A,F),ring_subst_4(A,E),x_subst(B,C,E),ring_subst_5(A,D).
great_rsd(A,B):- ring_subst_6(B,D),r_subst_1(B,C),ring_subst_2(A,E),ring_subst_6(A,D).
great_rsd(A,B):- r_subst_3(A,D),ring_subst_3(B,C),alk_groups(B,E).
great_rsd(A,B):- n_val(A,F),ring_subst_6(B,C),x_subst(A,D,E),ring_substitutions(B,F).
great_rsd(A,B):- ring_subst_6(A,E),ring_subst_2(A,D),pi_doner(D,C),ring_subst_2(B,E).
great_rsd(A,B):- ring_subst_3(A,C),alk_groups(B,D),ring_subst_3(B,E),r_subst_3(B,F).
great_rsd(A,B):- x_subst(A,F,E),x_subst(B,F,C),alk_groups(A,F),h_acceptor(C,D).
great_rsd(A,B):- x_subst(A,D,C),polar(F,E),ring_subst_6(B,F),ring_subst_6(A,F).
great_rsd(A,B):- h_acceptor(C,E),ring_subst_4(B,C),ring_subst_5(A,F),polar(F,D).
great_rsd(A,B):- ring_substitutions(B,E),x_subst(B,D,C),ring_subst_6(A,F),n_val(B,E).
great_rsd(A,B):- ring_substitutions(B,C),h_acceptor(E,D),pi_doner(E,F),ring_subst_2(A,E).
great_rsd(A,B):- polarisable(E,D),x_subst(B,C,E),ring_substitutions(A,C).
great_rsd(A,B):- gt(C,E),r_subst_3(B,C),ring_subst_3(A,F),r_subst_2(A,D).
great_rsd(A,B):- n_val(A,F),ring_subst_3(A,D),polar(D,E),r_subst_3(B,C).
great_rsd(A,B):- ring_subst_4(A,D),r_subst_1(A,C),ring_subst_4(A,E),n_val(B,F).
great_rsd(A,B):- r_subst_3(A,D),ring_subst_3(B,C),ring_subst_3(B,E),r_subst_2(A,F).
great_rsd(A,B):- ring_subst_2(A,C),ring_subst_2(B,D),r_subst_3(A,E),ring_subst_5(B,D).
