great_rsd(A,B):- ring_substitutions(A,E),sigma(C,D),pi_doner(C,F),ring_subst_3(B,C).
great_rsd(A,B):- ring_substitutions(A,E),ring_subst_2(B,D),r_subst_1(B,C),r_subst_2(A,F).
great_rsd(A,B):- r_subst_2(B,C),ring_subst_4(B,F),r_subst_1(A,D),n_val(A,E).
great_rsd(A,B):- ring_subst_5(A,E),pi_acceptor(E,F),x_subst(B,C,E),ring_subst_5(A,D).
great_rsd(A,B):- x_subst(A,F,E),ring_subst_2(A,C),x_subst(A,D,E),ring_substitutions(B,F).
great_rsd(A,B):- gt(C,E),ring_subst_4(B,D),r_subst_3(B,C),x_subst(A,C,D).
great_rsd(A,B):- ring_subst_3(A,F),x_subst(B,D,C),r_subst_3(A,E).
great_rsd(A,B):- ring_subst_2(B,D),ring_subst_6(B,C),ring_subst_6(A,F),ring_subst_2(A,E).
great_rsd(A,B):- r_subst_1(B,D),r_subst_2(A,F),x_subst(A,E,C),alk_groups(B,E).
great_rsd(A,B):- ring_subst_2(A,C),x_subst(B,F,C),alk_groups(B,D),h_doner(C,E).
great_rsd(A,B):- x_subst(A,F,C),r_subst_1(A,E),x_subst(B,F,D),ring_subst_6(A,C).
great_rsd(A,B):- ring_subst_6(B,E),ring_subst_3(B,D),ring_subst_5(A,E),ring_subst_2(B,C).
great_rsd(A,B):- r_subst_3(A,D),h_acceptor(E,C),ring_subst_2(B,E),ring_subst_3(B,E).
great_rsd(A,B):- r_subst_3(B,D),ring_subst_2(A,C),ring_subst_4(A,E),r_subst_3(A,F).
great_rsd(A,B):- r_subst_1(B,E),ring_subst_3(A,D),pi_doner(C,F),ring_subst_3(B,C).
great_rsd(A,B):- ring_subst_2(B,C),ring_subst_6(A,D),size(D,F),alk_groups(B,E).
great_rsd(A,B):- n_val(B,F),ring_subst_4(B,C),sigma(C,D),ring_subst_3(A,E).
great_rsd(A,B):- ring_substitutions(A,E),r_subst_3(B,E),h_acceptor(C,D),ring_subst_2(B,C).
great_rsd(A,B):- r_subst_3(B,D),sigma(F,C),ring_subst_5(B,F),x_subst(A,D,E).
great_rsd(A,B):- x_subst(B,F,E),r_subst_2(A,C),ring_subst_2(A,D),ring_subst_2(B,D).
great_rsd(A,B):- n_val(B,D),size(F,E),ring_subst_5(A,F),ring_subst_3(B,C).
great_rsd(A,B):- r_subst_3(A,D),x_subst(B,D,C),ring_subst_6(B,C),alk_groups(B,E).
great_rsd(A,B):- x_subst(B,F,E),ring_subst_2(A,C),x_subst(B,D,C),x_subst(B,D,E).
great_rsd(A,B):- ring_subst_4(B,D),ring_subst_6(B,F),ring_subst_4(A,E),ring_subst_3(B,C).
great_rsd(A,B):- alk_groups(B,F),ring_subst_6(A,C),sigma(C,D),h_doner(C,E).
great_rsd(A,B):- r_subst_3(B,D),ring_subst_5(A,E),gt(D,C),ring_subst_3(A,E).
great_rsd(A,B):- ring_subst_2(B,E),r_subst_2(B,C),ring_subst_5(A,F),ring_subst_6(B,D).
great_rsd(A,B):- r_subst_1(B,D),ring_subst_2(A,C),ring_substitutions(B,E),ring_subst_2(B,C).
great_rsd(A,B):- gt(F,C),r_subst_1(B,E),ring_substitutions(A,F),ring_subst_6(A,D).
great_rsd(A,B):- ring_subst_3(A,F),ring_subst_3(B,D),ring_subst_4(B,F),x_subst(A,E,C).
great_rsd(A,B):- ring_subst_2(A,F),r_subst_3(B,C),x_subst(A,C,D),ring_subst_2(B,E).
great_rsd(A,B):- ring_subst_2(A,F),ring_subst_6(A,E),r_subst_2(A,D),ring_subst_3(B,C).
great_rsd(A,B):- ring_subst_3(B,D),flex(E,F),ring_subst_3(A,E),ring_subst_2(B,C).
great_rsd(A,B):- alk_groups(B,F),ring_subst_6(A,D),polarisable(D,C),ring_subst_5(A,E).
great_rsd(A,B):- ring_subst_4(B,D),ring_subst_5(A,F),pi_doner(F,E),ring_subst_2(B,C).
great_rsd(A,B):- r_subst_2(B,D),ring_subst_6(A,C),ring_subst_4(A,E),flex(C,F).
great_rsd(A,B):- ring_subst_5(B,E),ring_subst_3(B,D),n_val(A,F),pi_doner(D,C).
great_rsd(A,B):- ring_subst_3(A,F),size(C,D),ring_subst_6(B,C),x_subst(B,E,F).
great_rsd(A,B):- ring_subst_4(A,D),h_acceptor(D,F),ring_subst_6(A,C),alk_groups(B,E).
great_rsd(A,B):- ring_subst_5(B,E),ring_subst_2(B,D),ring_subst_4(A,C),ring_subst_5(A,E).
great_rsd(A,B):- n_val(A,C),alk_groups(B,C),ring_subst_2(B,D),ring_subst_5(B,D).
great_rsd(A,B):- x_subst(B,F,E),gt(F,D),ring_subst_4(A,C),ring_subst_2(B,E).
great_rsd(A,B):- r_subst_1(B,D),ring_subst_5(A,E),ring_subst_2(B,E),ring_subst_2(B,C).
great_rsd(A,B):- ring_subst_3(B,F),flex(F,D),ring_subst_6(A,C),h_doner(F,E).
great_rsd(A,B):- x_subst(A,D,F),x_subst(B,D,C),ring_subst_6(B,C),n_val(B,E).
great_rsd(A,B):- ring_subst_2(B,D),x_subst(A,C,D),alk_groups(B,E).
great_rsd(A,B):- ring_subst_3(A,C),h_acceptor(E,D),ring_subst_5(B,C),ring_subst_3(A,E).
great_rsd(A,B):- alk_groups(B,C),ring_subst_3(A,D),ring_subst_3(B,E),ring_subst_6(A,D).
great_rsd(A,B):- x_subst(B,F,E),ring_subst_6(B,C),ring_subst_2(A,D).
great_rsd(A,B):- n_val(B,D),ring_subst_4(A,E),x_subst(B,C,E),size(E,F).
great_rsd(A,B):- ring_subst_5(B,E),ring_subst_3(B,D),r_subst_3(B,F),ring_substitutions(A,C).
great_rsd(A,B):- ring_subst_2(B,E),alk_groups(A,C),ring_subst_4(B,F),ring_substitutions(B,D).
great_rsd(A,B):- ring_subst_3(A,C),size(C,D),sigma(C,F),ring_subst_2(B,E).
great_rsd(A,B):- h_doner(D,F),r_subst_2(B,E),r_subst_3(B,C),ring_subst_3(A,D).
great_rsd(A,B):- n_val(B,D),r_subst_1(A,E),ring_subst_2(B,C).
great_rsd(A,B):- h_doner(D,F),polarisable(C,E),ring_subst_5(A,D),ring_subst_3(B,C).
great_rsd(A,B):- r_subst_2(B,D),x_subst(A,C,E),sigma(E,F),ring_subst_2(B,E).
great_rsd(A,B):- r_subst_3(B,D),h_doner(E,F),r_subst_3(A,C),ring_subst_2(A,E).
great_rsd(A,B):- ring_subst_3(A,C),ring_subst_6(A,E),alk_groups(A,D),x_subst(B,D,E).
great_rsd(A,B):- ring_substitutions(A,D),ring_subst_4(A,F),ring_subst_6(B,C),x_subst(B,E,C).
great_rsd(A,B):- ring_substitutions(A,E),x_subst(B,C,D),r_subst_3(A,E),ring_subst_6(A,D).
great_rsd(A,B):- x_subst(A,D,C),ring_subst_5(A,C),pi_acceptor(C,F),n_val(B,E).
great_rsd(A,B):- ring_substitutions(A,D),n_val(B,D),gt(D,C),ring_subst_3(A,E).
great_rsd(A,B):- r_subst_3(B,D),ring_subst_3(B,C),size(C,E),r_subst_3(A,F).
great_rsd(A,B):- r_subst_3(B,D),x_subst(B,F,C),x_subst(A,D,E),ring_subst_3(A,C).
great_rsd(A,B):- ring_subst_4(B,D),x_subst(B,C,D),r_subst_1(B,F),ring_subst_5(A,E).
great_rsd(A,B):- x_subst(B,C,D),alk_groups(A,C),size(D,F),h_doner(D,E).
great_rsd(A,B):- ring_subst_4(A,D),r_subst_2(A,C),ring_subst_5(B,F),ring_subst_3(B,E).
great_rsd(A,B):- r_subst_3(B,D),size(F,E),ring_subst_6(A,C),ring_subst_6(B,F).
great_rsd(A,B):- ring_subst_4(A,D),x_subst(B,C,D),size(D,E),flex(D,F).
great_rsd(A,B):- x_subst(B,D,F),n_val(A,D),x_subst(B,D,E),n_val(B,C).
great_rsd(A,B):- ring_subst_4(A,D),pi_doner(C,F),r_subst_3(B,E),x_subst(A,E,C).
great_rsd(A,B):- alk_groups(B,C),ring_subst_5(A,E),r_subst_3(A,D),ring_subst_4(A,E).
great_rsd(A,B):- r_subst_1(B,C),n_val(A,D),ring_subst_4(A,F),x_subst(B,D,E).
great_rsd(A,B):- r_subst_2(B,D),sigma(C,F),r_subst_1(A,E),ring_subst_2(B,C).
great_rsd(A,B):- r_subst_3(A,D),alk_groups(A,C),x_subst(A,E,F),r_subst_3(B,C).
great_rsd(A,B):- x_subst(A,F,E),ring_subst_4(A,C),sigma(C,D),n_val(B,F).
great_rsd(A,B):- r_subst_2(A,C),ring_subst_3(A,E),alk_groups(A,D),r_subst_1(B,F).
great_rsd(A,B):- r_subst_3(B,D),ring_subst_6(A,C),polarisable(C,F),sigma(C,E).
great_rsd(A,B):- h_acceptor(E,C),ring_subst_5(B,F),x_subst(A,D,E),ring_subst_3(A,E).
great_rsd(A,B):- h_acceptor(E,F),ring_subst_5(A,E),ring_subst_5(B,D),ring_subst_2(B,C).
great_rsd(A,B):- polar(C,F),polarisable(C,E),ring_subst_6(B,C),alk_groups(A,D).
great_rsd(A,B):- r_subst_1(A,D),alk_groups(B,F),gt(C,F),x_subst(B,C,E).
great_rsd(A,B):- ring_subst_3(B,F),x_subst(A,C,E),ring_subst_6(B,E),gt(C,D).
great_rsd(A,B):- x_subst(A,C,E),pi_doner(E,D),gt(C,F),ring_substitutions(B,F).
great_rsd(A,B):- pi_acceptor(E,D),ring_subst_6(B,C),ring_subst_2(A,E),r_subst_3(A,F).
great_rsd(A,B):- ring_substitutions(A,E),size(C,D),ring_subst_6(B,C),n_val(B,E).
great_rsd(A,B):- ring_subst_3(B,F),size(E,C),ring_subst_4(A,E),polar(F,D).
great_rsd(A,B):- ring_subst_6(A,E),alk_groups(B,D),x_subst(B,C,E),r_subst_1(A,F).
great_rsd(A,B):- x_subst(B,F,E),r_subst_2(B,C),x_subst(A,D,E),ring_subst_3(B,E).
great_rsd(A,B):- r_subst_2(B,D),ring_subst_4(A,E),x_subst(B,C,E),r_subst_1(B,F).
great_rsd(A,B):- h_acceptor(E,F),n_val(B,D),ring_subst_4(B,E),ring_substitutions(A,C).
great_rsd(A,B):- ring_subst_5(B,F),x_subst(A,C,F),r_subst_2(A,D),ring_subst_2(A,E).
great_rsd(A,B):- r_subst_3(B,D),ring_subst_5(B,F),n_val(A,C),gt(D,E).
great_rsd(A,B):- ring_subst_2(B,D),ring_subst_2(B,E),r_subst_3(A,C),ring_substitutions(A,C).
great_rsd(A,B):- ring_subst_4(A,F),ring_subst_5(B,D),x_subst(A,C,D),h_acceptor(D,E).
great_rsd(A,B):- ring_substitutions(A,D),ring_subst_5(B,E),ring_subst_4(B,F),pi_doner(F,C).
great_rsd(A,B):- x_subst(A,D,F),polar(F,C),ring_subst_2(B,F),pi_doner(F,E).
great_rsd(A,B):- x_subst(A,C,E),ring_subst_5(B,E),ring_subst_3(A,D),r_subst_1(A,F).
great_rsd(A,B):- ring_subst_3(A,C),pi_acceptor(D,E),ring_subst_6(A,C),ring_subst_6(B,D).
great_rsd(A,B):- ring_subst_3(B,F),h_doner(C,D),r_subst_3(A,E),ring_subst_3(B,C).
great_rsd(A,B):- ring_subst_2(B,D),polarisable(D,F),ring_subst_6(A,E),x_subst(B,C,E).
great_rsd(A,B):- ring_substitutions(A,E),ring_subst_6(A,C),h_acceptor(C,D),r_subst_3(B,F).
great_rsd(A,B):- n_val(B,F),x_subst(A,C,E),ring_subst_4(B,D),ring_substitutions(B,F).
great_rsd(A,B):- ring_subst_5(B,E),r_subst_1(A,C),size(E,D).
great_rsd(A,B):- ring_substitutions(B,E),ring_subst_2(A,D),r_subst_3(B,C),ring_subst_3(A,D).
great_rsd(A,B):- pi_acceptor(E,D),ring_subst_5(A,E),n_val(A,C),r_subst_2(B,F).
great_rsd(A,B):- gt(F,D),alk_groups(A,C),alk_groups(B,F),alk_groups(B,E).
great_rsd(A,B):- r_subst_2(B,D),sigma(E,C),r_subst_2(A,D),ring_subst_3(A,E).
great_rsd(A,B):- x_subst(B,D,F),h_acceptor(F,C),ring_subst_5(A,F),h_doner(F,E).
great_rsd(A,B):- x_subst(B,D,C),ring_subst_4(A,F),h_doner(C,E),ring_subst_6(B,F).
great_rsd(A,B):- r_subst_1(B,D),gt(F,E),ring_substitutions(A,F),x_subst(A,E,C).
great_rsd(A,B):- n_val(A,C),ring_subst_6(A,E),h_doner(E,D),ring_subst_4(B,E).
great_rsd(A,B):- polarisable(D,E),ring_subst_4(A,C),ring_subst_4(B,F),ring_subst_5(A,D).
great_rsd(A,B):- ring_subst_3(A,F),ring_subst_5(B,E),r_subst_1(B,C),ring_subst_5(A,D).
great_rsd(A,B):- ring_subst_2(B,D),flex(D,E),ring_subst_6(A,C),flex(D,F).
great_rsd(A,B):- ring_substitutions(A,E),r_subst_1(A,D),ring_subst_5(A,F),ring_subst_2(B,C).
great_rsd(A,B):- n_val(A,D),ring_subst_4(B,F),n_val(A,E),ring_subst_3(B,C).
great_rsd(A,B):- n_val(A,E),ring_subst_2(B,F),x_subst(A,C,D),ring_subst_6(A,D).
great_rsd(A,B):- h_doner(F,E),ring_subst_2(B,D),ring_subst_6(B,F),r_subst_3(A,C).
