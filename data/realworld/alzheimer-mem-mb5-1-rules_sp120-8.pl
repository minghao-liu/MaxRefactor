great_rsd(A,B):- x_subst(B,F,E),size(E,D),alk_groups(A,F),r_subst_3(B,C).
great_rsd(A,B):- ring_subst_3(B,D),ring_subst_5(B,E),alk_groups(B,F),ring_subst_5(A,C).
great_rsd(A,B):- r_subst_3(B,D),h_acceptor(E,F),pi_acceptor(E,C),ring_subst_3(A,E).
great_rsd(A,B):- ring_substitutions(A,D),ring_subst_4(A,C),x_subst(A,E,C),x_subst(B,E,C).
great_rsd(A,B):- x_subst(A,D,F),polarisable(C,E),alk_groups(A,D),ring_subst_2(B,C).
great_rsd(A,B):- ring_subst_4(A,D),ring_subst_6(B,D),r_subst_3(B,C),x_subst(A,C,D).
great_rsd(A,B):- r_subst_3(A,D),alk_groups(A,D),ring_subst_4(B,C),x_subst(B,D,E).
great_rsd(A,B):- h_doner(F,C),ring_subst_4(A,F),sigma(F,D),ring_subst_2(B,E).
great_rsd(A,B):- ring_subst_3(A,C),ring_subst_6(A,C),r_subst_1(A,D),x_subst(B,E,C).
great_rsd(A,B):- x_subst(B,D,C),ring_subst_6(A,E),ring_subst_5(A,F),ring_subst_2(A,E).
great_rsd(A,B):- alk_groups(B,C),ring_substitutions(A,E),ring_subst_5(A,F),pi_acceptor(F,D).
great_rsd(A,B):- ring_subst_5(B,E),ring_subst_4(A,C),ring_subst_4(B,F),pi_acceptor(F,D).
great_rsd(A,B):- n_val(A,D),ring_subst_5(A,E),ring_subst_4(A,E),r_subst_3(B,C).
great_rsd(A,B):- ring_substitutions(A,E),ring_subst_6(B,C),ring_subst_5(B,F),pi_doner(F,D).
great_rsd(A,B):- x_subst(B,F,E),r_subst_1(A,C),ring_subst_3(B,D),ring_subst_6(A,D).
great_rsd(A,B):- x_subst(A,F,E),ring_subst_3(B,D),pi_acceptor(E,C),ring_subst_6(A,D).
great_rsd(A,B):- ring_subst_3(A,C),pi_acceptor(F,D),x_subst(A,E,F),ring_subst_3(B,C).
great_rsd(A,B):- r_subst_3(B,D),ring_substitutions(A,E),ring_subst_6(A,C),r_subst_1(B,F).
great_rsd(A,B):- ring_subst_2(A,C),ring_subst_6(A,E),ring_subst_2(B,F),ring_subst_6(B,D).
great_rsd(A,B):- ring_subst_2(A,F),h_doner(F,E),r_subst_3(B,C),ring_subst_4(B,D).
great_rsd(A,B):- h_doner(E,C),ring_subst_5(A,E),alk_groups(B,D),ring_substitutions(B,D).
great_rsd(A,B):- r_subst_1(B,C),r_subst_1(A,E),x_subst(A,F,D),ring_substitutions(B,F).
great_rsd(A,B):- alk_groups(A,E),polar(C,D),x_subst(A,E,F),ring_subst_3(B,C).
great_rsd(A,B):- ring_substitutions(A,D),ring_subst_6(A,E),alk_groups(B,D),ring_subst_2(B,C).
great_rsd(A,B):- n_val(A,D),gt(E,F),n_val(A,E),ring_subst_3(B,C).
great_rsd(A,B):- ring_subst_2(B,E),ring_subst_4(B,C),r_subst_2(A,D),size(C,F).
great_rsd(A,B):- polarisable(D,E),n_val(B,C),x_subst(A,C,D),ring_substitutions(A,C).
great_rsd(A,B):- ring_subst_4(B,D),r_subst_2(B,E),ring_subst_5(B,F),ring_subst_6(A,C).
great_rsd(A,B):- ring_substitutions(A,E),ring_subst_6(B,C),ring_subst_6(B,D),alk_groups(B,E).
great_rsd(A,B):- alk_groups(B,C),alk_groups(B,D),gt(C,D),ring_substitutions(A,C).
great_rsd(A,B):- ring_subst_5(B,C),h_doner(C,D),ring_subst_3(B,E),ring_subst_3(A,E).
great_rsd(A,B):- h_doner(F,C),x_subst(A,E,D),r_subst_3(A,E),ring_subst_5(B,F).
great_rsd(A,B):- x_subst(B,F,E),x_subst(B,C,D),ring_subst_6(A,E),ring_substitutions(B,F).
great_rsd(A,B):- ring_subst_3(A,F),ring_subst_4(A,F),x_subst(B,D,E),ring_subst_2(B,C).
great_rsd(A,B):- alk_groups(A,E),ring_subst_4(A,D),r_subst_1(B,C),h_doner(D,F).
great_rsd(A,B):- ring_subst_4(A,D),ring_subst_6(A,F),r_subst_3(B,C),h_acceptor(F,E).
great_rsd(A,B):- ring_substitutions(B,E),r_subst_3(A,E),r_subst_2(A,D),x_subst(A,E,C).
great_rsd(A,B):- ring_subst_2(B,D),x_subst(B,C,E),ring_substitutions(A,F),ring_subst_6(A,D).
great_rsd(A,B):- ring_subst_3(A,F),ring_subst_5(B,F),x_subst(B,D,E),flex(F,C).
great_rsd(A,B):- ring_subst_5(B,F),ring_subst_5(A,E),ring_subst_5(A,C),x_subst(B,D,E).
great_rsd(A,B):- r_subst_2(B,E),ring_subst_6(B,F),n_val(A,D),flex(F,C).
great_rsd(A,B):- n_val(B,D),r_subst_3(B,C),ring_subst_5(B,E),alk_groups(A,D).
great_rsd(A,B):- ring_subst_2(B,D),ring_subst_3(A,D),flex(D,E),r_subst_3(B,C).
great_rsd(A,B):- r_subst_3(A,D),ring_substitutions(B,E),polar(F,C),x_subst(A,E,F).
great_rsd(A,B):- h_doner(C,D),ring_subst_6(B,C),r_subst_1(A,E),r_subst_1(A,F).
great_rsd(A,B):- ring_subst_5(B,C),r_subst_2(A,E),x_subst(A,F,D),ring_subst_6(A,D).
great_rsd(A,B):- r_subst_3(B,D),ring_subst_2(A,C),ring_subst_4(B,F),ring_subst_4(A,E).
great_rsd(A,B):- ring_substitutions(A,D),r_subst_3(A,E),ring_subst_6(A,C),ring_subst_6(B,F).
great_rsd(A,B):- ring_substitutions(A,E),ring_subst_3(B,D),ring_subst_2(B,F),flex(F,C).
great_rsd(A,B):- ring_subst_3(A,C),h_acceptor(C,E),alk_groups(B,D),r_subst_2(A,F).
great_rsd(A,B):- alk_groups(A,C),ring_subst_4(A,E),x_subst(A,C,D),r_subst_2(B,F).
great_rsd(A,B):- x_subst(B,C,D),gt(E,F),n_val(B,E),ring_substitutions(A,C).
great_rsd(A,B):- ring_subst_3(B,F),x_subst(A,C,E),ring_subst_2(A,D),ring_subst_3(A,E).
great_rsd(A,B):- ring_subst_6(A,E),r_subst_2(B,C),ring_subst_5(B,F),x_subst(A,D,E).
great_rsd(A,B):- gt(E,F),r_subst_3(B,E),r_subst_3(B,C),ring_subst_2(A,D).
great_rsd(A,B):- ring_subst_2(A,C),x_subst(B,D,E),ring_subst_4(B,E),flex(C,F).
great_rsd(A,B):- ring_subst_3(A,F),r_subst_1(A,E),pi_doner(D,C),ring_subst_6(B,D).
great_rsd(A,B):- n_val(A,F),x_subst(B,F,C),ring_subst_6(A,E),x_subst(B,F,D).
great_rsd(A,B):- flex(D,C),ring_subst_4(B,D),ring_subst_2(B,E),r_subst_3(A,F).
great_rsd(A,B):- ring_substitutions(A,D),x_subst(B,E,F),ring_subst_6(A,C),ring_subst_6(B,F).
great_rsd(A,B):- alk_groups(B,F),gt(D,C),alk_groups(A,D),n_val(B,E).
great_rsd(A,B):- h_acceptor(F,C),r_subst_1(A,E),ring_subst_2(B,F),ring_subst_6(A,D).
great_rsd(A,B):- ring_subst_4(A,D),r_subst_3(A,E),x_subst(A,E,C),r_subst_1(B,F).
great_rsd(A,B):- x_subst(A,D,C),ring_subst_4(B,C),ring_subst_2(A,E),ring_subst_3(B,C).
great_rsd(A,B):- alk_groups(B,C),x_subst(A,E,F),r_subst_3(A,C),alk_groups(B,D).
great_rsd(A,B):- n_val(A,F),n_val(B,D),polarisable(E,C),ring_subst_3(A,E).
great_rsd(A,B):- ring_subst_2(B,E),ring_subst_6(A,E),r_subst_1(B,C),ring_subst_4(B,D).
great_rsd(A,B):- n_val(A,D),polarisable(E,F),r_subst_1(B,C),ring_subst_2(A,E).
great_rsd(A,B):- size(F,D),r_subst_3(B,E),ring_subst_2(B,F),x_subst(A,E,C).
great_rsd(A,B):- x_subst(B,E,D),ring_subst_2(B,D),ring_subst_4(A,C),ring_subst_5(B,C).
great_rsd(A,B):- pi_doner(C,E),ring_subst_5(B,F),polar(F,D),ring_subst_6(A,C).
great_rsd(A,B):- pi_doner(F,E),ring_subst_4(B,F),r_subst_1(B,C),ring_subst_6(A,D).
great_rsd(A,B):- r_subst_2(B,D),ring_subst_6(B,E),ring_subst_5(A,F),flex(F,C).
great_rsd(A,B):- ring_subst_5(B,D),pi_acceptor(D,F),x_subst(A,C,D),ring_subst_2(A,E).
great_rsd(A,B):- ring_subst_6(B,C),alk_groups(B,D),r_subst_2(A,E),polarisable(C,F).
great_rsd(A,B):- x_subst(B,F,E),ring_subst_2(B,C),pi_doner(C,D),r_subst_3(A,F).
great_rsd(A,B):- r_subst_2(A,C),flex(D,E),ring_subst_5(B,F),ring_subst_5(A,D).
great_rsd(A,B):- h_acceptor(C,E),ring_subst_2(A,D),ring_subst_2(B,F),ring_subst_3(B,C).
great_rsd(A,B):- n_val(B,F),polar(D,E),x_subst(A,C,D),n_val(B,C).
great_rsd(A,B):- x_subst(A,F,E),ring_subst_6(B,E),ring_subst_2(B,D),r_subst_1(B,C).
great_rsd(A,B):- ring_subst_6(B,D),ring_subst_6(A,E),flex(E,F),x_subst(A,C,D).
great_rsd(A,B):- polarisable(E,C),ring_subst_4(A,F),ring_subst_4(B,F),x_subst(B,D,E).
great_rsd(A,B):- ring_subst_3(A,C),flex(E,D),h_acceptor(C,F),ring_subst_2(B,E).
great_rsd(A,B):- x_subst(B,E,D),h_doner(D,C),gt(F,E),x_subst(A,F,D).
great_rsd(A,B):- r_subst_2(B,E),ring_subst_3(A,D),polar(D,C),ring_subst_6(A,D).
great_rsd(A,B):- ring_subst_2(A,C),ring_subst_6(B,E),flex(E,D),ring_subst_2(B,C).
great_rsd(A,B):- alk_groups(B,C),n_val(A,F),r_subst_2(A,E),gt(F,D).
great_rsd(A,B):- r_subst_1(B,D),ring_subst_4(A,F),ring_subst_2(B,E),flex(E,C).
great_rsd(A,B):- ring_subst_3(A,F),ring_subst_6(A,E),r_subst_3(B,C),pi_acceptor(F,D).
great_rsd(A,B):- size(D,E),ring_subst_5(B,C),r_subst_2(B,F),ring_subst_6(A,D).
great_rsd(A,B):- x_subst(A,F,E),ring_subst_2(A,C),r_subst_3(B,D),ring_subst_6(A,C).
great_rsd(A,B):- r_subst_2(B,D),alk_groups(B,F),size(E,C),ring_subst_4(A,E).
great_rsd(A,B):- ring_subst_3(B,C),ring_subst_3(A,D),ring_subst_4(A,E),r_subst_3(A,F).
great_rsd(A,B):- ring_subst_4(A,D),ring_subst_2(B,D),r_subst_3(A,E),x_subst(A,C,D).
great_rsd(A,B):- x_subst(A,C,E),n_val(B,D),alk_groups(A,D),alk_groups(B,C).
great_rsd(A,B):- alk_groups(A,E),ring_subst_2(B,D),ring_subst_4(B,C),flex(C,F).
great_rsd(A,B):- x_subst(A,F,E),alk_groups(B,C),ring_subst_2(B,E),r_subst_1(B,D).
great_rsd(A,B):- r_subst_2(B,C),n_val(A,D),alk_groups(A,D),gt(D,E).
great_rsd(A,B):- x_subst(B,F,E),x_subst(A,C,E),ring_subst_6(A,E),x_subst(B,D,E).
great_rsd(A,B):- ring_subst_2(A,C),h_doner(C,D),r_subst_1(B,E),ring_subst_5(B,F).
great_rsd(A,B):- size(D,E),polar(D,C),x_subst(B,F,D),ring_subst_6(A,D).
great_rsd(A,B):- x_subst(B,E,D),ring_subst_6(B,C),ring_subst_5(B,C),n_val(A,E).
great_rsd(A,B):- ring_substitutions(A,E),gt(E,D),ring_subst_6(A,F),ring_subst_3(B,C).
great_rsd(A,B):- x_subst(B,F,E),ring_subst_5(A,C),x_subst(B,D,E).
great_rsd(A,B):- ring_subst_3(A,D),pi_acceptor(E,F),ring_subst_4(B,E),great_pi_acc(F,C).
great_rsd(A,B):- n_val(B,F),ring_subst_4(A,E),sigma(E,D),ring_subst_3(B,C).
great_rsd(A,B):- ring_subst_3(B,F),ring_subst_3(B,D),ring_subst_6(A,C),sigma(D,E).
great_rsd(A,B):- x_subst(A,C,E),ring_subst_2(B,D),ring_subst_5(B,D),r_subst_1(B,F).
great_rsd(A,B):- ring_substitutions(A,E),x_subst(B,C,D),ring_subst_3(A,D),ring_subst_3(A,F).
great_rsd(A,B):- r_subst_3(B,D),x_subst(B,D,C),ring_subst_4(A,E),x_subst(B,D,E).
great_rsd(A,B):- ring_subst_4(A,D),sigma(D,F),ring_subst_2(B,E),pi_acceptor(D,C).
great_rsd(A,B):- ring_substitutions(A,D),ring_subst_6(A,E),sigma(E,C),ring_subst_2(B,F).
great_rsd(A,B):- ring_subst_3(B,D),polar(D,E),ring_subst_5(A,F),ring_subst_2(B,C).
great_rsd(A,B):- ring_subst_3(A,F),sigma(D,E),ring_subst_4(B,D),polar(D,C).
great_rsd(A,B):- x_subst(A,D,C),r_subst_1(B,E),alk_groups(B,F),r_subst_1(A,E).
great_rsd(A,B):- polarisable(E,C),ring_subst_2(B,D),ring_subst_6(A,E),ring_subst_6(A,F).
great_rsd(A,B):- ring_subst_4(B,D),polarisable(D,E),r_subst_3(B,F),ring_substitutions(A,C).
great_rsd(A,B):- ring_subst_2(A,F),great_pi_acc(C,D),ring_subst_2(B,E),pi_acceptor(E,C).
great_rsd(A,B):- n_val(A,C),pi_doner(F,E),n_val(A,D),ring_subst_6(B,F).
great_rsd(A,B):- ring_subst_5(A,E),n_val(A,D),ring_subst_2(B,C).
