great_rsd(A,B):- n_val(A,C),r_subst_2(A,D),ring_subst_5(A,F),n_val(B,E).
great_rsd(A,B):- ring_substitutions(A,E),x_subst(B,F,C),x_subst(A,E,C),ring_subst_6(A,D).
great_rsd(A,B):- sigma(C,E),ring_subst_5(A,C),ring_subst_5(A,D),ring_subst_2(B,C).
great_rsd(A,B):- x_subst(A,C,E),ring_subst_5(B,E),pi_acceptor(E,F),x_subst(A,C,D).
great_rsd(A,B):- n_val(A,F),sigma(E,C),ring_subst_3(B,E),ring_subst_5(B,D).
great_rsd(A,B):- size(E,F),gt(C,D),ring_subst_3(B,E),r_subst_3(A,C).
great_rsd(A,B):- r_subst_2(A,C),ring_subst_3(A,E),ring_substitutions(B,D),ring_subst_2(A,E).
great_rsd(A,B):- x_subst(B,D,C),ring_subst_5(B,C),polar(C,F),ring_subst_2(A,E).
great_rsd(A,B):- ring_subst_4(B,D),h_acceptor(E,F),ring_subst_4(A,E),ring_subst_3(B,C).
great_rsd(A,B):- alk_groups(B,C),ring_subst_2(B,D),r_subst_1(A,E),ring_subst_4(A,F).
great_rsd(A,B):- x_subst(A,F,C),polar(C,D),ring_subst_4(A,E),ring_substitutions(B,F).
great_rsd(A,B):- ring_subst_2(B,D),alk_groups(A,F),n_val(B,E),ring_subst_3(B,C).
great_rsd(A,B):- ring_subst_3(B,D),polar(F,E),ring_subst_2(B,F),r_subst_3(A,C).
great_rsd(A,B):- n_val(B,F),ring_subst_5(B,E),ring_subst_6(A,C),alk_groups(A,D).
great_rsd(A,B):- n_val(A,D),ring_subst_4(B,F),n_val(B,E),ring_subst_2(B,C).
great_rsd(A,B):- n_val(A,D),ring_subst_5(A,C),size(C,E),ring_subst_3(B,C).
great_rsd(A,B):- flex(D,C),ring_subst_2(A,D),ring_subst_3(A,E),r_subst_2(B,F).
great_rsd(A,B):- alk_groups(A,E),pi_acceptor(C,F),alk_groups(A,D),ring_subst_2(B,C).
great_rsd(A,B):- x_subst(B,C,D),n_val(A,E),x_subst(A,E,F),r_subst_3(A,C).
great_rsd(A,B):- n_val(A,C),ring_subst_5(B,E),n_val(A,F),r_subst_2(A,D).
great_rsd(A,B):- x_subst(B,E,D),ring_subst_2(A,D),ring_subst_6(A,C),ring_subst_6(A,D).
great_rsd(A,B):- ring_substitutions(A,D),x_subst(A,F,C),ring_subst_3(B,E).
great_rsd(A,B):- x_subst(B,E,D),ring_subst_3(B,D),x_subst(A,C,D),ring_substitutions(A,C).
great_rsd(A,B):- x_subst(A,D,F),ring_subst_6(B,E),ring_subst_5(A,C),ring_subst_2(B,C).
great_rsd(A,B):- x_subst(B,E,D),ring_subst_4(B,C),ring_subst_5(A,F),ring_subst_5(B,D).
great_rsd(A,B):- x_subst(B,E,D),h_acceptor(D,F),ring_subst_3(A,D),r_subst_3(A,C).
great_rsd(A,B):- x_subst(A,C,E),ring_subst_4(A,E),ring_subst_3(B,E),size(E,D).
great_rsd(A,B):- pi_acceptor(D,E),x_subst(B,C,D),x_subst(A,C,F),ring_subst_5(A,D).
great_rsd(A,B):- r_subst_1(B,E),x_subst(A,C,F),r_subst_1(A,D),ring_subst_4(B,F).
great_rsd(A,B):- r_subst_3(B,D),x_subst(A,D,C),pi_acceptor(C,E),ring_subst_3(A,C).
great_rsd(A,B):- ring_subst_5(B,D),ring_subst_4(B,E),x_subst(A,C,D),ring_substitutions(B,F).
great_rsd(A,B):- r_subst_1(B,E),x_subst(B,F,D),r_subst_3(B,F),ring_substitutions(A,C).
great_rsd(A,B):- ring_subst_3(A,F),ring_subst_5(B,E),great_flex(C,D),flex(E,C).
great_rsd(A,B):- ring_subst_3(B,D),h_acceptor(F,C),ring_subst_5(A,F),size(F,E).
great_rsd(A,B):- ring_subst_4(B,D),alk_groups(A,C),ring_subst_4(A,E),size(E,F).
great_rsd(A,B):- ring_subst_6(B,C),ring_subst_6(A,F),great_pi_acc(D,E),pi_acceptor(F,D).
great_rsd(A,B):- x_subst(A,F,E),ring_subst_6(B,D),r_subst_2(B,C),ring_substitutions(A,F).
great_rsd(A,B):- r_subst_2(B,D),gt(C,F),gt(C,E),n_val(A,C).
great_rsd(A,B):- r_subst_3(A,E),alk_groups(B,D),n_val(A,D),ring_subst_6(A,C).
great_rsd(A,B):- polarisable(F,C),r_subst_3(B,E),ring_subst_6(B,F),n_val(A,D).
great_rsd(A,B):- ring_subst_6(B,E),ring_subst_2(A,D),r_subst_1(B,C),ring_subst_3(A,D).
great_rsd(A,B):- polar(C,E),n_val(A,D),great_polar(E,F),ring_subst_2(B,C).
great_rsd(A,B):- ring_subst_4(B,D),polarisable(D,E),ring_subst_4(B,C),ring_subst_5(A,F).
great_rsd(A,B):- ring_subst_5(A,E),ring_subst_6(B,C),ring_subst_6(A,D),ring_subst_3(B,C).
great_rsd(A,B):- r_subst_2(B,E),x_subst(A,C,F),polarisable(F,D).
great_rsd(A,B):- alk_groups(A,E),polarisable(C,D),r_subst_1(B,F),ring_subst_2(B,C).
great_rsd(A,B):- ring_subst_5(A,E),ring_subst_5(B,C),flex(E,F),h_acceptor(C,D).
great_rsd(A,B):- polar(D,E),ring_subst_4(B,F),r_subst_3(A,C),ring_subst_6(A,D).
great_rsd(A,B):- ring_substitutions(A,E),x_subst(B,D,C),h_acceptor(C,F),x_subst(B,E,C).
great_rsd(A,B):- ring_substitutions(B,C),sigma(E,F),alk_groups(A,D),ring_subst_2(A,E).
great_rsd(A,B):- h_acceptor(F,C),n_val(A,E),x_subst(A,E,F),alk_groups(B,D).
great_rsd(A,B):- ring_subst_2(B,E),ring_subst_4(A,F),polar(F,C),alk_groups(A,D).
great_rsd(A,B):- ring_subst_3(A,D),ring_subst_4(B,F),ring_subst_5(B,C),ring_subst_3(A,E).
great_rsd(A,B):- ring_substitutions(B,C),x_subst(A,F,D),n_val(A,C),n_val(B,E).
great_rsd(A,B):- ring_subst_3(B,F),r_subst_3(A,D),r_subst_3(A,E),ring_subst_6(A,C).
great_rsd(A,B):- ring_subst_3(A,F),ring_subst_4(A,C),x_subst(B,E,F),h_doner(F,D).
great_rsd(A,B):- r_subst_1(B,D),polar(E,F),ring_subst_6(A,C),ring_subst_4(B,E).
great_rsd(A,B):- ring_subst_2(A,C),sigma(D,E),ring_subst_5(B,F),ring_subst_5(A,D).
great_rsd(A,B):- x_subst(B,C,D),ring_subst_4(A,F),ring_subst_6(A,E),ring_subst_5(B,D).
great_rsd(A,B):- alk_groups(A,E),x_subst(B,C,D),alk_groups(A,C),ring_substitutions(A,F).
great_rsd(A,B):- x_subst(A,C,E),ring_subst_6(A,E),pi_acceptor(E,F),ring_subst_4(B,D).
great_rsd(A,B):- ring_subst_6(B,E),x_subst(A,C,F),r_subst_3(B,C),ring_subst_6(A,D).
great_rsd(A,B):- n_val(A,C),x_subst(A,D,E),r_subst_2(B,F),ring_substitutions(A,C).
great_rsd(A,B):- alk_groups(B,F),ring_subst_6(A,C),ring_substitutions(B,D),pi_acceptor(C,E).
great_rsd(A,B):- r_subst_2(B,D),ring_subst_3(A,F),alk_groups(A,C),r_subst_3(A,E).
great_rsd(A,B):- ring_subst_6(B,E),ring_subst_2(B,D),ring_subst_3(A,D),h_acceptor(D,C).
great_rsd(A,B):- r_subst_1(B,D),ring_subst_2(A,C),ring_subst_3(A,F),h_acceptor(C,E).
great_rsd(A,B):- ring_subst_3(A,C),ring_subst_4(A,C),ring_subst_2(B,D),r_subst_1(B,E).
great_rsd(A,B):- polar(E,C),r_subst_3(A,D),ring_subst_5(A,E),ring_subst_6(B,F).
great_rsd(A,B):- ring_subst_3(A,C),ring_subst_6(B,E),alk_groups(A,D),r_subst_3(B,F).
great_rsd(A,B):- ring_subst_3(B,E),h_acceptor(C,F),r_subst_1(A,D),ring_subst_2(B,C).
great_rsd(A,B):- x_subst(B,F,C),ring_subst_2(A,D),ring_subst_2(A,E),ring_subst_3(B,C).
great_rsd(A,B):- h_acceptor(F,D),r_subst_3(A,E),ring_subst_2(B,F),great_h_acc(D,C).
great_rsd(A,B):- flex(F,D),r_subst_1(A,C),ring_subst_2(B,F),great_flex(D,E).
great_rsd(A,B):- ring_subst_4(A,C),alk_groups(A,D),x_subst(A,D,E),r_subst_1(B,F).
great_rsd(A,B):- h_acceptor(C,F),ring_subst_2(B,D),ring_subst_4(A,C),pi_acceptor(C,E).
great_rsd(A,B):- gt(F,D),ring_subst_6(B,C),x_subst(A,E,C),r_subst_3(A,F).
great_rsd(A,B):- r_subst_3(B,D),gt(D,C),ring_subst_4(B,F),ring_subst_2(A,E).
great_rsd(A,B):- ring_subst_5(A,E),ring_subst_5(A,C),x_subst(B,D,E),ring_subst_6(B,F).
great_rsd(A,B):- gt(F,D),ring_subst_2(B,C),x_subst(A,D,E),r_subst_3(A,F).
great_rsd(A,B):- ring_subst_2(A,C),ring_subst_3(A,F),ring_subst_3(B,D),h_acceptor(C,E).
great_rsd(A,B):- r_subst_1(B,C),x_subst(A,E,F),alk_groups(A,D),ring_subst_6(B,F).
great_rsd(A,B):- ring_substitutions(B,E),x_subst(A,D,C),ring_subst_2(B,F),ring_subst_6(A,F).
great_rsd(A,B):- ring_subst_3(A,F),ring_subst_5(B,E),r_subst_1(A,D),n_val(B,C).
great_rsd(A,B):- r_subst_3(A,D),ring_subst_5(B,C),r_subst_1(A,E),r_subst_3(A,F).
great_rsd(A,B):- x_subst(B,F,E),size(D,C),ring_subst_2(B,D),ring_subst_3(A,D).
great_rsd(A,B):- r_subst_2(A,C),r_subst_1(B,E),ring_substitutions(A,F),ring_subst_6(A,D).
great_rsd(A,B):- ring_subst_6(A,E),ring_subst_6(B,C),pi_acceptor(D,F),ring_subst_5(A,D).
great_rsd(A,B):- polar(F,D),r_subst_2(A,E),ring_subst_4(B,C),ring_subst_4(B,F).
great_rsd(A,B):- ring_subst_5(A,D),polar(E,C),ring_subst_2(B,E),ring_substitutions(B,F).
great_rsd(A,B):- ring_subst_4(A,D),gt(F,E),r_subst_3(B,C),n_val(B,F).
great_rsd(A,B):- x_subst(A,C,E),x_subst(B,C,F),ring_subst_5(A,F),alk_groups(B,D).
great_rsd(A,B):- ring_subst_5(B,E),h_doner(E,D),ring_subst_6(B,C),ring_subst_5(A,C).
great_rsd(A,B):- size(D,E),alk_groups(B,C),r_subst_3(A,C),ring_subst_5(A,D).
great_rsd(A,B):- ring_subst_2(A,F),ring_subst_3(B,D),ring_subst_3(A,F),x_subst(B,E,C).
great_rsd(A,B):- x_subst(A,C,E),pi_doner(E,D),r_subst_3(B,C),r_subst_1(A,F).
great_rsd(A,B):- ring_subst_3(A,C),ring_subst_3(B,D),ring_subst_6(A,C),ring_subst_4(A,E).
great_rsd(A,B):- n_val(A,C),ring_substitutions(A,E),ring_subst_3(A,F),ring_subst_4(B,D).
great_rsd(A,B):- alk_groups(B,C),ring_subst_5(B,E),x_subst(A,D,E),ring_subst_2(B,E).
great_rsd(A,B):- ring_subst_2(A,C),ring_subst_2(B,D),ring_subst_3(A,E),ring_subst_5(A,D).
great_rsd(A,B):- ring_subst_3(B,F),n_val(A,C),x_subst(A,D,E),ring_subst_4(B,E).
great_rsd(A,B):- n_val(A,C),alk_groups(B,C),x_subst(B,C,D),ring_subst_6(A,D).
great_rsd(A,B):- h_doner(D,F),ring_subst_2(B,D),pi_doner(D,E),x_subst(A,C,D).
great_rsd(A,B):- ring_substitutions(B,D),r_subst_3(A,E),r_subst_3(B,C),r_subst_3(A,C).
great_rsd(A,B):- r_subst_3(B,E),ring_subst_6(A,C),r_subst_3(B,F),polarisable(C,D).
great_rsd(A,B):- alk_groups(B,F),r_subst_2(A,C),x_subst(B,D,E),ring_subst_4(B,E).
great_rsd(A,B):- n_val(B,D),r_subst_3(A,D),x_subst(A,F,C),ring_subst_3(A,E).
great_rsd(A,B):- ring_subst_3(A,F),ring_subst_3(B,D),ring_subst_6(B,C),h_acceptor(D,E).
great_rsd(A,B):- n_val(A,C),ring_subst_4(B,D),r_subst_1(B,E),x_subst(A,C,D).
great_rsd(A,B):- x_subst(B,C,D),x_subst(B,E,F),ring_subst_4(B,F),x_subst(A,C,D).
