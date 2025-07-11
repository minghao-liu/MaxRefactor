great_rsd(A,B):- ring_subst_5(A,C),alk_groups(B,D),alk_groups(A,D),ring_subst_3(B,E).
great_rsd(A,B):- ring_subst_2(B,D),ring_subst_5(B,C),pi_acceptor(D,F),x_subst(A,E,C).
great_rsd(A,B):- ring_subst_6(B,E),ring_subst_3(A,F),size(F,C),alk_groups(A,D).
great_rsd(A,B):- ring_subst_6(A,F),x_subst(A,D,E),ring_subst_5(A,F),ring_subst_2(B,C).
great_rsd(A,B):- gt(C,D),x_subst(A,C,E),x_subst(B,C,E),ring_subst_4(B,E).
great_rsd(A,B):- ring_subst_4(A,D),ring_substitutions(B,E),size(D,C),gt(E,F).
great_rsd(A,B):- ring_subst_6(B,D),r_subst_1(A,E),ring_substitutions(A,F),r_subst_3(A,C).
great_rsd(A,B):- ring_subst_2(A,C),ring_subst_2(B,E),h_acceptor(C,F),x_subst(B,D,E).
great_rsd(A,B):- x_subst(B,F,C),n_val(A,D),size(C,E).
great_rsd(A,B):- ring_subst_3(A,F),ring_subst_5(B,C),r_subst_2(A,E),ring_subst_5(B,D).
great_rsd(A,B):- ring_subst_3(B,D),ring_subst_5(B,F),x_subst(B,C,D),r_subst_2(A,E).
great_rsd(A,B):- ring_subst_6(A,E),pi_doner(E,D),ring_subst_2(B,F),r_subst_3(B,C).
great_rsd(A,B):- n_val(A,C),ring_subst_6(B,E),ring_subst_2(A,D),ring_substitutions(A,F).
great_rsd(A,B):- x_subst(A,E,D),ring_subst_2(B,D),ring_subst_2(B,F),ring_subst_2(B,C).
great_rsd(A,B):- ring_subst_2(A,C),n_val(B,D),size(C,F),ring_subst_3(A,E).
great_rsd(A,B):- ring_subst_5(B,E),ring_subst_4(A,F),ring_subst_4(A,E),x_subst(A,C,D).
great_rsd(A,B):- ring_subst_4(A,D),r_subst_2(B,E),x_subst(B,C,F),ring_subst_4(B,F).
great_rsd(A,B):- x_subst(B,F,E),n_val(A,F),ring_subst_4(A,D),size(D,C).
great_rsd(A,B):- alk_groups(A,E),alk_groups(B,C),ring_subst_3(B,D),n_val(A,F).
great_rsd(A,B):- ring_subst_3(A,F),polarisable(F,C),alk_groups(A,D),ring_subst_4(B,E).
great_rsd(A,B):- gt(C,E),ring_subst_2(A,F),x_subst(B,C,D),ring_subst_4(B,D).
great_rsd(A,B):- ring_subst_6(A,F),ring_subst_2(B,C),ring_substitutions(B,D),alk_groups(B,E).
great_rsd(A,B):- x_subst(A,C,E),ring_subst_5(B,E),x_subst(B,D,E),n_val(B,C).
great_rsd(A,B):- ring_subst_4(B,D),ring_subst_4(A,F),x_subst(B,E,F),x_subst(A,C,D).
great_rsd(A,B):- r_subst_1(B,D),n_val(A,F),ring_subst_4(A,C),flex(C,E).
great_rsd(A,B):- pi_doner(E,F),ring_subst_5(B,E),ring_subst_4(A,C),r_subst_1(A,D).
great_rsd(A,B):- ring_subst_3(A,C),ring_subst_2(B,D),size(D,F),ring_subst_3(B,E).
great_rsd(A,B):- ring_subst_4(A,D),gt(F,E),r_subst_3(B,F),ring_subst_2(B,C).
great_rsd(A,B):- x_subst(B,E,D),x_subst(A,E,D),x_subst(A,F,D),x_subst(A,C,D).
great_rsd(A,B):- r_subst_3(A,D),alk_groups(A,C),ring_subst_4(A,E),r_subst_3(B,C).
great_rsd(A,B):- great_h_don(D,F),h_doner(E,D),ring_subst_4(B,C),ring_subst_3(A,E).
great_rsd(A,B):- x_subst(A,D,F),x_subst(B,D,C),r_subst_1(A,E),ring_subst_4(A,F).
great_rsd(A,B):- ring_substitutions(A,D),ring_subst_5(B,E),ring_subst_5(A,C),size(E,F).
great_rsd(A,B):- alk_groups(A,E),x_subst(B,E,D),n_val(B,F),x_subst(A,C,D).
great_rsd(A,B):- ring_subst_4(A,D),x_subst(A,E,D),r_subst_1(B,F),ring_subst_3(B,C).
great_rsd(A,B):- r_subst_1(A,C),alk_groups(B,F),r_subst_3(B,E),gt(F,D).
great_rsd(A,B):- ring_subst_2(B,F),h_acceptor(D,E),pi_acceptor(D,C),ring_subst_6(A,D).
great_rsd(A,B):- n_val(A,D),ring_subst_6(B,C),sigma(C,F),size(C,E).
great_rsd(A,B):- sigma(D,F),x_subst(B,C,D),x_subst(B,C,E),ring_subst_3(A,E).
great_rsd(A,B):- ring_subst_6(B,D),ring_subst_2(B,F),r_subst_3(A,C),h_acceptor(D,E).
great_rsd(A,B):- x_subst(B,F,C),alk_groups(B,F),r_subst_1(A,D),size(C,E).
great_rsd(A,B):- x_subst(A,D,F),r_subst_3(B,D),r_subst_3(A,C),alk_groups(B,E).
great_rsd(A,B):- ring_subst_3(B,D),r_subst_1(A,C),alk_groups(B,F),polar(D,E).
great_rsd(A,B):- r_subst_2(B,D),ring_subst_3(A,F),ring_subst_4(A,C),r_subst_2(A,E).
great_rsd(A,B):- n_val(A,C),ring_subst_6(A,F),x_subst(B,D,E),ring_substitutions(A,C).
great_rsd(A,B):- ring_subst_3(A,C),sigma(C,E),ring_subst_6(A,C),ring_subst_6(B,D).
great_rsd(A,B):- h_acceptor(C,E),ring_subst_6(B,C),ring_subst_4(B,F),r_subst_1(A,D).
great_rsd(A,B):- r_subst_1(B,C),polar(F,E),ring_subst_6(B,F),alk_groups(A,D).
great_rsd(A,B):- polarisable(E,C),ring_subst_4(B,D),ring_subst_4(A,F),ring_subst_4(A,E).
great_rsd(A,B):- ring_subst_3(A,C),ring_subst_4(B,D),ring_subst_2(B,D),pi_doner(C,E).
great_rsd(A,B):- gt(D,E),n_val(A,D),gt(D,F),n_val(B,C).
great_rsd(A,B):- ring_subst_5(A,E),ring_subst_4(B,C),r_subst_1(A,D).
great_rsd(A,B):- x_subst(B,D,F),alk_groups(A,C),ring_subst_2(B,E),ring_subst_5(A,E).
great_rsd(A,B):- r_subst_1(B,D),ring_subst_6(A,E),ring_subst_6(A,C),size(C,F).
great_rsd(A,B):- gt(C,E),alk_groups(A,C),ring_subst_2(B,D),ring_subst_6(A,F).
great_rsd(A,B):- ring_subst_3(A,C),ring_substitutions(A,E),ring_subst_2(B,D),h_acceptor(C,F).
great_rsd(A,B):- ring_subst_5(B,E),ring_subst_4(A,F),n_val(B,C),ring_subst_6(A,D).
great_rsd(A,B):- r_subst_1(B,D),ring_subst_4(A,C),ring_subst_6(A,C),ring_subst_2(A,E).
great_rsd(A,B):- h_acceptor(D,E),r_subst_1(B,C),ring_subst_6(A,D).
great_rsd(A,B):- flex(C,D),x_subst(B,E,F),x_subst(A,E,C),ring_subst_3(B,C).
great_rsd(A,B):- ring_substitutions(B,C),alk_groups(B,D),r_subst_1(A,E),ring_substitutions(A,F).
great_rsd(A,B):- r_subst_2(B,D),flex(C,E),ring_subst_6(A,C),ring_subst_5(A,F).
great_rsd(A,B):- ring_subst_4(A,D),n_val(A,F),h_acceptor(D,C),ring_subst_3(B,E).
great_rsd(A,B):- ring_subst_3(A,C),polarisable(C,E),ring_subst_3(B,D),ring_subst_5(B,F).
great_rsd(A,B):- x_subst(B,E,D),ring_subst_2(B,D),ring_subst_3(A,F),alk_groups(B,C).
great_rsd(A,B):- r_subst_1(B,C),ring_subst_3(A,D),x_subst(B,F,D),ring_subst_5(A,E).
great_rsd(A,B):- ring_subst_2(A,C),ring_subst_6(B,E),n_val(B,D),sigma(E,F).
great_rsd(A,B):- ring_subst_5(B,E),r_subst_2(A,C),x_subst(B,F,D).
great_rsd(A,B):- h_doner(F,C),ring_substitutions(B,E),n_val(A,D),ring_subst_5(A,F).
great_rsd(A,B):- h_doner(F,C),n_val(A,D),ring_subst_4(B,F),n_val(A,E).
great_rsd(A,B):- ring_subst_2(A,C),ring_subst_5(B,E),x_subst(B,D,C),ring_subst_4(A,C).
great_rsd(A,B):- r_subst_2(B,D),ring_subst_5(A,C),alk_groups(B,F),r_subst_1(A,E).
great_rsd(A,B):- x_subst(B,D,F),x_subst(A,C,E),alk_groups(A,C),ring_subst_4(B,F).
great_rsd(A,B):- alk_groups(A,E),ring_subst_3(B,D),pi_doner(C,F),ring_subst_2(B,C).
great_rsd(A,B):- sigma(F,D),ring_subst_6(A,E),ring_subst_5(B,F),size(F,C).
great_rsd(A,B):- x_subst(A,F,C),ring_subst_6(A,C),n_val(B,E),polar(C,D).
great_rsd(A,B):- sigma(E,F),x_subst(B,D,C),ring_subst_6(A,C),ring_subst_6(A,E).
great_rsd(A,B):- great_h_acc(D,C),ring_subst_4(B,F),h_acceptor(F,D),n_val(A,E).
great_rsd(A,B):- ring_subst_5(B,E),polarisable(F,C),ring_subst_5(A,F),ring_subst_5(A,D).
great_rsd(A,B):- x_subst(A,E,F),r_subst_1(A,D),n_val(A,E),ring_subst_3(B,C).
great_rsd(A,B):- r_subst_3(A,D),ring_subst_6(A,E),r_subst_2(B,C),size(E,F).
great_rsd(A,B):- ring_subst_6(A,E),alk_groups(B,D),x_subst(B,D,E),r_subst_3(A,C).
great_rsd(A,B):- flex(F,D),sigma(F,C),x_subst(B,E,F),ring_subst_6(A,F).
great_rsd(A,B):- x_subst(A,D,F),ring_subst_4(A,C),flex(C,E),ring_subst_3(B,C).
great_rsd(A,B):- sigma(F,E),pi_doner(C,D),ring_subst_5(A,F),ring_subst_3(B,C).
great_rsd(A,B):- polar(E,F),alk_groups(B,D),ring_subst_4(A,E),flex(E,C).
great_rsd(A,B):- alk_groups(B,F),r_subst_1(A,D),ring_subst_4(B,E),ring_subst_3(B,C).
great_rsd(A,B):- ring_subst_4(B,D),ring_subst_5(B,D),x_subst(A,E,C),pi_doner(D,F).
great_rsd(A,B):- flex(C,D),ring_subst_6(B,C),ring_subst_3(A,E),ring_subst_4(B,E).
great_rsd(A,B):- ring_subst_3(A,F),r_subst_2(B,E),polarisable(F,C),ring_subst_5(A,D).
great_rsd(A,B):- ring_subst_3(B,F),pi_doner(C,E),x_subst(A,D,C),ring_subst_6(B,C).
great_rsd(A,B):- x_subst(B,E,D),r_subst_3(A,E),ring_subst_2(B,F),ring_subst_3(B,C).
great_rsd(A,B):- ring_subst_5(A,D),alk_groups(A,F),ring_subst_2(B,E),ring_substitutions(A,C).
great_rsd(A,B):- r_subst_2(B,D),ring_subst_4(A,F),ring_subst_3(B,E),ring_subst_2(B,C).
great_rsd(A,B):- x_subst(A,E,D),alk_groups(B,F),x_subst(A,C,D),ring_substitutions(A,C).
great_rsd(A,B):- alk_groups(A,E),size(F,D),ring_subst_2(B,F),h_doner(F,C).
great_rsd(A,B):- r_subst_1(B,D),ring_subst_2(A,F),gt(C,E),n_val(A,C).
great_rsd(A,B):- x_subst(A,D,F),ring_subst_2(A,C),x_subst(B,D,E),ring_subst_3(A,C).
great_rsd(A,B):- ring_subst_2(B,D),ring_subst_4(A,E),r_subst_3(A,C).
great_rsd(A,B):- ring_subst_2(A,F),pi_acceptor(C,E),r_subst_1(A,D),ring_subst_3(B,C).
