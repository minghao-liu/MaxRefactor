great(A,B):- r_subst_3(B,C),r_subst_3(A,F),gt(C,E),n_val(A,D).
great(A,B):- r_subst_1(B,E),ring_subst_3(A,C),ring_subst_2(B,D),ring_subst_4(B,C).
great(A,B):- ring_subst_2(B,C),ring_subst_4(A,C),x_subst(A,E,D),ring_subst_2(A,D).
great(A,B):- x_subst(B,D,C),gt(D,E),ring_subst_3(A,C),ring_subst_2(A,F).
great(A,B):- ring_subst_6(B,E),ring_subst_6(A,C),n_val(A,F),h_acceptor(E,D).
great(A,B):- ring_subst_2(A,E),ring_subst_5(B,C),h_doner(E,F),ring_subst_6(A,D).
great(A,B):- ring_substitutions(A,E),ring_subst_2(B,C),alk_groups(A,D),ring_subst_6(A,F).
great(A,B):- size(C,F),ring_substitutions(A,E),ring_subst_3(A,C),ring_subst_2(B,D).
great(A,B):- n_val(B,E),x_subst(A,D,F),x_subst(A,D,C).
great(A,B):- ring_subst_2(B,F),alk_groups(A,D),polarisable(F,C),r_subst_3(A,E).
great(A,B):- x_subst(B,C,E),r_subst_3(B,F),ring_subst_2(A,E),ring_subst_4(A,D).
great(A,B):- alk_groups(B,C),flex(D,E),ring_subst_5(A,F),ring_subst_3(B,D).
great(A,B):- ring_substitutions(B,E),x_subst(B,D,C),gt(D,F),n_val(A,D).
great(A,B):- ring_subst_6(B,C),ring_subst_5(B,C),ring_subst_5(B,D),ring_subst_5(A,D).
great(A,B):- x_subst(B,D,C),ring_subst_4(A,E),ring_subst_6(A,F),x_subst(B,D,F).
great(A,B):- ring_substitutions(B,E),alk_groups(B,F),n_val(B,C),alk_groups(A,D).
great(A,B):- alk_groups(B,C),x_subst(A,C,D),r_subst_1(A,E),ring_subst_4(A,F).
great(A,B):- x_subst(A,E,C),ring_subst_5(A,C),x_subst(A,D,C),ring_substitutions(B,D).
great(A,B):- ring_substitutions(B,E),x_subst(B,D,C),n_val(A,D),r_subst_3(A,E).
great(A,B):- r_subst_2(B,E),ring_subst_6(A,D),x_subst(A,F,C),ring_subst_4(B,C).
great(A,B):- h_acceptor(C,D),x_subst(A,E,C),ring_subst_5(A,F),r_subst_3(B,E).
great(A,B):- n_val(A,E),r_subst_3(A,C),r_subst_1(B,F),ring_subst_2(A,D).
great(A,B):- r_subst_3(A,C),flex(F,E),ring_subst_3(B,D),ring_subst_5(B,F).
great(A,B):- ring_subst_3(B,E),polarisable(E,C),ring_subst_3(A,F),ring_subst_6(A,D).
great(A,B):- ring_subst_2(B,E),x_subst(A,D,F),ring_subst_6(A,C),ring_subst_6(B,E).
great(A,B):- x_subst(A,D,E),ring_subst_3(A,E),x_subst(A,F,C),ring_substitutions(B,D).
great(A,B):- alk_groups(B,C),x_subst(A,C,D),h_acceptor(D,F),ring_subst_5(B,E).
great(A,B):- ring_subst_6(B,C),r_subst_2(B,E),x_subst(A,D,F),ring_subst_5(A,F).
great(A,B):- r_subst_2(B,C),alk_groups(A,D),ring_subst_3(A,F),x_subst(A,E,F).
great(A,B):- x_subst(B,D,C),ring_subst_5(A,C),pi_doner(C,E),n_val(B,D).
great(A,B):- ring_subst_3(A,E),ring_subst_4(B,C),polarisable(E,F),ring_subst_5(A,D).
great(A,B):- ring_substitutions(A,E),ring_subst_4(B,C),ring_subst_5(A,C),r_subst_3(A,D).
great(A,B):- r_subst_3(B,F),ring_substitutions(B,C),gt(D,E),ring_substitutions(A,D).
great(A,B):- ring_subst_4(B,E),r_subst_1(B,C),polarisable(E,F),n_val(A,D).
great(A,B):- ring_substitutions(B,E),x_subst(B,D,C),ring_subst_5(A,C),x_subst(A,F,C).
great(A,B):- ring_subst_3(A,E),ring_subst_3(B,C),ring_subst_4(B,D),r_subst_2(A,F).
great(A,B):- ring_subst_2(B,F),size(F,E),x_subst(A,D,C),x_subst(B,D,F).
great(A,B):- ring_subst_3(B,C),ring_subst_5(A,C),polarisable(F,D),x_subst(A,E,F).
great(A,B):- ring_subst_4(B,E),polarisable(E,C),x_subst(A,F,E),ring_subst_2(A,D).
great(A,B):- size(C,E),ring_subst_6(A,C),ring_subst_3(B,D),ring_subst_3(A,D).
great(A,B):- ring_subst_2(A,E),ring_subst_3(B,C),h_doner(E,F),x_subst(A,D,C).
great(A,B):- flex(C,E),pi_acceptor(F,D),ring_subst_6(A,C),ring_subst_5(B,F).
great(A,B):- pi_doner(E,C),ring_subst_5(A,E),ring_subst_4(B,F),n_val(B,D).
great(A,B):- flex(F,C),ring_subst_4(B,F),great_flex(C,D),n_val(A,E).
great(A,B):- ring_subst_6(B,E),flex(E,F),ring_subst_3(A,C),x_subst(A,D,C).
great(A,B):- ring_subst_3(A,E),ring_substitutions(B,C),ring_subst_3(A,F),r_subst_2(B,D).
great(A,B):- pi_acceptor(D,C),r_subst_1(A,E),ring_subst_2(B,D),r_subst_1(A,F).
great(A,B):- ring_subst_2(A,F),size(E,D),r_subst_1(B,C),ring_subst_2(B,E).
great(A,B):- x_subst(A,C,D),ring_subst_2(B,F),polarisable(D,E),ring_subst_2(B,D).
great(A,B):- ring_substitutions(B,E),ring_subst_2(B,C),x_subst(A,D,F),r_subst_3(B,E).
great(A,B):- ring_substitutions(B,E),alk_groups(A,D),sigma(F,C),ring_subst_5(B,F).
great(A,B):- ring_subst_4(A,E),ring_subst_5(B,C),ring_subst_2(A,C),ring_substitutions(B,D).
great(A,B):- ring_subst_4(B,F),h_acceptor(F,D),great_h_acc(D,C),alk_groups(A,E).
great(A,B):- ring_subst_3(B,E),r_subst_3(A,C),ring_subst_3(A,F),x_subst(B,C,D).
great(A,B):- ring_subst_2(B,E),ring_subst_5(A,C),polar(E,D),ring_subst_5(B,F).
great(A,B):- x_subst(A,D,E),ring_subst_4(B,E),x_subst(A,F,C),ring_subst_5(B,E).
great(A,B):- ring_subst_3(A,E),n_val(B,C),x_subst(A,D,F),ring_substitutions(A,C).
great(A,B):- x_subst(B,E,D),pi_doner(C,F),ring_subst_6(A,C),pi_doner(D,F).
great(A,B):- n_val(A,E),ring_subst_6(A,C),h_doner(F,D),ring_subst_5(B,F).
great(A,B):- ring_subst_2(B,D),ring_subst_5(A,E),r_subst_3(A,F),ring_substitutions(A,C).
great(A,B):- r_subst_3(A,C),alk_groups(A,C),h_doner(D,E),ring_subst_3(B,D).
great(A,B):- n_val(A,E),ring_subst_2(A,C),x_subst(B,E,F),ring_subst_6(A,D).
great(A,B):- ring_substitutions(B,E),ring_subst_2(B,F),r_subst_2(A,C),ring_subst_5(A,D).
great(A,B):- ring_subst_3(B,C),x_subst(A,E,D),r_subst_2(B,F),alk_groups(A,E).
great(A,B):- r_subst_3(B,C),ring_subst_3(A,E),ring_subst_6(A,E),x_subst(B,D,F).
great(A,B):- alk_groups(A,F),n_val(A,F),x_subst(B,C,D),h_acceptor(D,E).
great(A,B):- ring_subst_4(A,E),ring_subst_6(A,F),ring_subst_2(B,D),flex(D,C).
great(A,B):- gt(C,E),ring_subst_5(A,F),ring_subst_3(A,F),x_subst(B,C,D).
great(A,B):- size(E,C),r_subst_3(B,F),ring_subst_5(B,E),ring_subst_3(A,D).
great(A,B):- n_val(B,E),x_subst(A,E,C),ring_subst_5(A,D),r_subst_3(B,E).
great(A,B):- x_subst(A,D,E),ring_subst_2(B,C),ring_subst_2(B,F),ring_subst_2(A,F).
great(A,B):- ring_subst_6(B,E),ring_subst_3(B,C),pi_acceptor(E,F),n_val(A,D).
great(A,B):- x_subst(A,D,E),r_subst_3(B,D),ring_substitutions(A,C),ring_substitutions(B,D).
great(A,B):- n_val(A,F),h_acceptor(D,C),x_subst(A,E,D),ring_subst_5(B,D).
great(A,B):- ring_subst_3(B,E),ring_subst_3(A,F),r_subst_1(A,C),r_subst_1(B,D).
great(A,B):- ring_subst_4(B,E),alk_groups(A,C),polarisable(E,F),sigma(E,D).
great(A,B):- great_pi_don(D,E),pi_doner(F,D),r_subst_2(B,C),ring_subst_3(A,F).
great(A,B):- x_subst(A,C,D),size(D,E),ring_subst_6(B,D),r_subst_1(A,F).
great(A,B):- great_pi_acc(D,E),ring_subst_6(B,C),ring_subst_3(A,C),pi_acceptor(C,D).
great(A,B):- ring_subst_2(B,E),ring_subst_4(A,C),ring_subst_3(B,D),polarisable(E,F).
great(A,B):- r_subst_2(A,D),x_subst(A,E,C),ring_subst_2(B,C),ring_subst_4(B,F).
great(A,B):- ring_subst_6(A,E),x_subst(A,C,E),ring_subst_2(A,D),x_subst(B,F,E).
great(A,B):- ring_subst_6(B,C),alk_groups(B,D),ring_subst_4(A,F),r_subst_3(B,E).
great(A,B):- ring_subst_2(A,E),ring_subst_2(B,C),ring_subst_4(B,D),sigma(C,F).
great(A,B):- h_doner(F,E),ring_subst_6(B,C),r_subst_3(A,D),ring_subst_3(A,F).
great(A,B):- h_acceptor(F,C),x_subst(B,E,F),r_subst_3(A,D),r_subst_3(A,E).
great(A,B):- x_subst(A,E,C),alk_groups(B,F),gt(E,F),ring_subst_5(A,D).
great(A,B):- r_subst_3(B,C),n_val(B,E),x_subst(A,E,D),ring_subst_5(A,D).
great(A,B):- x_subst(B,E,D),x_subst(A,C,D),ring_subst_6(B,D),ring_substitutions(B,E).
great(A,B):- r_subst_3(B,C),n_val(A,C),gt(C,D),ring_substitutions(B,D).
great(A,B):- alk_groups(B,C),x_subst(A,F,E),ring_subst_5(B,E),pi_acceptor(E,D).
great(A,B):- great_sigma(E,F),ring_subst_5(B,D),sigma(D,E),r_subst_1(A,C).
great(A,B):- r_subst_3(B,C),n_val(B,C),polarisable(D,E),ring_subst_5(A,D).
great(A,B):- ring_subst_3(B,C),n_val(A,F),ring_subst_2(B,D),r_subst_3(A,E).
great(A,B):- ring_subst_2(B,E),polarisable(E,D),gt(C,F),n_val(A,C).
great(A,B):- ring_subst_6(A,F),x_subst(B,C,F),x_subst(A,C,E),pi_doner(F,D).
great(A,B):- n_val(B,C),size(D,E),ring_subst_4(B,D),ring_subst_6(A,D).
great(A,B):- x_subst(A,D,E),ring_subst_2(A,F),x_subst(B,C,E),n_val(A,C).
great(A,B):- ring_subst_6(A,C),r_subst_3(B,D),r_subst_1(B,F),r_subst_3(A,E).
great(A,B):- ring_subst_2(A,E),ring_subst_5(B,C),h_acceptor(E,D),ring_subst_4(A,E).
great(A,B):- ring_subst_2(A,E),ring_subst_3(B,C),polar(E,F),ring_subst_6(A,D).
great(A,B):- ring_subst_4(A,E),flex(E,C),x_subst(A,F,E),x_subst(B,D,E).
great(A,B):- ring_subst_3(B,E),x_subst(A,C,E),ring_subst_5(B,D),ring_subst_3(A,D).
great(A,B):- x_subst(B,F,C),ring_substitutions(A,E),n_val(A,D),r_subst_3(A,E).
great(A,B):- ring_subst_3(A,E),r_subst_1(A,C),r_subst_1(B,F),r_subst_2(B,D).
great(A,B):- x_subst(B,D,C),x_subst(A,E,C),ring_subst_6(B,C),r_subst_2(A,F).
great(A,B):- polar(D,C),x_subst(A,F,E),ring_substitutions(A,F),ring_subst_2(B,D).
great(A,B):- ring_subst_6(A,E),polarisable(D,C),ring_subst_2(A,D),ring_subst_5(B,F).
great(A,B):- polar(D,E),r_subst_1(B,C),ring_subst_3(B,D),r_subst_2(A,F).
great(A,B):- flex(C,D),n_val(B,F),ring_subst_3(B,C),r_subst_2(A,E).
great(A,B):- n_val(A,E),ring_subst_6(A,C),ring_subst_4(B,D),r_subst_1(A,F).
great(A,B):- ring_subst_3(A,E),h_acceptor(E,C),polarisable(E,D),r_subst_2(B,F).
great(A,B):- ring_substitutions(A,E),ring_subst_4(B,C),alk_groups(B,D),ring_subst_6(A,C).
great(A,B):- x_subst(A,F,D),ring_subst_2(B,C),polarisable(C,E),ring_subst_3(A,D).
great(A,B):- ring_substitutions(B,C),ring_subst_6(A,F),ring_subst_6(B,D),pi_doner(F,E).
great(A,B):- alk_groups(B,C),gt(E,C),x_subst(B,D,F),x_subst(A,E,F).
great(A,B):- ring_substitutions(B,E),ring_subst_2(B,D),r_subst_1(A,C),ring_subst_5(A,D).
great(A,B):- r_subst_3(A,C),alk_groups(B,D),gt(C,F),r_subst_3(A,E).
great(A,B):- x_subst(A,D,E),ring_subst_3(A,E),ring_subst_4(B,C),ring_subst_2(B,F).
great(A,B):- n_val(A,E),gt(C,E),n_val(A,C),ring_subst_2(B,D).
great(A,B):- r_subst_3(A,C),ring_subst_3(B,F),ring_subst_3(A,E),r_subst_1(B,D).
great(A,B):- r_subst_2(B,E),ring_subst_4(A,C),pi_acceptor(C,F),x_subst(A,D,C).
great(A,B):- polarisable(D,C),x_subst(A,F,E),n_val(A,F),ring_subst_6(B,D).
great(A,B):- ring_subst_4(B,C),ring_subst_5(A,F),flex(F,D),alk_groups(A,E).
great(A,B):- ring_subst_3(A,C),x_subst(A,D,F),pi_doner(F,E),ring_subst_2(B,F).
great(A,B):- r_subst_3(A,C),r_subst_2(B,E),x_subst(A,D,F),ring_subst_4(A,F).
great(A,B):- gt(F,E),alk_groups(B,D),r_subst_1(B,C),n_val(A,F).
great(A,B):- x_subst(B,C,E),x_subst(A,C,D),sigma(D,F),ring_subst_4(A,D).
great(A,B):- pi_acceptor(D,E),ring_subst_6(B,F),ring_subst_6(A,F),x_subst(B,C,D).
great(A,B):- pi_acceptor(C,E),ring_subst_5(B,C),alk_groups(A,D).
great(A,B):- pi_acceptor(D,E),r_subst_3(B,F),ring_subst_6(B,C),ring_subst_4(A,D).
great(A,B):- ring_substitutions(B,E),r_subst_3(A,C),x_subst(A,E,D),r_subst_1(A,F).
great(A,B):- r_subst_1(A,E),x_subst(B,C,D),ring_subst_2(B,F),ring_subst_6(B,D).
great(A,B):- x_subst(B,C,E),ring_subst_6(A,E),pi_acceptor(E,F),gt(C,D).
great(A,B):- r_subst_1(A,D),ring_subst_5(A,E),ring_subst_3(B,C),ring_subst_3(B,E).
great(A,B):- ring_subst_6(B,E),ring_subst_2(B,F),r_subst_1(B,C),ring_subst_5(A,D).
great(A,B):- ring_subst_4(B,F),ring_subst_2(A,C),x_subst(A,D,F),ring_subst_6(A,E).
great(A,B):- x_subst(B,C,E),flex(E,F),r_subst_1(A,D).
great(A,B):- gt(D,E),ring_subst_3(A,C),ring_subst_6(A,C),n_val(B,D).
great(A,B):- x_subst(A,E,C),ring_subst_4(B,F),ring_subst_4(A,F),r_subst_2(B,D).
great(A,B):- r_subst_1(A,D),n_val(B,C),ring_subst_3(B,F),x_subst(A,C,E).
great(A,B):- ring_substitutions(B,E),gt(E,C),ring_subst_2(A,F),ring_subst_2(A,D).
great(A,B):- n_val(B,E),ring_subst_5(B,C),pi_acceptor(C,F),n_val(A,D).
great(A,B):- ring_subst_4(B,E),polar(D,C),ring_subst_4(A,F),ring_subst_6(A,D).
great(A,B):- ring_subst_6(B,C),r_subst_2(B,E),ring_subst_3(A,F),r_subst_2(B,D).
great(A,B):- x_subst(B,C,E),ring_subst_5(A,F),ring_subst_2(B,E),r_subst_1(B,D).
great(A,B):- alk_groups(B,D),ring_subst_5(A,F),alk_groups(B,E),polar(F,C).
great(A,B):- ring_subst_2(B,C),ring_subst_4(B,F),ring_substitutions(A,D),alk_groups(B,E).
great(A,B):- ring_subst_4(B,E),polar(D,C),ring_subst_4(A,D).
great(A,B):- x_subst(A,D,E),x_subst(A,D,F),polar(E,C),ring_subst_6(B,E).
great(A,B):- alk_groups(B,C),ring_subst_4(A,F),ring_subst_2(B,E),pi_acceptor(E,D).
great(A,B):- x_subst(B,C,E),ring_subst_3(B,E),x_subst(B,D,E),ring_substitutions(A,D).
great(A,B):- ring_subst_6(B,C),ring_subst_5(A,C),ring_subst_6(B,D).
great(A,B):- ring_subst_6(B,C),ring_subst_5(A,C),x_subst(A,E,D),ring_subst_3(B,D).
great(A,B):- r_subst_3(A,C),ring_substitutions(B,F),x_subst(A,C,E),r_subst_2(B,D).
great(A,B):- x_subst(B,C,E),ring_subst_3(A,E),r_subst_3(B,D),ring_subst_3(A,F).
great(A,B):- n_val(B,E),x_subst(A,C,D),ring_subst_2(B,F),x_subst(A,C,F).
great(A,B):- alk_groups(A,C),ring_substitutions(B,F),x_subst(A,C,E),n_val(B,D).
great(A,B):- r_subst_1(A,D),n_val(A,C),ring_substitutions(B,E),ring_subst_5(B,F).
great(A,B):- x_subst(A,D,E),ring_subst_4(B,C),ring_subst_2(A,C),sigma(E,F).
