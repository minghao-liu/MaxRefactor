great(A,B):- ring_subst_4(B,C),ring_subst_4(B,F),x_subst(A,E,D),ring_subst_3(A,D).
great(A,B):- alk_groups(B,C),ring_subst_5(A,E),n_val(A,F),h_acceptor(E,D).
great(A,B):- ring_subst_2(B,E),flex(E,C),alk_groups(A,D),ring_substitutions(B,D).
great(A,B):- ring_subst_6(B,E),ring_subst_5(A,E),ring_subst_6(A,C),ring_subst_2(B,D).
great(A,B):- h_doner(F,E),r_subst_3(A,C),size(F,D),ring_subst_5(B,F).
great(A,B):- ring_subst_6(B,C),ring_subst_3(A,C),pi_acceptor(C,D),x_subst(A,E,F).
great(A,B):- pi_acceptor(D,E),ring_subst_6(B,C),ring_subst_3(B,D),x_subst(A,F,C).
great(A,B):- pi_acceptor(D,E),polarisable(C,F),ring_subst_3(A,C),ring_subst_2(B,D).
great(A,B):- alk_groups(A,C),ring_subst_6(A,E),ring_subst_2(B,F),x_subst(B,D,F).
great(A,B):- x_subst(A,D,E),ring_subst_4(A,E),ring_subst_6(B,C),ring_substitutions(A,D).
great(A,B):- ring_subst_2(B,D),sigma(D,E),ring_subst_3(A,C),r_subst_2(B,F).
great(A,B):- ring_substitutions(A,E),ring_subst_4(B,C),ring_subst_4(B,F),size(F,D).
great(A,B):- r_subst_3(A,C),r_subst_1(A,E),ring_substitutions(A,F),ring_subst_3(B,D).
great(A,B):- r_subst_3(B,C),ring_subst_2(A,E),ring_subst_3(B,F),ring_subst_6(B,D).
great(A,B):- gt(D,C),r_subst_3(B,D),ring_subst_5(A,F),h_acceptor(F,E).
great(A,B):- ring_subst_4(A,E),ring_subst_3(B,C),flex(E,D),ring_subst_5(B,F).
great(A,B):- ring_subst_6(A,E),ring_subst_3(A,C),x_subst(A,D,C),ring_substitutions(B,D).
great(A,B):- r_subst_3(B,F),ring_subst_2(B,C),x_subst(A,F,E),pi_acceptor(E,D).
great(A,B):- x_subst(A,C,D),x_subst(B,C,F),ring_subst_5(A,D),x_subst(A,E,F).
great(A,B):- n_val(B,E),n_val(A,F),x_subst(A,E,D),x_subst(A,F,C).
great(A,B):- ring_subst_4(B,E),r_subst_3(A,C),r_subst_2(B,F),ring_substitutions(A,D).
great(A,B):- ring_subst_4(A,E),ring_subst_2(A,C),ring_subst_6(B,D).
great(A,B):- ring_subst_2(B,E),x_subst(B,F,C),r_subst_3(A,F),polar(E,D).
great(A,B):- ring_subst_3(B,E),ring_subst_5(B,C),ring_subst_6(A,C),ring_substitutions(A,D).
great(A,B):- r_subst_1(A,D),ring_subst_3(A,E),ring_subst_3(B,E),n_val(B,C).
great(A,B):- ring_subst_3(B,E),ring_subst_5(B,C),ring_subst_5(A,F),h_acceptor(E,D).
great(A,B):- x_subst(A,D,E),pi_doner(C,F),ring_subst_5(A,C),ring_subst_4(B,E).
great(A,B):- n_val(A,C),r_subst_3(B,E),r_subst_1(B,D).
great(A,B):- r_subst_2(B,E),r_subst_2(A,E),r_subst_3(A,D),r_subst_1(A,C).
great(A,B):- r_subst_3(B,F),n_val(B,D),r_subst_1(A,C),alk_groups(A,E).
great(A,B):- ring_subst_2(B,E),ring_subst_5(A,E),flex(E,C),ring_subst_2(B,D).
great(A,B):- flex(E,F),ring_subst_2(A,E),ring_subst_4(B,D),ring_substitutions(A,C).
great(A,B):- n_val(B,E),x_subst(A,C,D),ring_substitutions(A,F),gt(E,F).
great(A,B):- ring_subst_4(A,F),x_subst(B,D,C),ring_subst_2(A,E),ring_subst_4(B,E).
great(A,B):- ring_subst_4(B,E),ring_substitutions(A,C),polarisable(E,F),r_subst_1(B,D).
great(A,B):- ring_subst_2(B,D),flex(D,F),r_subst_2(A,C),r_subst_3(A,E).
great(A,B):- ring_subst_4(B,E),size(E,D),ring_subst_6(A,C),flex(C,F).
great(A,B):- x_subst(B,F,C),n_val(A,F),polarisable(C,E),r_subst_2(B,D).
great(A,B):- ring_subst_2(A,E),ring_subst_6(B,C),ring_subst_2(B,D),pi_acceptor(E,F).
great(A,B):- ring_subst_3(B,E),ring_subst_3(B,F),ring_subst_6(A,C),pi_acceptor(C,D).
great(A,B):- ring_subst_5(A,F),ring_subst_5(B,E),h_doner(F,D),pi_doner(F,C).
great(A,B):- ring_subst_4(A,E),flex(E,D),polarisable(F,C),ring_subst_5(B,F).
great(A,B):- ring_subst_4(B,E),size(E,D),ring_subst_5(A,C),size(E,F).
great(A,B):- ring_subst_3(A,E),h_doner(D,C),ring_subst_4(B,D),ring_subst_5(B,F).
great(A,B):- ring_substitutions(A,E),alk_groups(B,D),x_subst(A,D,C),ring_subst_2(B,F).
great(A,B):- ring_subst_4(B,E),n_val(A,C),h_acceptor(E,F),ring_subst_5(A,D).
great(A,B):- h_doner(C,E),ring_subst_5(A,C),r_subst_3(A,D),ring_subst_6(B,F).
great(A,B):- ring_subst_5(A,E),x_subst(A,C,D),ring_subst_3(B,D),polar(E,F).
great(A,B):- ring_subst_6(B,E),pi_acceptor(F,D),ring_subst_5(A,F),pi_acceptor(F,C).
great(A,B):- ring_subst_5(A,F),ring_subst_3(A,F),x_subst(B,C,D),pi_doner(D,E).
great(A,B):- ring_subst_4(B,C),sigma(C,E),ring_subst_3(A,F),ring_subst_6(A,D).
great(A,B):- ring_subst_5(A,E),ring_subst_3(B,C),r_subst_1(B,F),ring_subst_6(B,D).
great(A,B):- polarisable(D,F),ring_subst_4(A,E),x_subst(B,C,D),ring_subst_6(B,D).
great(A,B):- r_subst_3(B,C),ring_subst_6(A,F),ring_subst_4(A,D),r_subst_3(A,E).
great(A,B):- ring_subst_2(B,E),sigma(C,D),polarisable(C,F),ring_subst_6(A,C).
great(A,B):- ring_subst_2(B,F),h_acceptor(D,C),ring_subst_3(A,D),alk_groups(A,E).
great(A,B):- r_subst_3(A,C),r_subst_2(B,E),ring_substitutions(A,C),ring_subst_6(B,D).
great(A,B):- x_subst(B,C,F),ring_subst_5(A,F),ring_subst_5(B,E),polar(E,D).
great(A,B):- ring_subst_4(B,F),r_subst_3(A,D),r_subst_1(A,C),r_subst_3(B,E).
great(A,B):- ring_subst_4(A,E),ring_subst_4(A,C),ring_subst_6(B,D),ring_subst_3(A,D).
great(A,B):- ring_subst_4(A,E),h_acceptor(D,F),ring_subst_5(B,D),h_acceptor(E,C).
great(A,B):- size(E,C),ring_subst_4(A,E),ring_subst_2(B,F),ring_subst_2(A,D).
great(A,B):- ring_subst_2(B,E),pi_doner(F,D),ring_subst_5(A,F),sigma(F,C).
great(A,B):- x_subst(A,F,D),ring_subst_2(A,E),r_subst_1(B,C),ring_subst_3(A,D).
great(A,B):- n_val(B,E),r_subst_3(A,D),r_subst_1(A,F),gt(D,C).
great(A,B):- ring_subst_6(A,D),r_subst_1(B,C),ring_subst_3(A,F),alk_groups(B,E).
great(A,B):- x_subst(B,D,C),x_subst(A,E,C),alk_groups(A,F),ring_substitutions(B,F).
great(A,B):- ring_substitutions(B,E),ring_subst_6(B,C),ring_subst_3(A,D),polar(D,F).
great(A,B):- ring_subst_2(B,C),ring_subst_3(A,C),sigma(D,E),ring_subst_3(A,D).
great(A,B):- r_subst_1(A,D),ring_subst_4(B,F),pi_doner(F,C),h_acceptor(F,E).
great(A,B):- size(D,C),n_val(A,F),ring_subst_2(B,D),alk_groups(B,E).
great(A,B):- x_subst(A,D,E),ring_subst_6(A,E),r_subst_3(B,C),alk_groups(A,D).
great(A,B):- size(D,C),ring_subst_5(B,E),ring_subst_2(A,D),pi_doner(E,F).
great(A,B):- ring_subst_3(B,C),n_val(B,D),x_subst(A,D,C),r_subst_3(B,E).
great(A,B):- ring_substitutions(B,E),pi_doner(C,F),alk_groups(B,D),ring_subst_6(A,C).
great(A,B):- h_doner(D,E),ring_subst_3(A,C),ring_subst_2(A,D),ring_subst_5(B,F).
great(A,B):- r_subst_1(A,D),ring_subst_2(B,C),size(C,E).
great(A,B):- r_subst_3(A,C),ring_subst_4(B,F),polar(D,E),x_subst(B,C,D).
great(A,B):- ring_subst_6(B,E),n_val(B,C),r_subst_3(B,D),n_val(A,F).
great(A,B):- ring_subst_6(A,E),ring_subst_3(B,D),polar(E,F),size(D,C).
great(A,B):- gt(D,E),x_subst(B,C,F),n_val(B,D),n_val(A,D).
great(A,B):- ring_subst_6(B,C),x_subst(B,D,C),ring_subst_4(A,C),ring_subst_3(A,C).
great(A,B):- r_subst_3(B,C),h_acceptor(F,D),ring_subst_3(A,F),ring_subst_5(B,E).
great(A,B):- ring_subst_6(B,C),h_doner(D,E),ring_subst_4(B,C),ring_subst_5(A,D).
great(A,B):- ring_substitutions(B,E),n_val(A,C),n_val(B,D),ring_subst_5(B,F).
great(A,B):- x_subst(B,D,C),polar(C,E),ring_substitutions(A,D).
great(A,B):- x_subst(A,D,E),alk_groups(A,C),r_subst_3(B,D),polar(E,F).
great(A,B):- ring_substitutions(A,E),ring_substitutions(B,C),x_subst(A,D,F).
great(A,B):- ring_subst_5(A,D),x_subst(A,E,C),r_subst_3(B,F),ring_subst_3(A,D).
great(A,B):- ring_subst_5(A,E),ring_subst_2(A,F),ring_subst_2(B,D),sigma(D,C).
great(A,B):- ring_subst_3(A,F),ring_subst_2(A,F),x_subst(A,D,C),r_subst_3(B,E).
great(A,B):- ring_subst_2(B,C),polarisable(C,E),size(C,D),x_subst(A,F,C).
great(A,B):- alk_groups(B,C),polarisable(E,D),x_subst(A,C,E),great_polari(D,F).
great(A,B):- ring_subst_2(B,E),polarisable(E,D),ring_subst_2(A,F),n_val(A,C).
great(A,B):- x_subst(B,E,D),polarisable(D,C),h_doner(D,F),ring_subst_6(A,D).
great(A,B):- ring_subst_5(B,D),ring_subst_4(A,C),ring_subst_6(A,C),ring_subst_4(B,D).
great(A,B):- r_subst_3(A,C),gt(D,E),ring_subst_6(B,F),n_val(B,D).
great(A,B):- ring_subst_2(B,E),ring_subst_4(A,E),polarisable(E,C),x_subst(B,F,D).
great(A,B):- ring_subst_4(B,E),ring_subst_5(B,E),r_subst_2(A,C),n_val(A,D).
great(A,B):- n_val(A,E),pi_acceptor(F,C),ring_subst_2(A,D),ring_subst_5(B,F).
great(A,B):- pi_doner(C,F),x_subst(B,D,C),ring_subst_5(B,E),ring_subst_3(A,E).
great(A,B):- ring_subst_2(B,D),polar(E,F),r_subst_1(A,C),ring_subst_6(B,E).
great(A,B):- r_subst_2(A,D),ring_subst_6(A,E),n_val(A,C),r_subst_2(B,D).
great(A,B):- ring_subst_5(A,E),ring_subst_3(B,C),ring_subst_6(A,E),h_doner(E,D).
great(A,B):- ring_subst_2(B,E),alk_groups(B,D),ring_subst_6(A,F),polarisable(E,C).
great(A,B):- great_h_acc(E,D),ring_subst_3(B,C),ring_subst_6(A,F),h_acceptor(C,E).
great(A,B):- ring_subst_4(B,E),ring_subst_6(A,C),pi_acceptor(C,D),x_subst(B,F,E).
great(A,B):- ring_subst_6(B,E),h_doner(D,C),ring_subst_6(B,D),ring_subst_6(A,D).
great(A,B):- ring_subst_4(A,E),flex(E,C),r_subst_3(A,D),ring_subst_5(B,F).
great(A,B):- x_subst(B,E,D),ring_substitutions(A,E),ring_subst_4(B,F),sigma(D,C).
great(A,B):- h_acceptor(D,F),ring_subst_6(A,C),ring_subst_5(B,E),ring_subst_3(A,D).
great(A,B):- n_val(A,C),h_doner(D,F),ring_subst_3(B,D),great_h_don(F,E).
great(A,B):- x_subst(A,D,E),ring_subst_4(B,C),ring_subst_5(A,C),r_subst_1(B,F).
great(A,B):- ring_subst_2(B,E),x_subst(A,D,F),r_subst_3(A,D),polar(E,C).
great(A,B):- ring_subst_4(A,E),ring_substitutions(B,F),ring_subst_5(B,D),pi_doner(D,C).
great(A,B):- ring_subst_3(A,E),sigma(E,D),pi_acceptor(E,C),ring_subst_5(B,F).
great(A,B):- x_subst(A,C,D),x_subst(B,C,F),ring_subst_4(B,F),polar(F,E).
great(A,B):- ring_subst_3(B,C),size(C,E),ring_subst_3(A,D),size(D,F).
great(A,B):- ring_subst_5(A,E),h_acceptor(D,C),ring_subst_3(A,F),ring_subst_4(B,D).
great(A,B):- ring_subst_4(B,C),ring_subst_6(A,C),n_val(A,D).
great(A,B):- gt(C,D),n_val(B,C),r_subst_1(A,E),n_val(A,D).
great(A,B):- ring_subst_6(A,E),n_val(B,C),great_sigma(F,D),sigma(E,F).
great(A,B):- x_subst(B,D,C),x_subst(B,E,F),ring_subst_5(A,F),ring_subst_6(B,F).
great(A,B):- r_subst_3(B,D),ring_subst_6(A,C),polarisable(C,E),ring_subst_5(B,F).
great(A,B):- r_subst_3(B,F),ring_subst_3(B,C),pi_doner(C,E),ring_subst_3(A,D).
great(A,B):- pi_doner(E,C),ring_subst_2(A,E),alk_groups(B,D),polar(E,F).
great(A,B):- ring_subst_4(B,F),alk_groups(B,D),x_subst(A,D,C),n_val(A,E).
great(A,B):- ring_subst_2(A,E),ring_subst_2(B,F),ring_subst_3(A,D),flex(F,C).
great(A,B):- ring_subst_6(A,F),r_subst_1(B,C),polar(F,D),x_subst(A,E,F).
great(A,B):- ring_subst_6(B,E),ring_subst_2(B,C),pi_acceptor(C,D),r_subst_1(A,F).
great(A,B):- x_subst(B,C,E),r_subst_3(B,F),polar(E,D),ring_subst_2(A,E).
great(A,B):- h_acceptor(C,F),ring_subst_6(A,C),size(D,E),ring_subst_5(B,D).
great(A,B):- n_val(B,E),r_subst_3(A,C),h_doner(D,F),x_subst(A,E,D).
great(A,B):- r_subst_3(A,F),ring_subst_2(A,C),gt(F,E),r_subst_2(B,D).
great(A,B):- ring_substitutions(A,E),ring_subst_4(B,D),r_subst_1(B,C),r_subst_1(A,C).
great(A,B):- ring_subst_6(B,E),size(C,F),ring_subst_6(A,C),flex(E,D).
great(A,B):- r_subst_1(A,D),n_val(B,C),ring_substitutions(B,E).
great(A,B):- x_subst(B,F,C),ring_subst_6(B,C),ring_subst_5(B,E),x_subst(A,D,C).
great(A,B):- ring_subst_4(B,E),h_acceptor(E,C),polar(E,F),ring_subst_4(A,D).
great(A,B):- x_subst(B,C,E),ring_subst_3(B,F),ring_subst_3(A,F),ring_subst_2(A,D).
great(A,B):- ring_subst_6(B,C),ring_subst_4(A,C),sigma(D,E),ring_subst_6(B,D).
great(A,B):- ring_subst_6(A,E),r_subst_3(A,F),ring_subst_3(B,C),n_val(B,D).
great(A,B):- r_subst_3(B,C),r_subst_3(A,F),h_acceptor(E,D),x_subst(B,F,E).
great(A,B):- x_subst(A,E,C),pi_doner(C,D),alk_groups(B,E),ring_subst_5(B,F).
great(A,B):- r_subst_1(A,D),h_doner(C,E),ring_subst_4(B,F),ring_subst_6(A,C).
great(A,B):- ring_substitutions(A,F),x_subst(A,D,C),x_subst(B,E,C),ring_substitutions(B,D).
great(A,B):- ring_subst_2(B,E),gt(C,D),alk_groups(A,D),ring_substitutions(A,C).
great(A,B):- ring_subst_4(B,E),n_val(B,F),ring_subst_6(A,C),ring_subst_6(B,D).
great(A,B):- n_val(A,C),pi_doner(D,E),x_subst(B,C,D),x_subst(A,C,F).
great(A,B):- gt(C,E),ring_substitutions(B,F),gt(F,C),n_val(A,D).
great(A,B):- alk_groups(B,C),ring_subst_5(A,E),ring_subst_3(B,D),ring_subst_2(B,D).
great(A,B):- ring_subst_6(A,C),ring_subst_2(B,D),ring_subst_6(B,D),r_subst_3(A,E).
great(A,B):- ring_subst_2(B,F),r_subst_2(A,C),ring_subst_3(A,D),r_subst_3(A,E).
great(A,B):- alk_groups(B,C),ring_subst_4(A,E),h_acceptor(F,D),ring_subst_4(A,F).
great(A,B):- ring_subst_6(B,E),ring_subst_4(B,C),alk_groups(A,D),ring_subst_3(A,F).
great(A,B):- ring_subst_6(A,E),n_val(B,C),polarisable(E,F),ring_subst_5(A,D).
great(A,B):- ring_subst_2(B,F),size(F,E),ring_subst_3(A,D),polar(F,C).
great(A,B):- x_subst(A,C,D),sigma(F,E),ring_subst_5(A,F),ring_subst_2(B,D).
great(A,B):- x_subst(A,C,D),ring_subst_5(B,F),flex(F,E),x_subst(A,C,F).
great(A,B):- r_subst_3(A,C),ring_substitutions(B,C),ring_subst_2(B,D),ring_subst_6(A,D).
