great(A,B):- x_subst(B,D,C),ring_subst_3(A,C),r_subst_3(A,D),polar(C,E).
great(A,B):- ring_subst_3(B,C),r_subst_2(B,E),alk_groups(A,D),n_val(A,F).
great(A,B):- ring_subst_2(B,C),ring_subst_2(A,C),size(D,E),ring_subst_6(B,D).
great(A,B):- sigma(C,E),ring_subst_3(A,C),flex(F,D),ring_subst_5(B,F).
great(A,B):- ring_subst_2(B,E),x_subst(B,F,C),x_subst(B,D,E),n_val(A,D).
great(A,B):- r_subst_2(A,D),ring_subst_4(A,E),ring_subst_2(B,C),ring_subst_5(A,F).
great(A,B):- x_subst(B,C,F),ring_subst_4(A,D),flex(F,E).
great(A,B):- x_subst(B,C,E),n_val(A,C),pi_doner(E,F),r_subst_1(B,D).
great(A,B):- sigma(C,E),x_subst(B,F,C),ring_subst_3(A,C),n_val(A,D).
great(A,B):- h_doner(F,E),ring_subst_6(B,C),alk_groups(A,D),ring_subst_3(A,F).
great(A,B):- flex(E,F),ring_subst_3(A,E),ring_subst_4(B,C),sigma(C,D).
great(A,B):- alk_groups(A,C),ring_subst_2(B,F),ring_subst_5(A,D),alk_groups(B,E).
great(A,B):- n_val(B,E),ring_subst_4(B,C),ring_subst_3(A,F),polarisable(F,D).
great(A,B):- h_acceptor(D,F),ring_subst_6(B,C),ring_subst_4(A,D),r_subst_3(A,E).
great(A,B):- r_subst_2(B,E),ring_subst_2(A,C),x_subst(A,D,C),x_subst(B,D,F).
great(A,B):- ring_subst_2(B,C),r_subst_3(B,D),ring_subst_5(B,E),ring_subst_6(A,C).
great(A,B):- h_doner(D,E),ring_subst_6(B,C),ring_subst_5(A,D),ring_subst_2(A,D).
great(A,B):- n_val(A,C),alk_groups(B,F),ring_subst_6(A,E),n_val(A,D).
great(A,B):- ring_subst_4(A,E),ring_subst_4(A,C),ring_subst_3(B,F),ring_subst_3(B,D).
great(A,B):- x_subst(B,D,C),ring_subst_4(B,C),sigma(C,E),ring_subst_4(A,F).
great(A,B):- ring_subst_2(B,E),ring_subst_4(A,E),alk_groups(A,D),polar(E,C).
great(A,B):- ring_subst_3(B,C),x_subst(A,E,D),ring_subst_4(B,D),h_doner(C,F).
great(A,B):- ring_subst_3(B,C),ring_subst_4(B,F),x_subst(A,E,D),ring_subst_5(A,D).
great(A,B):- ring_subst_2(B,C),ring_subst_2(A,F),flex(F,E),x_subst(B,D,F).
great(A,B):- ring_subst_4(B,E),ring_substitutions(B,F),x_subst(A,C,E),gt(F,D).
great(A,B):- ring_subst_4(B,F),h_doner(F,C),x_subst(A,D,F),great_h_don(C,E).
great(A,B):- x_subst(A,F,D),pi_doner(E,C),ring_subst_2(B,E),ring_subst_5(A,D).
great(A,B):- r_subst_3(B,C),ring_subst_4(A,E),polarisable(E,D),n_val(B,F).
great(A,B):- polar(D,C),ring_subst_3(A,F),ring_subst_4(B,D),flex(F,E).
great(A,B):- r_subst_3(B,C),ring_subst_2(A,E),ring_subst_4(B,D),r_subst_1(B,F).
great(A,B):- alk_groups(B,F),polarisable(E,D),r_subst_2(B,C),ring_subst_2(A,E).
great(A,B):- r_subst_3(B,F),x_subst(A,F,E),ring_substitutions(A,F),x_subst(A,D,C).
great(A,B):- n_val(A,E),ring_subst_2(B,C),ring_subst_4(A,F),size(C,D).
great(A,B):- ring_subst_2(A,E),ring_subst_4(B,C),ring_subst_5(A,F),x_subst(A,D,C).
great(A,B):- r_subst_2(A,D),ring_subst_2(A,E),ring_subst_2(B,C),ring_subst_2(B,E).
great(A,B):- pi_acceptor(D,E),h_doner(D,F),x_subst(B,C,D),ring_subst_5(A,D).
great(A,B):- ring_subst_4(B,E),ring_subst_6(B,F),r_subst_1(B,C),ring_substitutions(A,D).
great(A,B):- gt(E,F),ring_subst_3(B,C),alk_groups(A,D),alk_groups(A,E).
great(A,B):- alk_groups(B,D),ring_subst_5(A,F),x_subst(A,D,C),polar(C,E).
great(A,B):- polarisable(F,D),ring_subst_2(B,F),x_subst(B,E,C),alk_groups(A,E).
great(A,B):- flex(E,F),ring_subst_3(A,E),n_val(B,C),h_acceptor(E,D).
great(A,B):- ring_subst_2(B,F),pi_acceptor(D,C),ring_subst_3(A,D),alk_groups(A,E).
great(A,B):- ring_subst_4(A,E),ring_subst_3(B,C),ring_subst_2(A,F),x_subst(B,D,F).
great(A,B):- h_acceptor(E,F),ring_subst_3(A,E),x_subst(B,C,D),ring_subst_3(A,D).
great(A,B):- ring_subst_4(B,E),ring_subst_5(B,C),x_subst(A,D,C),polar(E,F).
great(A,B):- ring_subst_6(B,C),ring_subst_2(B,C),ring_subst_2(B,D),ring_subst_2(A,D).
great(A,B):- h_acceptor(F,D),ring_subst_2(B,F),r_subst_1(B,C),alk_groups(A,E).
great(A,B):- ring_subst_6(B,E),ring_subst_2(A,E),ring_subst_2(B,C),n_val(A,D).
great(A,B):- ring_subst_5(B,C),alk_groups(B,D),gt(D,E),ring_subst_5(A,C).
great(A,B):- ring_subst_3(B,E),ring_subst_3(B,C),pi_acceptor(E,F),ring_subst_3(A,D).
great(A,B):- x_subst(A,D,E),x_subst(B,F,C),x_subst(A,F,E),n_val(B,D).
great(A,B):- ring_subst_5(A,E),ring_subst_2(B,F),x_subst(B,D,E),ring_subst_5(A,C).
great(A,B):- r_subst_2(A,D),n_val(B,E),ring_substitutions(A,C),gt(E,C).
great(A,B):- pi_doner(D,C),ring_subst_6(A,D),ring_subst_6(B,D),ring_subst_5(A,D).
great(A,B):- n_val(B,E),x_subst(A,C,D),ring_substitutions(B,C),alk_groups(A,E).
great(A,B):- ring_subst_6(A,C),n_val(A,F),ring_subst_4(A,D),x_subst(B,F,E).
great(A,B):- x_subst(B,E,D),polarisable(D,C),ring_subst_3(A,F),ring_subst_5(A,D).
great(A,B):- x_subst(B,E,D),r_subst_3(A,F),ring_subst_3(B,C),ring_subst_6(B,D).
great(A,B):- alk_groups(B,F),n_val(A,C),x_subst(A,E,D),alk_groups(B,E).
great(A,B):- ring_subst_2(A,E),h_doner(E,F),n_val(B,C),r_subst_3(A,D).
great(A,B):- r_subst_3(B,C),ring_subst_3(A,E),ring_subst_5(A,F),h_doner(E,D).
great(A,B):- gt(E,D),ring_subst_6(B,C),n_val(B,F),r_subst_3(A,E).
great(A,B):- x_subst(B,E,D),ring_substitutions(B,F),ring_subst_6(A,C),ring_subst_5(A,C).
great(A,B):- pi_acceptor(D,E),x_subst(B,C,F),ring_subst_3(B,D),ring_subst_6(A,D).
great(A,B):- x_subst(A,F,D),ring_subst_2(B,C),ring_subst_2(A,C),x_subst(B,F,E).
great(A,B):- alk_groups(B,C),ring_subst_5(A,F),ring_subst_4(B,D),alk_groups(B,E).
great(A,B):- ring_subst_4(B,E),r_subst_3(A,C),x_subst(A,D,F),x_subst(B,D,F).
great(A,B):- h_acceptor(D,F),polar(D,E),x_subst(B,C,D),ring_subst_5(A,D).
great(A,B):- x_subst(B,D,C),ring_subst_6(B,C),sigma(E,F),ring_subst_3(A,E).
great(A,B):- alk_groups(B,F),r_subst_3(A,D),ring_subst_5(B,E),h_doner(E,C).
great(A,B):- r_subst_3(A,C),ring_subst_6(A,F),n_val(B,D),flex(F,E).
great(A,B):- ring_subst_3(B,E),polar(C,D),ring_subst_6(A,C),ring_substitutions(A,F).
great(A,B):- gt(D,E),ring_subst_3(A,F),ring_substitutions(B,D),polar(F,C).
great(A,B):- ring_subst_3(A,D),n_val(A,C),alk_groups(B,E),x_subst(A,E,F).
great(A,B):- x_subst(B,C,E),r_subst_3(A,F),alk_groups(B,C),n_val(A,D).
great(A,B):- alk_groups(B,C),ring_subst_6(B,F),r_subst_3(A,D),ring_subst_4(B,E).
great(A,B):- ring_subst_4(A,C),x_subst(B,E,F),ring_subst_5(A,F),ring_subst_3(B,D).
great(A,B):- x_subst(B,E,F),r_subst_2(B,C),r_subst_3(A,D).
great(A,B):- size(E,C),alk_groups(A,D),ring_subst_5(B,E),h_acceptor(E,F).
great(A,B):- ring_subst_3(B,E),r_subst_3(B,F),ring_subst_6(A,C),flex(C,D).
great(A,B):- r_subst_3(A,F),ring_subst_3(B,C),polarisable(C,E),r_subst_1(B,D).
great(A,B):- ring_subst_3(B,E),polarisable(E,C),r_subst_1(A,F),n_val(A,D).
great(A,B):- ring_subst_6(B,E),ring_subst_6(A,E),r_subst_1(A,C),n_val(A,D).
great(A,B):- r_subst_1(B,F),ring_substitutions(A,D),x_subst(A,D,C),x_subst(B,E,C).
great(A,B):- ring_subst_2(A,D),ring_subst_3(B,F),r_subst_1(B,C),alk_groups(B,E).
great(A,B):- ring_subst_4(B,C),ring_subst_5(B,E),n_val(A,D),x_subst(B,F,E).
great(A,B):- ring_subst_2(B,C),sigma(D,F),ring_subst_5(A,D),alk_groups(A,E).
great(A,B):- ring_substitutions(A,E),ring_subst_3(B,C),ring_subst_2(B,D).
great(A,B):- ring_subst_2(B,E),ring_subst_6(A,E),pi_acceptor(C,F),x_subst(A,D,C).
great(A,B):- ring_subst_6(B,C),ring_subst_6(A,D),ring_subst_4(B,D),alk_groups(B,E).
great(A,B):- x_subst(B,D,C),ring_subst_2(B,C),alk_groups(A,D),ring_subst_5(B,C).
great(A,B):- size(E,C),ring_subst_5(A,E),x_subst(B,D,E),r_subst_1(A,F).
great(A,B):- h_acceptor(E,C),ring_subst_3(A,F),ring_subst_5(B,E),h_doner(E,D).
great(A,B):- ring_subst_3(A,E),ring_subst_6(B,C),ring_subst_2(A,D),ring_subst_4(A,E).
great(A,B):- x_subst(A,E,C),ring_subst_4(B,C),ring_substitutions(A,E),x_subst(A,E,D).
great(A,B):- ring_subst_2(B,D),ring_substitutions(A,E),n_val(A,C),r_subst_2(B,F).
great(A,B):- ring_substitutions(B,E),ring_subst_3(A,C),sigma(D,F),ring_subst_6(A,D).
great(A,B):- ring_subst_4(B,F),x_subst(B,E,F),x_subst(B,C,D),alk_groups(A,E).
great(A,B):- x_subst(A,D,E),x_subst(B,D,E),x_subst(A,C,E),polarisable(E,F).
great(A,B):- ring_subst_2(A,E),ring_subst_5(B,C),n_val(A,F),ring_subst_2(B,D).
great(A,B):- ring_subst_4(A,E),n_val(B,C),x_subst(B,D,F),x_subst(A,C,F).
great(A,B):- x_subst(B,D,C),r_subst_3(B,D),h_doner(C,F),ring_subst_3(A,E).
great(A,B):- ring_subst_2(B,E),ring_subst_3(B,C),ring_subst_3(A,C),x_subst(B,F,D).
great(A,B):- r_subst_1(A,D),r_subst_3(B,C),ring_subst_2(B,E),polar(E,F).
great(A,B):- ring_subst_6(A,E),n_val(A,F),ring_subst_2(B,D),polarisable(D,C).
great(A,B):- ring_substitutions(B,C),ring_subst_3(B,F),r_subst_3(A,D),flex(F,E).
great(A,B):- x_subst(A,D,E),n_val(B,C),ring_subst_5(B,E),ring_substitutions(A,D).
great(A,B):- ring_subst_4(B,E),ring_subst_3(A,E),x_subst(A,D,F),x_subst(A,C,E).
great(A,B):- ring_subst_3(B,E),r_subst_3(A,F),size(E,D),ring_subst_3(B,C).
great(A,B):- ring_subst_2(A,F),ring_subst_5(B,F),x_subst(A,C,E),r_subst_1(B,D).
great(A,B):- flex(F,C),x_subst(A,D,F),ring_subst_3(A,F),r_subst_3(B,E).
great(A,B):- ring_subst_3(A,E),h_doner(F,C),alk_groups(B,D),ring_subst_2(B,F).
great(A,B):- ring_subst_2(A,E),r_subst_1(B,C),ring_subst_5(B,D),ring_subst_4(A,E).
great(A,B):- ring_substitutions(B,E),ring_substitutions(B,F),ring_subst_6(A,C),ring_subst_6(B,D).
great(A,B):- ring_subst_5(B,D),n_val(A,C),ring_substitutions(A,C),h_acceptor(D,E).
great(A,B):- x_subst(B,C,E),x_subst(A,F,E),ring_subst_3(A,D),x_subst(B,F,E).
great(A,B):- size(E,C),ring_subst_4(A,E),ring_subst_2(B,D),ring_subst_3(A,D).
great(A,B):- r_subst_1(B,C),ring_subst_6(A,E),alk_groups(A,D),ring_subst_5(B,E).
great(A,B):- ring_subst_4(B,F),ring_subst_2(A,C),h_doner(F,D),ring_subst_6(A,E).
great(A,B):- x_subst(B,D,E),x_subst(A,D,C),h_doner(C,F),ring_subst_5(B,E).
great(A,B):- ring_subst_6(A,C),x_subst(B,D,E),x_subst(A,D,C),ring_subst_3(A,F).
great(A,B):- alk_groups(B,F),x_subst(B,D,E),x_subst(A,D,C),gt(D,F).
great(A,B):- ring_subst_2(B,E),r_subst_3(B,D),r_subst_1(A,C),ring_substitutions(B,D).
great(A,B):- ring_subst_5(A,E),n_val(B,C),alk_groups(B,D),ring_subst_5(B,E).
great(A,B):- ring_subst_2(B,E),ring_subst_5(B,C),h_doner(D,F),ring_subst_3(A,D).
great(A,B):- x_subst(A,F,D),ring_subst_6(A,C),polarisable(D,E),ring_subst_6(B,D).
great(A,B):- n_val(A,C),alk_groups(A,C),polar(E,D),ring_subst_5(B,E).
great(A,B):- h_acceptor(F,D),ring_subst_3(B,C),r_subst_1(A,E),ring_subst_4(A,F).
great(A,B):- x_subst(B,E,D),ring_subst_2(B,C),ring_subst_4(A,C),flex(C,F).
great(A,B):- polar(F,E),x_subst(A,D,F),r_subst_2(A,C),ring_subst_2(B,F).
great(A,B):- pi_acceptor(F,D),ring_subst_2(B,F),ring_subst_6(A,C),h_acceptor(C,E).
great(A,B):- r_subst_3(B,C),n_val(B,D),x_subst(A,E,F).
great(A,B):- flex(E,F),ring_subst_3(A,E),h_doner(E,C),r_subst_2(B,D).
great(A,B):- h_acceptor(E,F),ring_subst_5(B,E),n_val(A,D),pi_acceptor(E,C).
great(A,B):- r_subst_1(A,D),pi_acceptor(E,F),ring_subst_2(A,C),ring_subst_6(B,E).
great(A,B):- alk_groups(B,C),x_subst(A,F,E),ring_subst_2(B,D),r_subst_3(B,C).
great(A,B):- r_subst_1(A,D),ring_subst_2(B,F),pi_doner(F,C),r_subst_3(A,E).
great(A,B):- r_subst_3(B,F),r_subst_1(B,E),ring_subst_4(A,D),flex(D,C).
great(A,B):- r_subst_3(A,C),flex(D,E),x_subst(B,F,D),ring_subst_6(B,D).
great(A,B):- x_subst(A,F,D),x_subst(A,F,E),r_subst_3(B,C).
great(A,B):- ring_subst_3(A,C),ring_subst_2(B,F),pi_acceptor(F,E),ring_subst_3(A,D).
great(A,B):- polarisable(E,C),ring_subst_3(A,E),n_val(A,D),x_subst(B,D,F).
great(A,B):- ring_subst_3(A,E),pi_doner(D,F),ring_subst_4(B,D),pi_doner(D,C).
great(A,B):- ring_subst_3(A,F),ring_subst_4(B,D),pi_doner(F,E),size(F,C).
great(A,B):- ring_subst_3(A,E),ring_subst_3(B,C),r_subst_3(B,D),h_doner(E,F).
great(A,B):- ring_subst_4(A,E),r_subst_3(A,F),flex(E,C),x_subst(B,D,E).
great(A,B):- ring_subst_3(A,C),ring_subst_2(B,F),ring_subst_6(B,E),h_doner(E,D).
great(A,B):- ring_subst_2(B,D),ring_subst_3(A,C),x_subst(B,E,C),x_subst(A,E,F).
great(A,B):- x_subst(A,C,D),size(F,E),ring_subst_3(B,D),x_subst(A,C,F).
great(A,B):- n_val(B,C),alk_groups(A,D),alk_groups(A,E).
