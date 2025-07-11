great(A,B):- x_subst(A,F,D),ring_subst_3(A,E),polar(D,C),x_subst(B,F,D).
great(A,B):- x_subst(A,E,C),x_subst(B,F,C),ring_substitutions(B,F),r_subst_2(B,D).
great(A,B):- ring_subst_2(A,C),ring_subst_5(A,F),x_subst(B,E,C),ring_subst_3(A,D).
great(A,B):- x_subst(B,C,E),ring_subst_5(A,E),ring_subst_2(B,F),flex(F,D).
great(A,B):- alk_groups(B,C),alk_groups(A,C),x_subst(B,D,E),n_val(B,D).
great(A,B):- r_subst_2(A,E),ring_subst_3(A,F),ring_subst_3(B,D),polar(F,C).
great(A,B):- ring_subst_4(B,E),ring_subst_6(B,F),ring_subst_3(B,D),n_val(A,C).
great(A,B):- x_subst(B,C,E),x_subst(A,C,D),ring_subst_2(B,F),ring_subst_4(B,F).
great(A,B):- r_subst_3(A,C),n_val(A,D),ring_subst_3(A,E),ring_subst_5(B,F).
great(A,B):- r_subst_1(A,D),n_val(B,C),ring_subst_5(A,F),polar(F,E).
great(A,B):- ring_subst_6(B,C),r_subst_2(A,E),alk_groups(A,D),r_subst_1(B,F).
great(A,B):- ring_subst_3(A,E),ring_subst_2(A,C),x_subst(B,D,E),ring_subst_5(A,E).
great(A,B):- ring_subst_6(B,C),sigma(C,D),ring_subst_4(A,C),ring_subst_3(A,C).
great(A,B):- flex(C,D),x_subst(A,E,C),ring_subst_3(B,F),n_val(A,E).
great(A,B):- polarisable(C,F),ring_subst_4(B,C),r_subst_2(A,E),ring_subst_6(A,D).
great(A,B):- ring_subst_6(B,C),r_subst_3(B,D),ring_subst_5(A,F),pi_acceptor(F,E).
great(A,B):- x_subst(B,D,C),ring_subst_2(A,C),n_val(B,F),ring_subst_3(A,E).
great(A,B):- sigma(F,E),r_subst_3(A,D),n_val(B,D),x_subst(A,C,F).
great(A,B):- ring_subst_2(A,E),ring_subst_2(B,C),pi_acceptor(C,F),ring_subst_4(B,D).
great(A,B):- r_subst_1(B,E),ring_subst_6(A,C),size(C,D),ring_subst_6(B,F).
great(A,B):- r_subst_3(B,C),ring_subst_5(A,E),gt(C,D),ring_subst_6(A,F).
great(A,B):- ring_subst_6(B,E),alk_groups(B,D),n_val(A,F),r_subst_2(A,C).
great(A,B):- r_subst_2(A,D),ring_subst_6(A,E),ring_subst_5(B,C),ring_subst_6(A,C).
great(A,B):- ring_subst_4(B,E),r_subst_3(A,C),sigma(D,F),ring_subst_2(B,D).
great(A,B):- h_acceptor(D,C),ring_subst_6(A,D),ring_subst_2(B,D),alk_groups(B,E).
great(A,B):- ring_subst_4(B,E),x_subst(B,D,C),ring_subst_2(A,C),ring_subst_4(A,F).
great(A,B):- ring_subst_3(A,E),ring_subst_6(B,D),r_subst_1(A,C),ring_subst_4(A,E).
great(A,B):- ring_subst_2(A,E),h_doner(F,C),ring_subst_2(B,F),ring_subst_4(A,D).
great(A,B):- alk_groups(B,C),x_subst(A,C,D),ring_subst_5(B,D),h_acceptor(D,E).
great(A,B):- ring_subst_5(A,C),ring_subst_2(A,F),ring_subst_2(B,D),flex(F,E).
great(A,B):- r_subst_1(A,D),ring_subst_6(B,C),ring_subst_5(A,C),h_doner(C,E).
great(A,B):- ring_substitutions(B,E),h_acceptor(D,C),ring_subst_3(A,F),ring_subst_4(B,D).
great(A,B):- ring_substitutions(B,E),gt(E,C),ring_subst_4(B,D),ring_subst_4(A,D).
great(A,B):- ring_subst_2(B,C),r_subst_3(A,D),alk_groups(B,E),n_val(A,D).
great(A,B):- r_subst_1(B,E),ring_subst_3(A,F),r_subst_2(A,C),r_subst_2(B,D).
great(A,B):- ring_subst_3(A,E),ring_subst_4(B,F),h_doner(E,D),ring_subst_5(A,C).
great(A,B):- ring_subst_5(A,E),ring_subst_3(B,C),ring_subst_6(A,E),pi_doner(C,D).
great(A,B):- pi_doner(C,F),ring_subst_4(A,E),ring_subst_6(B,C),great_pi_don(F,D).
great(A,B):- ring_subst_2(B,E),sigma(E,D),ring_subst_4(A,C),ring_subst_3(A,C).
great(A,B):- alk_groups(B,F),polarisable(D,C),x_subst(A,E,D),r_subst_3(A,E).
great(A,B):- x_subst(B,E,D),n_val(A,C),alk_groups(B,C),ring_subst_3(A,D).
great(A,B):- ring_subst_6(B,C),ring_subst_3(A,F),polarisable(C,E),ring_subst_4(A,D).
great(A,B):- h_acceptor(D,F),ring_subst_4(A,E),ring_subst_6(B,C),ring_subst_4(B,D).
great(A,B):- pi_acceptor(F,E),ring_subst_3(A,F),x_subst(A,D,C),ring_substitutions(B,D).
great(A,B):- ring_subst_5(A,C),x_subst(A,E,D),ring_subst_6(A,C),ring_subst_5(B,F).
great(A,B):- gt(D,C),ring_subst_4(B,F),n_val(A,D),flex(F,E).
great(A,B):- x_subst(A,D,E),ring_subst_2(A,E),x_subst(B,C,F).
great(A,B):- ring_subst_6(B,E),size(F,D),ring_subst_3(A,F),polar(E,C).
great(A,B):- alk_groups(B,F),sigma(D,E),gt(F,C),ring_subst_5(A,D).
great(A,B):- r_subst_3(B,F),ring_substitutions(A,E),r_subst_2(B,C),r_subst_2(B,D).
great(A,B):- ring_subst_2(A,F),x_subst(B,C,F),x_subst(A,E,D),n_val(A,C).
great(A,B):- ring_subst_2(A,E),h_doner(E,F),r_subst_1(B,C),h_acceptor(E,D).
great(A,B):- x_subst(A,C,D),ring_subst_3(B,F),ring_subst_2(B,F),polarisable(F,E).
great(A,B):- ring_subst_2(B,C),polar(C,E),x_subst(A,F,C),n_val(A,D).
great(A,B):- alk_groups(A,F),alk_groups(B,D),r_subst_2(B,C),r_subst_1(A,E).
great(A,B):- ring_subst_2(B,E),ring_subst_6(A,C),ring_subst_6(B,D),x_subst(B,F,E).
great(A,B):- x_subst(A,C,D),r_subst_2(B,E),ring_subst_4(B,D),polar(D,F).
great(A,B):- size(C,F),ring_subst_3(B,C),r_subst_3(B,D),alk_groups(A,E).
great(A,B):- n_val(B,E),ring_subst_2(B,C),ring_subst_6(A,C),ring_subst_6(B,D).
great(A,B):- ring_subst_5(A,C),n_val(A,F),x_subst(B,E,C),ring_substitutions(A,D).
great(A,B):- ring_subst_4(A,E),ring_subst_6(B,C),ring_subst_5(A,C),ring_subst_2(B,D).
great(A,B):- pi_acceptor(C,E),x_subst(B,D,C),ring_subst_6(A,C),ring_subst_5(A,F).
great(A,B):- gt(C,D),x_subst(B,C,F),gt(E,C),alk_groups(A,E).
great(A,B):- x_subst(A,D,E),ring_subst_5(B,C),alk_groups(B,D),n_val(A,D).
great(A,B):- ring_subst_3(A,E),ring_substitutions(B,F),h_acceptor(E,D),great_h_acc(D,C).
great(A,B):- r_subst_3(A,F),ring_subst_6(A,C),flex(E,D),x_subst(B,F,E).
great(A,B):- x_subst(B,C,E),ring_subst_2(B,F),ring_subst_3(A,F),n_val(A,D).
great(A,B):- x_subst(B,E,D),alk_groups(B,F),ring_subst_2(B,C),n_val(A,E).
great(A,B):- ring_subst_5(B,C),x_subst(A,F,E),ring_subst_2(A,D),ring_subst_5(A,C).
great(A,B):- x_subst(B,E,D),ring_subst_3(A,F),ring_subst_5(B,D),pi_doner(F,C).
great(A,B):- ring_subst_3(A,E),polarisable(E,D),x_subst(B,C,F),x_subst(A,C,E).
great(A,B):- r_subst_2(A,D),flex(E,F),ring_subst_3(B,E),ring_subst_4(A,C).
great(A,B):- x_subst(B,C,E),x_subst(A,D,F),ring_subst_5(A,F),alk_groups(B,C).
great(A,B):- polar(C,F),sigma(C,D),ring_subst_6(A,C),ring_subst_5(B,E).
great(A,B):- ring_substitutions(B,E),x_subst(B,C,F),ring_subst_4(A,F),alk_groups(B,D).
great(A,B):- ring_subst_2(B,E),ring_subst_2(B,C),alk_groups(B,D),ring_subst_4(A,F).
great(A,B):- x_subst(A,E,C),ring_subst_3(A,F),ring_subst_3(B,D),alk_groups(B,E).
great(A,B):- ring_subst_6(B,C),ring_subst_3(B,C),r_subst_2(A,E),ring_subst_3(A,D).
great(A,B):- ring_subst_3(B,E),ring_subst_5(A,C),x_subst(A,D,C),n_val(A,D).
great(A,B):- size(E,C),ring_subst_4(A,E),n_val(B,D),h_acceptor(E,F).
great(A,B):- ring_subst_4(B,E),ring_subst_4(A,E),ring_subst_6(A,C),sigma(E,D).
great(A,B):- ring_subst_6(A,E),ring_subst_2(B,D),polar(E,F),size(D,C).
great(A,B):- ring_subst_3(B,E),pi_doner(E,D),ring_subst_3(A,C).
great(A,B):- ring_subst_2(B,E),ring_subst_5(A,F),n_val(A,D),polarisable(F,C).
great(A,B):- x_subst(A,D,E),ring_subst_5(B,C),ring_substitutions(B,F),ring_subst_2(B,E).
great(A,B):- x_subst(B,C,E),r_subst_3(B,C),ring_subst_2(A,F),ring_subst_3(B,D).
great(A,B):- ring_subst_6(B,E),ring_subst_6(A,C),ring_subst_4(A,F),ring_subst_3(B,D).
great(A,B):- r_subst_3(A,C),x_subst(A,E,D),x_subst(B,C,D),ring_subst_5(B,F).
great(A,B):- x_subst(B,D,C),ring_subst_4(B,C),ring_substitutions(A,E),alk_groups(A,E).
great(A,B):- ring_subst_3(A,E),r_subst_2(B,C),r_subst_2(A,F),ring_subst_4(A,D).
