great(A,B):- n_val(B,E),x_subst(A,E,C),alk_groups(B,E),x_subst(B,D,F).
great(A,B):- n_val(B,E),x_subst(A,D,F),ring_subst_2(A,F),x_subst(A,D,C).
great(A,B):- x_subst(A,E,C),r_subst_3(A,F),n_val(B,F),pi_doner(C,D).
great(A,B):- ring_subst_2(B,E),sigma(E,F),x_subst(A,D,C),ring_substitutions(A,D).
great(A,B):- ring_subst_2(B,E),polar(E,C),ring_subst_4(A,D),ring_subst_5(B,F).
great(A,B):- ring_subst_6(B,E),ring_subst_6(B,C),ring_subst_6(A,C),ring_subst_2(B,D).
great(A,B):- ring_subst_6(B,C),ring_subst_3(A,C),polarisable(C,E),ring_subst_5(A,D).
great(A,B):- ring_subst_4(B,E),ring_subst_5(A,C),h_acceptor(E,F),n_val(A,D).
great(A,B):- ring_subst_2(B,C),ring_subst_2(A,F),pi_acceptor(C,D),r_subst_3(B,E).
great(A,B):- pi_acceptor(C,E),ring_subst_5(B,F),x_subst(A,D,C),ring_substitutions(B,D).
great(A,B):- gt(F,D),x_subst(B,D,C),ring_subst_6(A,E),n_val(A,F).
great(A,B):- ring_substitutions(A,E),ring_subst_4(B,F),ring_subst_5(A,D),flex(F,C).
great(A,B):- r_subst_3(B,C),ring_subst_3(A,E),pi_doner(F,D),x_subst(A,C,F).
great(A,B):- x_subst(B,D,E),r_subst_2(A,C),gt(D,F),ring_substitutions(B,D).
great(A,B):- ring_subst_4(B,C),x_subst(B,E,C),n_val(A,D),x_subst(B,D,F).
great(A,B):- r_subst_3(B,C),n_val(B,E),ring_subst_4(A,F),r_subst_1(B,D).
great(A,B):- r_subst_3(A,C),polarisable(F,D),ring_subst_4(B,F),ring_subst_6(A,E).
great(A,B):- ring_subst_3(A,C),alk_groups(B,D),ring_subst_6(B,E),ring_subst_2(B,F).
great(A,B):- ring_subst_3(B,E),ring_subst_6(A,F),ring_subst_6(A,C),x_subst(B,D,E).
great(A,B):- r_subst_2(A,D),n_val(A,C),ring_subst_2(B,F),alk_groups(A,E).
great(A,B):- ring_substitutions(B,E),ring_subst_6(A,C),flex(C,F),n_val(A,D).
great(A,B):- pi_acceptor(E,C),ring_subst_4(A,E),size(E,D),ring_subst_5(B,E).
great(A,B):- x_subst(A,E,C),r_subst_3(B,F),alk_groups(B,E),ring_subst_4(A,D).
great(A,B):- ring_substitutions(B,E),ring_subst_6(A,C),h_doner(C,F),x_subst(A,D,C).
great(A,B):- r_subst_1(A,D),ring_subst_6(A,C),r_subst_1(B,F),h_acceptor(C,E).
great(A,B):- n_val(A,C),x_subst(B,C,F),gt(C,D),r_subst_1(A,E).
great(A,B):- ring_substitutions(B,C),gt(C,E),ring_subst_3(A,F),ring_subst_2(A,D).
great(A,B):- ring_subst_2(A,E),x_subst(A,F,E),ring_subst_5(B,D),r_subst_1(A,C).
great(A,B):- ring_subst_4(B,E),x_subst(B,D,C),ring_subst_3(A,F),x_subst(B,D,F).
great(A,B):- ring_subst_3(B,D),x_subst(B,E,C),ring_subst_5(A,C).
great(A,B):- alk_groups(B,F),sigma(D,E),ring_subst_6(A,C),ring_subst_2(B,D).
great(A,B):- x_subst(A,D,E),ring_subst_2(A,C),x_subst(B,D,E),r_subst_2(A,F).
great(A,B):- ring_subst_3(A,C),flex(D,E),ring_subst_2(B,F),ring_subst_5(A,D).
great(A,B):- x_subst(A,D,F),alk_groups(A,D),x_subst(B,E,C),ring_subst_2(B,F).
great(A,B):- r_subst_3(A,C),x_subst(A,C,D),ring_subst_4(A,E),x_subst(B,F,E).
great(A,B):- x_subst(B,E,D),ring_subst_3(A,F),gt(E,C),r_subst_3(A,E).
great(A,B):- x_subst(B,E,D),r_subst_3(A,C),x_subst(B,E,F),ring_subst_4(A,F).
great(A,B):- r_subst_3(B,C),r_subst_1(A,E),ring_subst_2(A,F),ring_subst_3(A,D).
great(A,B):- n_val(A,E),n_val(A,C),r_subst_2(B,F),ring_substitutions(A,D).
great(A,B):- polarisable(F,E),ring_subst_2(A,F),ring_subst_2(B,D),sigma(D,C).
great(A,B):- flex(F,C),ring_subst_6(A,F),ring_subst_2(B,D),pi_doner(D,E).
great(A,B):- ring_subst_6(A,E),ring_subst_2(B,C),ring_subst_5(A,D),x_subst(B,F,E).
great(A,B):- ring_subst_4(B,F),ring_subst_4(A,C),x_subst(A,D,C),ring_subst_6(A,E).
great(A,B):- x_subst(A,D,E),pi_doner(E,C),r_subst_3(B,D),n_val(A,D).
great(A,B):- alk_groups(B,C),n_val(A,F),ring_subst_5(B,E),ring_substitutions(B,D).
great(A,B):- x_subst(A,D,E),ring_subst_5(A,E),r_subst_1(B,F),ring_substitutions(A,C).
great(A,B):- alk_groups(A,C),alk_groups(B,F),r_subst_1(B,D),x_subst(B,F,E).
great(A,B):- alk_groups(B,C),ring_subst_4(A,E),ring_subst_3(A,F),flex(E,D).
great(A,B):- x_subst(A,E,C),polarisable(F,D),x_subst(B,E,F),ring_substitutions(A,E).
great(A,B):- ring_subst_6(B,C),ring_subst_4(B,D),ring_subst_2(A,F),x_subst(B,E,C).
great(A,B):- ring_subst_3(A,E),n_val(B,C),ring_subst_2(B,D),gt(C,F).
great(A,B):- alk_groups(A,C),x_subst(B,D,E),ring_substitutions(B,D),gt(C,F).
great(A,B):- gt(F,D),alk_groups(B,F),ring_substitutions(A,C),ring_subst_4(A,E).
great(A,B):- ring_subst_2(B,D),r_subst_2(A,E),r_subst_2(B,F),ring_subst_5(A,C).
great(A,B):- ring_subst_6(B,F),ring_subst_5(B,C),r_subst_1(A,E),x_subst(A,D,C).
great(A,B):- ring_subst_2(B,C),pi_acceptor(C,F),h_doner(C,E),ring_subst_2(A,D).
great(A,B):- x_subst(A,C,D),r_subst_3(A,F),ring_subst_4(B,D),h_acceptor(D,E).
great(A,B):- x_subst(B,E,D),ring_subst_3(B,C),ring_subst_5(A,C),ring_subst_3(B,D).
great(A,B):- size(C,E),ring_subst_2(A,C),ring_subst_5(A,F),ring_substitutions(B,D).
great(A,B):- alk_groups(B,F),size(D,E),ring_subst_3(A,D),sigma(D,C).
great(A,B):- x_subst(B,D,C),ring_subst_4(B,C),h_doner(C,F),ring_subst_4(A,E).
great(A,B):- polarisable(F,D),ring_subst_2(A,F),x_subst(B,E,C),ring_subst_5(B,F).
great(A,B):- ring_subst_4(A,E),ring_substitutions(B,C),ring_subst_6(A,E),ring_subst_3(B,D).
great(A,B):- ring_subst_3(A,E),alk_groups(A,F),ring_subst_3(A,C),r_subst_1(B,D).
great(A,B):- ring_subst_6(B,C),r_subst_3(A,D),sigma(C,F),r_subst_3(A,E).
great(A,B):- ring_substitutions(A,E),x_subst(A,D,C),r_subst_1(B,F),r_subst_3(A,E).
great(A,B):- ring_subst_5(A,E),x_subst(B,D,C),n_val(B,D),r_subst_2(B,F).
great(A,B):- ring_subst_3(B,E),ring_subst_5(A,E),ring_subst_3(B,C),r_subst_1(B,D).
great(A,B):- ring_subst_5(A,E),pi_doner(F,C),x_subst(B,D,F).
great(A,B):- x_subst(B,E,D),r_subst_3(B,F),ring_subst_3(A,C),ring_subst_2(A,D).
great(A,B):- ring_subst_3(A,E),ring_subst_2(B,C),ring_subst_6(A,D),x_subst(B,F,E).
great(A,B):- ring_subst_2(B,E),ring_subst_2(B,F),ring_substitutions(A,C),h_acceptor(E,D).
great(A,B):- x_subst(B,E,D),alk_groups(A,C),ring_subst_6(A,D),pi_doner(D,F).
great(A,B):- x_subst(B,E,D),ring_subst_6(B,C),ring_subst_2(B,F),ring_subst_4(A,F).
great(A,B):- r_subst_3(A,C),x_subst(A,C,D),r_subst_3(B,C),n_val(A,C).
great(A,B):- ring_subst_3(A,E),n_val(B,C),sigma(D,F),ring_subst_6(B,D).
great(A,B):- ring_subst_2(A,E),ring_subst_2(B,F),h_doner(E,C),ring_subst_3(B,D).
great(A,B):- ring_subst_6(A,E),ring_subst_3(B,D),r_subst_1(B,C),r_subst_2(B,F).
great(A,B):- ring_substitutions(B,E),ring_subst_6(A,C),ring_subst_5(A,C),x_subst(A,D,C).
great(A,B):- ring_subst_6(B,E),x_subst(B,C,F),ring_subst_5(B,D),ring_subst_6(A,D).
great(A,B):- flex(F,C),ring_subst_6(B,F),alk_groups(B,E),n_val(A,D).
great(A,B):- r_subst_3(B,F),ring_subst_4(B,C),size(C,D),alk_groups(A,E).
great(A,B):- ring_subst_4(B,E),h_doner(E,F),ring_subst_5(A,C),great_h_don(F,D).
great(A,B):- size(D,C),n_val(A,F),ring_subst_5(B,D),r_subst_3(A,E).
great(A,B):- ring_subst_5(A,E),ring_subst_3(B,C),ring_subst_4(B,D),x_subst(A,F,C).
great(A,B):- alk_groups(B,C),pi_doner(E,D),x_subst(A,C,E),ring_subst_4(B,E).
great(A,B):- r_subst_3(B,C),r_subst_1(A,E),ring_subst_6(A,D),x_subst(A,C,F).
great(A,B):- alk_groups(B,D),ring_substitutions(B,D),r_subst_3(A,E),x_subst(A,C,F).
great(A,B):- ring_subst_4(A,F),x_subst(B,D,E),sigma(F,C),n_val(A,D).
great(A,B):- x_subst(B,F,C),ring_subst_3(B,C),alk_groups(A,D),x_subst(B,F,E).
great(A,B):- ring_subst_4(B,F),polarisable(D,E),ring_subst_6(A,D),x_subst(A,C,F).
great(A,B):- h_doner(E,F),ring_subst_5(A,C),ring_subst_5(B,E),h_doner(E,D).
great(A,B):- ring_subst_3(A,E),ring_subst_5(B,C),ring_subst_6(A,E),r_subst_2(B,D).
great(A,B):- x_subst(A,D,E),ring_subst_4(A,F),r_subst_1(A,C),ring_subst_6(B,E).
great(A,B):- ring_subst_2(B,D),ring_subst_6(A,C),ring_subst_5(B,E),x_subst(A,F,C).
great(A,B):- pi_acceptor(C,E),ring_subst_6(B,C),pi_acceptor(C,F),x_subst(A,D,C).
great(A,B):- ring_subst_4(A,E),r_subst_2(B,C),h_acceptor(E,D),n_val(A,F).
great(A,B):- sigma(C,E),x_subst(B,F,C),ring_subst_6(A,C),ring_subst_5(B,D).
great(A,B):- x_subst(A,D,E),r_subst_3(A,F),x_subst(B,D,E),r_subst_1(B,C).
great(A,B):- x_subst(A,F,D),r_subst_2(B,E),n_val(B,F),x_subst(B,C,D).
