great(A,B):- n_val(A,C),ring_subst_5(A,E),size(E,D),r_subst_1(B,F).
great(A,B):- ring_subst_6(B,C),ring_subst_6(A,F),r_subst_3(B,E),n_val(A,D).
great(A,B):- pi_acceptor(D,E),ring_subst_4(A,D),x_subst(B,C,D),r_subst_2(A,F).
great(A,B):- r_subst_3(A,C),ring_subst_3(B,D),pi_doner(D,E),r_subst_1(B,F).
great(A,B):- ring_subst_4(B,C),ring_subst_2(A,F),flex(F,D),flex(F,E).
great(A,B):- ring_substitutions(B,E),ring_subst_2(B,D),x_subst(B,C,D),r_subst_1(A,F).
great(A,B):- ring_subst_3(B,E),n_val(B,F),ring_subst_6(A,C),r_subst_2(B,D).
great(A,B):- ring_subst_6(B,C),great_polar(D,E),ring_subst_2(A,F),polar(C,D).
great(A,B):- r_subst_3(B,F),r_subst_3(A,D),x_subst(A,D,C),h_acceptor(C,E).
great(A,B):- ring_subst_2(B,C),x_subst(B,E,F),ring_subst_4(A,C),ring_subst_2(A,D).
great(A,B):- ring_subst_2(B,E),ring_subst_4(A,C),x_subst(A,F,E),pi_acceptor(C,D).
great(A,B):- ring_subst_6(B,E),r_subst_3(A,C),n_val(B,F),ring_subst_3(B,D).
great(A,B):- ring_subst_4(B,E),alk_groups(A,C),h_doner(E,F),r_subst_3(B,D).
great(A,B):- x_subst(B,D,C),r_subst_3(A,F),ring_subst_6(A,E),ring_subst_2(A,E).
great(A,B):- r_subst_3(B,C),r_subst_1(B,D),ring_subst_2(A,F),alk_groups(A,E).
great(A,B):- ring_subst_6(B,C),gt(D,E),ring_substitutions(A,D),alk_groups(B,E).
great(A,B):- x_subst(A,F,D),alk_groups(A,C),x_subst(A,E,D),ring_subst_2(B,D).
great(A,B):- ring_subst_2(B,E),ring_subst_5(A,E),n_val(B,C),flex(E,D).
great(A,B):- ring_subst_5(B,C),ring_subst_5(A,C),ring_subst_2(B,D),r_subst_3(A,E).
great(A,B):- r_subst_1(A,D),ring_subst_3(B,C),r_subst_2(A,E),pi_doner(C,F).
great(A,B):- flex(C,D),ring_subst_2(B,F),x_subst(B,E,C),x_subst(A,E,F).
great(A,B):- r_subst_1(B,E),n_val(A,C),n_val(A,F),ring_subst_4(B,D).
great(A,B):- ring_subst_3(B,C),great_polar(D,E),ring_subst_5(A,F),polar(C,D).
great(A,B):- x_subst(B,C,E),gt(C,D),r_subst_3(A,D),ring_subst_5(B,E).
great(A,B):- pi_acceptor(E,C),ring_subst_6(A,E),ring_subst_4(B,F),flex(F,D).
great(A,B):- ring_subst_2(B,E),alk_groups(A,F),ring_subst_2(A,C),x_subst(B,D,E).
great(A,B):- ring_subst_4(B,C),r_subst_3(A,D),h_doner(C,F),alk_groups(B,E).
great(A,B):- ring_subst_5(A,E),r_subst_3(B,D),r_subst_2(B,C),n_val(A,D).
great(A,B):- r_subst_3(A,C),ring_subst_5(B,E),n_val(B,D),x_subst(A,C,F).
great(A,B):- ring_subst_4(B,D),x_subst(A,E,D),ring_subst_3(A,F),sigma(D,C).
great(A,B):- ring_subst_6(B,C),r_subst_2(B,E),ring_subst_2(A,C),ring_subst_5(B,D).
great(A,B):- ring_subst_2(B,D),ring_subst_4(A,E),ring_substitutions(A,C),ring_subst_3(A,D).
great(A,B):- h_doner(F,E),ring_subst_4(B,F),r_subst_2(B,C),ring_substitutions(A,D).
great(A,B):- ring_subst_3(A,E),x_subst(B,F,D),h_doner(E,C),n_val(A,F).
great(A,B):- r_subst_3(A,F),x_subst(B,F,D),ring_subst_2(B,C),x_subst(B,F,E).
great(A,B):- ring_subst_3(B,E),n_val(B,C),polar(E,F),n_val(A,D).
great(A,B):- ring_subst_2(B,E),h_doner(C,F),x_subst(A,D,C),ring_subst_6(B,E).
great(A,B):- x_subst(B,C,E),ring_subst_2(B,E),n_val(B,D),r_subst_2(A,F).
great(A,B):- x_subst(B,E,D),n_val(B,C),n_val(A,C),r_subst_3(A,E).
great(A,B):- gt(D,F),x_subst(A,F,E),alk_groups(B,D),ring_substitutions(A,C).
great(A,B):- x_subst(A,D,E),ring_subst_3(A,F),alk_groups(B,C),gt(D,C).
great(A,B):- gt(E,D),ring_subst_2(B,C),ring_subst_4(B,C),alk_groups(A,E).
great(A,B):- sigma(F,D),ring_subst_4(A,E),ring_subst_6(B,C),ring_subst_4(B,F).
great(A,B):- ring_subst_5(B,C),pi_acceptor(D,F),x_subst(A,E,D),ring_subst_2(B,D).
great(A,B):- r_subst_2(B,C),r_subst_3(B,F),x_subst(B,D,E),n_val(A,D).
great(A,B):- x_subst(A,E,C),pi_acceptor(F,D),x_subst(B,E,F),ring_subst_3(A,F).
great(A,B):- size(F,D),ring_subst_5(A,F),r_subst_2(B,C),ring_subst_5(B,E).
great(A,B):- ring_substitutions(B,E),n_val(A,C),ring_subst_3(B,D),r_subst_3(A,E).
great(A,B):- pi_acceptor(D,E),ring_subst_6(B,C),ring_subst_3(B,F),ring_subst_5(A,D).
great(A,B):- h_acceptor(C,F),alk_groups(B,D),x_subst(A,D,C),gt(D,E).
great(A,B):- r_subst_3(B,F),pi_doner(E,D),x_subst(A,F,C),ring_subst_4(A,E).
great(A,B):- gt(E,C),x_subst(B,E,F),ring_subst_5(A,D),alk_groups(B,E).
great(A,B):- ring_subst_3(B,C),ring_subst_4(A,F),ring_subst_5(B,D),polar(F,E).
great(A,B):- ring_subst_2(B,E),n_val(A,C),ring_subst_5(A,D),r_subst_1(A,F).
great(A,B):- x_subst(A,C,D),alk_groups(A,C),r_subst_1(A,F),r_subst_1(B,E).
great(A,B):- r_subst_3(B,C),n_val(B,C),n_val(A,C),x_subst(B,D,E).
great(A,B):- n_val(B,E),h_acceptor(F,C),ring_subst_5(A,F),r_subst_1(B,D).
great(A,B):- alk_groups(A,C),n_val(A,C),ring_subst_2(A,D),alk_groups(B,E).
great(A,B):- ring_subst_5(B,C),great_size(F,E),ring_subst_6(A,D),size(D,F).
great(A,B):- ring_subst_4(A,E),h_doner(E,C),ring_subst_2(B,D),polarisable(D,F).
