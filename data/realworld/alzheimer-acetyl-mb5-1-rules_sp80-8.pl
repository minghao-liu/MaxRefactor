great(A,B):- x_subst(B,D,C),alk_groups(B,D),x_subst(B,E,C),ring_substitutions(A,D).
great(A,B):- ring_subst_3(A,E),sigma(D,C),ring_subst_4(B,D),ring_subst_6(B,D).
great(A,B):- x_subst(A,E,C),ring_subst_6(A,C),ring_subst_3(B,D),ring_subst_3(A,D).
great(A,B):- ring_substitutions(B,E),ring_subst_2(B,C),x_subst(A,D,C),ring_substitutions(B,D).
great(A,B):- ring_subst_2(B,E),pi_acceptor(E,F),r_subst_1(A,C),ring_subst_6(B,D).
great(A,B):- flex(C,D),r_subst_1(B,E),ring_subst_6(A,C),x_subst(A,F,C).
great(A,B):- sigma(C,E),ring_subst_3(B,C),pi_acceptor(D,F),ring_subst_6(A,D).
great(A,B):- ring_subst_3(B,C),ring_subst_4(A,C),ring_subst_5(A,D),flex(D,E).
great(A,B):- ring_subst_2(A,F),x_subst(A,E,D),ring_subst_2(B,D),flex(D,C).
great(A,B):- gt(E,D),n_val(B,D),x_subst(A,D,C),alk_groups(A,E).
great(A,B):- ring_subst_6(A,E),size(E,D),ring_subst_6(A,C),ring_subst_6(B,F).
great(A,B):- ring_subst_4(A,E),ring_substitutions(B,C),ring_subst_3(B,F),r_subst_3(A,D).
great(A,B):- n_val(A,C),ring_subst_2(B,D),x_subst(B,F,E).
great(A,B):- x_subst(B,E,D),n_val(A,C),ring_substitutions(B,E),r_subst_3(B,E).
great(A,B):- alk_groups(B,C),ring_subst_6(A,F),ring_subst_2(B,E),n_val(A,D).
great(A,B):- r_subst_1(B,F),r_subst_1(A,E),x_subst(A,D,C),r_subst_1(A,F).
great(A,B):- ring_subst_2(B,E),ring_subst_3(B,C),ring_subst_4(A,C),pi_doner(E,D).
great(A,B):- ring_subst_3(A,C),great_size(E,F),alk_groups(B,D),size(C,E).
great(A,B):- ring_subst_2(A,E),polarisable(E,D),ring_subst_4(B,F),r_subst_2(B,C).
great(A,B):- size(C,E),ring_subst_4(B,C),alk_groups(B,D),ring_subst_6(A,C).
great(A,B):- x_subst(B,F,D),ring_subst_6(A,D),x_subst(A,C,E),ring_subst_4(A,D).
great(A,B):- r_subst_3(A,C),r_subst_1(A,E),r_subst_3(B,F),ring_substitutions(B,D).
great(A,B):- x_subst(B,C,F),alk_groups(A,D),r_subst_3(B,E),r_subst_3(A,D).
great(A,B):- r_subst_2(A,D),ring_subst_6(B,C),ring_subst_2(B,E),polarisable(E,F).
great(A,B):- ring_subst_6(A,C),ring_subst_5(A,F),alk_groups(B,E),ring_subst_3(A,D).
great(A,B):- n_val(B,E),ring_subst_2(B,C),ring_subst_6(A,C),ring_subst_2(A,D).
great(A,B):- ring_subst_3(B,E),ring_subst_3(A,C),x_subst(B,F,D),ring_subst_2(B,D).
great(A,B):- x_subst(A,E,C),n_val(B,F),ring_subst_4(A,D),alk_groups(A,E).
great(A,B):- x_subst(B,D,C),ring_subst_4(B,C),ring_subst_2(A,E),r_subst_1(B,F).
great(A,B):- x_subst(B,E,D),ring_subst_2(B,C),ring_subst_2(A,C),ring_subst_4(A,F).
great(A,B):- ring_subst_5(A,E),ring_subst_6(A,F),ring_subst_3(A,F),x_subst(B,C,D).
great(A,B):- size(C,F),ring_subst_4(A,E),ring_subst_2(B,C),sigma(C,D).
great(A,B):- x_subst(A,E,C),x_subst(B,E,F),ring_subst_6(B,F),h_doner(F,D).
great(A,B):- ring_subst_4(A,E),ring_subst_4(B,D),r_subst_1(B,F),sigma(E,C).
great(A,B):- r_subst_3(B,F),ring_subst_2(B,C),h_acceptor(C,D),n_val(A,E).
great(A,B):- ring_subst_6(A,E),ring_subst_6(B,C),ring_subst_3(A,F),pi_acceptor(C,D).
great(A,B):- r_subst_3(B,C),alk_groups(A,F),ring_subst_5(B,E),ring_subst_3(A,D).
great(A,B):- x_subst(B,E,D),r_subst_3(A,C),n_val(A,C),ring_substitutions(A,F).
great(A,B):- ring_subst_6(B,E),pi_acceptor(E,C),ring_subst_5(A,D).
great(A,B):- n_val(A,C),alk_groups(B,D),ring_subst_5(A,F),alk_groups(A,E).
great(A,B):- ring_subst_5(A,E),ring_subst_4(A,C),size(E,F),r_subst_2(B,D).
great(A,B):- alk_groups(A,C),alk_groups(B,D),ring_subst_3(A,F),ring_subst_4(A,E).
great(A,B):- r_subst_3(B,F),ring_subst_4(A,C),r_subst_2(B,D),x_subst(B,F,E).
great(A,B):- r_subst_3(B,C),alk_groups(A,C),n_val(B,E),ring_substitutions(A,D).
great(A,B):- ring_subst_2(B,E),flex(C,D),ring_subst_5(B,E),x_subst(A,F,C).
great(A,B):- r_subst_2(A,D),r_subst_3(B,C),ring_subst_5(A,F),size(F,E).
great(A,B):- x_subst(B,E,D),r_subst_3(B,E),n_val(A,F),alk_groups(B,C).
great(A,B):- ring_substitutions(B,E),ring_substitutions(A,E),x_subst(A,D,F),r_subst_1(B,C).
great(A,B):- r_subst_3(A,C),polar(F,D),ring_subst_6(B,F),ring_subst_4(A,E).
great(A,B):- ring_subst_4(B,E),pi_acceptor(D,C),ring_subst_2(A,D),ring_subst_5(B,F).
great(A,B):- flex(C,E),flex(F,E),x_subst(A,D,C),x_subst(B,D,F).
great(A,B):- sigma(F,E),ring_subst_2(B,F),n_val(B,C),ring_subst_2(A,D).
great(A,B):- ring_subst_3(B,E),ring_subst_2(A,C),ring_subst_5(A,F),pi_acceptor(C,D).
great(A,B):- r_subst_3(B,F),ring_subst_5(A,C),ring_subst_5(B,E),r_subst_1(B,D).
great(A,B):- ring_subst_2(A,C),ring_subst_3(A,F),ring_subst_5(B,E),ring_subst_3(A,D).
great(A,B):- flex(E,F),ring_subst_6(A,E),ring_subst_4(B,C),r_subst_2(B,D).
great(A,B):- r_subst_3(B,F),r_subst_2(B,E),ring_subst_6(A,C),r_subst_1(B,D).
great(A,B):- ring_subst_3(B,E),ring_substitutions(A,C),pi_doner(E,F),pi_acceptor(E,D).
great(A,B):- ring_subst_6(B,C),sigma(F,E),ring_subst_6(A,F),size(F,D).
great(A,B):- x_subst(B,F,C),size(C,D),n_val(A,F),n_val(A,E).
great(A,B):- r_subst_3(B,C),ring_subst_6(A,D),r_subst_3(B,E).
great(A,B):- x_subst(A,E,C),size(F,D),ring_substitutions(A,E),ring_subst_4(B,F).
great(A,B):- ring_substitutions(B,E),ring_subst_6(B,C),ring_subst_5(A,F),flex(C,D).
great(A,B):- n_val(B,E),ring_subst_4(B,C),ring_substitutions(A,F),ring_subst_2(B,D).
great(A,B):- x_subst(B,C,E),ring_subst_6(A,E),n_val(A,F),n_val(A,D).
great(A,B):- x_subst(B,E,D),gt(C,E),x_subst(B,C,D),ring_subst_2(A,D).
great(A,B):- ring_subst_2(A,F),x_subst(A,C,E),ring_substitutions(B,D).
great(A,B):- alk_groups(A,C),r_subst_3(A,F),x_subst(A,C,E),ring_subst_4(B,D).
great(A,B):- ring_subst_3(A,C),x_subst(B,F,C),ring_substitutions(A,E),ring_subst_6(A,D).
great(A,B):- r_subst_2(B,E),x_subst(A,D,F),r_subst_2(A,C).
great(A,B):- ring_subst_3(B,E),r_subst_3(A,D),ring_substitutions(A,C),ring_substitutions(B,D).
great(A,B):- sigma(C,D),ring_subst_3(B,C),sigma(C,E),ring_subst_5(A,F).
great(A,B):- polarisable(D,C),r_subst_1(A,E),ring_subst_2(B,D),r_subst_2(A,F).
great(A,B):- ring_subst_4(A,F),ring_subst_6(B,C),flex(C,E),alk_groups(A,D).
great(A,B):- ring_subst_4(B,E),x_subst(A,C,D),ring_subst_6(A,D),polarisable(D,F).
great(A,B):- r_subst_3(B,F),ring_subst_6(A,E),x_subst(B,F,D),x_subst(B,C,D).
great(A,B):- r_subst_3(B,C),r_subst_1(A,E),alk_groups(A,D),n_val(A,D).
great(A,B):- alk_groups(A,C),ring_subst_4(B,F),polar(E,D),ring_subst_6(A,E).
great(A,B):- ring_substitutions(B,E),n_val(A,C),r_subst_1(A,F),r_subst_2(B,D).
great(A,B):- ring_subst_3(A,E),r_subst_3(B,D),r_subst_3(A,D),ring_substitutions(A,C).
