great(A,B):- x_subst(A,F,D),r_subst_3(B,F),r_subst_3(B,C),ring_subst_4(B,E).
great(A,B):- gt(E,C),x_subst(A,E,D),r_subst_3(B,E).
great(A,B):- pi_doner(C,F),ring_subst_2(A,E),ring_subst_6(B,C),pi_doner(E,D).
great(A,B):- alk_groups(A,F),ring_substitutions(B,F),x_subst(A,E,D),ring_subst_2(B,C).
great(A,B):- ring_subst_5(B,C),ring_subst_2(A,F),size(C,E),n_val(A,D).
great(A,B):- ring_subst_4(B,C),ring_subst_5(A,C),ring_subst_4(A,D).
great(A,B):- n_val(B,C),ring_subst_4(B,F),r_subst_3(A,E),x_subst(B,D,F).
great(A,B):- n_val(A,E),ring_subst_5(B,C),ring_subst_6(A,F),n_val(A,D).
great(A,B):- r_subst_3(B,D),r_subst_1(A,E),n_val(A,F),ring_subst_6(A,C).
great(A,B):- ring_subst_5(A,E),ring_subst_2(B,C),ring_subst_3(A,F),flex(F,D).
great(A,B):- gt(C,D),x_subst(B,D,E),n_val(A,D),gt(D,C).
great(A,B):- alk_groups(A,C),x_subst(A,F,E),ring_subst_6(B,D),ring_subst_6(A,E).
great(A,B):- ring_subst_6(A,F),r_subst_3(A,D),alk_groups(B,E),gt(E,C).
great(A,B):- r_subst_1(A,D),ring_subst_3(A,E),h_acceptor(E,C),x_subst(B,F,E).
great(A,B):- x_subst(B,E,D),r_subst_3(B,C),ring_subst_5(A,F),r_subst_3(B,E).
great(A,B):- x_subst(B,E,F),ring_subst_3(A,F),x_subst(B,C,D),ring_subst_5(A,D).
great(A,B):- ring_subst_2(A,E),ring_subst_6(B,C),ring_substitutions(A,F),r_subst_2(B,D).
great(A,B):- ring_subst_6(A,E),ring_subst_5(B,C),ring_subst_5(B,D).
great(A,B):- polar(D,C),ring_subst_2(A,E),sigma(E,F),ring_subst_2(B,D).
great(A,B):- ring_subst_3(B,C),ring_subst_2(A,C),h_doner(C,E),r_subst_2(B,D).
great(A,B):- ring_substitutions(B,E),x_subst(A,C,D),ring_subst_2(B,D),r_subst_2(B,F).
great(A,B):- r_subst_3(B,F),ring_subst_4(A,E),n_val(A,C),r_subst_1(B,D).
great(A,B):- ring_subst_3(B,C),x_subst(B,F,D),ring_subst_6(A,D),r_subst_3(A,E).
great(A,B):- ring_subst_2(B,C),ring_subst_3(A,F),alk_groups(B,E),x_subst(B,D,F).
great(A,B):- ring_subst_4(B,E),x_subst(A,C,D),ring_substitutions(A,C),ring_subst_5(A,E).
great(A,B):- x_subst(B,E,D),n_val(A,C),ring_substitutions(B,E),r_subst_3(B,E).
great(A,B):- ring_subst_4(B,F),x_subst(B,C,F),pi_acceptor(F,E),ring_substitutions(A,D).
great(A,B):- ring_subst_6(B,E),flex(E,F),h_doner(E,C),ring_substitutions(A,D).
great(A,B):- r_subst_3(B,C),alk_groups(A,F),pi_acceptor(E,D),x_subst(B,F,E).
great(A,B):- polar(D,E),ring_subst_2(B,D),ring_subst_3(A,D),sigma(D,C).
great(A,B):- ring_subst_3(B,C),n_val(B,D),ring_subst_6(A,F),pi_doner(C,E).
great(A,B):- n_val(B,E),gt(E,D),ring_subst_4(A,C),ring_subst_2(B,F).
great(A,B):- x_subst(B,C,E),alk_groups(B,D),alk_groups(A,D),ring_subst_5(B,F).
great(A,B):- gt(E,F),alk_groups(A,C),alk_groups(A,D),r_subst_3(B,E).
great(A,B):- x_subst(A,C,D),r_subst_1(B,E),ring_subst_6(A,F),ring_subst_6(A,D).
great(A,B):- ring_subst_3(A,E),ring_subst_3(A,C),ring_subst_6(B,F),ring_subst_4(B,D).
great(A,B):- ring_subst_3(A,E),ring_subst_6(B,C),ring_subst_6(A,D),x_subst(B,F,E).
great(A,B):- n_val(B,F),n_val(A,F),x_subst(B,E,C),r_subst_2(B,D).
great(A,B):- r_subst_3(B,C),alk_groups(A,F),pi_doner(E,D),x_subst(A,C,E).
great(A,B):- r_subst_2(A,E),ring_subst_5(A,F),ring_subst_6(A,C),n_val(B,D).
great(A,B):- r_subst_2(A,D),ring_subst_5(A,F),r_subst_1(B,C),ring_subst_6(B,E).
great(A,B):- alk_groups(B,C),ring_subst_4(A,E),ring_substitutions(B,F),ring_subst_3(A,D).
great(A,B):- ring_subst_4(A,E),ring_subst_4(A,C),h_doner(C,F),ring_subst_4(B,D).
great(A,B):- alk_groups(B,C),alk_groups(B,F),alk_groups(B,E),ring_subst_4(A,D).
great(A,B):- ring_subst_6(B,E),ring_subst_3(B,C),ring_subst_5(A,C),x_subst(B,D,F).
great(A,B):- r_subst_2(A,D),n_val(B,F),ring_subst_3(B,E),r_subst_3(B,C).
great(A,B):- alk_groups(B,F),ring_subst_6(B,C),h_doner(C,D),ring_subst_2(A,E).
great(A,B):- x_subst(A,C,D),size(D,E),ring_substitutions(A,C),ring_subst_6(B,D).
great(A,B):- r_subst_3(A,C),sigma(D,F),ring_subst_2(B,D),n_val(A,E).
great(A,B):- ring_subst_2(B,E),size(C,D),ring_subst_4(A,C),ring_subst_2(A,F).
great(A,B):- x_subst(B,C,E),ring_subst_3(A,F),ring_subst_5(B,D).
great(A,B):- flex(C,D),x_subst(A,E,C),ring_substitutions(A,F),r_subst_3(B,E).
great(A,B):- size(F,E),sigma(F,C),ring_subst_3(A,F),ring_substitutions(B,D).
great(A,B):- x_subst(A,E,C),x_subst(A,E,D),x_subst(A,F,C),r_subst_3(B,E).
great(A,B):- ring_substitutions(A,F),x_subst(A,E,D),ring_subst_6(B,D),ring_subst_2(B,C).
great(A,B):- r_subst_3(B,C),ring_subst_5(A,E),great_sigma(F,D),sigma(E,F).
great(A,B):- ring_subst_2(A,D),ring_subst_6(B,C),r_subst_3(B,E),alk_groups(A,E).
great(A,B):- ring_subst_4(B,E),ring_subst_6(B,C),ring_subst_2(A,F),h_doner(F,D).
great(A,B):- x_subst(A,E,C),ring_subst_4(B,C),flex(D,F),ring_subst_5(B,D).
great(A,B):- ring_subst_4(B,C),r_subst_1(A,F),x_subst(A,D,C),x_subst(B,E,C).
great(A,B):- alk_groups(A,C),alk_groups(A,F),gt(F,E),x_subst(B,C,D).
great(A,B):- ring_subst_5(B,E),alk_groups(A,D),x_subst(A,D,C),r_subst_3(A,D).
great(A,B):- h_acceptor(E,C),x_subst(B,D,E),pi_acceptor(E,F),ring_substitutions(A,D).
great(A,B):- ring_subst_6(A,E),ring_subst_4(B,D),ring_subst_6(A,D),flex(D,C).
great(A,B):- alk_groups(B,C),ring_subst_3(A,E),ring_subst_4(B,D),gt(C,F).
great(A,B):- x_subst(B,F,C),ring_subst_5(B,C),size(E,D),ring_subst_3(A,E).
great(A,B):- n_val(B,C),pi_doner(D,E),x_subst(B,C,D),ring_subst_3(A,D).
great(A,B):- ring_subst_2(B,E),ring_subst_3(A,E),x_subst(B,C,D),ring_subst_4(A,D).
great(A,B):- ring_subst_6(B,E),r_subst_3(A,C),n_val(A,F),ring_subst_3(A,D).
great(A,B):- ring_subst_2(B,E),ring_subst_4(A,E),ring_subst_3(A,C),h_acceptor(E,D).
great(A,B):- r_subst_2(A,E),ring_subst_2(B,D),ring_subst_2(B,F),sigma(F,C).
great(A,B):- gt(F,D),x_subst(A,E,C),alk_groups(B,F),r_subst_3(A,E).
great(A,B):- ring_subst_2(B,E),x_subst(A,C,E),ring_substitutions(A,D),ring_subst_5(B,F).
great(A,B):- ring_subst_4(B,E),n_val(B,C),ring_subst_5(A,F),flex(F,D).
great(A,B):- ring_subst_3(B,E),pi_doner(E,F),ring_subst_3(B,C),ring_substitutions(A,D).
great(A,B):- ring_subst_2(B,C),flex(C,E),ring_substitutions(A,D),sigma(C,F).
great(A,B):- r_subst_3(B,C),x_subst(B,D,E),r_subst_2(A,F),gt(D,C).
great(A,B):- alk_groups(B,F),n_val(B,D),pi_acceptor(C,E),x_subst(A,F,C).
great(A,B):- x_subst(B,E,D),ring_substitutions(A,E),x_subst(B,C,D),ring_subst_2(A,D).
great(A,B):- n_val(B,E),n_val(A,C),ring_substitutions(B,D),n_val(B,D).
great(A,B):- ring_subst_3(B,F),x_subst(B,E,F),ring_subst_6(A,D),size(D,C).
great(A,B):- sigma(F,E),r_subst_2(B,C),ring_subst_3(A,F),x_subst(B,D,F).
great(A,B):- pi_doner(C,F),ring_subst_6(B,C),r_subst_2(B,D),alk_groups(A,E).
great(A,B):- r_subst_2(A,E),alk_groups(B,D),ring_subst_5(A,F),pi_acceptor(F,C).
great(A,B):- ring_subst_5(A,E),ring_subst_5(B,C),size(E,D),h_doner(E,F).
great(A,B):- r_subst_3(A,F),ring_subst_6(A,D),r_subst_1(B,C),alk_groups(B,E).
great(A,B):- ring_subst_5(B,C),x_subst(A,D,C),alk_groups(B,E).
great(A,B):- ring_subst_2(B,E),sigma(C,D),ring_subst_3(B,E),ring_subst_4(A,C).
great(A,B):- alk_groups(B,F),ring_substitutions(B,C),ring_substitutions(B,D),n_val(A,E).
great(A,B):- sigma(C,D),h_doner(F,E),ring_subst_4(B,F),ring_subst_5(A,C).
great(A,B):- pi_doner(C,F),x_subst(A,E,C),alk_groups(A,D),alk_groups(B,E).
great(A,B):- r_subst_1(A,D),x_subst(A,C,E),ring_subst_4(B,E),r_subst_1(A,F).
great(A,B):- x_subst(B,D,C),ring_subst_6(B,C),x_subst(A,F,C),alk_groups(A,E).
great(A,B):- ring_subst_2(B,D),r_subst_1(A,E),ring_substitutions(A,C),ring_subst_2(A,D).
great(A,B):- alk_groups(B,C),ring_subst_2(B,F),ring_substitutions(B,E),ring_subst_3(A,D).
great(A,B):- ring_subst_3(B,C),r_subst_2(A,E),ring_subst_6(A,F),r_subst_1(B,D).
great(A,B):- x_subst(A,D,E),sigma(F,C),ring_subst_4(A,F),ring_subst_5(B,E).
great(A,B):- ring_subst_4(B,F),alk_groups(A,D),x_subst(B,E,C),ring_subst_5(A,F).
great(A,B):- h_acceptor(C,E),ring_subst_4(A,C),ring_subst_2(B,F),r_subst_1(B,D).
great(A,B):- alk_groups(A,F),r_subst_3(A,D),ring_subst_4(B,C),h_acceptor(C,E).
great(A,B):- n_val(B,C),alk_groups(B,D),polarisable(F,E),x_subst(A,C,F).
great(A,B):- ring_subst_6(B,E),size(E,C),n_val(B,D),n_val(A,D).
great(A,B):- ring_subst_3(A,E),ring_subst_4(B,C),r_subst_3(A,D),polar(E,F).
great(A,B):- ring_subst_2(A,E),ring_subst_2(B,C),size(E,D).
great(A,B):- r_subst_1(B,C),ring_subst_4(B,D),ring_subst_6(A,D),r_subst_3(A,E).
great(A,B):- n_val(B,E),r_subst_3(A,C),ring_subst_6(B,D),alk_groups(A,E).
great(A,B):- size(D,C),ring_subst_4(B,D),ring_subst_5(A,D).
great(A,B):- ring_subst_3(A,C),alk_groups(B,D),ring_substitutions(B,F),ring_subst_6(B,E).
great(A,B):- x_subst(A,C,D),x_subst(B,C,F),x_subst(B,E,F),ring_subst_5(B,D).
great(A,B):- ring_substitutions(B,F),r_subst_3(A,F),r_subst_1(A,E),x_subst(A,D,C).
great(A,B):- ring_subst_6(B,E),polarisable(C,D),x_subst(A,F,E),x_subst(A,F,C).
great(A,B):- x_subst(A,C,D),x_subst(B,C,F),ring_subst_6(B,D),ring_subst_3(A,E).
great(A,B):- n_val(A,C),r_subst_2(B,F),r_subst_3(B,E),ring_subst_6(B,D).
great(A,B):- n_val(A,E),x_subst(A,E,C),ring_subst_2(B,D),ring_subst_6(A,D).
great(A,B):- x_subst(A,D,E),ring_subst_6(B,C),ring_subst_6(B,F),n_val(A,D).
great(A,B):- r_subst_3(B,F),r_subst_2(A,E),h_doner(D,C),ring_subst_4(A,D).
great(A,B):- r_subst_3(B,D),x_subst(A,F,E),ring_substitutions(A,C).
great(A,B):- alk_groups(B,F),x_subst(A,E,D),ring_subst_4(A,D),polarisable(D,C).
great(A,B):- r_subst_1(A,D),r_subst_3(B,C),ring_substitutions(A,C),ring_substitutions(B,E).
great(A,B):- gt(F,D),r_subst_3(A,F),ring_subst_3(B,C),polar(C,E).
great(A,B):- ring_subst_3(A,E),alk_groups(A,F),r_subst_1(B,C),r_subst_2(B,D).
great(A,B):- r_subst_2(A,D),r_subst_3(A,C),ring_subst_3(B,E),ring_subst_3(B,F).
great(A,B):- ring_subst_2(B,E),ring_subst_2(B,C),ring_subst_5(A,F),ring_subst_2(B,D).
great(A,B):- ring_subst_2(A,E),ring_subst_3(B,C),ring_subst_6(B,F),r_subst_3(A,D).
great(A,B):- ring_subst_6(B,E),n_val(A,F),polar(E,C),ring_subst_2(B,D).
great(A,B):- ring_subst_2(B,E),h_acceptor(E,C),n_val(B,D),r_subst_1(A,F).
great(A,B):- alk_groups(B,F),h_doner(D,C),ring_subst_6(A,D),r_subst_3(A,E).
great(A,B):- r_subst_2(A,D),ring_subst_5(B,C),ring_subst_4(A,C),x_subst(A,F,E).
great(A,B):- r_subst_3(B,C),gt(C,E),r_subst_1(B,F),ring_subst_3(A,D).
great(A,B):- ring_subst_2(B,C),flex(C,E),ring_subst_3(A,F),great_flex(E,D).
great(A,B):- r_subst_3(B,C),r_subst_2(A,E),ring_subst_6(A,D),n_val(A,C).
great(A,B):- gt(D,E),r_subst_3(B,D),ring_subst_3(A,F),ring_subst_6(A,C).
great(A,B):- n_val(A,E),n_val(B,C),ring_subst_2(B,D),r_subst_3(A,E).
great(A,B):- r_subst_2(A,D),ring_subst_3(A,E),pi_doner(E,C),ring_subst_5(B,E).
great(A,B):- polarisable(C,F),ring_subst_5(B,C),great_polari(F,E),n_val(A,D).
great(A,B):- ring_subst_5(A,E),ring_subst_6(B,C),ring_subst_4(B,D),size(D,F).
great(A,B):- ring_subst_3(A,E),polarisable(E,D),x_subst(B,C,F),ring_subst_6(A,F).
great(A,B):- r_subst_3(B,F),flex(C,E),ring_subst_5(B,D),x_subst(A,F,C).
great(A,B):- pi_doner(C,F),ring_subst_3(B,C),r_subst_1(A,E),size(C,D).
great(A,B):- sigma(C,E),x_subst(B,D,C),ring_substitutions(B,F),ring_subst_5(A,C).
