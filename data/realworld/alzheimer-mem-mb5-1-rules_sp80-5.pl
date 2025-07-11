great_rsd(A,B):- ring_subst_2(A,C),ring_subst_6(B,C),ring_subst_2(B,E),h_acceptor(E,D).
great_rsd(A,B):- n_val(A,F),h_doner(E,D),x_subst(B,C,E),ring_subst_2(A,E).
great_rsd(A,B):- r_subst_1(A,E),ring_substitutions(B,D),ring_subst_6(A,C),ring_subst_2(B,C).
great_rsd(A,B):- ring_subst_2(B,D),pi_doner(D,C),n_val(A,E).
great_rsd(A,B):- n_val(B,D),size(E,C),x_subst(A,D,E),gt(D,F).
great_rsd(A,B):- r_subst_3(A,D),ring_subst_2(B,C),n_val(A,D),alk_groups(B,E).
great_rsd(A,B):- x_subst(B,C,D),ring_subst_6(A,F),h_doner(D,E),ring_substitutions(A,C).
great_rsd(A,B):- x_subst(B,F,E),n_val(B,C),ring_subst_6(A,D),ring_substitutions(B,C).
great_rsd(A,B):- x_subst(A,E,D),ring_subst_4(B,F),x_subst(A,C,D),gt(E,C).
great_rsd(A,B):- ring_subst_6(A,F),ring_subst_6(B,C),ring_subst_4(A,C),x_subst(B,D,E).
great_rsd(A,B):- n_val(B,D),ring_subst_5(A,E),ring_subst_6(B,C),ring_subst_2(B,F).
great_rsd(A,B):- polarisable(D,E),x_subst(B,C,D),r_subst_3(A,C),r_subst_2(A,F).
great_rsd(A,B):- h_doner(D,F),ring_subst_6(B,D),ring_subst_2(B,D),x_subst(A,E,C).
great_rsd(A,B):- ring_substitutions(A,E),ring_subst_3(A,D),ring_subst_4(B,F),x_subst(A,C,D).
great_rsd(A,B):- ring_substitutions(B,D),alk_groups(A,C),r_subst_3(B,C),n_val(A,C).
great_rsd(A,B):- ring_subst_2(B,D),r_subst_1(B,E),ring_subst_6(A,C),ring_subst_6(A,F).
great_rsd(A,B):- x_subst(A,F,E),x_subst(B,F,E),alk_groups(A,D),ring_substitutions(B,C).
great_rsd(A,B):- n_val(B,D),flex(F,E),x_subst(A,C,F),alk_groups(B,D).
great_rsd(A,B):- ring_subst_5(A,E),ring_subst_2(B,E),ring_subst_5(B,D),n_val(B,C).
great_rsd(A,B):- ring_subst_4(B,D),x_subst(B,C,D),x_subst(A,E,F),alk_groups(A,C).
great_rsd(A,B):- x_subst(A,F,E),ring_subst_5(B,C),polarisable(E,D),ring_subst_2(B,C).
great_rsd(A,B):- x_subst(A,C,E),ring_subst_3(B,D),ring_subst_5(B,D),ring_subst_4(B,E).
great_rsd(A,B):- polarisable(E,C),n_val(B,D),x_subst(A,D,E),r_subst_2(B,F).
great_rsd(A,B):- h_acceptor(C,E),ring_subst_6(B,F),r_subst_2(A,D),ring_subst_3(B,C).
great_rsd(A,B):- flex(E,F),x_subst(B,C,E),flex(D,F),ring_subst_6(A,D).
great_rsd(A,B):- polar(E,F),ring_subst_5(A,E),ring_subst_4(A,C),alk_groups(B,D).
great_rsd(A,B):- ring_substitutions(B,C),r_subst_2(A,E),ring_substitutions(B,D),r_subst_3(A,C).
great_rsd(A,B):- polar(E,F),ring_subst_3(A,D),r_subst_3(B,C),ring_subst_4(B,E).
great_rsd(A,B):- x_subst(B,F,C),h_acceptor(C,D),ring_subst_2(B,E),ring_substitutions(A,F).
great_rsd(A,B):- n_val(A,C),ring_subst_4(B,D),ring_subst_4(B,F),ring_subst_4(A,E).
great_rsd(A,B):- ring_subst_3(A,C),size(C,D),ring_subst_3(A,E),r_subst_3(B,F).
great_rsd(A,B):- ring_subst_4(A,D),ring_subst_4(B,C),gt(F,E),r_subst_3(A,F).
great_rsd(A,B):- x_subst(A,F,E),ring_subst_5(B,E),alk_groups(A,C),n_val(B,D).
great_rsd(A,B):- ring_subst_6(A,E),x_subst(B,C,D),alk_groups(B,F),x_subst(B,F,D).
great_rsd(A,B):- x_subst(B,D,F),pi_acceptor(F,C),ring_subst_2(B,F),ring_subst_4(A,E).
great_rsd(A,B):- ring_subst_3(B,C),r_subst_1(A,F),ring_substitutions(B,D),alk_groups(B,E).
great_rsd(A,B):- n_val(A,C),x_subst(A,C,E),ring_subst_6(A,E),ring_substitutions(B,D).
great_rsd(A,B):- x_subst(B,F,E),ring_substitutions(A,D),ring_subst_6(B,C),ring_subst_3(B,C).
great_rsd(A,B):- ring_subst_3(B,F),x_subst(A,D,C),h_acceptor(F,E),ring_subst_5(A,C).
great_rsd(A,B):- ring_subst_3(B,F),r_subst_2(A,C),n_val(A,D),h_doner(F,E).
great_rsd(A,B):- sigma(E,F),ring_subst_6(B,C),alk_groups(A,D),ring_subst_3(A,E).
great_rsd(A,B):- x_subst(B,C,D),r_subst_2(A,E),ring_subst_5(A,D),r_subst_2(A,F).
great_rsd(A,B):- ring_subst_5(B,F),alk_groups(A,C),x_subst(B,E,F),polar(F,D).
great_rsd(A,B):- x_subst(B,E,D),n_val(B,E),r_subst_3(A,C),ring_subst_5(A,D).
great_rsd(A,B):- ring_substitutions(B,C),n_val(A,D),r_subst_2(B,F),ring_subst_2(A,E).
great_rsd(A,B):- x_subst(B,D,C),ring_subst_4(A,F),flex(F,E),ring_subst_6(B,F).
great_rsd(A,B):- ring_subst_6(A,F),r_subst_3(A,E),ring_subst_5(A,D),ring_subst_2(B,C).
great_rsd(A,B):- ring_subst_5(B,F),x_subst(A,E,F),ring_substitutions(B,D),ring_substitutions(A,C).
great_rsd(A,B):- r_subst_3(B,D),polar(F,C),ring_subst_2(B,F),n_val(A,E).
great_rsd(A,B):- ring_substitutions(A,D),h_doner(C,F),great_h_don(F,E),ring_subst_2(B,C).
great_rsd(A,B):- ring_subst_2(A,C),ring_subst_5(B,E),flex(F,D),ring_subst_5(A,F).
great_rsd(A,B):- ring_subst_3(A,C),size(C,D),ring_subst_5(B,C),ring_subst_4(A,E).
great_rsd(A,B):- ring_subst_2(B,C),ring_subst_6(A,D),x_subst(A,E,C),r_subst_1(A,F).
great_rsd(A,B):- ring_subst_4(A,C),ring_subst_2(A,D),ring_subst_2(B,E),ring_substitutions(B,F).
great_rsd(A,B):- pi_acceptor(E,C),ring_substitutions(A,D),x_subst(B,D,E),size(E,F).
great_rsd(A,B):- alk_groups(B,C),n_val(A,D),x_subst(A,E,F),x_subst(B,E,F).
great_rsd(A,B):- x_subst(A,D,F),alk_groups(B,C),ring_subst_4(A,E),ring_substitutions(B,C).
great_rsd(A,B):- ring_subst_3(B,D),ring_subst_5(A,C),ring_subst_3(B,E),h_doner(E,F).
great_rsd(A,B):- ring_substitutions(B,E),x_subst(A,D,C),x_subst(A,F,C),ring_substitutions(A,F).
great_rsd(A,B):- ring_subst_5(A,E),ring_substitutions(B,D),flex(E,C).
great_rsd(A,B):- sigma(F,D),gt(E,C),ring_subst_6(A,F),alk_groups(B,E).
great_rsd(A,B):- alk_groups(A,F),pi_doner(C,D),ring_subst_2(B,E),ring_subst_3(B,C).
great_rsd(A,B):- x_subst(A,F,E),polar(E,D),ring_subst_3(B,E),ring_subst_3(A,C).
great_rsd(A,B):- ring_subst_3(A,F),pi_acceptor(C,D),n_val(B,E),ring_subst_3(B,C).
great_rsd(A,B):- h_acceptor(E,D),r_subst_1(A,C),ring_subst_3(B,E),size(E,F).
great_rsd(A,B):- ring_subst_3(A,C),ring_subst_2(B,D),ring_subst_3(A,D),ring_subst_4(A,D).
great_rsd(A,B):- x_subst(B,C,D),x_subst(A,E,F),x_subst(B,E,F),x_subst(A,C,D).
great_rsd(A,B):- ring_subst_2(A,F),ring_subst_4(A,E),h_doner(E,D),r_subst_1(B,C).
great_rsd(A,B):- ring_subst_4(B,E),x_subst(A,D,E),ring_subst_3(A,E),ring_subst_3(B,C).
great_rsd(A,B):- x_subst(B,F,E),x_subst(A,F,C),h_acceptor(C,D),ring_subst_3(A,E).
great_rsd(A,B):- size(F,D),r_subst_2(B,E),ring_subst_5(B,C),ring_subst_5(A,F).
great_rsd(A,B):- flex(E,D),x_subst(A,C,F),ring_subst_3(B,E),ring_subst_4(B,F).
great_rsd(A,B):- alk_groups(A,E),ring_subst_4(B,F),ring_subst_6(B,D),ring_substitutions(B,C).
great_rsd(A,B):- n_val(A,C),ring_subst_3(B,D),ring_subst_3(B,E),h_doner(E,F).
great_rsd(A,B):- x_subst(B,F,E),r_subst_3(A,D),x_subst(B,D,C),ring_subst_5(A,C).
great_rsd(A,B):- x_subst(A,F,E),ring_subst_3(B,D),ring_substitutions(A,F),polar(E,C).
great_rsd(A,B):- ring_subst_3(B,D),x_subst(B,C,D),ring_subst_4(A,F),ring_subst_5(A,E).
great_rsd(A,B):- ring_subst_2(A,F),r_subst_1(A,E),r_subst_1(B,C),ring_subst_5(A,D).
great_rsd(A,B):- ring_subst_2(A,C),n_val(B,D),ring_subst_4(B,F),sigma(F,E).
great_rsd(A,B):- r_subst_3(B,D),ring_subst_3(A,F),x_subst(B,E,F),n_val(A,C).
