great_rsd(A,B):- ring_subst_3(B,D),ring_substitutions(B,E),alk_groups(A,F),r_subst_3(A,C).
great_rsd(A,B):- ring_subst_2(A,D),x_subst(B,C,F),x_subst(B,C,E).
great_rsd(A,B):- ring_subst_4(A,D),alk_groups(B,C),r_subst_2(A,E),ring_subst_5(B,F).
great_rsd(A,B):- ring_subst_3(A,E),r_subst_1(B,C),r_subst_1(B,F),sigma(E,D).
great_rsd(A,B):- alk_groups(A,E),ring_subst_4(A,D),r_subst_1(B,C),n_val(B,E).
great_rsd(A,B):- sigma(E,F),ring_subst_2(A,D),ring_subst_2(B,E),ring_subst_3(B,C).
great_rsd(A,B):- size(E,D),alk_groups(A,C),x_subst(B,C,F),ring_subst_3(A,E).
great_rsd(A,B):- n_val(B,D),ring_substitutions(B,E),gt(E,D),r_subst_3(A,C).
great_rsd(A,B):- flex(C,D),ring_subst_5(A,E),ring_subst_5(B,C),r_subst_3(B,F).
great_rsd(A,B):- x_subst(A,D,C),x_subst(B,D,C),h_doner(C,E),ring_subst_3(B,C).
great_rsd(A,B):- size(D,E),ring_subst_2(B,D),ring_subst_6(B,C),ring_subst_5(A,C).
great_rsd(A,B):- ring_subst_2(A,C),r_subst_1(A,E),ring_subst_6(B,D),ring_subst_6(A,D).
great_rsd(A,B):- x_subst(B,D,C),x_subst(B,F,C),x_subst(A,E,C),ring_subst_6(A,C).
great_rsd(A,B):- alk_groups(B,C),ring_subst_3(A,F),sigma(F,D),pi_doner(F,E).
great_rsd(A,B):- ring_subst_2(A,C),n_val(A,D),x_subst(A,E,C),ring_subst_2(B,C).
great_rsd(A,B):- x_subst(A,F,E),n_val(A,D),r_subst_3(B,F),flex(E,C).
great_rsd(A,B):- r_subst_1(B,D),r_subst_1(A,D),n_val(A,C),n_val(B,E).
great_rsd(A,B):- ring_subst_2(B,C),polarisable(D,F),ring_subst_6(A,D),alk_groups(B,E).
great_rsd(A,B):- x_subst(B,C,D),alk_groups(B,F),x_subst(B,C,E),ring_subst_6(A,D).
great_rsd(A,B):- n_val(B,C),n_val(A,D),r_subst_1(A,E),r_subst_1(A,F).
great_rsd(A,B):- sigma(F,E),ring_subst_2(A,D),ring_subst_4(B,F),pi_doner(D,C).
great_rsd(A,B):- x_subst(B,C,D),pi_doner(D,E),x_subst(A,C,D),ring_substitutions(A,C).
great_rsd(A,B):- alk_groups(A,E),x_subst(B,D,C),alk_groups(B,D),ring_subst_6(A,C).
great_rsd(A,B):- n_val(A,C),gt(D,F),alk_groups(B,D),gt(C,E).
great_rsd(A,B):- ring_substitutions(A,D),ring_subst_5(B,C),r_subst_1(A,E),r_subst_3(B,F).
great_rsd(A,B):- r_subst_1(B,D),ring_subst_6(A,E),ring_subst_6(B,F),r_subst_3(B,C).
great_rsd(A,B):- ring_subst_6(B,F),polar(E,D),r_subst_3(A,C),ring_subst_4(B,E).
great_rsd(A,B):- alk_groups(B,D),ring_subst_6(A,F),h_doner(F,E),ring_subst_3(B,C).
great_rsd(A,B):- ring_subst_5(B,E),n_val(A,D),ring_subst_6(B,F),flex(E,C).
great_rsd(A,B):- flex(D,C),polarisable(D,E),ring_subst_3(A,D),ring_subst_2(B,F).
great_rsd(A,B):- ring_subst_3(B,D),polarisable(F,E),ring_subst_6(A,F),ring_subst_3(B,C).
great_rsd(A,B):- ring_subst_2(A,F),x_subst(B,D,C),alk_groups(A,D),h_doner(F,E).
great_rsd(A,B):- pi_doner(E,F),pi_acceptor(E,C),x_subst(B,D,E),ring_subst_2(A,E).
great_rsd(A,B):- ring_subst_5(B,C),pi_doner(C,D),ring_subst_2(B,E),ring_subst_3(A,E).
great_rsd(A,B):- ring_subst_3(A,C),r_subst_3(A,D),pi_acceptor(C,E),ring_substitutions(B,F).
great_rsd(A,B):- x_subst(A,E,D),ring_subst_4(A,F),ring_subst_4(A,C),ring_subst_6(B,C).
great_rsd(A,B):- r_subst_3(B,D),x_subst(A,C,F),ring_subst_2(B,F),size(F,E).
great_rsd(A,B):- pi_acceptor(F,E),ring_subst_2(B,F),ring_subst_4(B,C),ring_subst_6(A,D).
great_rsd(A,B):- ring_subst_4(B,D),ring_subst_3(A,E),ring_subst_2(A,E),polar(D,C).
great_rsd(A,B):- ring_subst_3(A,F),r_subst_2(B,C),sigma(E,D),ring_subst_3(B,E).
