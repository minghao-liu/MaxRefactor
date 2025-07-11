great_rsd(A,B):- ring_subst_4(A,D),ring_subst_4(B,C),size(D,F),x_subst(A,E,C).
great_rsd(A,B):- ring_subst_3(A,C),x_subst(A,D,C),ring_subst_6(B,C),ring_subst_3(A,E).
great_rsd(A,B):- ring_subst_3(B,F),flex(F,D),ring_subst_6(B,F),x_subst(A,E,C).
great_rsd(A,B):- gt(E,F),r_subst_3(A,E),pi_doner(D,C),ring_subst_6(B,D).
great_rsd(A,B):- alk_groups(A,E),x_subst(B,C,D),ring_subst_6(A,F),ring_subst_5(B,D).
great_rsd(A,B):- alk_groups(A,E),x_subst(B,E,D),pi_acceptor(D,F),r_subst_1(B,C).
great_rsd(A,B):- ring_subst_3(B,D),sigma(E,C),ring_subst_6(B,F),ring_subst_3(A,E).
great_rsd(A,B):- ring_subst_6(B,C),ring_subst_4(B,F),ring_subst_3(A,E),pi_acceptor(C,D).
great_rsd(A,B):- ring_subst_3(B,F),polar(D,E),x_subst(A,C,D),n_val(B,C).
great_rsd(A,B):- h_acceptor(C,E),n_val(A,D),r_subst_2(B,F),ring_subst_3(B,C).
great_rsd(A,B):- ring_substitutions(B,C),x_subst(B,D,E),ring_substitutions(A,F),r_subst_3(A,F).
great_rsd(A,B):- ring_subst_3(A,C),x_subst(B,F,C),ring_subst_4(A,D),x_subst(A,E,C).
great_rsd(A,B):- size(D,E),size(C,F),ring_subst_6(A,D),ring_subst_3(B,C).
great_rsd(A,B):- h_doner(E,C),h_doner(E,D),ring_subst_6(B,F),ring_subst_4(A,E).
great_rsd(A,B):- x_subst(B,D,C),n_val(A,D),ring_subst_2(B,C).
great_rsd(A,B):- x_subst(B,C,E),x_subst(B,D,E),gt(D,C),x_subst(A,D,E).
great_rsd(A,B):- sigma(F,E),polarisable(C,D),ring_subst_5(A,F),ring_subst_2(B,C).
great_rsd(A,B):- x_subst(A,D,C),n_val(A,D),x_subst(B,D,E),ring_subst_3(A,E).
great_rsd(A,B):- ring_subst_5(B,E),ring_subst_6(A,C),h_acceptor(C,D),r_subst_3(B,F).
great_rsd(A,B):- polar(E,F),ring_subst_4(A,E),x_subst(A,D,E),ring_subst_2(B,C).
great_rsd(A,B):- ring_subst_4(A,D),n_val(B,C),ring_subst_4(A,E),r_subst_3(A,F).
great_rsd(A,B):- ring_subst_2(B,E),ring_subst_6(A,F),ring_substitutions(B,D),h_acceptor(E,C).
great_rsd(A,B):- x_subst(B,D,C),r_subst_3(A,E),pi_acceptor(C,F),x_subst(B,E,C).
great_rsd(A,B):- ring_subst_3(A,E),x_subst(A,F,D),ring_substitutions(A,F),ring_subst_2(B,C).
great_rsd(A,B):- x_subst(B,C,D),ring_subst_3(A,D),pi_acceptor(D,F),ring_subst_4(A,E).
great_rsd(A,B):- ring_subst_3(B,C),r_subst_2(A,D),ring_subst_2(A,E),r_subst_1(A,F).
great_rsd(A,B):- ring_subst_2(A,C),r_subst_3(A,D),ring_substitutions(A,F),x_subst(B,E,C).
great_rsd(A,B):- ring_subst_3(A,C),ring_subst_4(B,D),ring_subst_3(B,D),ring_subst_2(B,E).
great_rsd(A,B):- ring_substitutions(B,D),alk_groups(A,D),x_subst(A,E,C).
great_rsd(A,B):- x_subst(B,C,D),alk_groups(A,C),r_subst_1(A,E),alk_groups(B,F).
great_rsd(A,B):- r_subst_3(A,D),h_acceptor(E,C),sigma(E,F),ring_subst_3(B,E).
great_rsd(A,B):- n_val(B,D),r_subst_3(B,E),ring_subst_6(A,C),ring_substitutions(B,D).
great_rsd(A,B):- alk_groups(B,F),ring_subst_2(A,D),r_subst_3(B,C),h_acceptor(D,E).
great_rsd(A,B):- size(E,D),ring_subst_6(B,C),flex(E,F),ring_subst_2(A,E).
great_rsd(A,B):- ring_subst_5(A,C),ring_subst_3(B,D),ring_subst_2(B,F),sigma(D,E).
great_rsd(A,B):- r_subst_3(B,C),ring_subst_5(A,E),polar(E,F),x_subst(A,D,E).
great_rsd(A,B):- r_subst_3(A,D),ring_substitutions(B,E),n_val(B,C),r_subst_2(A,F).
great_rsd(A,B):- h_doner(E,C),ring_subst_5(B,D),ring_subst_3(A,E),polarisable(E,F).
great_rsd(A,B):- alk_groups(A,F),ring_subst_4(B,C),ring_subst_2(B,E),ring_subst_6(B,D).
great_rsd(A,B):- r_subst_1(B,C),x_subst(B,F,D),ring_subst_3(A,E),ring_subst_5(A,D).
