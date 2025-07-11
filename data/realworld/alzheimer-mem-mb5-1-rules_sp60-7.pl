great_rsd(A,B):- ring_subst_4(A,D),ring_subst_6(B,E),x_subst(B,C,D),ring_subst_4(B,E).
great_rsd(A,B):- ring_substitutions(A,E),n_val(A,D),alk_groups(B,D),ring_subst_2(B,C).
great_rsd(A,B):- x_subst(A,D,C),sigma(C,F),n_val(A,E),ring_subst_2(B,C).
great_rsd(A,B):- ring_subst_3(B,F),flex(F,D),ring_subst_5(A,E),x_subst(B,C,F).
great_rsd(A,B):- alk_groups(A,C),ring_subst_5(B,F),ring_subst_3(A,E),sigma(E,D).
great_rsd(A,B):- ring_subst_3(A,E),x_subst(B,C,E),x_subst(A,C,D),r_subst_3(A,F).
great_rsd(A,B):- r_subst_3(B,D),ring_subst_4(A,E),r_subst_3(B,F),ring_subst_2(B,C).
great_rsd(A,B):- ring_subst_3(B,D),ring_substitutions(A,E),ring_subst_2(B,D),x_subst(A,C,F).
great_rsd(A,B):- ring_substitutions(A,E),ring_subst_2(B,D),ring_subst_6(A,C),ring_subst_4(B,D).
great_rsd(A,B):- alk_groups(B,F),pi_doner(E,D),ring_subst_6(A,C),ring_subst_2(A,E).
great_rsd(A,B):- x_subst(B,F,E),ring_subst_2(A,C),flex(E,D),ring_subst_3(A,E).
great_rsd(A,B):- r_subst_3(A,D),x_subst(B,D,C),ring_subst_4(B,C),ring_subst_4(A,E).
great_rsd(A,B):- ring_substitutions(B,C),x_subst(A,E,D),gt(E,C).
great_rsd(A,B):- r_subst_2(B,D),ring_subst_6(B,C),ring_subst_4(A,E),flex(C,F).
great_rsd(A,B):- r_subst_2(B,D),ring_subst_5(A,E),polarisable(C,F),ring_subst_2(B,C).
great_rsd(A,B):- ring_substitutions(A,D),ring_subst_5(A,E),ring_subst_6(B,C),ring_subst_6(A,E).
great_rsd(A,B):- n_val(A,F),ring_subst_3(B,D),r_subst_3(A,E),pi_acceptor(D,C).
great_rsd(A,B):- ring_substitutions(B,C),ring_subst_4(A,E),gt(D,C),alk_groups(A,D).
great_rsd(A,B):- flex(D,C),ring_subst_4(B,D),h_acceptor(F,E),ring_subst_5(A,F).
great_rsd(A,B):- r_subst_2(B,D),ring_substitutions(A,E),ring_subst_2(A,F),r_subst_3(A,C).
great_rsd(A,B):- ring_subst_6(A,E),ring_subst_4(B,F),sigma(E,D),ring_subst_3(B,C).
great_rsd(A,B):- x_subst(A,D,F),ring_subst_2(A,C),ring_subst_4(B,C),x_subst(A,D,E).
great_rsd(A,B):- ring_subst_3(A,F),polarisable(F,E),alk_groups(B,D),flex(F,C).
great_rsd(A,B):- x_subst(B,E,D),x_subst(A,F,C),ring_substitutions(A,F),ring_subst_2(B,C).
great_rsd(A,B):- ring_substitutions(B,D),ring_subst_5(B,C),x_subst(B,D,E),ring_substitutions(A,F).
great_rsd(A,B):- ring_subst_6(B,E),x_subst(B,C,D),alk_groups(B,F),r_subst_3(A,C).
great_rsd(A,B):- ring_subst_2(A,C),ring_subst_6(B,C),x_subst(B,F,D),sigma(D,E).
great_rsd(A,B):- n_val(B,D),alk_groups(A,C),r_subst_2(A,E),r_subst_3(A,C).
great_rsd(A,B):- ring_subst_5(B,C),ring_subst_2(B,F),r_subst_2(A,D),size(C,E).
great_rsd(A,B):- size(D,E),ring_subst_3(A,D),ring_subst_6(A,C),r_subst_1(B,F).
great_rsd(A,B):- r_subst_3(A,D),pi_acceptor(C,E),ring_subst_6(B,F),ring_subst_2(B,C).
great_rsd(A,B):- x_subst(A,F,E),ring_subst_2(B,D),n_val(B,F),r_subst_3(A,C).
great_rsd(A,B):- r_subst_3(B,D),r_subst_3(A,D),polarisable(C,E),ring_subst_2(B,C).
great_rsd(A,B):- x_subst(A,C,E),ring_subst_5(B,D),x_subst(B,C,E),ring_subst_4(B,D).
great_rsd(A,B):- ring_subst_3(A,F),ring_substitutions(B,E),pi_acceptor(F,C),great_pi_acc(C,D).
great_rsd(A,B):- ring_subst_2(A,C),ring_substitutions(B,E),x_subst(B,D,C),ring_subst_5(B,F).
great_rsd(A,B):- polarisable(C,E),n_val(A,F),ring_subst_2(B,D),ring_subst_5(A,C).
great_rsd(A,B):- ring_subst_5(A,E),ring_subst_2(B,F),x_subst(A,D,E),n_val(B,C).
great_rsd(A,B):- ring_subst_3(B,F),ring_subst_6(A,E),ring_subst_6(B,C),pi_acceptor(C,D).
great_rsd(A,B):- ring_subst_3(A,F),ring_subst_5(B,C),ring_subst_3(B,E),ring_subst_5(B,D).
great_rsd(A,B):- great_flex(F,D),ring_subst_4(A,E),flex(E,F),ring_subst_2(B,C).
great_rsd(A,B):- x_subst(B,C,D),ring_subst_4(A,F),pi_doner(D,E).
great_rsd(A,B):- pi_acceptor(E,D),r_subst_1(A,C),ring_subst_2(B,E),r_subst_2(B,F).
great_rsd(A,B):- ring_substitutions(B,E),r_subst_3(A,D),alk_groups(B,F),ring_subst_3(A,C).
great_rsd(A,B):- ring_subst_4(B,D),alk_groups(A,C),r_subst_3(B,E),gt(E,C).
great_rsd(A,B):- flex(F,D),ring_subst_5(B,C),x_subst(A,E,F),x_subst(B,E,C).
great_rsd(A,B):- x_subst(A,F,E),alk_groups(B,F),r_subst_1(A,D),flex(E,C).
great_rsd(A,B):- x_subst(B,D,C),alk_groups(A,D),x_subst(A,E,C),gt(D,E).
great_rsd(A,B):- r_subst_1(B,D),ring_subst_6(A,E),polarisable(E,F),r_subst_3(B,C).
great_rsd(A,B):- sigma(C,D),ring_subst_6(A,C),ring_subst_2(B,E),flex(E,F).
great_rsd(A,B):- n_val(A,C),ring_subst_3(B,D),flex(D,F),h_acceptor(D,E).
great_rsd(A,B):- ring_subst_6(A,D),ring_subst_3(B,E),r_subst_3(A,C),ring_subst_4(B,E).
great_rsd(A,B):- x_subst(A,D,F),alk_groups(B,D),r_subst_1(A,E),ring_subst_6(A,C).
great_rsd(A,B):- x_subst(A,C,E),pi_doner(D,F),x_subst(A,C,D),ring_subst_6(B,D).
great_rsd(A,B):- ring_subst_2(B,C),r_subst_3(B,E),r_subst_3(B,F),ring_subst_2(A,D).
great_rsd(A,B):- ring_subst_2(A,C),x_subst(B,D,C),sigma(C,F),x_subst(B,D,E).
great_rsd(A,B):- ring_subst_2(B,D),ring_subst_4(A,C),flex(C,E),polar(C,F).
great_rsd(A,B):- pi_acceptor(C,D),x_subst(A,F,C),h_doner(C,E),ring_subst_3(B,C).
great_rsd(A,B):- ring_subst_5(A,E),ring_subst_4(A,F),alk_groups(A,D),ring_subst_2(B,C).
great_rsd(A,B):- ring_subst_3(B,D),r_subst_3(B,E),ring_subst_4(A,F),x_subst(A,E,C).
