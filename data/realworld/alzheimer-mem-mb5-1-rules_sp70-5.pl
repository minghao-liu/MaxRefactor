great_rsd(A,B):- alk_groups(B,C),ring_subst_5(B,E),ring_subst_3(A,D),ring_subst_3(A,F).
great_rsd(A,B):- r_subst_3(B,F),ring_subst_3(B,D),n_val(A,F),x_subst(A,E,C).
great_rsd(A,B):- n_val(A,C),ring_substitutions(A,D),r_subst_1(B,E),ring_subst_6(A,F).
great_rsd(A,B):- gt(C,E),ring_subst_5(B,D),r_subst_3(A,C),ring_substitutions(A,C).
great_rsd(A,B):- x_subst(B,D,F),r_subst_3(A,D),great_sigma(E,C),sigma(F,E).
great_rsd(A,B):- ring_subst_4(A,D),ring_substitutions(B,E),size(D,F),ring_subst_2(B,C).
great_rsd(A,B):- x_subst(B,F,E),x_subst(A,F,C),ring_subst_4(A,E),sigma(C,D).
great_rsd(A,B):- ring_subst_3(A,C),flex(F,D),ring_subst_3(B,F),pi_doner(F,E).
great_rsd(A,B):- x_subst(B,F,E),pi_doner(E,C),ring_subst_2(B,D),ring_subst_3(A,E).
great_rsd(A,B):- n_val(B,D),n_val(A,D),x_subst(A,C,F),ring_subst_3(B,E).
great_rsd(A,B):- x_subst(A,F,E),n_val(A,D),x_subst(B,D,E),ring_subst_3(A,C).
great_rsd(A,B):- alk_groups(B,C),ring_subst_3(A,E),r_subst_3(A,C),sigma(E,D).
great_rsd(A,B):- r_subst_2(B,D),pi_acceptor(F,E),ring_subst_6(B,C),ring_subst_6(A,F).
great_rsd(A,B):- ring_subst_2(B,D),ring_subst_5(B,F),x_subst(B,C,E),ring_subst_3(A,E).
great_rsd(A,B):- ring_substitutions(A,E),ring_subst_6(A,F),sigma(C,D),ring_subst_3(B,C).
great_rsd(A,B):- pi_acceptor(F,D),r_subst_3(B,C),ring_subst_5(A,F),alk_groups(B,E).
great_rsd(A,B):- ring_substitutions(B,E),x_subst(B,D,C),r_subst_3(A,E),alk_groups(A,D).
great_rsd(A,B):- pi_acceptor(E,D),ring_subst_4(B,F),ring_subst_2(B,E),ring_substitutions(A,C).
great_rsd(A,B):- x_subst(A,D,F),ring_subst_5(B,E),alk_groups(A,D),ring_subst_2(B,C).
great_rsd(A,B):- r_subst_3(B,D),alk_groups(A,C),polarisable(E,F),ring_subst_3(A,E).
great_rsd(A,B):- n_val(B,F),ring_subst_2(B,E),r_subst_1(A,C),r_subst_1(A,D).
great_rsd(A,B):- alk_groups(A,E),r_subst_2(B,D),n_val(A,C),ring_subst_3(B,F).
great_rsd(A,B):- ring_subst_6(A,F),r_subst_3(B,E),alk_groups(A,D),x_subst(A,E,C).
great_rsd(A,B):- ring_subst_5(B,E),ring_subst_6(A,F),size(E,C),x_subst(B,D,E).
great_rsd(A,B):- ring_substitutions(B,C),x_subst(B,C,D),ring_subst_3(A,D),flex(D,E).
great_rsd(A,B):- r_subst_2(B,D),r_subst_2(A,D),x_subst(A,E,C),pi_acceptor(C,F).
great_rsd(A,B):- ring_subst_2(B,D),r_subst_3(B,C),ring_subst_4(B,E),ring_subst_5(A,D).
great_rsd(A,B):- x_subst(A,D,F),gt(D,E),r_subst_3(B,C),ring_substitutions(A,C).
great_rsd(A,B):- ring_subst_6(B,C),ring_subst_6(A,C),x_subst(B,D,E),ring_subst_4(B,E).
great_rsd(A,B):- ring_subst_5(B,E),x_subst(B,F,C),x_subst(A,D,E),r_subst_3(A,F).
great_rsd(A,B):- h_acceptor(D,F),r_subst_2(B,E),r_subst_3(B,C),ring_subst_5(A,D).
great_rsd(A,B):- ring_subst_2(B,E),r_subst_1(B,C),ring_substitutions(A,F),gt(F,D).
great_rsd(A,B):- ring_subst_4(A,D),x_subst(B,C,D),h_acceptor(D,F),n_val(B,E).
great_rsd(A,B):- pi_acceptor(E,D),pi_acceptor(C,D),ring_subst_2(A,E),ring_subst_3(B,C).
great_rsd(A,B):- pi_acceptor(E,D),ring_subst_5(B,E),x_subst(A,C,F),ring_subst_2(B,F).
great_rsd(A,B):- ring_substitutions(B,C),ring_substitutions(A,D),x_subst(A,C,F),x_subst(A,D,E).
great_rsd(A,B):- x_subst(A,D,C),ring_subst_6(B,C),r_subst_3(A,E),n_val(B,E).
great_rsd(A,B):- r_subst_1(B,D),ring_substitutions(A,E),r_subst_1(B,C),r_subst_1(A,F).
great_rsd(A,B):- pi_acceptor(E,D),alk_groups(B,C),ring_subst_3(B,E),ring_subst_3(A,E).
great_rsd(A,B):- ring_subst_6(B,E),ring_subst_5(B,C),x_subst(A,D,E),ring_subst_4(B,E).
great_rsd(A,B):- pi_acceptor(D,E),ring_subst_2(A,D),r_subst_3(B,C).
great_rsd(A,B):- ring_subst_3(B,F),polarisable(C,E),x_subst(A,D,C),n_val(B,D).
great_rsd(A,B):- ring_substitutions(A,E),ring_subst_5(B,D),r_subst_3(B,F),n_val(B,C).
great_rsd(A,B):- x_subst(A,E,D),ring_subst_4(A,F),r_subst_3(B,C),n_val(B,C).
great_rsd(A,B):- ring_subst_4(A,D),ring_subst_4(B,C),h_doner(D,E).
great_rsd(A,B):- ring_subst_3(B,D),ring_subst_4(A,E),polarisable(D,C),r_subst_1(A,F).
great_rsd(A,B):- x_subst(B,D,F),n_val(A,D),ring_subst_3(A,C),sigma(F,E).
great_rsd(A,B):- r_subst_3(B,D),polar(F,C),ring_subst_3(B,F),ring_subst_3(A,E).
great_rsd(A,B):- ring_subst_2(A,F),ring_subst_4(A,C),n_val(A,D),alk_groups(B,E).
great_rsd(A,B):- x_subst(A,D,C),x_subst(B,D,C),flex(C,E),ring_substitutions(A,F).
great_rsd(A,B):- ring_substitutions(B,C),ring_subst_4(A,F),n_val(A,D),ring_subst_3(A,E).
great_rsd(A,B):- r_subst_2(A,E),r_subst_3(B,C),ring_subst_6(B,D),ring_substitutions(A,C).
great_rsd(A,B):- n_val(A,C),ring_subst_3(B,D),ring_substitutions(A,F),ring_subst_2(A,E).
great_rsd(A,B):- alk_groups(A,F),ring_subst_5(B,C),x_subst(B,D,E),ring_substitutions(A,F).
great_rsd(A,B):- ring_subst_4(A,D),flex(C,E),ring_subst_5(B,D),ring_subst_2(B,C).
great_rsd(A,B):- ring_subst_2(A,C),x_subst(B,D,C),ring_subst_3(A,C),ring_subst_2(A,E).
great_rsd(A,B):- pi_acceptor(D,E),r_subst_1(B,C),ring_subst_2(A,D),x_subst(B,F,D).
great_rsd(A,B):- x_subst(B,D,F),n_val(A,D),n_val(B,E),n_val(B,C).
great_rsd(A,B):- h_acceptor(D,E),pi_doner(D,C),ring_subst_6(B,D),ring_subst_6(A,D).
great_rsd(A,B):- size(E,D),ring_subst_5(A,E),ring_subst_5(B,F),ring_subst_3(B,C).
great_rsd(A,B):- n_val(A,F),alk_groups(B,F),r_subst_1(A,D),x_subst(A,E,C).
great_rsd(A,B):- n_val(A,C),ring_subst_2(A,D),x_subst(B,C,E),ring_subst_5(A,D).
great_rsd(A,B):- r_subst_3(B,D),ring_subst_2(A,F),r_subst_1(A,E),r_subst_1(B,C).
great_rsd(A,B):- flex(C,D),ring_subst_6(A,C),ring_subst_3(B,E),h_doner(E,F).
great_rsd(A,B):- polarisable(C,E),ring_subst_3(A,F),x_subst(B,D,C),ring_subst_5(B,C).
great_rsd(A,B):- h_acceptor(F,E),ring_subst_2(A,F),x_subst(B,C,D),ring_substitutions(A,C).
great_rsd(A,B):- ring_subst_4(A,C),r_subst_3(B,E),ring_subst_6(B,D),ring_subst_3(B,C).
great_rsd(A,B):- n_val(B,C),alk_groups(B,D),x_subst(B,D,E),r_subst_1(A,F).
great_rsd(A,B):- ring_substitutions(A,E),ring_subst_6(B,C),n_val(A,E),pi_acceptor(C,D).
great_rsd(A,B):- size(D,E),n_val(A,F),x_subst(B,C,D),x_subst(B,F,D).
