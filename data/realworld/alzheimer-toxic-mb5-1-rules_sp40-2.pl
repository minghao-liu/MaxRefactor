less_toxic(A,B):- n_val(B,C),ring_substitutions(B,E),gt(F,D),n_val(A,F).
less_toxic(A,B):- ring_subst_5(A,F),x_subst(B,E,C),x_subst(B,D,F),ring_subst_3(A,F).
less_toxic(A,B):- ring_subst_6(B,F),ring_subst_2(B,E),polar(E,C),ring_subst_2(A,D).
less_toxic(A,B):- x_subst(B,F,E),polar(E,C),ring_subst_4(A,E),great_polar(C,D).
less_toxic(A,B):- pi_doner(C,F),pi_doner(D,E),ring_subst_2(A,D),ring_subst_6(B,C).
less_toxic(A,B):- polar(E,D),ring_subst_2(B,C),ring_subst_2(A,E),great_polar(D,F).
less_toxic(A,B):- h_acceptor(D,C),ring_substitutions(B,E),x_subst(A,F,D),r_subst_3(B,F).
less_toxic(A,B):- polarisable(E,D),ring_subst_5(A,E),polar(E,C),r_subst_3(B,F).
less_toxic(A,B):- sigma(D,C),ring_subst_5(A,F),ring_subst_6(A,D),ring_subst_5(B,E).
less_toxic(A,B):- alk_groups(A,D),n_val(A,D),gt(D,C),alk_groups(B,C).
less_toxic(A,B):- ring_subst_5(A,F),ring_subst_3(B,C),ring_subst_2(B,E),ring_subst_5(A,D).
less_toxic(A,B):- x_subst(B,D,E),ring_subst_4(B,C),ring_subst_2(A,C),alk_groups(A,F).
less_toxic(A,B):- n_val(A,D),alk_groups(A,E),r_subst_3(B,C),alk_groups(A,F).
less_toxic(A,B):- alk_groups(B,D),gt(E,D),x_subst(A,E,C),ring_subst_5(A,C).
less_toxic(A,B):- ring_substitutions(A,F),polar(C,E),ring_subst_2(B,C),ring_subst_4(B,D).
less_toxic(A,B):- n_val(B,E),size(F,D),ring_subst_3(A,F),ring_subst_5(B,C).
less_toxic(A,B):- ring_subst_5(A,F),polarisable(F,D),alk_groups(B,E),n_val(B,C).
less_toxic(A,B):- ring_subst_3(A,E),r_subst_2(A,C),r_subst_2(B,D),ring_subst_3(A,F).
less_toxic(A,B):- size(E,D),r_subst_1(A,F),ring_subst_2(B,E),ring_subst_3(A,C).
less_toxic(A,B):- ring_subst_3(A,E),ring_substitutions(B,C),ring_subst_4(A,D),ring_subst_6(B,E).
less_toxic(A,B):- x_subst(B,E,C),ring_substitutions(A,D),n_val(B,F),ring_subst_6(B,C).
less_toxic(A,B):- x_subst(A,F,E),ring_subst_3(B,E),ring_subst_3(B,C),r_subst_1(A,D).
less_toxic(A,B):- ring_subst_6(B,D),alk_groups(B,C),ring_subst_2(A,D),ring_subst_4(A,E).
less_toxic(A,B):- gt(C,F),x_subst(A,C,D),r_subst_3(B,E),x_subst(A,F,D).
less_toxic(A,B):- r_subst_3(B,D),ring_subst_6(B,C),polarisable(C,E),ring_subst_2(A,F).
less_toxic(A,B):- ring_subst_4(B,E),alk_groups(B,C),ring_subst_6(A,E),ring_subst_2(B,D).
less_toxic(A,B):- ring_subst_3(A,E),x_subst(A,C,D),polar(E,F),x_subst(B,C,D).
less_toxic(A,B):- ring_subst_6(B,F),alk_groups(A,D),polar(F,E),ring_subst_6(B,C).
less_toxic(A,B):- ring_substitutions(B,F),ring_subst_2(B,C),ring_subst_5(A,D),x_subst(A,E,D).
less_toxic(A,B):- gt(C,E),ring_substitutions(B,C),r_subst_1(A,D),alk_groups(B,F).
less_toxic(A,B):- ring_subst_2(B,C),x_subst(A,E,C),ring_subst_3(A,C),h_doner(C,D).
less_toxic(A,B):- ring_subst_4(A,E),ring_subst_5(B,F),alk_groups(A,C),ring_substitutions(B,D).
less_toxic(A,B):- ring_subst_3(A,E),ring_subst_3(B,F),x_subst(A,C,E),size(F,D).
less_toxic(A,B):- r_subst_2(A,E),x_subst(B,C,D),polar(D,F),ring_subst_5(B,D).
less_toxic(A,B):- ring_subst_4(B,D),pi_doner(D,E),ring_subst_3(A,F),h_doner(D,C).
less_toxic(A,B):- ring_substitutions(A,F),h_acceptor(D,E),ring_subst_3(A,C),ring_subst_2(B,D).
less_toxic(A,B):- ring_subst_2(A,F),r_subst_2(B,C),ring_subst_3(A,E),polar(E,D).
less_toxic(A,B):- ring_subst_2(A,E),x_subst(B,F,E),x_subst(A,D,C),r_subst_3(A,F).
less_toxic(A,B):- ring_subst_6(B,F),x_subst(A,C,D),ring_substitutions(A,E),ring_subst_6(A,D).
less_toxic(A,B):- ring_subst_2(B,C),x_subst(A,E,C),n_val(B,D),r_subst_3(A,E).
