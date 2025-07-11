great_ne(A,B):- ring_subst_6(B,D),n_val(A,C),polarisable(D,E),sigma(D,F).
great_ne(A,B):- x_subst(A,C,F),alk_groups(B,C),pi_doner(F,E),ring_subst_4(A,D).
great_ne(A,B):- ring_subst_4(B,E),pi_doner(C,D),ring_subst_5(A,E),ring_subst_6(B,C).
great_ne(A,B):- r_subst_2(B,D),ring_subst_3(B,E),ring_subst_3(A,E),flex(E,C).
great_ne(A,B):- r_subst_3(A,E),pi_doner(D,C),ring_subst_3(B,F),ring_subst_4(A,D).
great_ne(A,B):- ring_subst_5(B,D),x_subst(A,F,E),h_doner(E,C),ring_subst_3(A,D).
great_ne(A,B):- pi_acceptor(E,D),ring_subst_3(A,E),x_subst(B,F,E),r_subst_2(B,C).
great_ne(A,B):- r_subst_3(B,C),x_subst(A,C,D),x_subst(B,E,F),x_subst(B,C,D).
great_ne(A,B):- polarisable(D,F),x_subst(B,E,D),x_subst(A,E,C),r_subst_3(B,E).
great_ne(A,B):- size(D,F),ring_subst_3(B,C),pi_acceptor(D,E),ring_subst_2(A,D).
great_ne(A,B):- r_subst_1(B,D),ring_subst_2(A,C),ring_substitutions(A,E),ring_subst_5(B,F).
great_ne(A,B):- n_val(A,D),ring_substitutions(A,D),alk_groups(B,C),r_subst_3(A,D).
great_ne(A,B):- pi_doner(C,D),ring_subst_3(A,C),ring_substitutions(A,E),ring_subst_6(B,C).
great_ne(A,B):- alk_groups(A,C),r_subst_1(A,E),ring_subst_5(B,D).
great_ne(A,B):- ring_subst_6(A,C),ring_subst_6(B,D),gt(F,E),n_val(A,F).
great_ne(A,B):- x_subst(A,E,F),n_val(B,E),x_subst(A,E,C),r_subst_2(B,D).
great_ne(A,B):- ring_substitutions(A,C),ring_subst_5(A,F),r_subst_3(B,D),size(F,E).
great_ne(A,B):- ring_subst_2(B,C),ring_subst_4(A,F),polarisable(C,E),ring_subst_2(A,D).
great_ne(A,B):- ring_subst_3(A,C),r_subst_3(B,F),pi_doner(C,D),x_subst(A,F,E).
great_ne(A,B):- ring_subst_5(A,C),x_subst(A,D,E),r_subst_3(B,F),ring_subst_5(A,E).
great_ne(A,B):- x_subst(A,F,D),x_subst(B,F,C),x_subst(B,E,D).
great_ne(A,B):- gt(E,C),ring_substitutions(B,D),gt(D,E),r_subst_1(A,F).
great_ne(A,B):- ring_subst_5(A,F),size(E,D),ring_subst_6(B,E),h_acceptor(E,C).
great_ne(A,B):- ring_subst_6(A,D),n_val(A,E),r_subst_3(A,F),ring_subst_6(B,C).
great_ne(A,B):- ring_subst_3(B,E),x_subst(B,D,E),x_subst(A,D,C),r_subst_3(A,D).
great_ne(A,B):- x_subst(B,D,E),x_subst(A,D,F),x_subst(A,C,E),ring_subst_6(A,F).
great_ne(A,B):- x_subst(A,D,E),ring_subst_6(B,E),n_val(B,D),sigma(E,C).
great_ne(A,B):- r_subst_1(A,D),ring_subst_2(A,E),ring_subst_3(B,C),ring_subst_5(B,C).
great_ne(A,B):- ring_subst_4(A,C),r_subst_2(A,E),ring_subst_2(B,D),ring_subst_5(B,C).
great_ne(A,B):- x_subst(A,E,F),r_subst_3(B,C),x_subst(B,D,F),alk_groups(B,E).
great_ne(A,B):- ring_subst_2(A,F),x_subst(B,E,F),r_subst_3(A,D),r_subst_1(A,C).
great_ne(A,B):- great_pi_don(E,D),r_subst_3(B,C),ring_subst_4(A,F),pi_doner(F,E).
great_ne(A,B):- gt(F,D),alk_groups(B,E),ring_subst_3(A,C),alk_groups(B,F).
great_ne(A,B):- ring_subst_4(B,E),size(E,C),ring_subst_2(B,D),r_subst_2(A,F).
great_ne(A,B):- gt(C,E),r_subst_3(A,C),polarisable(F,D),ring_subst_2(B,F).
great_ne(A,B):- ring_substitutions(B,D),ring_subst_3(B,C),ring_subst_2(A,C),ring_subst_3(A,E).
great_ne(A,B):- ring_subst_6(A,C),ring_subst_5(B,D),sigma(C,F),h_acceptor(D,E).
great_ne(A,B):- ring_subst_4(B,C),ring_subst_2(B,C),x_subst(A,D,C),r_subst_3(B,E).
great_ne(A,B):- flex(E,F),ring_subst_6(B,E),great_flex(F,C),ring_subst_4(A,D).
great_ne(A,B):- pi_doner(D,C),sigma(F,E),ring_subst_2(B,F),ring_subst_3(A,D).
great_ne(A,B):- x_subst(B,D,F),h_doner(F,E),great_h_don(E,C),ring_subst_3(A,F).
great_ne(A,B):- x_subst(B,C,E),flex(F,D),ring_subst_5(B,E),ring_subst_6(A,F).
great_ne(A,B):- h_acceptor(C,E),ring_subst_6(B,C),x_subst(A,D,C),r_subst_2(A,F).
great_ne(A,B):- ring_subst_4(B,E),ring_substitutions(A,D),ring_subst_3(B,F),h_doner(F,C).
great_ne(A,B):- ring_substitutions(A,C),ring_subst_4(A,E),r_subst_3(B,D),n_val(A,C).
great_ne(A,B):- ring_substitutions(B,F),ring_substitutions(A,F),x_subst(A,E,C),flex(C,D).
great_ne(A,B):- alk_groups(B,D),x_subst(B,C,E),ring_subst_5(B,F),ring_subst_5(A,F).
great_ne(A,B):- r_subst_3(A,F),ring_subst_6(B,E),flex(E,D),ring_subst_6(B,C).
great_ne(A,B):- polar(E,C),ring_substitutions(A,D),ring_subst_6(B,E),polar(E,F).
great_ne(A,B):- r_subst_3(A,E),ring_subst_6(A,D),ring_subst_2(B,C),ring_substitutions(A,E).
great_ne(A,B):- n_val(A,C),ring_subst_4(B,E),x_subst(B,C,F),gt(C,D).
great_ne(A,B):- x_subst(A,E,F),x_subst(B,D,F),ring_subst_4(B,C).
great_ne(A,B):- ring_substitutions(A,F),ring_subst_6(B,D),gt(F,E),pi_acceptor(D,C).
great_ne(A,B):- alk_groups(B,D),ring_subst_2(A,E),h_acceptor(C,F),ring_subst_6(B,C).
great_ne(A,B):- ring_subst_6(B,F),ring_subst_5(B,D),ring_subst_3(A,E),r_subst_1(A,C).
great_ne(A,B):- ring_subst_2(B,E),r_subst_3(A,F),ring_subst_4(B,C),ring_subst_3(A,D).
great_ne(A,B):- ring_subst_2(B,E),polarisable(E,D),ring_subst_3(A,F),ring_subst_6(B,C).
great_ne(A,B):- ring_subst_4(A,E),ring_subst_2(B,C),ring_subst_3(B,D),ring_subst_6(B,C).
great_ne(A,B):- x_subst(A,C,F),x_subst(A,D,F),ring_subst_2(A,F),x_subst(B,E,F).
great_ne(A,B):- ring_subst_6(A,C),n_val(B,D),x_subst(A,F,C),ring_subst_6(A,E).
great_ne(A,B):- x_subst(B,C,E),ring_subst_5(B,D),x_subst(A,F,E),x_subst(B,F,D).
great_ne(A,B):- ring_subst_5(A,F),r_subst_2(A,D),ring_subst_2(B,E),r_subst_1(B,C).
great_ne(A,B):- ring_subst_2(B,C),r_subst_1(A,E),ring_subst_3(B,D),ring_subst_2(B,D).
great_ne(A,B):- size(F,C),ring_subst_4(B,F),great_size(C,D),ring_subst_5(A,E).
great_ne(A,B):- flex(C,E),pi_acceptor(C,F),ring_subst_2(A,C),r_subst_3(B,D).
great_ne(A,B):- ring_subst_5(A,F),ring_substitutions(A,D),r_subst_2(B,E),ring_subst_6(B,C).
great_ne(A,B):- ring_subst_5(B,F),n_val(A,E),pi_acceptor(F,C),x_subst(A,E,D).
great_ne(A,B):- r_subst_1(A,D),x_subst(B,F,C),ring_subst_2(B,C),alk_groups(A,E).
great_ne(A,B):- sigma(D,C),ring_subst_3(A,D),r_subst_3(B,F),r_subst_3(B,E).
great_ne(A,B):- x_subst(B,F,D),x_subst(A,E,C),ring_subst_2(A,C),x_subst(A,E,D).
great_ne(A,B):- ring_subst_3(B,E),alk_groups(A,C),great_pi_acc(F,D),pi_acceptor(E,F).
great_ne(A,B):- ring_substitutions(A,F),x_subst(A,E,D),ring_subst_2(B,D),gt(E,C).
great_ne(A,B):- ring_subst_6(B,F),ring_substitutions(A,D),sigma(F,E),x_subst(A,D,C).
great_ne(A,B):- ring_subst_2(B,E),ring_subst_6(B,D),flex(E,F),x_subst(A,C,E).
great_ne(A,B):- ring_substitutions(A,D),ring_subst_6(B,C),size(C,E),ring_subst_5(B,C).
great_ne(A,B):- ring_substitutions(A,C),r_subst_3(A,C),r_subst_3(B,D),ring_substitutions(A,E).
great_ne(A,B):- ring_subst_5(B,F),n_val(B,C),x_subst(B,E,F),ring_subst_2(A,D).
great_ne(A,B):- ring_subst_3(A,C),ring_subst_6(A,D),x_subst(B,F,E),ring_subst_3(B,D).
great_ne(A,B):- ring_subst_6(B,D),ring_subst_5(B,E),x_subst(A,F,C).
great_ne(A,B):- ring_subst_2(B,E),ring_subst_5(A,D),r_subst_3(A,F),ring_subst_6(B,C).
