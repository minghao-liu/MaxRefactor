great_ne(A,B):- ring_substitutions(A,D),x_subst(B,C,F),ring_substitutions(A,E),r_subst_3(B,E).
great_ne(A,B):- ring_subst_6(A,C),ring_subst_6(B,D),r_subst_2(A,E),ring_subst_2(A,D).
great_ne(A,B):- ring_subst_2(B,E),x_subst(A,D,F),ring_subst_6(B,E),ring_subst_5(B,C).
great_ne(A,B):- alk_groups(B,D),ring_subst_6(A,F),h_doner(F,E),great_h_don(E,C).
great_ne(A,B):- r_subst_3(A,C),x_subst(A,C,D),x_subst(B,E,F),ring_subst_5(B,D).
great_ne(A,B):- pi_acceptor(D,F),x_subst(A,E,C),ring_subst_3(B,C),ring_subst_2(A,D).
great_ne(A,B):- r_subst_3(B,C),gt(D,E),ring_subst_2(A,F),n_val(B,D).
great_ne(A,B):- ring_substitutions(A,C),x_subst(B,C,E),n_val(A,C),x_subst(B,F,D).
great_ne(A,B):- ring_subst_5(A,F),ring_subst_4(B,C),r_subst_2(A,E),pi_acceptor(F,D).
great_ne(A,B):- ring_subst_6(A,C),ring_substitutions(A,F),ring_subst_5(B,D),sigma(C,E).
great_ne(A,B):- x_subst(B,F,E),h_doner(C,D),ring_subst_6(A,E),ring_subst_6(B,C).
great_ne(A,B):- ring_subst_4(A,E),ring_subst_4(B,C),sigma(E,F),flex(E,D).
great_ne(A,B):- pi_doner(E,F),r_subst_3(B,C),ring_subst_4(B,E),ring_subst_2(A,D).
great_ne(A,B):- pi_acceptor(C,D),ring_subst_2(B,C),ring_subst_6(B,E),ring_subst_5(A,E).
great_ne(A,B):- r_subst_3(A,C),r_subst_1(A,E),x_subst(B,C,F),n_val(B,D).
great_ne(A,B):- ring_subst_6(A,C),x_subst(A,F,D),n_val(B,F),ring_subst_5(B,E).
great_ne(A,B):- ring_subst_4(A,F),r_subst_2(B,E),alk_groups(A,D),ring_subst_6(B,C).
great_ne(A,B):- ring_subst_5(A,C),r_subst_3(B,D),n_val(A,F),size(C,E).
great_ne(A,B):- x_subst(B,C,E),r_subst_3(A,D),ring_subst_6(A,E),gt(C,F).
great_ne(A,B):- pi_doner(F,C),ring_subst_6(A,F),x_subst(B,E,F),n_val(B,D).
great_ne(A,B):- r_subst_3(A,C),ring_subst_5(A,D),r_subst_2(B,F),h_acceptor(D,E).
great_ne(A,B):- x_subst(A,E,C),ring_subst_5(A,D),ring_subst_3(B,D),h_acceptor(C,F).
great_ne(A,B):- ring_subst_6(A,C),x_subst(A,D,E),ring_subst_4(A,E),n_val(B,F).
great_ne(A,B):- ring_subst_5(A,E),ring_substitutions(B,D),pi_doner(C,F),x_subst(A,D,C).
great_ne(A,B):- r_subst_3(A,E),x_subst(B,F,C),r_subst_3(A,D),n_val(A,D).
great_ne(A,B):- ring_subst_4(A,E),pi_doner(C,D),x_subst(B,F,E),x_subst(A,F,C).
great_ne(A,B):- h_acceptor(E,F),alk_groups(A,C),polarisable(E,D),ring_subst_6(B,E).
great_ne(A,B):- ring_subst_6(A,C),ring_subst_4(B,E),flex(E,F),polar(C,D).
great_ne(A,B):- ring_subst_5(A,D),alk_groups(B,E),ring_subst_3(A,F),sigma(F,C).
great_ne(A,B):- ring_subst_6(A,D),ring_subst_3(A,C),ring_substitutions(A,E),ring_subst_5(B,C).
great_ne(A,B):- ring_subst_5(B,D),h_acceptor(D,C),ring_subst_2(A,F),flex(D,E).
great_ne(A,B):- r_subst_3(A,F),pi_acceptor(D,E),alk_groups(B,C),x_subst(B,C,D).
great_ne(A,B):- ring_subst_6(A,F),h_doner(C,E),ring_subst_3(B,C),ring_subst_3(A,D).
great_ne(A,B):- x_subst(A,D,E),polar(E,C),r_subst_3(B,D),ring_subst_2(A,F).
great_ne(A,B):- ring_subst_3(B,E),x_subst(A,C,D),r_subst_3(A,F),ring_subst_6(B,E).
great_ne(A,B):- r_subst_1(B,D),ring_subst_3(B,E),flex(C,F),ring_subst_6(A,C).
great_ne(A,B):- flex(D,F),r_subst_2(B,E),ring_subst_3(A,C),ring_subst_2(B,D).
great_ne(A,B):- r_subst_2(A,D),n_val(B,F),ring_subst_4(A,C),ring_substitutions(A,E).
great_ne(A,B):- ring_subst_3(A,E),ring_subst_4(B,F),x_subst(A,D,F),h_acceptor(F,C).
great_ne(A,B):- r_subst_1(A,D),pi_acceptor(E,C),x_subst(B,F,E),n_val(A,F).
great_ne(A,B):- ring_subst_4(A,E),x_subst(B,F,C),ring_subst_4(B,D),ring_subst_3(A,D).
great_ne(A,B):- x_subst(A,D,E),pi_acceptor(E,C),x_subst(B,F,E),alk_groups(B,F).
great_ne(A,B):- n_val(B,D),r_subst_3(A,D),polarisable(C,E),ring_subst_5(B,C).
great_ne(A,B):- ring_subst_4(A,E),x_subst(A,D,E),r_subst_3(B,F),x_subst(A,D,C).
great_ne(A,B):- r_subst_3(A,E),flex(D,F),n_val(A,C),ring_subst_4(B,D).
great_ne(A,B):- ring_subst_6(A,C),r_subst_1(A,D),h_acceptor(E,F),ring_subst_6(B,E).
great_ne(A,B):- r_subst_3(B,C),ring_subst_2(B,E),n_val(A,D),alk_groups(A,F).
great_ne(A,B):- ring_subst_3(B,E),ring_subst_3(A,C),x_subst(B,D,E),sigma(E,F).
great_ne(A,B):- alk_groups(B,D),ring_subst_2(A,C),x_subst(B,E,C),r_subst_2(A,F).
great_ne(A,B):- x_subst(A,D,E),ring_subst_2(B,C),size(E,F),ring_subst_6(B,C).
great_ne(A,B):- ring_subst_5(A,C),ring_subst_5(B,D),ring_substitutions(A,E),r_subst_1(A,F).
great_ne(A,B):- pi_acceptor(D,C),x_subst(B,E,F),ring_subst_2(B,D),ring_subst_3(A,D).
great_ne(A,B):- alk_groups(B,D),r_subst_3(B,F),ring_subst_2(A,C),size(C,E).
great_ne(A,B):- ring_subst_5(A,F),sigma(D,E),sigma(F,C),ring_subst_3(B,D).
great_ne(A,B):- ring_subst_6(B,F),r_subst_2(A,D),ring_subst_3(A,E),r_subst_2(B,C).
great_ne(A,B):- polarisable(D,F),n_val(B,E),x_subst(A,E,C),ring_subst_5(A,D).
great_ne(A,B):- n_val(B,D),n_val(A,F),x_subst(A,D,C),r_subst_3(B,E).
great_ne(A,B):- x_subst(B,D,F),ring_subst_4(A,F),ring_subst_3(B,C),ring_substitutions(B,E).
great_ne(A,B):- ring_subst_6(A,C),x_subst(B,E,D),ring_subst_4(B,C),ring_substitutions(A,F).
great_ne(A,B):- n_val(A,D),ring_subst_2(B,F),h_acceptor(F,C),pi_doner(F,E).
great_ne(A,B):- ring_subst_6(A,F),polar(D,E),ring_subst_5(B,C),ring_subst_3(A,D).
great_ne(A,B):- ring_subst_5(B,F),ring_subst_6(B,E),alk_groups(A,D),h_acceptor(E,C).
great_ne(A,B):- ring_subst_5(B,F),ring_subst_4(A,C),r_subst_2(A,E),pi_acceptor(F,D).
great_ne(A,B):- pi_acceptor(C,F),ring_subst_2(B,C),r_subst_1(A,E),ring_subst_2(A,D).
great_ne(A,B):- ring_subst_5(A,C),x_subst(B,E,D),ring_subst_4(B,D),ring_subst_5(A,F).
great_ne(A,B):- sigma(F,E),ring_subst_4(B,D),ring_subst_4(A,F),x_subst(B,C,D).
great_ne(A,B):- x_subst(A,C,F),ring_subst_4(B,F),x_subst(A,E,F),h_doner(F,D).
great_ne(A,B):- ring_subst_3(A,E),x_subst(B,C,F),ring_subst_3(B,D),ring_subst_2(A,D).
great_ne(A,B):- pi_doner(E,C),ring_subst_3(A,E),ring_subst_4(A,F),ring_subst_2(B,D).
great_ne(A,B):- ring_subst_6(B,D),sigma(D,E),ring_subst_2(A,F),sigma(F,C).
great_ne(A,B):- ring_subst_6(A,C),ring_subst_6(B,C),ring_subst_5(A,E),ring_subst_2(A,D).
great_ne(A,B):- r_subst_2(B,D),ring_subst_3(B,E),x_subst(A,F,E),ring_substitutions(B,C).
great_ne(A,B):- polarisable(F,C),ring_subst_3(B,E),ring_substitutions(A,D),ring_subst_2(A,F).
great_ne(A,B):- ring_subst_4(B,C),ring_subst_3(B,F),n_val(B,D),ring_substitutions(A,E).
great_ne(A,B):- ring_subst_6(B,D),ring_subst_6(B,C),ring_substitutions(A,E),ring_subst_3(A,D).
great_ne(A,B):- ring_subst_2(B,C),ring_subst_3(A,C),pi_doner(C,E),ring_subst_2(A,D).
great_ne(A,B):- ring_subst_3(B,F),pi_acceptor(D,E),sigma(F,C),ring_subst_2(A,D).
great_ne(A,B):- r_subst_3(B,C),alk_groups(A,C),x_subst(B,D,E),ring_subst_3(A,E).
great_ne(A,B):- gt(C,D),ring_substitutions(A,D),r_subst_1(B,E),n_val(A,C).
great_ne(A,B):- ring_subst_2(A,E),ring_subst_2(B,C),ring_subst_6(B,D),r_subst_2(B,F).
great_ne(A,B):- ring_subst_6(A,C),pi_acceptor(C,F),x_subst(A,E,D),ring_subst_6(B,C).
great_ne(A,B):- alk_groups(B,D),x_subst(A,D,E),flex(E,F),r_subst_2(A,C).
great_ne(A,B):- ring_subst_3(B,F),r_subst_3(B,D),alk_groups(A,E),h_acceptor(F,C).
great_ne(A,B):- n_val(A,C),ring_subst_4(B,F),flex(F,D),pi_acceptor(F,E).
great_ne(A,B):- r_subst_3(B,F),x_subst(B,D,C),n_val(A,F),x_subst(B,E,C).
great_ne(A,B):- gt(C,D),r_subst_2(B,E),x_subst(B,C,F),n_val(A,D).
great_ne(A,B):- ring_subst_5(A,C),x_subst(A,E,C),r_subst_3(B,D),x_subst(B,E,C).
great_ne(A,B):- x_subst(A,F,D),ring_subst_6(B,D),gt(F,E),r_subst_2(A,C).
great_ne(A,B):- r_subst_1(A,E),r_subst_3(A,D),r_subst_2(B,F),ring_subst_5(B,C).
great_ne(A,B):- n_val(B,E),gt(E,C),r_subst_3(B,D),r_subst_2(A,F).
