great_ne(A,B):- n_val(A,C),r_subst_1(B,E),r_subst_3(B,D),r_subst_3(A,F).
great_ne(A,B):- size(E,F),ring_subst_3(A,E),ring_subst_5(B,C),ring_subst_3(A,D).
great_ne(A,B):- ring_subst_5(B,D),x_subst(A,C,D),polar(D,E),ring_subst_2(B,D).
great_ne(A,B):- polarisable(F,C),r_subst_2(B,E),ring_subst_3(B,F),alk_groups(A,D).
great_ne(A,B):- ring_substitutions(A,C),ring_subst_3(A,E),ring_subst_5(B,E),x_subst(B,F,D).
great_ne(A,B):- ring_substitutions(B,F),size(C,D),ring_subst_2(A,C),r_subst_3(B,E).
great_ne(A,B):- ring_subst_2(A,E),ring_substitutions(A,D),ring_subst_4(B,C),ring_subst_3(A,E).
great_ne(A,B):- ring_subst_5(A,C),ring_subst_6(A,C),ring_subst_6(B,E),ring_subst_3(B,D).
great_ne(A,B):- ring_subst_4(B,E),x_subst(B,D,C),ring_subst_2(A,C),ring_subst_5(A,E).
great_ne(A,B):- gt(E,F),ring_subst_4(B,C),x_subst(A,E,D),ring_subst_4(B,D).
great_ne(A,B):- ring_subst_6(B,F),alk_groups(A,C),x_subst(A,E,D),x_subst(B,C,D).
great_ne(A,B):- sigma(D,C),n_val(B,F),ring_subst_6(A,D),r_subst_1(A,E).
great_ne(A,B):- pi_acceptor(E,D),ring_subst_3(A,E),ring_subst_4(B,F),sigma(E,C).
great_ne(A,B):- x_subst(B,E,D),r_subst_3(A,C),ring_substitutions(B,E),alk_groups(B,C).
great_ne(A,B):- r_subst_3(A,C),x_subst(B,F,E),n_val(A,F),ring_subst_6(B,D).
great_ne(A,B):- r_subst_3(A,F),gt(F,E),alk_groups(A,D),x_subst(B,E,C).
great_ne(A,B):- ring_subst_5(B,F),alk_groups(A,C),r_subst_2(B,E),h_doner(F,D).
great_ne(A,B):- x_subst(A,E,F),ring_subst_6(A,C),h_doner(F,D),ring_subst_5(B,C).
great_ne(A,B):- r_subst_1(A,D),h_doner(C,E),ring_subst_3(A,C),alk_groups(B,F).
great_ne(A,B):- pi_acceptor(C,D),ring_subst_3(B,C),ring_substitutions(A,E),alk_groups(A,F).
great_ne(A,B):- n_val(A,C),ring_subst_2(A,E),n_val(B,C),x_subst(A,D,F).
great_ne(A,B):- r_subst_1(A,D),ring_subst_4(B,E),polar(E,C),sigma(E,F).
great_ne(A,B):- gt(D,C),ring_subst_5(A,F),ring_substitutions(A,D),ring_subst_5(B,E).
great_ne(A,B):- n_val(B,D),ring_subst_3(A,F),x_subst(B,E,C),ring_substitutions(A,E).
great_ne(A,B):- ring_subst_5(A,F),ring_substitutions(B,E),h_doner(F,C),x_subst(A,E,D).
great_ne(A,B):- ring_subst_3(B,E),x_subst(A,C,E),ring_subst_3(B,D),ring_subst_4(A,D).
great_ne(A,B):- ring_substitutions(A,C),h_doner(F,E),ring_subst_2(B,F),ring_subst_3(A,D).
great_ne(A,B):- x_subst(B,C,E),ring_subst_4(B,D),r_subst_2(A,F).
great_ne(A,B):- n_val(A,C),ring_subst_5(B,E),ring_subst_3(B,D),ring_subst_6(A,E).
great_ne(A,B):- ring_subst_5(A,F),ring_subst_6(B,D),pi_acceptor(D,E),alk_groups(B,C).
great_ne(A,B):- x_subst(A,C,F),x_subst(B,E,D),x_subst(B,E,F),ring_subst_5(B,F).
great_ne(A,B):- x_subst(A,D,E),ring_subst_3(B,E),ring_subst_4(A,C),ring_subst_2(B,E).
great_ne(A,B):- h_doner(E,D),ring_subst_6(A,F),ring_subst_3(A,E),ring_subst_2(B,C).
great_ne(A,B):- ring_subst_4(A,E),h_acceptor(C,F),ring_subst_4(A,C),ring_subst_4(B,D).
great_ne(A,B):- ring_subst_5(B,F),ring_subst_6(A,C),n_val(A,E),polar(C,D).
great_ne(A,B):- n_val(A,E),gt(E,C),n_val(B,D),n_val(A,D).
great_ne(A,B):- x_subst(B,C,E),r_subst_3(A,C),n_val(A,D),polar(E,F).
great_ne(A,B):- ring_substitutions(A,C),ring_subst_4(B,E),n_val(B,D),polarisable(E,F).
great_ne(A,B):- r_subst_3(B,C),n_val(A,E),pi_acceptor(F,D),ring_subst_3(A,F).
great_ne(A,B):- x_subst(A,E,F),alk_groups(B,D),gt(E,C),ring_subst_5(A,F).
great_ne(A,B):- sigma(D,C),ring_subst_2(B,E),ring_subst_3(A,E),ring_subst_6(B,D).
great_ne(A,B):- r_subst_2(A,D),n_val(B,E),ring_subst_3(A,F),x_subst(B,E,C).
great_ne(A,B):- ring_subst_6(B,F),ring_subst_6(A,D),polar(D,E),x_subst(B,C,D).
great_ne(A,B):- ring_subst_4(A,E),ring_substitutions(A,D),ring_subst_4(B,E),h_doner(E,C).
great_ne(A,B):- ring_subst_4(B,D),r_subst_2(A,C),r_subst_3(B,E).
great_ne(A,B):- ring_subst_5(A,C),ring_subst_4(B,E),ring_substitutions(A,D),ring_subst_3(A,F).
great_ne(A,B):- ring_subst_3(B,E),ring_subst_4(A,E),ring_subst_5(A,D),alk_groups(B,C).
great_ne(A,B):- alk_groups(B,D),x_subst(A,D,E),pi_doner(C,F),ring_subst_5(B,C).
great_ne(A,B):- alk_groups(B,D),ring_subst_3(B,E),pi_acceptor(E,C),alk_groups(A,F).
great_ne(A,B):- n_val(A,D),n_val(B,E),alk_groups(B,F),ring_subst_5(B,C).
great_ne(A,B):- ring_substitutions(B,F),ring_subst_2(A,E),ring_subst_2(B,C),pi_doner(E,D).
great_ne(A,B):- x_subst(A,C,D),ring_subst_6(B,E),alk_groups(B,C),size(E,F).
great_ne(A,B):- r_subst_2(A,D),ring_subst_3(B,C),x_subst(A,F,E),x_subst(B,F,E).
great_ne(A,B):- sigma(D,C),ring_substitutions(A,F),ring_subst_2(B,D),ring_substitutions(A,E).
great_ne(A,B):- ring_subst_5(B,F),sigma(F,D),ring_subst_5(A,E),h_acceptor(E,C).
great_ne(A,B):- ring_subst_6(A,C),ring_subst_3(B,E),pi_doner(C,D).
great_ne(A,B):- ring_subst_2(B,E),r_subst_3(A,C),n_val(A,F),ring_subst_3(A,D).
great_ne(A,B):- pi_doner(E,C),ring_subst_4(A,E),ring_subst_5(B,E),ring_subst_3(B,D).
great_ne(A,B):- ring_subst_6(A,C),ring_substitutions(A,D),flex(C,E),n_val(B,D).
great_ne(A,B):- alk_groups(B,D),r_subst_1(A,E),x_subst(A,D,C),r_subst_1(A,F).
great_ne(A,B):- r_subst_1(A,D),ring_subst_3(A,E),ring_subst_2(B,C),h_acceptor(C,F).
great_ne(A,B):- ring_subst_3(B,E),x_subst(A,D,E),r_subst_3(A,C),alk_groups(B,C).
great_ne(A,B):- gt(C,D),n_val(B,C),x_subst(A,F,E),x_subst(A,C,E).
great_ne(A,B):- h_doner(C,E),ring_subst_4(B,C),x_subst(A,D,F).
great_ne(A,B):- size(E,D),ring_subst_4(A,E),x_subst(A,F,E),r_subst_2(B,C).
great_ne(A,B):- gt(D,C),ring_substitutions(B,E),r_subst_3(A,D),r_subst_2(A,F).
great_ne(A,B):- r_subst_1(B,D),ring_substitutions(A,C),ring_subst_3(A,F),r_subst_3(B,E).
great_ne(A,B):- ring_subst_6(A,D),h_acceptor(D,C),ring_subst_5(B,E),alk_groups(A,F).
great_ne(A,B):- ring_substitutions(A,D),n_val(B,C),ring_subst_3(B,F),pi_doner(F,E).
great_ne(A,B):- r_subst_2(B,E),r_subst_3(B,D),ring_subst_3(A,F),ring_subst_2(B,C).
great_ne(A,B):- ring_subst_6(A,D),ring_subst_2(B,C),pi_doner(C,E),great_pi_don(E,F).
great_ne(A,B):- r_subst_3(A,E),r_subst_3(B,F),x_subst(A,D,C),n_val(A,E).
great_ne(A,B):- flex(C,E),ring_subst_5(B,D),ring_subst_4(B,F),ring_subst_2(A,C).
great_ne(A,B):- n_val(A,F),size(E,D),r_subst_1(B,C),ring_subst_6(A,E).
great_ne(A,B):- ring_subst_4(B,E),r_subst_3(A,F),ring_subst_3(B,D),x_subst(B,C,D).
great_ne(A,B):- ring_subst_3(B,F),size(C,D),ring_subst_2(A,C),polar(C,E).
great_ne(A,B):- size(C,F),x_subst(A,E,C),ring_subst_3(A,C),ring_subst_3(B,D).
great_ne(A,B):- alk_groups(B,D),ring_subst_2(B,E),ring_subst_3(A,E),polar(E,C).
great_ne(A,B):- ring_subst_5(A,C),ring_subst_2(B,C),ring_subst_4(B,D),ring_subst_6(B,C).
great_ne(A,B):- gt(D,C),x_subst(A,D,E),r_subst_3(B,C),polarisable(E,F).
great_ne(A,B):- r_subst_2(B,D),size(E,C),ring_subst_3(A,E),ring_subst_5(B,F).
great_ne(A,B):- ring_subst_2(B,F),ring_subst_2(A,C),r_subst_1(A,E),size(F,D).
great_ne(A,B):- n_val(A,D),x_subst(B,F,E),ring_subst_6(B,C),alk_groups(A,F).
great_ne(A,B):- ring_subst_2(B,E),ring_substitutions(B,D),flex(E,C),ring_subst_4(A,F).
great_ne(A,B):- n_val(B,E),gt(E,C),ring_subst_2(B,F),n_val(A,D).
great_ne(A,B):- n_val(A,C),ring_substitutions(A,F),alk_groups(A,E),x_subst(B,C,D).
great_ne(A,B):- ring_subst_2(B,E),r_subst_3(B,F),ring_subst_6(A,D),flex(D,C).
great_ne(A,B):- r_subst_1(B,D),x_subst(A,E,C),gt(F,E),ring_substitutions(B,F).
great_ne(A,B):- r_subst_1(A,D),ring_subst_3(B,C),ring_subst_2(A,C),ring_subst_6(B,E).
great_ne(A,B):- ring_subst_6(B,F),ring_subst_2(B,E),r_subst_1(B,C),ring_subst_3(A,D).
great_ne(A,B):- ring_subst_3(B,F),ring_subst_3(A,C),r_subst_3(A,D),size(F,E).
great_ne(A,B):- alk_groups(B,E),ring_subst_3(A,C),gt(E,F),pi_doner(C,D).
great_ne(A,B):- r_subst_2(B,D),x_subst(B,C,E),ring_substitutions(B,F),ring_subst_3(A,E).
great_ne(A,B):- ring_subst_5(B,F),h_acceptor(F,D),r_subst_2(A,E),polarisable(F,C).
great_ne(A,B):- n_val(B,E),r_subst_3(A,C),ring_subst_4(B,D),ring_subst_4(A,D).
great_ne(A,B):- ring_substitutions(B,D),ring_subst_4(B,C),ring_subst_3(A,C),x_subst(A,D,C).
great_ne(A,B):- ring_substitutions(B,F),alk_groups(A,D),x_subst(A,C,E),ring_substitutions(A,F).
great_ne(A,B):- ring_substitutions(A,F),r_subst_3(B,D),polar(C,E),x_subst(A,D,C).
great_ne(A,B):- x_subst(A,D,E),ring_subst_2(A,E),flex(E,C),alk_groups(B,F).
great_ne(A,B):- r_subst_1(B,D),ring_subst_4(B,C),ring_subst_5(A,E),ring_subst_6(B,C).
great_ne(A,B):- ring_subst_3(A,D),ring_subst_2(B,C),sigma(D,F),r_subst_3(B,E).
great_ne(A,B):- ring_subst_2(B,F),r_subst_2(A,E),r_subst_1(B,C),flex(F,D).
great_ne(A,B):- ring_subst_3(B,E),ring_subst_4(A,E),flex(D,C),ring_subst_2(A,D).
great_ne(A,B):- ring_subst_2(A,E),ring_subst_3(B,C),ring_subst_4(B,F),h_doner(C,D).
great_ne(A,B):- r_subst_3(A,E),r_subst_3(A,C),ring_subst_5(B,D),r_subst_2(A,F).
great_ne(A,B):- ring_subst_6(A,F),ring_subst_5(A,E),ring_subst_3(A,C),ring_subst_2(B,D).
great_ne(A,B):- ring_subst_5(A,F),r_subst_2(B,C),ring_subst_5(A,D),x_subst(A,E,D).
great_ne(A,B):- ring_subst_3(A,C),ring_subst_6(A,C),x_subst(B,E,F),polar(F,D).
great_ne(A,B):- alk_groups(A,C),n_val(B,D),ring_substitutions(A,E),gt(E,D).
great_ne(A,B):- r_subst_1(B,D),alk_groups(A,C),ring_subst_3(B,F),ring_subst_3(A,E).
great_ne(A,B):- x_subst(A,F,D),x_subst(B,F,C),ring_subst_3(B,C),h_doner(C,E).
great_ne(A,B):- r_subst_1(B,C),n_val(A,E),ring_substitutions(B,E),alk_groups(A,D).
great_ne(A,B):- flex(E,F),ring_subst_3(A,E),h_doner(D,C),ring_subst_4(B,D).
great_ne(A,B):- x_subst(A,D,E),ring_subst_3(A,E),ring_subst_3(B,C),gt(D,F).
great_ne(A,B):- r_subst_2(A,D),x_subst(A,E,C),ring_subst_2(B,C),ring_substitutions(A,F).
great_ne(A,B):- flex(D,C),ring_subst_2(B,F),alk_groups(A,E),ring_subst_2(A,D).
great_ne(A,B):- alk_groups(B,C),x_subst(B,F,E),x_subst(A,C,E),n_val(A,D).
great_ne(A,B):- ring_subst_2(B,E),polarisable(E,D),ring_subst_2(A,C),polar(E,F).
great_ne(A,B):- ring_substitutions(A,D),ring_substitutions(B,D),x_subst(A,C,E),r_subst_1(A,F).
great_ne(A,B):- ring_subst_6(B,F),ring_subst_5(B,D),ring_substitutions(A,E),ring_substitutions(B,C).
great_ne(A,B):- r_subst_3(B,C),alk_groups(A,C),ring_subst_5(A,E),sigma(E,D).
great_ne(A,B):- r_subst_3(A,E),r_subst_3(B,C),flex(D,F),ring_subst_3(B,D).
great_ne(A,B):- ring_subst_4(B,E),great_size(C,F),size(E,C),n_val(A,D).
great_ne(A,B):- x_subst(A,D,E),ring_substitutions(B,C),x_subst(A,C,E),alk_groups(A,F).
great_ne(A,B):- sigma(C,D),x_subst(A,E,C),ring_subst_2(B,F),ring_substitutions(B,E).
great_ne(A,B):- ring_subst_5(B,D),x_subst(B,E,F),x_subst(B,C,D),ring_subst_2(A,D).
great_ne(A,B):- r_subst_3(A,E),x_subst(B,F,C),gt(E,F),ring_subst_2(B,D).
great_ne(A,B):- r_subst_1(A,D),r_subst_2(B,C),ring_subst_6(A,E).
great_ne(A,B):- alk_groups(B,D),r_subst_3(B,C),x_subst(A,C,E),gt(D,F).
great_ne(A,B):- flex(F,E),ring_subst_6(A,F),ring_subst_3(B,C),size(C,D).
great_ne(A,B):- r_subst_1(B,E),ring_subst_6(B,C),ring_subst_4(B,D),ring_subst_3(A,D).
great_ne(A,B):- ring_subst_6(A,C),ring_subst_2(B,C),ring_substitutions(B,E),ring_subst_4(B,D).
great_ne(A,B):- x_subst(A,E,F),ring_subst_5(A,F),flex(F,C),ring_subst_3(B,D).
great_ne(A,B):- ring_subst_4(A,F),ring_subst_3(B,E),r_subst_3(A,C),x_subst(B,D,E).
great_ne(A,B):- ring_subst_6(A,F),ring_subst_6(B,D),ring_subst_2(A,C),ring_subst_6(B,E).
great_ne(A,B):- n_val(A,D),x_subst(B,D,C),ring_subst_6(B,E),ring_subst_3(A,E).
great_ne(A,B):- polar(E,C),r_subst_3(B,D),ring_subst_6(A,E).
great_ne(A,B):- ring_substitutions(B,F),gt(F,D),x_subst(A,E,C),ring_subst_4(A,C).
great_ne(A,B):- n_val(A,C),sigma(E,F),x_subst(B,C,D),ring_subst_6(A,E).
great_ne(A,B):- x_subst(B,D,F),ring_subst_3(B,C),alk_groups(A,D),flex(F,E).
