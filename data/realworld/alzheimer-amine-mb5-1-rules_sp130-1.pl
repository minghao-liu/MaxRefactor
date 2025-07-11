great_ne(A,B):- alk_groups(B,D),polar(C,E),x_subst(A,D,C),n_val(A,D).
great_ne(A,B):- ring_subst_5(A,C),ring_subst_2(A,E),ring_subst_3(B,C),r_subst_3(A,D).
great_ne(A,B):- ring_subst_6(A,F),x_subst(B,D,C),r_subst_2(B,E),x_subst(A,D,C).
great_ne(A,B):- x_subst(B,E,D),ring_subst_2(B,C),r_subst_2(A,F).
great_ne(A,B):- ring_subst_4(B,E),x_subst(B,D,C),ring_subst_3(A,C),x_subst(A,F,C).
great_ne(A,B):- ring_substitutions(B,F),ring_subst_2(B,E),alk_groups(A,C),ring_subst_3(B,D).
great_ne(A,B):- ring_subst_6(A,D),pi_acceptor(F,C),r_subst_1(B,E),ring_subst_3(B,F).
great_ne(A,B):- ring_subst_6(A,F),ring_substitutions(B,D),ring_subst_3(B,C),ring_substitutions(B,E).
great_ne(A,B):- polar(C,F),ring_subst_5(B,D),ring_subst_2(B,C),r_subst_2(A,E).
great_ne(A,B):- h_doner(E,D),r_subst_3(B,C),ring_subst_6(A,E),polar(E,F).
great_ne(A,B):- polar(C,D),h_acceptor(E,F),ring_subst_5(A,E),ring_subst_6(B,C).
great_ne(A,B):- ring_subst_6(A,C),x_subst(A,E,D),ring_subst_3(B,D),ring_subst_2(A,D).
great_ne(A,B):- x_subst(A,F,D),x_subst(B,C,E),r_subst_3(B,C),n_val(A,F).
great_ne(A,B):- ring_subst_2(B,F),x_subst(B,E,F),polar(F,C),n_val(A,D).
great_ne(A,B):- ring_subst_2(B,E),n_val(B,C),pi_doner(E,D),r_subst_1(A,F).
great_ne(A,B):- r_subst_2(A,D),n_val(B,F),r_subst_3(B,C),x_subst(A,C,E).
great_ne(A,B):- h_acceptor(C,E),ring_subst_3(B,C),ring_subst_4(A,C),h_acceptor(C,D).
great_ne(A,B):- ring_substitutions(A,F),ring_subst_5(B,D),ring_subst_4(B,C),ring_substitutions(A,E).
great_ne(A,B):- r_subst_3(A,C),n_val(B,D),ring_subst_4(B,F),ring_subst_5(A,E).
great_ne(A,B):- ring_subst_5(B,D),ring_subst_4(B,C),alk_groups(A,E),gt(E,F).
great_ne(A,B):- ring_subst_6(A,D),n_val(B,C),r_subst_1(B,E),h_doner(D,F).
great_ne(A,B):- ring_subst_3(B,E),ring_subst_6(A,D),ring_subst_4(B,F),polarisable(E,C).
great_ne(A,B):- ring_substitutions(B,F),ring_substitutions(A,F),polar(E,D),x_subst(A,C,E).
great_ne(A,B):- ring_substitutions(A,C),r_subst_2(B,E),ring_subst_3(A,F),n_val(B,D).
great_ne(A,B):- x_subst(A,C,F),r_subst_3(B,C),sigma(F,E),ring_subst_2(A,D).
great_ne(A,B):- pi_doner(D,F),x_subst(A,E,D),ring_subst_2(B,D),ring_substitutions(B,C).
great_ne(A,B):- n_val(A,E),h_acceptor(D,C),x_subst(A,E,D),ring_subst_2(B,D).
great_ne(A,B):- flex(C,E),ring_subst_2(B,C),great_flex(E,F),ring_subst_2(A,D).
great_ne(A,B):- ring_substitutions(A,F),ring_subst_3(B,C),r_subst_2(A,E),ring_subst_2(B,D).
great_ne(A,B):- ring_subst_4(A,E),ring_subst_4(B,C),n_val(B,D),r_subst_1(A,F).
great_ne(A,B):- n_val(A,E),ring_subst_6(B,D),ring_subst_2(B,F),ring_subst_6(B,C).
great_ne(A,B):- pi_doner(C,F),x_subst(B,D,C),ring_subst_4(A,C),x_subst(B,D,E).
great_ne(A,B):- n_val(A,E),ring_subst_4(B,D),r_subst_1(B,C),r_subst_2(B,F).
great_ne(A,B):- x_subst(B,D,C),gt(D,E),alk_groups(A,E),ring_subst_5(B,C).
great_ne(A,B):- size(F,C),ring_subst_6(B,D),ring_subst_2(B,F),ring_subst_5(A,E).
great_ne(A,B):- ring_subst_6(A,C),ring_subst_3(B,C),sigma(D,E),ring_subst_3(A,D).
great_ne(A,B):- ring_subst_2(B,E),n_val(B,C),ring_subst_4(B,F),ring_subst_3(A,D).
great_ne(A,B):- polar(C,F),ring_subst_3(B,C),pi_acceptor(C,E),ring_subst_2(A,D).
great_ne(A,B):- polarisable(E,D),ring_subst_2(A,C),ring_subst_5(A,E),ring_subst_5(B,C).
great_ne(A,B):- x_subst(B,D,F),ring_subst_2(B,C),r_subst_1(A,E).
great_ne(A,B):- n_val(B,E),r_subst_3(B,D),alk_groups(B,C),n_val(A,D).
great_ne(A,B):- ring_subst_4(B,E),ring_substitutions(A,D),polarisable(E,C),ring_subst_6(A,F).
great_ne(A,B):- ring_subst_6(B,D),gt(C,E),n_val(A,C).
great_ne(A,B):- pi_acceptor(E,C),n_val(B,D),ring_subst_3(A,F),ring_subst_5(A,E).
great_ne(A,B):- size(F,E),ring_subst_2(B,F),x_subst(A,D,F),x_subst(A,D,C).
great_ne(A,B):- x_subst(A,D,E),ring_subst_3(A,E),x_subst(A,C,E),alk_groups(B,F).
great_ne(A,B):- pi_acceptor(F,C),r_subst_1(A,D),alk_groups(B,E),ring_subst_4(B,F).
great_ne(A,B):- ring_subst_4(A,E),ring_subst_5(B,E),r_subst_3(A,D),ring_subst_5(B,C).
great_ne(A,B):- x_subst(A,E,C),h_doner(D,F),ring_subst_5(B,D),r_subst_3(B,E).
great_ne(A,B):- ring_substitutions(A,C),r_subst_3(A,F),ring_substitutions(B,E),x_subst(B,C,D).
great_ne(A,B):- r_subst_1(A,D),great_polar(F,C),ring_subst_5(B,E),polar(E,F).
great_ne(A,B):- x_subst(B,D,C),gt(D,E),ring_subst_2(A,C),n_val(A,D).
great_ne(A,B):- polarisable(E,F),size(D,C),ring_subst_5(B,E),ring_subst_3(A,D).
great_ne(A,B):- ring_subst_5(A,F),ring_subst_2(A,E),ring_subst_5(B,D),h_acceptor(E,C).
great_ne(A,B):- n_val(B,E),r_subst_3(A,D),r_subst_2(A,C),r_subst_2(A,F).
great_ne(A,B):- ring_subst_6(A,F),pi_acceptor(D,C),size(F,E),ring_subst_2(B,D).
great_ne(A,B):- x_subst(B,C,E),r_subst_3(A,C),x_subst(A,D,F),x_subst(A,C,E).
great_ne(A,B):- ring_subst_5(A,C),x_subst(B,E,F),ring_subst_2(A,F),n_val(B,D).
great_ne(A,B):- ring_subst_6(B,F),x_subst(A,E,C),x_subst(B,D,C),n_val(A,E).
great_ne(A,B):- ring_subst_6(A,F),ring_subst_2(B,C),size(C,E),ring_subst_3(A,D).
great_ne(A,B):- pi_doner(F,C),ring_subst_3(B,E),ring_subst_2(B,F),ring_subst_2(A,D).
great_ne(A,B):- ring_subst_6(A,C),size(C,D),ring_subst_2(A,C),ring_subst_5(B,E).
great_ne(A,B):- ring_subst_6(A,D),ring_subst_5(B,D),r_subst_2(B,E),polarisable(D,C).
great_ne(A,B):- alk_groups(B,D),ring_substitutions(A,D),ring_subst_3(B,C).
great_ne(A,B):- flex(F,E),x_subst(A,C,D),ring_subst_2(A,F),x_subst(B,C,D).
great_ne(A,B):- ring_subst_5(A,E),ring_subst_3(B,D),r_subst_2(A,C),polar(E,F).
great_ne(A,B):- alk_groups(B,E),n_val(A,F),ring_subst_2(B,D),r_subst_1(A,C).
great_ne(A,B):- n_val(B,F),alk_groups(B,E),ring_subst_4(A,C),r_subst_3(A,D).
great_ne(A,B):- polar(C,F),ring_subst_4(A,E),r_subst_3(B,D),x_subst(A,D,C).
great_ne(A,B):- x_subst(A,D,E),x_subst(B,D,C),sigma(E,F),n_val(A,D).
great_ne(A,B):- ring_substitutions(B,F),ring_subst_5(A,D),ring_subst_4(A,C),ring_substitutions(A,E).
great_ne(A,B):- ring_subst_5(A,F),r_subst_2(A,D),x_subst(B,E,C),ring_substitutions(A,E).
great_ne(A,B):- ring_subst_4(B,F),alk_groups(A,E),ring_subst_6(B,C),ring_subst_2(A,D).
great_ne(A,B):- x_subst(A,F,D),ring_subst_2(A,C),ring_subst_4(B,D),flex(D,E).
great_ne(A,B):- x_subst(A,E,C),n_val(B,D),ring_substitutions(A,E),sigma(C,F).
great_ne(A,B):- ring_subst_2(B,E),flex(E,F),ring_subst_2(A,C),polarisable(E,D).
great_ne(A,B):- ring_subst_6(A,C),r_subst_3(B,F),ring_subst_2(B,D),h_acceptor(D,E).
great_ne(A,B):- size(F,C),ring_subst_4(A,E),ring_subst_3(B,F),polarisable(E,D).
great_ne(A,B):- ring_subst_6(A,D),r_subst_2(B,E),pi_acceptor(D,F),h_doner(D,C).
great_ne(A,B):- ring_subst_4(B,E),x_subst(B,F,C),pi_doner(C,D),ring_subst_6(A,E).
great_ne(A,B):- ring_subst_6(B,D),h_acceptor(D,C),ring_subst_5(B,E),ring_subst_3(A,F).
great_ne(A,B):- ring_subst_3(B,E),ring_subst_2(B,F),ring_subst_4(A,F),x_subst(B,C,D).
great_ne(A,B):- ring_subst_5(B,D),ring_subst_2(A,E),ring_subst_2(B,D),r_subst_2(A,C).
great_ne(A,B):- ring_subst_5(A,C),polar(C,E),x_subst(B,F,D),alk_groups(B,F).
great_ne(A,B):- ring_subst_6(A,C),ring_subst_2(B,E),polarisable(C,D),sigma(E,F).
great_ne(A,B):- ring_subst_5(A,F),ring_subst_6(B,C),h_doner(D,E),ring_subst_4(A,D).
great_ne(A,B):- ring_subst_3(B,E),pi_doner(D,C),ring_subst_6(A,D),ring_subst_3(A,F).
great_ne(A,B):- x_subst(B,C,E),polarisable(E,D),ring_subst_4(B,F),x_subst(A,C,E).
great_ne(A,B):- ring_subst_3(A,C),ring_subst_3(B,C),alk_groups(A,E),size(C,D).
great_ne(A,B):- ring_subst_6(B,F),ring_subst_5(B,E),x_subst(A,C,E),ring_subst_2(B,D).
great_ne(A,B):- ring_subst_4(A,F),ring_subst_3(A,F),ring_subst_2(B,D),x_subst(B,E,C).
great_ne(A,B):- ring_subst_3(B,E),n_val(A,D),ring_subst_6(B,E),ring_substitutions(B,C).
great_ne(A,B):- polarisable(C,F),r_subst_1(B,E),ring_subst_4(B,C),n_val(A,D).
great_ne(A,B):- n_val(B,E),x_subst(A,E,C),x_subst(B,F,D),ring_subst_4(B,D).
great_ne(A,B):- x_subst(B,C,F),r_subst_3(A,D),n_val(B,D),r_subst_3(B,E).
great_ne(A,B):- polarisable(D,E),ring_subst_5(A,F),alk_groups(B,C),ring_subst_3(B,D).
great_ne(A,B):- ring_subst_3(B,F),size(F,D),ring_subst_2(A,C),ring_subst_6(B,E).
great_ne(A,B):- n_val(B,E),ring_subst_5(A,D),ring_subst_2(A,C),sigma(C,F).
great_ne(A,B):- polarisable(D,F),ring_subst_4(A,E),ring_subst_6(B,D),h_doner(D,C).
great_ne(A,B):- ring_subst_5(B,D),ring_subst_4(A,C),ring_subst_3(A,F),ring_subst_6(A,E).
great_ne(A,B):- x_subst(B,D,F),polar(E,C),ring_subst_2(A,E),ring_subst_2(B,F).
great_ne(A,B):- ring_subst_4(A,E),ring_subst_3(A,E),ring_subst_2(B,C),size(E,D).
great_ne(A,B):- ring_substitutions(A,D),flex(C,F),ring_subst_5(A,E),ring_subst_6(B,C).
great_ne(A,B):- r_subst_2(B,D),ring_subst_4(A,E),great_sigma(F,C),sigma(E,F).
great_ne(A,B):- ring_subst_4(A,E),ring_subst_4(B,F),ring_subst_2(B,D),r_subst_1(A,C).
great_ne(A,B):- ring_subst_6(A,C),polarisable(C,E),h_doner(D,F),ring_subst_3(B,D).
great_ne(A,B):- ring_subst_3(B,E),flex(E,C),ring_subst_3(B,F),alk_groups(A,D).
great_ne(A,B):- ring_subst_6(A,D),ring_subst_5(B,E),x_subst(B,C,D),pi_acceptor(E,F).
great_ne(A,B):- h_acceptor(C,E),ring_subst_5(B,D),ring_subst_3(B,C),ring_subst_2(A,D).
great_ne(A,B):- x_subst(A,E,C),ring_subst_2(A,C),alk_groups(B,F),ring_subst_3(A,D).
great_ne(A,B):- ring_subst_3(B,E),pi_acceptor(F,D),ring_subst_2(A,F),h_doner(E,C).
great_ne(A,B):- ring_subst_4(B,E),r_subst_3(A,C),ring_subst_5(B,D),alk_groups(A,F).
great_ne(A,B):- ring_subst_5(B,F),r_subst_3(B,C),ring_subst_5(B,E),alk_groups(A,D).
great_ne(A,B):- ring_subst_4(A,E),x_subst(B,F,D),gt(F,C),ring_substitutions(B,C).
great_ne(A,B):- x_subst(A,C,D),ring_subst_6(B,D),ring_substitutions(A,E),r_subst_2(A,F).
great_ne(A,B):- ring_subst_6(A,D),ring_subst_3(B,D),x_subst(A,C,E),ring_subst_3(A,F).
great_ne(A,B):- gt(D,C),r_subst_3(A,C),n_val(B,D).
great_ne(A,B):- r_subst_3(A,E),x_subst(A,E,C),ring_substitutions(B,D),gt(E,F).
great_ne(A,B):- r_subst_3(A,E),ring_subst_2(B,F),r_subst_1(B,C),r_subst_3(A,D).
great_ne(A,B):- alk_groups(B,E),x_subst(B,C,F),x_subst(B,C,D),ring_subst_4(A,D).
great_ne(A,B):- ring_subst_4(B,C),ring_subst_6(B,C),pi_doner(D,E),ring_subst_4(A,D).
great_ne(A,B):- ring_subst_5(B,F),ring_subst_5(A,D),r_subst_2(B,E),polarisable(D,C).
great_ne(A,B):- sigma(D,C),ring_subst_2(B,E),x_subst(B,F,D),ring_subst_4(A,D).
great_ne(A,B):- x_subst(B,F,C),x_subst(A,F,E),n_val(A,F),flex(E,D).
great_ne(A,B):- r_subst_3(A,E),r_subst_3(B,F),r_subst_3(A,D),ring_substitutions(B,C).
great_ne(A,B):- x_subst(B,D,C),ring_subst_2(B,F),ring_subst_6(B,E),ring_subst_5(A,E).
great_ne(A,B):- ring_substitutions(A,F),ring_subst_3(B,C),pi_doner(C,E),h_doner(C,D).
great_ne(A,B):- alk_groups(B,D),alk_groups(A,C),n_val(A,C),ring_substitutions(A,E).
great_ne(A,B):- h_doner(E,D),ring_subst_3(B,C),ring_subst_2(A,C),ring_subst_6(B,E).
great_ne(A,B):- ring_subst_6(B,F),r_subst_3(B,C),r_subst_3(B,D),ring_subst_6(A,E).
