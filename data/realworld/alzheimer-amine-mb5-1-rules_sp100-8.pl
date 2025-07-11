great_ne(A,B):- polarisable(E,C),x_subst(B,F,E),gt(F,D),n_val(A,D).
great_ne(A,B):- ring_substitutions(A,C),gt(C,D),ring_subst_4(B,F),ring_substitutions(B,E).
great_ne(A,B):- ring_subst_6(A,C),pi_acceptor(C,F),x_subst(A,E,D),ring_subst_4(B,D).
great_ne(A,B):- pi_doner(E,C),x_subst(A,F,E),x_subst(B,F,E),ring_subst_4(B,D).
great_ne(A,B):- x_subst(B,D,E),x_subst(A,C,E),ring_substitutions(A,F),alk_groups(A,F).
great_ne(A,B):- r_subst_2(A,D),x_subst(A,E,C),r_subst_1(B,F),r_subst_3(B,E).
great_ne(A,B):- ring_subst_5(A,F),ring_subst_6(B,C),x_subst(B,E,C),ring_subst_2(A,D).
great_ne(A,B):- n_val(B,E),ring_subst_5(A,F),x_subst(A,C,D),ring_subst_2(A,F).
great_ne(A,B):- ring_subst_4(B,E),pi_doner(E,C),flex(F,D),ring_subst_6(A,F).
great_ne(A,B):- n_val(A,D),ring_subst_2(A,E),ring_subst_2(B,C),size(E,F).
great_ne(A,B):- alk_groups(B,D),ring_subst_4(A,E),ring_subst_4(A,C),x_subst(A,F,C).
great_ne(A,B):- r_subst_3(B,F),x_subst(A,C,E),flex(E,D),gt(F,C).
great_ne(A,B):- ring_subst_6(A,C),x_subst(A,D,E),ring_subst_4(B,E),n_val(B,D).
great_ne(A,B):- x_subst(A,E,C),gt(D,E),ring_substitutions(B,D),gt(D,F).
great_ne(A,B):- polarisable(F,E),ring_subst_3(B,F),ring_subst_3(A,F),x_subst(B,C,D).
great_ne(A,B):- x_subst(B,D,F),ring_subst_4(B,E),ring_subst_2(B,C),r_subst_3(A,D).
great_ne(A,B):- ring_subst_2(B,F),pi_doner(F,E),r_subst_2(A,C),ring_subst_3(A,D).
great_ne(A,B):- ring_subst_6(A,D),polarisable(C,F),r_subst_1(B,E),ring_subst_5(B,C).
great_ne(A,B):- ring_substitutions(B,F),ring_subst_3(B,C),x_subst(A,E,D),n_val(A,F).
great_ne(A,B):- ring_subst_2(B,E),polarisable(C,D),ring_subst_3(A,C),ring_subst_5(B,E).
great_ne(A,B):- sigma(E,C),ring_subst_3(A,E),ring_substitutions(B,D),r_subst_2(A,F).
great_ne(A,B):- r_subst_3(A,E),gt(E,D),ring_subst_2(B,F),size(F,C).
great_ne(A,B):- ring_subst_6(A,D),ring_subst_5(B,E),ring_subst_5(B,C),r_subst_2(A,F).
great_ne(A,B):- r_subst_3(A,E),r_subst_3(B,F),x_subst(B,C,D),r_subst_3(B,E).
great_ne(A,B):- x_subst(A,D,E),ring_substitutions(B,D),polar(E,C),alk_groups(A,D).
great_ne(A,B):- ring_subst_6(B,F),ring_subst_6(A,F),x_subst(A,C,D),sigma(F,E).
great_ne(A,B):- gt(E,F),pi_acceptor(D,C),x_subst(B,F,D),n_val(A,E).
great_ne(A,B):- ring_subst_5(A,E),ring_subst_6(B,D),ring_subst_3(B,C),ring_subst_4(B,C).
great_ne(A,B):- ring_subst_6(A,C),r_subst_1(A,D),ring_subst_4(B,C),x_subst(B,F,E).
great_ne(A,B):- r_subst_3(A,C),r_subst_3(A,F),x_subst(B,F,E),flex(E,D).
great_ne(A,B):- x_subst(A,E,C),ring_subst_2(B,F),n_val(B,D),r_subst_3(B,E).
great_ne(A,B):- ring_subst_4(A,E),r_subst_3(B,F),x_subst(A,D,C),ring_subst_5(B,C).
great_ne(A,B):- r_subst_3(B,F),x_subst(B,D,C),ring_substitutions(B,E),n_val(A,D).
great_ne(A,B):- ring_subst_4(A,F),ring_subst_2(B,D),r_subst_2(A,C),r_subst_3(B,E).
great_ne(A,B):- ring_subst_6(A,C),r_subst_2(A,D),n_val(A,E),ring_subst_4(B,C).
great_ne(A,B):- r_subst_3(A,F),ring_subst_4(B,D),ring_substitutions(B,E),x_subst(B,C,D).
great_ne(A,B):- x_subst(A,F,D),ring_subst_3(A,E),ring_subst_3(B,C),alk_groups(A,F).
great_ne(A,B):- sigma(C,E),ring_substitutions(A,D),ring_subst_3(B,C),ring_subst_4(A,C).
great_ne(A,B):- ring_subst_4(B,E),ring_subst_6(A,D),ring_subst_2(A,F),ring_subst_5(B,C).
great_ne(A,B):- ring_subst_3(B,E),ring_subst_3(A,E),h_acceptor(D,C),ring_subst_4(B,D).
great_ne(A,B):- x_subst(B,D,F),ring_subst_2(A,E),ring_subst_6(B,F),r_subst_1(B,C).
great_ne(A,B):- ring_subst_4(A,E),ring_substitutions(B,D),ring_subst_2(B,C),alk_groups(B,F).
great_ne(A,B):- ring_subst_2(B,C),r_subst_2(A,E),h_doner(C,D).
great_ne(A,B):- polarisable(C,F),r_subst_3(B,D),r_subst_2(A,E),ring_subst_6(B,C).
great_ne(A,B):- x_subst(B,C,E),ring_subst_3(B,E),h_acceptor(E,D),ring_subst_3(A,F).
great_ne(A,B):- ring_subst_5(A,D),ring_subst_3(B,C),sigma(E,F),ring_subst_5(A,E).
great_ne(A,B):- flex(C,E),ring_subst_4(B,C),ring_subst_3(A,C),x_subst(A,D,C).
great_ne(A,B):- r_subst_3(A,E),r_subst_3(A,C),r_subst_3(B,D),gt(C,F).
great_ne(A,B):- ring_subst_3(B,E),x_subst(B,C,E),ring_subst_3(A,E),h_acceptor(E,D).
great_ne(A,B):- r_subst_2(B,D),pi_acceptor(E,F),ring_subst_2(A,E),ring_subst_5(B,C).
great_ne(A,B):- ring_subst_3(B,C),polar(C,E),ring_subst_2(B,D),ring_subst_4(A,D).
great_ne(A,B):- r_subst_2(B,D),ring_subst_2(A,E),ring_substitutions(A,C),n_val(A,F).
great_ne(A,B):- alk_groups(B,D),r_subst_3(B,C),ring_subst_6(A,F),ring_subst_5(A,E).
great_ne(A,B):- ring_subst_5(A,C),ring_subst_6(A,C),sigma(C,E),x_subst(B,F,D).
great_ne(A,B):- h_doner(E,D),ring_subst_6(A,F),x_subst(B,C,F),ring_subst_6(B,E).
great_ne(A,B):- r_subst_2(A,D),r_subst_3(A,C),r_subst_3(B,C),ring_subst_6(A,E).
great_ne(A,B):- flex(C,E),ring_subst_5(B,D),ring_subst_2(B,C),ring_subst_3(A,D).
great_ne(A,B):- ring_subst_2(B,F),r_subst_2(B,C),ring_subst_5(A,E),ring_subst_4(A,D).
great_ne(A,B):- ring_substitutions(B,F),n_val(B,E),x_subst(A,E,C),flex(C,D).
great_ne(A,B):- size(E,C),ring_subst_6(B,E),r_subst_3(A,D),size(E,F).
great_ne(A,B):- ring_subst_6(A,C),size(C,F),sigma(C,D),r_subst_1(B,E).
great_ne(A,B):- alk_groups(A,E),x_subst(A,E,D),ring_subst_6(B,C),r_subst_2(A,F).
great_ne(A,B):- x_subst(A,F,D),flex(E,C),x_subst(A,F,E),ring_subst_3(B,D).
great_ne(A,B):- r_subst_3(A,E),pi_doner(D,C),ring_subst_2(B,F),ring_subst_3(B,D).
great_ne(A,B):- n_val(A,E),ring_subst_3(B,C),ring_subst_3(A,F),flex(F,D).
great_ne(A,B):- ring_subst_5(B,F),ring_subst_4(B,E),size(F,D),r_subst_1(A,C).
great_ne(A,B):- h_acceptor(C,E),ring_subst_6(A,F),x_subst(B,D,C),ring_subst_4(B,C).
great_ne(A,B):- ring_subst_5(A,C),ring_subst_6(A,C),r_subst_3(B,D),ring_subst_5(A,E).
great_ne(A,B):- x_subst(B,F,C),ring_subst_6(A,E),ring_subst_2(B,D),ring_subst_3(A,D).
great_ne(A,B):- ring_subst_2(B,E),ring_subst_3(B,D),alk_groups(B,C),ring_subst_3(A,F).
great_ne(A,B):- ring_subst_4(B,E),alk_groups(A,C),x_subst(A,C,E),ring_subst_4(A,D).
great_ne(A,B):- r_subst_1(A,D),size(C,F),ring_subst_4(B,C),ring_subst_2(B,E).
great_ne(A,B):- sigma(C,E),r_subst_3(A,F),ring_subst_3(B,C),alk_groups(A,D).
great_ne(A,B):- x_subst(A,C,F),r_subst_2(A,D),alk_groups(B,E),ring_substitutions(A,E).
great_ne(A,B):- ring_subst_4(A,E),polar(F,D),ring_subst_4(A,F),ring_substitutions(B,C).
great_ne(A,B):- x_subst(B,D,C),ring_subst_2(B,F),ring_subst_2(A,C),size(F,E).
great_ne(A,B):- ring_subst_6(A,C),ring_substitutions(B,D),alk_groups(B,F),r_subst_3(B,E).
great_ne(A,B):- x_subst(B,C,E),polarisable(E,D),ring_subst_3(A,F),ring_subst_6(A,F).
great_ne(A,B):- x_subst(A,D,E),pi_doner(E,C),ring_subst_6(B,E),pi_acceptor(E,F).
great_ne(A,B):- r_subst_3(A,C),alk_groups(A,C),ring_subst_5(A,D),ring_subst_2(B,D).
great_ne(A,B):- r_subst_3(A,C),r_subst_3(A,F),gt(C,E),x_subst(B,F,D).
great_ne(A,B):- flex(E,F),ring_subst_2(A,E),ring_subst_2(A,C),r_subst_3(B,D).
great_ne(A,B):- x_subst(A,C,F),sigma(F,E),ring_subst_5(B,F),r_subst_3(A,D).
great_ne(A,B):- r_subst_3(A,E),n_val(B,E),ring_subst_2(B,C),r_subst_3(B,D).
great_ne(A,B):- r_subst_3(A,E),pi_acceptor(D,C),ring_subst_4(B,F),ring_subst_3(B,D).
great_ne(A,B):- r_subst_3(B,C),gt(C,D),ring_subst_2(B,E),ring_subst_3(A,F).
great_ne(A,B):- polar(E,C),ring_subst_2(A,E),x_subst(A,F,E),x_subst(B,F,D).
great_ne(A,B):- ring_subst_4(B,E),x_subst(B,D,C),n_val(A,D),pi_acceptor(E,F).
great_ne(A,B):- r_subst_3(B,C),ring_subst_2(A,E),r_subst_3(A,D),r_subst_2(B,F).
great_ne(A,B):- ring_subst_5(B,F),r_subst_2(A,D),ring_subst_6(A,E),h_acceptor(E,C).
great_ne(A,B):- polar(D,E),r_subst_3(A,C),ring_subst_4(B,D),alk_groups(B,F).
great_ne(A,B):- ring_subst_3(B,D),x_subst(B,E,F),ring_subst_3(A,F),r_subst_1(A,C).
great_ne(A,B):- alk_groups(B,D),ring_subst_2(B,C),n_val(A,F),ring_substitutions(A,E).
great_ne(A,B):- ring_subst_4(B,E),ring_subst_4(A,E),ring_subst_4(B,C),ring_subst_5(A,D).
great_ne(A,B):- h_doner(D,E),ring_subst_5(B,D),ring_subst_6(A,D),pi_acceptor(D,C).
great_ne(A,B):- great_h_acc(D,F),x_subst(A,E,C),h_acceptor(C,D),ring_subst_5(B,C).
great_ne(A,B):- alk_groups(A,C),ring_subst_6(A,D),ring_subst_4(B,F),pi_acceptor(D,E).
great_ne(A,B):- r_subst_3(A,E),r_subst_3(B,F),ring_substitutions(A,C),x_subst(B,F,D).
great_ne(A,B):- r_subst_2(A,E),alk_groups(B,C),ring_subst_3(A,D).
great_ne(A,B):- r_subst_2(B,F),ring_subst_6(A,E),x_subst(A,D,C),r_subst_2(A,F).
