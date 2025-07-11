great_ne(A,B):- n_val(B,E),ring_subst_5(B,D),flex(D,C),ring_substitutions(A,E).
great_ne(A,B):- alk_groups(B,D),n_val(B,F),r_subst_2(A,E),ring_subst_3(A,C).
great_ne(A,B):- x_subst(A,D,E),x_subst(B,D,C),n_val(B,D),alk_groups(A,F).
great_ne(A,B):- x_subst(A,D,E),size(E,F),gt(C,D),ring_substitutions(B,C).
great_ne(A,B):- x_subst(A,C,D),r_subst_2(B,E),n_val(A,C),ring_subst_5(A,D).
great_ne(A,B):- ring_substitutions(B,D),polarisable(F,E),alk_groups(B,C),ring_subst_3(A,F).
great_ne(A,B):- ring_subst_6(A,C),ring_subst_2(A,E),x_subst(B,D,C),ring_subst_4(A,F).
great_ne(A,B):- alk_groups(B,D),x_subst(A,D,E),alk_groups(A,C),r_subst_1(A,F).
great_ne(A,B):- n_val(A,E),ring_subst_3(B,C),x_subst(B,E,F),x_subst(A,E,D).
great_ne(A,B):- ring_subst_2(B,E),flex(E,C),ring_subst_4(B,E),n_val(A,D).
great_ne(A,B):- n_val(A,E),x_subst(B,E,F),n_val(B,D),ring_subst_6(B,C).
great_ne(A,B):- ring_subst_6(A,C),ring_subst_5(A,F),polarisable(F,D),x_subst(B,E,C).
great_ne(A,B):- ring_subst_6(B,F),r_subst_3(B,C),ring_subst_4(A,E),h_acceptor(F,D).
great_ne(A,B):- n_val(B,E),r_subst_3(A,C),alk_groups(B,E),ring_subst_5(A,D).
great_ne(A,B):- pi_acceptor(C,F),x_subst(A,E,C),ring_subst_3(B,C),sigma(C,D).
great_ne(A,B):- ring_subst_5(A,C),x_subst(B,E,D),ring_subst_6(A,F),x_subst(B,E,C).
great_ne(A,B):- ring_substitutions(A,C),sigma(F,D),ring_subst_3(B,F),great_sigma(D,E).
great_ne(A,B):- x_subst(B,C,E),ring_subst_5(A,D),ring_subst_2(A,F),ring_subst_2(B,D).
great_ne(A,B):- x_subst(A,D,E),flex(C,F),ring_subst_6(B,E),x_subst(A,D,C).
great_ne(A,B):- ring_subst_2(A,E),ring_subst_3(B,C),flex(C,D),ring_subst_3(A,E).
great_ne(A,B):- great_h_acc(C,D),x_subst(A,F,E),x_subst(B,F,E),h_acceptor(E,C).
great_ne(A,B):- gt(D,C),x_subst(A,D,E),x_subst(B,D,E),polarisable(E,F).
great_ne(A,B):- alk_groups(B,D),r_subst_3(A,C),gt(C,E),ring_substitutions(B,F).
great_ne(A,B):- ring_subst_5(B,F),ring_subst_4(A,D),h_acceptor(D,C),r_subst_3(B,E).
great_ne(A,B):- alk_groups(B,D),ring_subst_6(A,F),n_val(B,E),gt(E,C).
great_ne(A,B):- ring_subst_6(A,C),x_subst(A,E,D),x_subst(A,F,C),ring_subst_5(B,C).
great_ne(A,B):- ring_substitutions(B,D),ring_subst_4(A,C),ring_subst_6(B,E).
great_ne(A,B):- ring_substitutions(A,D),ring_substitutions(B,C),ring_subst_3(A,F),r_subst_3(B,E).
great_ne(A,B):- ring_subst_5(B,F),x_subst(B,E,D),ring_substitutions(B,E),r_subst_2(A,C).
great_ne(A,B):- x_subst(B,D,F),ring_subst_2(B,E),n_val(A,C),n_val(A,D).
great_ne(A,B):- ring_subst_2(B,C),ring_subst_5(B,E),alk_groups(A,D),n_val(B,D).
great_ne(A,B):- ring_subst_6(A,C),ring_subst_4(A,E),x_subst(B,D,E),sigma(C,F).
great_ne(A,B):- polar(E,F),ring_substitutions(B,D),ring_subst_4(B,C),ring_subst_3(A,E).
great_ne(A,B):- ring_subst_3(A,E),x_subst(A,C,E),ring_subst_5(B,D),polar(E,F).
great_ne(A,B):- r_subst_3(A,C),alk_groups(A,E),ring_subst_6(B,D),r_subst_2(A,F).
great_ne(A,B):- h_acceptor(E,D),ring_subst_3(B,C),ring_subst_6(B,E),alk_groups(A,F).
great_ne(A,B):- x_subst(A,C,F),ring_subst_2(B,E),ring_subst_5(A,D),ring_subst_6(A,E).
great_ne(A,B):- ring_subst_5(A,D),ring_subst_2(B,C),ring_subst_3(B,C),polar(D,E).
great_ne(A,B):- x_subst(A,C,F),ring_subst_5(A,F),ring_substitutions(B,E),x_subst(A,E,D).
great_ne(A,B):- size(C,F),ring_subst_4(A,E),ring_subst_3(B,C),alk_groups(A,D).
great_ne(A,B):- ring_subst_5(A,F),r_subst_3(A,C),ring_substitutions(B,E),ring_subst_4(A,D).
great_ne(A,B):- r_subst_3(B,C),h_doner(D,E),ring_subst_6(A,F),ring_subst_3(A,D).
great_ne(A,B):- ring_subst_6(B,F),ring_subst_2(A,C),x_subst(A,D,F),pi_doner(F,E).
great_ne(A,B):- ring_subst_6(B,F),ring_subst_2(A,E),ring_subst_6(A,D),pi_doner(F,C).
great_ne(A,B):- r_subst_3(B,C),x_subst(A,C,D),x_subst(A,F,E),ring_subst_5(B,E).
great_ne(A,B):- r_subst_3(A,E),ring_subst_5(A,F),sigma(C,D),ring_subst_3(B,C).
great_ne(A,B):- ring_subst_6(A,C),ring_subst_4(B,E),polarisable(D,F),ring_subst_2(B,D).
great_ne(A,B):- ring_subst_6(A,C),ring_subst_2(B,E),h_doner(E,D),r_subst_2(A,F).
great_ne(A,B):- ring_subst_3(A,D),ring_subst_6(B,D),x_subst(A,F,E),ring_substitutions(B,C).
great_ne(A,B):- ring_subst_5(B,F),r_subst_2(A,E),x_subst(A,D,F),ring_subst_6(B,C).
great_ne(A,B):- flex(C,E),ring_subst_4(B,C),ring_subst_2(A,F),h_doner(F,D).
great_ne(A,B):- ring_subst_6(B,C),alk_groups(A,D),pi_doner(C,E),alk_groups(A,F).
great_ne(A,B):- sigma(C,D),ring_subst_4(A,E),ring_subst_4(B,C),sigma(E,D).
great_ne(A,B):- ring_substitutions(B,F),sigma(C,D),n_val(B,E),ring_subst_2(A,C).
great_ne(A,B):- x_subst(A,E,F),ring_subst_3(B,F),r_subst_2(B,D),ring_subst_3(B,C).
great_ne(A,B):- x_subst(B,E,D),ring_subst_5(B,D),ring_subst_3(B,C),n_val(A,F).
great_ne(A,B):- ring_subst_3(B,E),ring_subst_2(A,C),h_doner(C,D),size(E,F).
great_ne(A,B):- ring_subst_5(B,F),ring_subst_3(B,C),size(C,D),ring_substitutions(A,E).
great_ne(A,B):- r_subst_3(B,C),x_subst(A,C,D),x_subst(A,E,D),r_subst_3(B,E).
great_ne(A,B):- x_subst(B,E,C),n_val(B,E),x_subst(A,D,C),r_subst_3(B,E).
great_ne(A,B):- ring_subst_4(B,E),sigma(E,F),r_subst_3(A,D),r_subst_2(A,C).
great_ne(A,B):- size(E,C),ring_subst_3(A,E),x_subst(B,F,E),ring_subst_3(B,D).
great_ne(A,B):- n_val(A,C),gt(C,D),x_subst(B,F,E),alk_groups(B,C).
great_ne(A,B):- ring_subst_5(A,F),x_subst(B,C,F),x_subst(A,E,D),ring_subst_3(B,D).
great_ne(A,B):- x_subst(B,E,D),flex(D,C),n_val(A,F),ring_subst_3(B,D).
great_ne(A,B):- n_val(B,E),ring_substitutions(B,E),x_subst(B,C,D),r_subst_2(A,F).
great_ne(A,B):- x_subst(A,C,F),ring_subst_4(A,E),polarisable(F,D),ring_subst_5(B,E).
great_ne(A,B):- ring_subst_4(A,F),ring_subst_4(B,E),r_subst_3(A,C),x_subst(B,D,E).
great_ne(A,B):- r_subst_3(B,C),h_doner(E,F),polar(E,D),x_subst(A,C,E).
great_ne(A,B):- ring_subst_4(A,E),x_subst(B,F,E),x_subst(B,C,D),ring_subst_2(A,D).
great_ne(A,B):- ring_subst_3(B,E),sigma(E,D),x_subst(A,C,E),r_subst_1(A,F).
great_ne(A,B):- n_val(B,D),ring_subst_3(A,C),x_subst(A,D,C),n_val(A,D).
great_ne(A,B):- r_subst_2(A,D),ring_subst_4(B,E),r_subst_1(B,C),pi_doner(E,F).
great_ne(A,B):- pi_acceptor(D,F),n_val(B,E),x_subst(A,C,D),alk_groups(A,C).
great_ne(A,B):- r_subst_3(B,C),sigma(F,D),ring_subst_3(B,F),ring_substitutions(A,E).
great_ne(A,B):- pi_doner(D,C),ring_subst_2(B,F),pi_doner(F,E),ring_subst_3(A,D).
great_ne(A,B):- sigma(D,C),ring_subst_4(A,E),sigma(D,F),ring_subst_5(B,D).
great_ne(A,B):- ring_subst_6(A,C),ring_subst_6(B,D),r_subst_3(A,F),pi_acceptor(C,E).
great_ne(A,B):- ring_substitutions(A,C),n_val(B,C),ring_subst_2(B,D),ring_substitutions(A,E).
great_ne(A,B):- x_subst(A,E,F),pi_doner(D,C),ring_subst_5(A,D),ring_subst_5(B,F).
