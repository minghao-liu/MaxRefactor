p12(A,B) :- place1(A,C),place1(C,B)
p47(A,B) :- right(A,C),place1(C,B)
p4(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p471(A,B) :- right(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p1151(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p1828(A,B) :- right(A,C),place1(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p1837(A,B) :- place1(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p127(A,B) :- right(A,C),place1(C,C1_0),right(C1_0,C2_0),right(C2_0,C3_0),place1(C3_0,B)
p7(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,B)
p15(A,B) :- right(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,B)
p39(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C1_0),place1(C1_0,B)
p235(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p995(A,B) :- place1(A,C0_0),place1(C0_0,C),place1(C,C1_0),place1(C1_0,B)
p1985(A,B) :- place1(A,C),right(C,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p2202(A,B) :- right(A,C),right(C,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p23(A,B) :- right(A,C),place1(C,C1_0),place1(C1_0,B)
p60(A,B) :- place1(A,C),right(C,C1_0),place1(C1_0,B)
p73(A,B) :- place1(A,C),place1(C,C1_0),place1(C1_0,B)
p203(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,B)
p1294(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p6(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,C4_0),place1(C4_0,B)
p30(A,B) :- right(A,C),place1(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),place1(C2_0,C4_0),place1(C4_0,B)
p178(A,B) :- right(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,C4_0),place1(C4_0,B)
p467(A,B) :- right(A,C),place1(C,C1_0),right(C1_0,C2_0-1),place1(C2_0-1,C2_0),right(C2_0,C3_0),place1(C3_0,B)
p617(A,B) :- right(A,C),right(C,C1_0),right(C1_0,C2_0-1),place1(C2_0-1,C2_0),place1(C2_0,C3_0),place1(C3_0,B)
p705(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p0(A,B) :- place1(A,C0_0),place1(C0_0,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p88(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p243(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p729(A,B) :- right(A,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p10(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),right(C1_0,C5_0),place1(C5_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p54(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0),place1(C2_0,C),place1(C,C1_0),right(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p94(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0),place1(C2_0,C),place1(C,C1_0),right(C1_0,C3_0),right(C3_0,C5_0),place1(C5_0,B)
p273(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),place1(C,C1_0),right(C1_0,C5_0),place1(C5_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p17(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0-1),place1(C2_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p38(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),right(C3_0,C7_0),place1(C7_0,B)
p67(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C6_0),place1(C6_0,C3_0),place1(C3_0,C7_0),place1(C7_0,B)
p3151(A,B) :- right(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C2_0-1),place1(C2_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C5_0),place1(C5_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p48(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,C3_0-1),place1(C3_0-1,C3_0),right(C3_0,C4_0),place1(C4_0,B)
p80(A,B) :- right(A,C),place1(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C3_0),place1(C3_0,C2_0),place1(C2_0,C4_0),place1(C4_0,B)
p126(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p280(A,B) :- right(A,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p2706(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p140(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0-1),place1(C2_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C5_0),place1(C5_0,C3_0),right(C3_0,C6_0),place1(C6_0,B)
p181(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C2_0),place1(C2_0,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),right(C,C1_0),right(C1_0,C5_0),place1(C5_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p590(A,B) :- right(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0-1),place1(C2_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C5_0),place1(C5_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
