p6(A,B) :- right(A,C),place1(C,B)
p56(A,B) :- place1(A,C),place1(C,B)
p3(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p55(A,B) :- right(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p57(A,B) :- right(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p115(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p153(A,B) :- place1(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p4(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,B)
p17(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p30(A,B) :- right(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,B)
p37(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C1_0),place1(C1_0,B)
p11(A,B) :- right(A,C),place1(C,C1_0),place1(C1_0,B)
p86(A,B) :- place1(A,C),right(C,C1_0),place1(C1_0,B)
p170(A,B) :- place1(A,C),place1(C,C1_0),place1(C1_0,B)
p173(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,B)
p24(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),place1(C,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p34(A,B) :- place1(A,C),right(C,C1_0),right(C1_0,C2_0),right(C2_0,C3_0),place1(C3_0,C4_0),place1(C4_0,B)
p51(A,B) :- right(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),place1(C2_0,C4_0),place1(C4_0,B)
p71(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p29(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),place1(C,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p88(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C2_0),place1(C2_0,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p0(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C2_0),place1(C2_0,C3_0-2),place1(C3_0-2,C3_0-1),right(C3_0-1,C4_0),place1(C4_0,C1_0),right(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p147(A,B) :- place1(A,C0_0),right(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),place1(C1_0-1,C2_0),place1(C2_0,C),right(C,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p164(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0-1),place1(C2_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p1(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0-1),place1(C2_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p73(A,B) :- right(A,C0_0-2),place1(C0_0-2,C0_0-1),place1(C0_0-1,C1_0-1),place1(C1_0-1,C0_0),right(C0_0,C2_0),place1(C2_0,C1_0),place1(C1_0,C3_0),place1(C3_0,C),place1(C,B)
p2(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p20(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0-1),place1(C3_0-1,C3_0),place1(C3_0,C4_0),place1(C4_0,B)
p64(A,B) :- right(A,C),place1(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C3_0),place1(C3_0,C2_0),right(C2_0,C4_0),place1(C4_0,B)
p185(A,B) :- right(A,C),right(C,C1_0-1),right(C1_0-1,C2_0-1),place1(C2_0-1,C3_0),place1(C3_0,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p10(A,B) :- place1(A,C0_0),place1(C0_0,C),place1(C,C2_0-1),place1(C2_0-1,C2_0),right(C2_0,C3_0-1),place1(C3_0-1,C5_0-1),place1(C5_0-1,C1_0),place1(C1_0,C4_0),place1(C4_0,C3_0),right(C3_0,C8_0),place1(C8_0,C5_0),right(C5_0,C9_0),place1(C9_0,B)
p54(A,B) :- place1(A,C0_0),place1(C0_0,C),place1(C,C2_0-1),place1(C2_0-1,C2_0),right(C2_0,C3_0-1),right(C3_0-1,C5_0-1),place1(C5_0-1,C1_0),place1(C1_0,C4_0),place1(C4_0,C3_0),right(C3_0,C8_0),place1(C8_0,C5_0),place1(C5_0,C9_0),place1(C9_0,B)
p16(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0-1),place1(C2_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C5_0),place1(C5_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p52(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),place1(C,C2_0),place1(C2_0,C4_0),place1(C4_0,C1_0),right(C1_0,C3_0),right(C3_0,C7_0),place1(C7_0,C6_0),place1(C6_0,C8_0),place1(C8_0,B)
p90(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C2_0-1),right(C2_0-1,C3_0-2),place1(C3_0-2,C2_0),place1(C2_0,C3_0-1),right(C3_0-1,C5_0-1),place1(C5_0-1,C1_0),place1(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p45(A,B) :- place1(A,C),place1(C,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C3_0-1),place1(C3_0-1,C2_0-1),place1(C2_0-1,C4_0-1),place1(C4_0-1,C1_0),right(C1_0,C5_0),place1(C5_0,C3_0),place1(C3_0,C6_0),place1(C6_0,C2_0),right(C2_0,C7_0),place1(C7_0,C4_0),place1(C4_0,C8_0),place1(C8_0,B)
p46(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),place1(C,C4_0),place1(C4_0,C2_0),right(C2_0,C5_0),right(C5_0,C7_0-1),place1(C7_0-1,C1_0),place1(C1_0,C3_0),place1(C3_0,C7_0),place1(C7_0,B)
p59(A,B) :- place1(A,C),place1(C,C1_0-1),place1(C1_0-1,C2_0-2),place1(C2_0-2,C2_0-1),right(C2_0-1,C3_0-1),place1(C3_0-1,C1_0),place1(C1_0,C3_0),right(C3_0,C5_0),place1(C5_0,C2_0),place1(C2_0,C4_0),right(C4_0,C7_0),place1(C7_0,B)
p84(A,B) :- place1(A,C),place1(C,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0-1),place1(C2_0-1,C4_0-1),place1(C4_0-1,C1_0),right(C1_0,C5_0),place1(C5_0,C3_0),place1(C3_0,C6_0),place1(C6_0,C2_0),right(C2_0,C7_0),place1(C7_0,C4_0),place1(C4_0,C8_0),place1(C8_0,B)
