p1(A,B) :- place1(A,C),place1(C,B)
p16(A,B) :- right(A,C),place1(C,B)
p9(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p35(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p51(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,C4_0),place1(C4_0,B)
p192(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),right(C1_0-1,C2_0),place1(C2_0,C),right(C,C1_0),place1(C1_0,B)
p259(A,B) :- right(A,C),place1(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),right(C2_0,C4_0),place1(C4_0,B)
p804(A,B) :- right(A,C),right(C,C1_0),right(C1_0,C2_0-1),place1(C2_0-1,C2_0),place1(C2_0,C3_0),place1(C3_0,B)
p12(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,B)
p62(A,B) :- place1(A,C),right(C,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p177(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p260(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C1_0),place1(C1_0,B)
p312(A,B) :- right(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,B)
p407(A,B) :- right(A,C),right(C,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p648(A,B) :- place1(A,C0_0),place1(C0_0,C),place1(C,C1_0),place1(C1_0,B)
p17(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p18(A,B) :- right(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p152(A,B) :- right(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p158(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p208(A,B) :- place1(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p209(A,B) :- right(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p231(A,B) :- place1(A,C),right(C,C1_0),right(C1_0,C2_0),right(C2_0,C3_0),place1(C3_0,B)
p24(A,B) :- place1(A,C),right(C,C1_0),place1(C1_0,B)
p33(A,B) :- right(A,C),place1(C,C1_0),place1(C1_0,B)
p87(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,B)
p187(A,B) :- place1(A,C),place1(C,C1_0),place1(C1_0,B)
p0(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p5(A,B) :- place1(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),place1(C1_0,C3_0),place1(C3_0,C2_0),right(C2_0,C4_0),place1(C4_0,B)
p38(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p275(A,B) :- right(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),place1(C1_0,C3_0),place1(C3_0,C2_0),right(C2_0,C4_0),place1(C4_0,B)
p750(A,B) :- right(A,C0_0),right(C0_0,C1_0-1),right(C1_0-1,C2_0),place1(C2_0,C),place1(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p1085(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p2(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),right(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p8(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p13(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C4_0),place1(C4_0,C3_0),right(C3_0,C5_0),place1(C5_0,B)
p138(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),right(C1_0-1,C3_0-1),place1(C3_0-1,C),place1(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p4(A,B) :- place1(A,C0_0),right(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),place1(C1_0-1,C2_0-1),place1(C2_0-1,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C5_0),place1(C5_0,C3_0),right(C3_0,C6_0),place1(C6_0,B)
p651(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C2_0),place1(C2_0,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),right(C,C1_0),right(C1_0,C5_0),place1(C5_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p1409(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C6_0),place1(C6_0,C3_0),place1(C3_0,C7_0),place1(C7_0,B)
p7(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C2_0),place1(C2_0,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p29(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0-1),place1(C2_0-1,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p278(A,B) :- right(A,C0_0),right(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),place1(C1_0-1,C2_0),place1(C2_0,C),place1(C,C1_0),right(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p378(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p58(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C2_0),place1(C2_0,C1_0-1),right(C1_0-1,C3_0-1),place1(C3_0-1,C),place1(C,C1_0),right(C1_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p159(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C2_0),place1(C2_0,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),place1(C,C1_0),right(C1_0,C3_0),right(C3_0,C6_0),place1(C6_0,B)
p237(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),place1(C0_0,C2_0),place1(C2_0,C1_0-1),right(C1_0-1,C3_0-1),place1(C3_0-1,C),place1(C,C1_0),right(C1_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p65(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C2_0-1),place1(C2_0-1,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C6_0),place1(C6_0,C3_0),right(C3_0,C7_0),place1(C7_0,B)
p194(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),place1(C0_0,C2_0-1),place1(C2_0-1,C1_0-1),right(C1_0-1,C3_0-1),place1(C3_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C6_0),place1(C6_0,C3_0),place1(C3_0,C7_0),place1(C7_0,B)
