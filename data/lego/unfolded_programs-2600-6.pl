p1(A,B) :- place1(A,C),place1(C,B)
p20(A,B) :- right(A,C),place1(C,B)
p2(A,B) :- place1(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p54(A,B) :- right(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p88(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p137(A,B) :- place1(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p285(A,B) :- right(A,C),place1(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p492(A,B) :- right(A,C),place1(C,C1_0-1),place1(C1_0-1,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p199(A,B) :- place1(A,C),right(C,C1_0),right(C1_0,C2_0),right(C2_0,C3_0),place1(C3_0,B)
p590(A,B) :- right(A,C),place1(C,C1_0),right(C1_0,C2_0),right(C2_0,C3_0),place1(C3_0,B)
p3(A,B) :- place1(A,C0_0),place1(C0_0,C),place1(C,C1_0),place1(C1_0,B)
p34(A,B) :- place1(A,C),right(C,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p197(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p318(A,B) :- place1(A,C),right(C,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p447(A,B) :- right(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,B)
p1075(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C1_0),place1(C1_0,B)
p1350(A,B) :- right(A,C),right(C,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p8(A,B) :- right(A,C),place1(C,C1_0),place1(C1_0,B)
p18(A,B) :- place1(A,C),right(C,C1_0),place1(C1_0,B)
p135(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,B)
p181(A,B) :- place1(A,C),place1(C,C1_0),place1(C1_0,B)
p191(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p2267(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p29(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0),right(C3_0,C4_0),place1(C4_0,B)
p126(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,C2_0-1),place1(C2_0-1,C2_0),right(C2_0,C3_0),place1(C3_0,B)
p327(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),right(C1_0-1,C2_0),place1(C2_0,C),right(C,C1_0),place1(C1_0,B)
p797(A,B) :- right(A,C),place1(C,C1_0),right(C1_0,C2_0-1),place1(C2_0-1,C2_0),right(C2_0,C3_0),place1(C3_0,B)
p928(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,C2_0-1),place1(C2_0-1,C2_0),place1(C2_0,C3_0),place1(C3_0,B)
p4(A,B) :- right(A,C),place1(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C3_0),place1(C3_0,C2_0),place1(C2_0,C4_0),place1(C4_0,B)
p31(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p80(A,B) :- right(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),place1(C,C1_0),right(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p110(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p1738(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p6(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),place1(C,C1_0),right(C1_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p51(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),place1(C,C1_0),right(C1_0,C5_0),place1(C5_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p399(A,B) :- right(A,C0_0),right(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),place1(C1_0-1,C2_0),place1(C2_0,C),place1(C,C1_0),right(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p435(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),place1(C,C1_0),right(C1_0,C3_0),right(C3_0,C6_0),place1(C6_0,B)
p9(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0),place1(C2_0,C),place1(C,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p38(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p48(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p66(A,B) :- right(A,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p14(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0-1),place1(C2_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C5_0),place1(C5_0,C3_0),right(C3_0,C6_0),place1(C6_0,B)
p40(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),right(C1_0-1,C3_0-1),place1(C3_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C6_0),place1(C6_0,C3_0),place1(C3_0,C7_0),place1(C7_0,B)
p295(A,B) :- right(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),place1(C1_0-1,C2_0-1),place1(C2_0-1,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C5_0),place1(C5_0,C3_0),right(C3_0,C6_0),place1(C6_0,B)
p33(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0-1),place1(C2_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p113(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C2_0),place1(C2_0,C1_0),right(C1_0,C6_0),place1(C6_0,C3_0),place1(C3_0,C7_0),place1(C7_0,B)
p258(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0-1),place1(C2_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),right(C3_0,C6_0),place1(C6_0,B)
p519(A,B) :- right(A,C0_0),right(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),place1(C1_0-1,C2_0),place1(C2_0,C),right(C,C1_0),place1(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p495(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C2_0-1),place1(C2_0-1,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C6_0),place1(C6_0,C3_0),right(C3_0,C7_0),place1(C7_0,B)
