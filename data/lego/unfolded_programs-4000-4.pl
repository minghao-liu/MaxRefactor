p9(A,B) :- place1(A,C),place1(C,B)
p47(A,B) :- right(A,C),place1(C,B)
p1(A,B) :- place1(A,C),right(C,C1_0),place1(C1_0,B)
p2(A,B) :- right(A,C),place1(C,C1_0),place1(C1_0,B)
p76(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,B)
p342(A,B) :- place1(A,C),place1(C,C1_0),place1(C1_0,B)
p3(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,B)
p5(A,B) :- right(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,B)
p75(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C1_0),place1(C1_0,B)
p961(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p87(A,B) :- place1(A,C),right(C,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p1379(A,B) :- right(A,C),right(C,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p498(A,B) :- right(A,C),place1(C,C1_0-1),place1(C1_0-1,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p561(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p1466(A,B) :- right(A,C),place1(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p2570(A,B) :- right(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p83(A,B) :- place1(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p122(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p1463(A,B) :- right(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p10(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p22(A,B) :- right(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p56(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0-1),place1(C3_0-1,C3_0),place1(C3_0,C4_0),place1(C4_0,B)
p302(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p358(A,B) :- right(A,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p12(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),place1(C1_0,C5_0),place1(C5_0,C3_0),right(C3_0,C6_0),place1(C6_0,B)
p140(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C2_0),place1(C2_0,C),right(C,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p157(A,B) :- right(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0),place1(C2_0,C),place1(C,C1_0),right(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p600(A,B) :- right(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),place1(C1_0-1,C2_0),place1(C2_0,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p17(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,C4_0),place1(C4_0,B)
p74(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p141(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p337(A,B) :- right(A,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p417(A,B) :- right(A,C),right(C,C1_0),right(C1_0,C2_0-1),place1(C2_0-1,C2_0),place1(C2_0,C3_0),place1(C3_0,B)
p39(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p49(A,B) :- right(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C2_0-1),place1(C2_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p51(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C2_0-1),place1(C2_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p211(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p60(A,B) :- right(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),place1(C1_0-1,C2_0),place1(C2_0,C),right(C,C1_0),place1(C1_0,C4_0),place1(C4_0,C3_0),right(C3_0,C5_0),place1(C5_0,B)
p276(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,C7_0),place1(C7_0,B)
p844(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),right(C,C1_0),right(C1_0,C5_0),place1(C5_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p2545(A,B) :- right(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),place1(C1_0-1,C2_0),place1(C2_0,C),right(C,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
