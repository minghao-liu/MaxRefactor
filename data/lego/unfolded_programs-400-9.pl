p9(A,B) :- place1(A,C),place1(C,B)
p10(A,B) :- right(A,C),place1(C,B)
p0(A,B) :- place1(A,C),right(C,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p89(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C1_0),place1(C1_0,B)
p133(A,B) :- place1(A,C),right(C,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p155(A,B) :- right(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,B)
p319(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p157(A,B) :- place1(A,C0_0),place1(C0_0,C1_0),place1(C1_0,C),p325(C,B)
p1(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p18(A,B) :- right(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p35(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p203(A,B) :- place1(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p217(A,B) :- right(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p387(A,B) :- place1(A,C),place1(C,C1_0-1),place1(C1_0-1,C2_0),place1(C2_0,C1_0),p325(C1_0,B)
p2(A,B) :- place1(A,C),right(C,C1_0),place1(C1_0,B)
p31(A,B) :- right(A,C),place1(C,C1_0),place1(C1_0,B)
p132(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,B)
p234(A,B) :- place1(A,C),place1(C,C1_0),place1(C1_0,B)
p13(A,B) :- right(A,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p218(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p12(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,C4_0),place1(C4_0,B)
p68(A,B) :- right(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),place1(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p97(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p372(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p300(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C2_0),place1(C2_0,C),place1(C,C1_0),right(C1_0,C3_0),right(C3_0,C5_0),place1(C5_0,B)
p392(A,B) :- right(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C2_0-1),place1(C2_0-1,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p3(A,B) :- place1(A,C),place1(C,C1_0-1),place1(C1_0-1,C2_0-2),place1(C2_0-2,C2_0-1),right(C2_0-1,C3_0-1),place1(C3_0-1,C1_0),place1(C1_0,C3_0),place1(C3_0,C2_0),right(C2_0,C6_0),place1(C6_0,C4_0),right(C4_0,C7_0),place1(C7_0,B)
p123(A,B) :- place1(A,C0_0),place1(C0_0,C),place1(C,C2_0-1),place1(C2_0-1,C2_0),right(C2_0,C3_0-1),place1(C3_0-1,C5_0-1),place1(C5_0-1,C1_0),place1(C1_0,C4_0),place1(C4_0,C3_0),right(C3_0,C5_0),right(C5_0,C9_0),place1(C9_0,B)
p5(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p11(A,B) :- right(A,C0_0),right(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),place1(C1_0-1,C2_0),place1(C2_0,C),place1(C,C1_0),right(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p39(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p99(A,B) :- place1(A,C),right(C,C1_0-1),right(C1_0-1,C2_0-1),place1(C2_0-1,C3_0-1),place1(C3_0-1,C1_0),right(C1_0,C3_0),place1(C3_0,C2_0),place1(C2_0,C4_0),place1(C4_0,B)
p6(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p24(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),right(C1_0-1,C2_0),place1(C2_0,C),place1(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p27(A,B) :- right(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),place1(C1_0,C3_0),place1(C3_0,C2_0),right(C2_0,C4_0),place1(C4_0,B)
p58(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p23(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C2_0-1),place1(C2_0-1,C2_0),right(C2_0,C3_0-1),place1(C3_0-1,C5_0-1),place1(C5_0-1,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p47(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C2_0),place1(C2_0,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),right(C,C1_0),right(C1_0,C5_0),place1(C5_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p96(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0-1),place1(C2_0-1,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C5_0),place1(C5_0,C3_0),right(C3_0,C6_0),place1(C6_0,B)
p28(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0),place1(C2_0,C),right(C,C1_0),place1(C1_0,C4_0),place1(C4_0,C3_0),right(C3_0,C5_0),place1(C5_0,B)
p62(A,B) :- right(A,C),place1(C,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C3_0),place1(C3_0,C2_0-1),right(C2_0-1,C4_0-1),place1(C4_0-1,C1_0),place1(C1_0,C2_0),place1(C2_0,C4_0),place1(C4_0,B)
p111(A,B) :- place1(A,C),place1(C,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0-1),right(C2_0-1,C4_0-1),place1(C4_0-1,C1_0),right(C1_0,C3_0),place1(C3_0,C2_0),place1(C2_0,C4_0),place1(C4_0,B)
p80(A,B) :- place1(A,C0_0),place1(C0_0,C),place1(C,C2_0-1),place1(C2_0-1,C2_0),right(C2_0,C3_0-1),place1(C3_0-1,C5_0-1),place1(C5_0-1,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),right(C3_0,C8_0),place1(C8_0,C5_0),place1(C5_0,C9_0),place1(C9_0,B)
p146(A,B) :- place1(A,C),place1(C,C1_0-3),place1(C1_0-3,C1_0-2),right(C1_0-2,C2_0-2),place1(C2_0-2,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C2_0-1),right(C2_0-1,C4_0-1),place1(C4_0-1,C1_0),place1(C1_0,C3_0),place1(C3_0,C2_0),right(C2_0,C7_0),place1(C7_0,C4_0),place1(C4_0,C8_0),place1(C8_0,B)
p325(A,B) :- at_end(A),place1(A,C1_0),place1(C1_0,B)
p325(A,B) :- right(A,C),p325(C,B)
