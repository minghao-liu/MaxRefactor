p30(A,B) :- place1(A,C),place1(C,B)
p54(A,B) :- right(A,C),place1(C,B)
p0(A,B) :- place1(A,C),right(C,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p22(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,B)
p32(A,B) :- right(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,B)
p276(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p284(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C1_0),place1(C1_0,B)
p7(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p12(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p53(A,B) :- place1(A,C),place1(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),right(C2_0,C4_0),place1(C4_0,B)
p55(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,C2_0-1),place1(C2_0-1,C2_0),right(C2_0,C3_0),place1(C3_0,B)
p8(A,B) :- place1(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p13(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p41(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p57(A,B) :- right(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p191(A,B) :- right(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p255(A,B) :- right(A,C),place1(C,C1_0-1),place1(C1_0-1,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p737(A,B) :- right(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p10(A,B) :- right(A,C),place1(C,C1_0),place1(C1_0,B)
p61(A,B) :- place1(A,C),right(C,C1_0),place1(C1_0,B)
p116(A,B) :- place1(A,C),place1(C,C1_0),place1(C1_0,B)
p227(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,B)
p2(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0),place1(C2_0,C),place1(C,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p173(A,B) :- right(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),place1(C1_0-1,C2_0),place1(C2_0,C),right(C,C1_0),place1(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p316(A,B) :- place1(A,C),right(C,C1_0-1),right(C1_0-1,C2_0-2),place1(C2_0-2,C2_0-1),place1(C2_0-1,C3_0),place1(C3_0,C1_0),place1(C1_0,C2_0),right(C2_0,C4_0),place1(C4_0,C6_0),place1(C6_0,B)
p697(A,B) :- right(A,C0_0),right(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),place1(C1_0-1,C2_0),place1(C2_0,C),right(C,C1_0),place1(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p3(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C4_0),place1(C4_0,C3_0),right(C3_0,C5_0),place1(C5_0,B)
p37(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p65(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),right(C3_0,C5_0),place1(C5_0,B)
p152(A,B) :- right(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p9(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C6_0),place1(C6_0,C3_0),right(C3_0,C7_0),place1(C7_0,B)
p319(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),right(C1_0-1,C3_0-1),place1(C3_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C6_0),place1(C6_0,C3_0),place1(C3_0,C7_0),place1(C7_0,B)
p486(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C2_0),place1(C2_0,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),right(C,C1_0),place1(C1_0,C5_0),place1(C5_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p15(A,B) :- place1(A,C),place1(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C3_0),place1(C3_0,C2_0),place1(C2_0,C4_0),place1(C4_0,B)
p24(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p67(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0-1),place1(C3_0-1,C3_0),place1(C3_0,C4_0),place1(C4_0,B)
p145(A,B) :- right(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0-1),place1(C3_0-1,C3_0),place1(C3_0,C4_0),place1(C4_0,B)
p21(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C2_0),place1(C2_0,C),place1(C,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p26(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0),place1(C2_0,C),place1(C,C1_0),right(C1_0,C3_0),right(C3_0,C5_0),place1(C5_0,B)
p99(A,B) :- right(A,C0_0),right(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),place1(C1_0-1,C2_0),place1(C2_0,C),place1(C,C1_0),right(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p149(A,B) :- right(A,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C2_0),place1(C2_0,C1_0),right(C1_0,C5_0),place1(C5_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p304(A,B) :- place1(A,C),right(C,C1_0-2),place1(C1_0-2,C1_0-1),place1(C1_0-1,C3_0),place1(C3_0,C2_0-1),right(C2_0-1,C4_0-1),place1(C4_0-1,C1_0),place1(C1_0,C2_0),right(C2_0,C6_0),place1(C6_0,C4_0),place1(C4_0,C7_0),place1(C7_0,B)
p409(A,B) :- place1(A,C),place1(C,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C3_0),place1(C3_0,C2_0-1),place1(C2_0-1,C4_0-1),place1(C4_0-1,C1_0),right(C1_0,C2_0),right(C2_0,C6_0),place1(C6_0,C4_0),place1(C4_0,C7_0),place1(C7_0,B)
p541(A,B) :- right(A,C),place1(C,C1_0-2),place1(C1_0-2,C1_0-1),place1(C1_0-1,C3_0),place1(C3_0,C2_0-1),right(C2_0-1,C4_0-1),place1(C4_0-1,C1_0),place1(C1_0,C2_0),right(C2_0,C6_0),place1(C6_0,C4_0),place1(C4_0,C7_0),place1(C7_0,B)
p471(A,B) :- place1(A,C),place1(C,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C3_0-1),place1(C3_0-1,C2_0-1),right(C2_0-1,C4_0-1),place1(C4_0-1,C1_0),place1(C1_0,C3_0),place1(C3_0,C2_0),right(C2_0,C7_0),place1(C7_0,C4_0),place1(C4_0,C8_0),place1(C8_0,B)
