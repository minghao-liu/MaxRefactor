p2(A,B) :- right(A,C),place1(C,B)
p12(A,B) :- place1(A,C),place1(C,B)
p1(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,B)
p5(A,B) :- place1(A,C),right(C,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p10(A,B) :- right(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,B)
p66(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p91(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C1_0),place1(C1_0,B)
p1829(A,B) :- right(A,C),right(C,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p3(A,B) :- right(A,C),place1(C,C1_0),place1(C1_0,B)
p29(A,B) :- place1(A,C),right(C,C1_0),place1(C1_0,B)
p43(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,B)
p89(A,B) :- place1(A,C),place1(C,C1_0),place1(C1_0,B)
p15(A,B) :- place1(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p116(A,B) :- right(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p142(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p319(A,B) :- right(A,C),place1(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p446(A,B) :- right(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p1098(A,B) :- place1(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p1766(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p73(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p94(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p659(A,B) :- right(A,C0_0),place1(C0_0,C),right(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p0(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,C4_0),place1(C4_0,B)
p84(A,B) :- right(A,C),place1(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),right(C2_0,C4_0),place1(C4_0,B)
p202(A,B) :- right(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),place1(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p292(A,B) :- place1(A,C),right(C,C1_0),right(C1_0,C2_0-1),place1(C2_0-1,C2_0),right(C2_0,C3_0),place1(C3_0,B)
p4(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C2_0),place1(C2_0,C),place1(C,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p9(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),place1(C0_0,C2_0),place1(C2_0,C1_0-1),right(C1_0-1,C3_0-1),place1(C3_0-1,C),place1(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p208(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C2_0),place1(C2_0,C),right(C,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p766(A,B) :- right(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C2_0-1),place1(C2_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p19(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),right(C3_0,C5_0),place1(C5_0,B)
p32(A,B) :- right(A,C),place1(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C3_0),place1(C3_0,C2_0),right(C2_0,C4_0),place1(C4_0,B)
p59(A,B) :- place1(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),place1(C1_0,C3_0),place1(C3_0,C2_0),right(C2_0,C4_0),place1(C4_0,B)
p102(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0-1),place1(C3_0-1,C3_0),place1(C3_0,C4_0),place1(C4_0,B)
p1364(A,B) :- place1(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C3_0),place1(C3_0,C2_0),right(C2_0,C4_0),place1(C4_0,B)
p1599(A,B) :- right(A,C0_0),right(C0_0,C1_0-1),right(C1_0-1,C2_0),place1(C2_0,C),place1(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p21(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),place1(C,C1_0),right(C1_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p75(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p81(A,B) :- right(A,C0_0),right(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0),place1(C2_0,C),place1(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p144(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p22(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C2_0),place1(C2_0,C1_0),place1(C1_0,C6_0),place1(C6_0,C3_0),right(C3_0,C7_0),place1(C7_0,B)
p28(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C2_0),place1(C2_0,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p48(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C6_0),place1(C6_0,C3_0),right(C3_0,C7_0),place1(C7_0,B)
p83(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),place1(C0_0,C2_0-1),place1(C2_0-1,C1_0-1),right(C1_0-1,C3_0-1),place1(C3_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C6_0),place1(C6_0,C3_0),place1(C3_0,C7_0),place1(C7_0,B)
p86(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C2_0-1),place1(C2_0-1,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),right(C,C2_0),place1(C2_0,C1_0),right(C1_0,C6_0),place1(C6_0,C3_0),place1(C3_0,C7_0),place1(C7_0,B)
p103(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C6_0),place1(C6_0,C3_0),place1(C3_0,C7_0),place1(C7_0,B)
p416(A,B) :- right(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0-1),place1(C2_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C5_0),place1(C5_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p892(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),place1(C0_0,C2_0-1),place1(C2_0-1,C1_0-1),right(C1_0-1,C3_0-1),place1(C3_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),right(C3_0,C7_0),place1(C7_0,B)
