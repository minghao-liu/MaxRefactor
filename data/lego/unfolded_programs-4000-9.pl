p2(A,B) :- place1(A,C),place1(C,B)
p11(A,B) :- right(A,C),place1(C,B)
p3(A,B) :- right(A,C),place1(C,C1_0),place1(C1_0,B)
p26(A,B) :- place1(A,C),right(C,C1_0),place1(C1_0,B)
p245(A,B) :- place1(A,C),place1(C,C1_0),place1(C1_0,B)
p262(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,B)
p10(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,B)
p72(A,B) :- right(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,B)
p342(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C1_0),place1(C1_0,B)
p376(A,B) :- place1(A,C0_0),place1(C0_0,C),place1(C,C1_0),place1(C1_0,B)
p3594(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p3694(A,B) :- place1(A,C),right(C,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p2810(A,B) :- right(A,C),right(C,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p822(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,C3_0),place1(C3_0,B)
p1018(A,B) :- right(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p1036(A,B) :- place1(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p1248(A,B) :- right(A,C),place1(C,C1_0-1),place1(C1_0-1,C1_0),place1(C1_0,C2_0),place1(C2_0,B)
p3901(A,B) :- right(A,C),place1(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p140(A,B) :- place1(A,C),right(C,C1_0),right(C1_0,C2_0),place1(C2_0,C3_0),place1(C3_0,B)
p972(A,B) :- right(A,C),right(C,C1_0-1),place1(C1_0-1,C1_0),right(C1_0,C2_0),place1(C2_0,B)
p1(A,B) :- place1(A,C),place1(C,C1_0),right(C1_0,C2_0-1),place1(C2_0-1,C2_0),right(C2_0,C3_0),place1(C3_0,B)
p35(A,B) :- right(A,C),place1(C,C1_0),place1(C1_0,C2_0-1),place1(C2_0-1,C2_0),right(C2_0,C3_0),place1(C3_0,B)
p37(A,B) :- right(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,C4_0),place1(C4_0,B)
p51(A,B) :- place1(A,C),right(C,C1_0),right(C1_0,C2_0-1),place1(C2_0-1,C2_0),place1(C2_0,C3_0),place1(C3_0,B)
p440(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),right(C1_0-1,C2_0),place1(C2_0,C),right(C,C1_0),place1(C1_0,B)
p1253(A,B) :- right(A,C),right(C,C1_0),place1(C1_0,C2_0-1),place1(C2_0-1,C2_0),place1(C2_0,C3_0),place1(C3_0,B)
p2686(A,B) :- right(A,C),place1(C,C1_0),right(C1_0,C2_0-1),place1(C2_0-1,C2_0),right(C2_0,C3_0),place1(C3_0,B)
p4(A,B) :- place1(A,C0_0),place1(C0_0,C),right(C,C1_0),place1(C1_0,C3_0-1),place1(C3_0-1,C3_0),place1(C3_0,C4_0),place1(C4_0,B)
p16(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p17(A,B) :- right(A,C0_0),place1(C0_0,C),place1(C,C1_0),right(C1_0,C3_0-1),place1(C3_0-1,C3_0),place1(C3_0,C4_0),place1(C4_0,B)
p769(A,B) :- right(A,C0_0),place1(C0_0,C),right(C,C1_0),right(C1_0,C3_0-1),place1(C3_0-1,C3_0),place1(C3_0,C4_0),place1(C4_0,B)
p1548(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,B)
p8(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p12(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),place1(C,C2_0),place1(C2_0,C1_0),right(C1_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p102(A,B) :- right(A,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),place1(C,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),right(C3_0,C5_0),place1(C5_0,B)
p130(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),right(C1_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p22(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),place1(C1_0,C5_0),place1(C5_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p119(A,B) :- right(A,C0_0),right(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),place1(C1_0-1,C2_0),place1(C2_0,C),place1(C,C1_0),right(C1_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p543(A,B) :- right(A,C0_0-1),place1(C0_0-1,C0_0),place1(C0_0,C1_0-1),place1(C1_0-1,C),right(C,C1_0),place1(C1_0,C5_0),place1(C5_0,C3_0),right(C3_0,C6_0),place1(C6_0,B)
p803(A,B) :- place1(A,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C2_0),place1(C2_0,C),right(C,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p28(A,B) :- place1(A,C0_0-1),place1(C0_0-1,C0_0),right(C0_0,C1_0-1),place1(C1_0-1,C3_0-1),place1(C3_0-1,C),place1(C,C1_0),right(C1_0,C5_0),place1(C5_0,C3_0),place1(C3_0,C6_0),place1(C6_0,B)
p60(A,B) :- place1(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0),place1(C2_0,C),right(C,C1_0),right(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p340(A,B) :- right(A,C0_0),right(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),place1(C1_0-1,C2_0),place1(C2_0,C),right(C,C1_0),place1(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
p367(A,B) :- right(A,C0_0),place1(C0_0,C1_0-2),place1(C1_0-2,C1_0-1),right(C1_0-1,C2_0),place1(C2_0,C),right(C,C1_0),place1(C1_0,C4_0),place1(C4_0,C3_0),place1(C3_0,C5_0),place1(C5_0,B)
