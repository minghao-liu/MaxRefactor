p7(A,B) :- copy1(A,C),copy1(C,B)
p16(A,B) :- not_empty(A),mk_uppercase(A,B)
p27(A,B) :- copy1(A,C),mk_uppercase(C,B)
p38(A,B) :- not_empty(A),skip1(A,B)
p41(A,B) :- not_empty(A),copy1(A,B)
p57(A,B) :- skip1(A,C),mk_lowercase(C,B)
p62(A,B) :- mk_uppercase(A,C),copy1(C,B)
p73(A,B) :- mk_lowercase(A,C),mk_uppercase(C,B)
p81(A,B) :- skip1(A,C),copy1(C,B)
p114(A,B) :- skip1(A,C),mk_uppercase(C,B)
p134(A,B) :- not_empty(A),mk_lowercase(A,B)
p135(A,B) :- copy1(A,C),mk_lowercase(C,B)
p2(A,B) :- skip1(A,C),skip1(C,C1_0),copy1(C1_0,B)
p11(A,B) :- skip1(A,C),copy1(C,C1_0),copy1(C1_0,B)
p12(A,B) :- copy1(A,C),copy1(C,C1_0),mk_uppercase(C1_0,B)
p14(A,B) :- mk_uppercase(A,C),skip1(C,C1_0),copy1(C1_0,B)
p15(A,B) :- copy1(A,C),skip1(C,C1_0),mk_lowercase(C1_0,B)
p25(A,B) :- copy1(A,C),skip1(C,C1_0),copy1(C1_0,B)
p28(A,B) :- copy1(A,C),mk_uppercase(C,C1_0),copy1(C1_0,B)
p39(A,B) :- skip1(A,C),copy1(C,C1_0),mk_lowercase(C1_0,B)
p59(A,B) :- skip1(A,C),copy1(C,C1_0),mk_uppercase(C1_0,B)
p60(A,B) :- copy1(A,C),copy1(C,C1_0),copy1(C1_0,B)
p64(A,B) :- mk_lowercase(A,C),mk_lowercase(C,C1_0),copy1(C1_0,B)
p69(A,B) :- mk_lowercase(A,C0_0),mk_uppercase(C0_0,C),mk_uppercase(C,B)
p77(A,B) :- mk_lowercase(A,C),mk_lowercase(C,C1_0),mk_lowercase(C1_0,B)
p94(A,B) :- copy1(A,C),copy1(C,C1_0),mk_lowercase(C1_0,B)
p148(A,B) :- skip1(A,C),skip1(C,C1_0),mk_lowercase(C1_0,B)
p155(A,B) :- mk_lowercase(A,C),copy1(C,C1_0),copy1(C1_0,B)
p175(A,B) :- mk_uppercase(A,C),mk_uppercase(C,C1_0),mk_lowercase(C1_0,B)
p188(A,B) :- copy1(A,C0_0),mk_uppercase(C0_0,C),mk_lowercase(C,B)
p193(A,B) :- copy1(A,C0_0),mk_lowercase(C0_0,C),copy1(C,B)
p5(A,B) :- mk_lowercase(A,C),copy1(C,C1_0),mk_uppercase(C1_0,C2_0),copy1(C2_0,B)
p13(A,B) :- skip1(A,C),skip1(C,C1_0),copy1(C1_0,C2_0),copy1(C2_0,B)
p20(A,B) :- copy1(A,C),skip1(C,C1_0),skip1(C1_0,C2_0),mk_lowercase(C2_0,B)
p42(A,B) :- copy1(A,C),skip1(C,C1_0),copy1(C1_0,C2_0),copy1(C2_0,B)
p43(A,B) :- mk_uppercase(A,C0_0),copy1(C0_0,C),copy1(C,C1_0),copy1(C1_0,B)
p66(A,B) :- copy1(A,C),skip1(C,C1_0),copy1(C1_0,C2_0),mk_lowercase(C2_0,B)
p68(A,B) :- mk_lowercase(A,C),copy1(C,C1_0-1),mk_lowercase(C1_0-1,C1_0),copy1(C1_0,B)
p71(A,B) :- skip1(A,C),copy1(C,C1_0-1),mk_lowercase(C1_0-1,C1_0),mk_lowercase(C1_0,B)
p103(A,B) :- copy1(A,C),copy1(C,C1_0-1),mk_uppercase(C1_0-1,C1_0),mk_lowercase(C1_0,B)
p106(A,B) :- skip1(A,C0_0),mk_uppercase(C0_0,C),copy1(C,C1_0),copy1(C1_0,B)
p110(A,B) :- copy1(A,C),skip1(C,C1_0),skip1(C1_0,C2_0),mk_uppercase(C2_0,B)
p139(A,B) :- copy1(A,C0_0),copy1(C0_0,C),copy1(C,C1_0),mk_lowercase(C1_0,B)
p151(A,B) :- skip1(A,C0_0),copy1(C0_0,C),skip1(C,C1_0),copy1(C1_0,B)
p168(A,B) :- skip1(A,C),skip1(C,C1_0),skip1(C1_0,C2_0),mk_lowercase(C2_0,B)
p177(A,B) :- skip1(A,C0_0),mk_lowercase(C0_0,C),copy1(C,C1_0),copy1(C1_0,B)
p179(A,B) :- copy1(A,C0_0),copy1(C0_0,C),skip1(C,C1_0),mk_lowercase(C1_0,B)
p185(A,B) :- copy1(A,C),skip1(C,C1_0),skip1(C1_0,C2_0),copy1(C2_0,B)
p17(A,B) :- skip1(A,C0_0),copy1(C0_0,C),skip1(C,C1_0),mk_uppercase(C1_0,C3_0),copy1(C3_0,B)
p18(A,B) :- skip1(A,C),skip1(C,C1_0-1),copy1(C1_0-1,C1_0),skip1(C1_0,C2_0),copy1(C2_0,B)
p26(A,B) :- copy1(A,C0_0),copy1(C0_0,C),skip1(C,C1_0),copy1(C1_0,C3_0),copy1(C3_0,B)
p34(A,B) :- skip1(A,C),copy1(C,C1_0-1),copy1(C1_0-1,C1_0),skip1(C1_0,C2_0),copy1(C2_0,B)
p45(A,B) :- skip1(A,C0_0),mk_uppercase(C0_0,C),skip1(C,C2_0),mk_lowercase(C2_0,C1_0),mk_lowercase(C1_0,B)
p65(A,B) :- skip1(A,C),copy1(C,C1_0-1),mk_uppercase(C1_0-1,C1_0),copy1(C1_0,C2_0),copy1(C2_0,B)
p93(A,B) :- skip1(A,C0_0),mk_uppercase(C0_0,C),skip1(C,C1_0),copy1(C1_0,C3_0),mk_uppercase(C3_0,B)
p102(A,B) :- skip1(A,C),copy1(C,C1_0-1),copy1(C1_0-1,C1_0),skip1(C1_0,C2_0),mk_uppercase(C2_0,B)
p112(A,B) :- mk_uppercase(A,C0_0),copy1(C0_0,C),skip1(C,C1_0),skip1(C1_0,C3_0),copy1(C3_0,B)
p113(A,B) :- skip1(A,C),skip1(C,C1_0-1),copy1(C1_0-1,C1_0),copy1(C1_0,C2_0),copy1(C2_0,B)
p117(A,B) :- skip1(A,C),skip1(C,C1_0-1),copy1(C1_0-1,C1_0),copy1(C1_0,C2_0),mk_uppercase(C2_0,B)
p132(A,B) :- copy1(A,C),skip1(C,C1_0-1),copy1(C1_0-1,C1_0),skip1(C1_0,C2_0),copy1(C2_0,B)
p138(A,B) :- skip1(A,C0_0),copy1(C0_0,C),skip1(C,C1_0),skip1(C1_0,C3_0),mk_uppercase(C3_0,B)
p149(A,B) :- skip1(A,C),mk_lowercase(C,C1_0-1),mk_uppercase(C1_0-1,C1_0),mk_uppercase(C1_0,C2_0),copy1(C2_0,B)
p173(A,B) :- skip1(A,C),skip1(C,C1_0-1),mk_uppercase(C1_0-1,C1_0),copy1(C1_0,C2_0),copy1(C2_0,B)
p184(A,B) :- copy1(A,C0_0),mk_lowercase(C0_0,C),copy1(C,C1_0),copy1(C1_0,C3_0),copy1(C3_0,B)
p116(A,B) :- skip1(A,C0_0),mk_lowercase(C0_0,C),p157(C,C1_0),mk_lowercase(C1_0,C3_0),mk_uppercase(C3_0,B)
p170(A,B) :- mk_lowercase(A,C),copy1(C,C1_0),skip1(C1_0,C2_0),copy1(C2_0,C3_0),copy1(C3_0,B)
p49(A,B) :- copy1(A,C0_0),mk_lowercase(C0_0,C),skip1(C,C2_0),mk_uppercase(C2_0,C1_0),copy1(C1_0,C3_0),copy1(C3_0,B)
p78(A,B) :- skip1(A,C0_0),mk_lowercase(C0_0,C),skip1(C,C2_0),copy1(C2_0,C1_0),copy1(C1_0,C3_0),mk_lowercase(C3_0,B)
p121(A,B) :- skip1(A,C0_0),copy1(C0_0,C),skip1(C,C2_0),copy1(C2_0,C1_0),copy1(C1_0,C3_0),copy1(C3_0,B)
p123(A,B) :- copy1(A,C0_0),copy1(C0_0,C),copy1(C,C2_0),copy1(C2_0,C1_0),copy1(C1_0,C3_0),mk_uppercase(C3_0,B)
p164(A,B) :- skip1(A,C0_0),skip1(C0_0,C1_0-1),copy1(C1_0-1,C),skip1(C,C1_0),skip1(C1_0,C3_0),copy1(C3_0,B)
p180(A,B) :- skip1(A,C0_0),mk_uppercase(C0_0,C),skip1(C,C2_0),copy1(C2_0,C1_0),skip1(C1_0,C3_0),copy1(C3_0,B)
p189(A,B) :- copy1(A,C0_0),copy1(C0_0,C),mk_uppercase(C,C2_0),copy1(C2_0,C1_0),copy1(C1_0,C3_0),copy1(C3_0,B)
p3(A,B) :- copy1(A,C0_0),copy1(C0_0,C1_0-1),mk_uppercase(C1_0-1,C),skip1(C,C1_0),copy1(C1_0,C3_0),copy1(C3_0,B)
p33(A,B) :- skip1(A,C0_0),mk_uppercase(C0_0,C),skip1(C,C2_0),skip1(C2_0,C3_0),mk_lowercase(C3_0,C1_0),copy1(C1_0,B)
p72(A,B) :- mk_lowercase(A,C0_0),copy1(C0_0,C),skip1(C,C2_0),copy1(C2_0,C1_0),copy1(C1_0,C3_0),mk_lowercase(C3_0,B)
p88(A,B) :- skip1(A,C),copy1(C,C1_0-1),skip1(C1_0-1,C2_0),skip1(C2_0,C3_0),copy1(C3_0,C1_0),mk_lowercase(C1_0,B)
p101(A,B) :- copy1(A,C),skip1(C,C1_0),copy1(C1_0,C2_0-1),mk_uppercase(C2_0-1,C2_0),copy1(C2_0,C3_0),copy1(C3_0,B)
p104(A,B) :- skip1(A,C0_0),skip1(C0_0,C1_0-1),skip1(C1_0-1,C2_0),mk_lowercase(C2_0,C),copy1(C,C1_0),mk_lowercase(C1_0,B)
p1(A,B) :- copy1(A,C0_0),mk_uppercase(C0_0,C),skip1(C,C2_0),mk_uppercase(C2_0,C1_0),copy1(C1_0,C3_0),skip1(C3_0,C5_0),copy1(C5_0,C6_0),copy1(C6_0,B)
p36(A,B) :- skip1(A,C0_0-1),copy1(C0_0-1,C0_0),skip1(C0_0,C1_0-1),copy1(C1_0-1,C),skip1(C,C1_0),skip1(C1_0,C3_0),copy1(C3_0,C6_0),copy1(C6_0,B)
p54(A,B) :- copy1(A,C0_0),skip1(C0_0,C1_0-2),copy1(C1_0-2,C1_0-1),copy1(C1_0-1,C2_0),copy1(C2_0,C),copy1(C,C1_0),copy1(C1_0,C3_0),copy1(C3_0,B)
p63(A,B) :- skip1(A,C0_0),skip1(C0_0,C1_0-1),copy1(C1_0-1,C2_0-1),copy1(C2_0-1,C),skip1(C,C2_0),copy1(C2_0,C1_0),copy1(C1_0,C3_0),mk_uppercase(C3_0,B)
p84(A,B) :- skip1(A,C),copy1(C,C1_0-1),skip1(C1_0-1,C2_0-1),copy1(C2_0-1,C3_0),mk_lowercase(C3_0,C1_0),skip1(C1_0,C2_0),copy1(C2_0,C4_0),copy1(C4_0,B)
p158(A,B) :- copy1(A,C0_0),copy1(C0_0,C1_0-1),copy1(C1_0-1,C),skip1(C,C1_0),skip1(C1_0,C4_0),copy1(C4_0,C3_0),copy1(C3_0,C5_0),copy1(C5_0,B)
p169(A,B) :- skip1(A,C0_0),skip1(C0_0,C1_0-1),copy1(C1_0-1,C),skip1(C,C1_0),mk_lowercase(C1_0,C3_0),copy1(C3_0,C5_0-1),mk_lowercase(C5_0-1,C5_0),copy1(C5_0,B)
p171(A,B) :- skip1(A,C),skip1(C,C1_0-1),skip1(C1_0-1,C2_0-1),mk_uppercase(C2_0-1,C1_0),copy1(C1_0,C2_0),skip1(C2_0,C4_0),copy1(C4_0,C6_0),copy1(C6_0,B)
p172(A,B) :- mk_uppercase(A,C),copy1(C,C1_0-1),skip1(C1_0-1,C2_0-1),copy1(C2_0-1,C1_0),copy1(C1_0,C3_0),copy1(C3_0,C2_0),copy1(C2_0,C4_0),mk_lowercase(C4_0,B)
p182(A,B) :- mk_uppercase(A,C),copy1(C,C1_0-1),copy1(C1_0-1,C1_0),skip1(C1_0,C2_0),skip1(C2_0,C4_0),skip1(C4_0,C5_0),copy1(C5_0,C6_0),copy1(C6_0,B)
p6(A,B) :- copy1(A,C),copy1(C,C1_0-1),skip1(C1_0-1,C2_0-2),copy1(C2_0-2,C2_0-1),copy1(C2_0-1,C3_0),copy1(C3_0,C1_0),skip1(C1_0,C2_0),skip1(C2_0,C4_0),copy1(C4_0,C6_0),copy1(C6_0,B)
p19(A,B) :- copy1(A,C0_0),copy1(C0_0,C),copy1(C,C2_0-1),copy1(C2_0-1,C2_0),skip1(C2_0,C3_0-1),copy1(C3_0-1,C5_0-1),copy1(C5_0-1,C1_0),copy1(C1_0,C3_0),skip1(C3_0,C5_0),copy1(C5_0,B)
p23(A,B) :- copy1(A,C0_0),skip1(C0_0,C1_0-1),copy1(C1_0-1,C2_0-1),copy1(C2_0-1,C),copy1(C,C2_0),skip1(C2_0,C4_0),skip1(C4_0,C6_0),mk_uppercase(C6_0,C1_0),copy1(C1_0,C3_0),mk_uppercase(C3_0,B)
p53(A,B) :- skip1(A,C0_0),copy1(C0_0,C),skip1(C,C2_0-1),copy1(C2_0-1,C2_0),skip1(C2_0,C4_0),copy1(C4_0,C3_0-1),copy1(C3_0-1,C5_0),copy1(C5_0,C1_0),copy1(C1_0,C3_0),copy1(C3_0,B)
p83(A,B) :- skip1(A,C),skip1(C,C1_0-2),copy1(C1_0-2,C1_0-1),skip1(C1_0-1,C3_0),copy1(C3_0,C2_0-1),copy1(C2_0-1,C4_0-1),copy1(C4_0-1,C1_0),copy1(C1_0,C2_0),copy1(C2_0,C4_0),copy1(C4_0,B)
p130(A,B) :- skip1(A,C0_0),copy1(C0_0,C1_0-1),copy1(C1_0-1,C),skip1(C,C2_0),skip1(C2_0,C4_0),copy1(C4_0,C5_0),copy1(C5_0,C1_0),skip1(C1_0,C3_0),mk_uppercase(C3_0,C6_0),copy1(C6_0,B)
p141(A,B) :- mk_uppercase(A,C),skip1(C,C1_0-2),mk_lowercase(C1_0-2,C1_0-1),copy1(C1_0-1,C2_0-1),copy1(C2_0-1,C1_0),mk_lowercase(C1_0,C3_0),copy1(C3_0,C2_0),copy1(C2_0,C4_0),copy1(C4_0,C8_0),copy1(C8_0,B)
p56(A,B) :- copy1(A,C0_0),mk_uppercase(C0_0,C),skip1(C,C2_0),mk_uppercase(C2_0,C1_0),copy1(C1_0,C4_0),mk_uppercase(C4_0,C3_0),skip1(C3_0,C5_0),skip1(C5_0,C7_0),copy1(C7_0,C8_0),copy1(C8_0,B)
p9(A,B) :- copy1(A,C),skip1(C,C1_0),skip1(C1_0,C2_0),skip1(C2_0,C3_0-1),copy1(C3_0-1,C3_0),skip1(C3_0,C4_0),copy1(C4_0,B)
p29(A,B) :- skip1(A,C0_0),copy1(C0_0,C1_0-2),mk_lowercase(C1_0-2,C1_0-1),mk_lowercase(C1_0-1,C),mk_uppercase(C,C1_0),skip1(C1_0,C3_0),copy1(C3_0,B)
p37(A,B) :- skip1(A,C),skip1(C,C1_0-1),copy1(C1_0-1,C1_0),skip1(C1_0,C3_0),copy1(C3_0,C2_0),copy1(C2_0,C4_0),copy1(C4_0,B)
p44(A,B) :- skip1(A,C0_0),skip1(C0_0,C1_0-1),skip1(C1_0-1,C2_0-1),mk_lowercase(C2_0-1,C),skip1(C,C2_0),mk_lowercase(C2_0,C1_0),mk_lowercase(C1_0,B)
p52(A,B) :- copy1(A,C0_0),copy1(C0_0,C1_0-1),copy1(C1_0-1,C),copy1(C,C2_0),mk_uppercase(C2_0,C1_0),copy1(C1_0,C3_0),copy1(C3_0,B)
p61(A,B) :- copy1(A,C0_0),skip1(C0_0,C1_0-1),skip1(C1_0-1,C2_0),copy1(C2_0,C),skip1(C,C1_0),mk_uppercase(C1_0,C3_0),copy1(C3_0,B)
p70(A,B) :- copy1(A,C0_0),skip1(C0_0,C1_0-1),copy1(C1_0-1,C),skip1(C,C2_0),copy1(C2_0,C1_0),skip1(C1_0,C3_0),copy1(C3_0,B)
p74(A,B) :- copy1(A,C),copy1(C,C1_0-1),copy1(C1_0-1,C2_0-1),copy1(C2_0-1,C1_0),copy1(C1_0,C2_0),copy1(C2_0,C4_0),copy1(C4_0,B)
p80(A,B) :- copy1(A,C0_0),skip1(C0_0,C1_0-1),copy1(C1_0-1,C),copy1(C,C1_0),skip1(C1_0,C3_0),copy1(C3_0,C5_0),mk_lowercase(C5_0,B)
p87(A,B) :- skip1(A,C),copy1(C,C1_0-2),copy1(C1_0-2,C1_0-1),copy1(C1_0-1,C2_0-1),mk_lowercase(C2_0-1,C1_0),mk_uppercase(C1_0,C2_0),copy1(C2_0,B)
p100(A,B) :- copy1(A,C0_0),skip1(C0_0,C1_0-1),mk_lowercase(C1_0-1,C),copy1(C,C2_0),copy1(C2_0,C1_0),copy1(C1_0,C3_0),mk_lowercase(C3_0,B)
p120(A,B) :- skip1(A,C),skip1(C,C1_0-1),copy1(C1_0-1,C2_0-1),mk_lowercase(C2_0-1,C1_0),mk_uppercase(C1_0,C2_0),mk_uppercase(C2_0,C4_0),mk_lowercase(C4_0,B)
p126(A,B) :- mk_uppercase(A,C),skip1(C,C1_0-1),mk_lowercase(C1_0-1,C1_0),skip1(C1_0,C3_0),copy1(C3_0,C2_0),skip1(C2_0,C4_0),copy1(C4_0,B)
p145(A,B) :- copy1(A,C0_0),copy1(C0_0,C1_0-1),copy1(C1_0-1,C),copy1(C,C2_0),copy1(C2_0,C1_0),skip1(C1_0,C3_0),copy1(C3_0,B)
p156(A,B) :- skip1(A,C0_0),copy1(C0_0,C1_0-2),copy1(C1_0-2,C1_0-1),skip1(C1_0-1,C2_0),mk_uppercase(C2_0,C),mk_lowercase(C,C1_0),mk_uppercase(C1_0,B)
p162(A,B) :- skip1(A,C),skip1(C,C1_0),skip1(C1_0,C2_0),skip1(C2_0,C3_0-1),copy1(C3_0-1,C3_0),copy1(C3_0,C4_0),copy1(C4_0,B)
p186(A,B) :- skip1(A,C0_0),copy1(C0_0,C),copy1(C,C2_0-1),copy1(C2_0-1,C2_0),copy1(C2_0,C3_0),mk_uppercase(C3_0,C1_0),mk_uppercase(C1_0,B)
p190(A,B) :- skip1(A,C0_0),skip1(C0_0,C1_0-1),copy1(C1_0-1,C),skip1(C,C2_0),copy1(C2_0,C1_0),copy1(C1_0,C3_0),mk_lowercase(C3_0,B)
p198(A,B) :- mk_uppercase(A,C),copy1(C,C1_0-1),mk_lowercase(C1_0-1,C1_0),skip1(C1_0,C3_0),mk_uppercase(C3_0,C2_0),skip1(C2_0,C4_0),mk_uppercase(C4_0,B)
p199(A,B) :- copy1(A,C0_0),mk_uppercase(C0_0,C),copy1(C,C2_0),copy1(C2_0,C1_0),skip1(C1_0,C3_0),copy1(C3_0,C5_0),copy1(C5_0,B)
p21(A,B) :- mk_lowercase(A,C0_0),copy1(C0_0,C),copy1(C,C2_0),skip1(C2_0,C3_0-1),copy1(C3_0-1,C4_0),mk_lowercase(C4_0,C1_0),skip1(C1_0,C3_0),copy1(C3_0,C5_0),mk_uppercase(C5_0,B)
p31(A,B) :- copy1(A,C0_0-1),copy1(C0_0-1,C0_0),skip1(C0_0,C1_0-1),mk_uppercase(C1_0-1,C),copy1(C,C2_0),skip1(C2_0,C5_0),copy1(C5_0,C1_0),skip1(C1_0,C3_0),mk_lowercase(C3_0,B)
p32(A,B) :- copy1(A,C0_0),skip1(C0_0,C1_0-1),copy1(C1_0-1,C2_0),mk_lowercase(C2_0,C),skip1(C,C1_0),skip1(C1_0,C4_0),copy1(C4_0,C3_0),copy1(C3_0,C5_0),copy1(C5_0,B)
p35(A,B) :- skip1(A,C),copy1(C,C1_0-1),skip1(C1_0-1,C2_0-1),mk_lowercase(C2_0-1,C1_0),copy1(C1_0,C3_0),mk_lowercase(C3_0,C2_0),copy1(C2_0,C4_0),copy1(C4_0,C7_0),copy1(C7_0,B)
p48(A,B) :- copy1(A,C0_0),copy1(C0_0,C),skip1(C,C2_0-1),mk_lowercase(C2_0-1,C2_0),copy1(C2_0,C3_0-1),copy1(C3_0-1,C1_0),copy1(C1_0,C3_0),copy1(C3_0,C5_0),copy1(C5_0,B)
p58(A,B) :- skip1(A,C),copy1(C,C1_0-1),skip1(C1_0-1,C2_0-1),skip1(C2_0-1,C3_0-1),copy1(C3_0-1,C1_0),copy1(C1_0,C3_0),copy1(C3_0,C2_0),skip1(C2_0,C4_0),copy1(C4_0,B)
p67(A,B) :- copy1(A,C0_0),copy1(C0_0,C1_0-1),copy1(C1_0-1,C),copy1(C,C2_0),copy1(C2_0,C4_0),copy1(C4_0,C1_0),copy1(C1_0,C3_0),copy1(C3_0,C6_0),copy1(C6_0,B)
p76(A,B) :- copy1(A,C0_0),copy1(C0_0,C1_0-1),mk_uppercase(C1_0-1,C),copy1(C,C3_0-1),copy1(C3_0-1,C2_0),skip1(C2_0,C4_0),mk_lowercase(C4_0,C1_0),skip1(C1_0,C3_0),copy1(C3_0,B)
p97(A,B) :- skip1(A,C0_0),copy1(C0_0,C1_0-1),mk_lowercase(C1_0-1,C),mk_uppercase(C,C2_0),mk_uppercase(C2_0,C4_0),mk_lowercase(C4_0,C1_0),copy1(C1_0,C3_0),copy1(C3_0,C6_0),copy1(C6_0,B)
p99(A,B) :- copy1(A,C0_0),mk_uppercase(C0_0,C1_0-1),copy1(C1_0-1,C),copy1(C,C3_0-1),copy1(C3_0-1,C2_0),skip1(C2_0,C4_0),mk_uppercase(C4_0,C1_0),skip1(C1_0,C3_0),copy1(C3_0,B)
p111(A,B) :- copy1(A,C0_0),mk_lowercase(C0_0,C),skip1(C,C2_0),copy1(C2_0,C1_0),skip1(C1_0,C4_0),copy1(C4_0,C3_0),skip1(C3_0,C5_0),skip1(C5_0,C7_0),mk_uppercase(C7_0,B)
p122(A,B) :- copy1(A,C0_0-1),copy1(C0_0-1,C0_0),skip1(C0_0,C1_0-1),copy1(C1_0-1,C),skip1(C,C1_0),skip1(C1_0,C5_0),copy1(C5_0,C3_0),skip1(C3_0,C6_0),copy1(C6_0,B)
p128(A,B) :- mk_uppercase(A,C0_0-1),copy1(C0_0-1,C0_0),copy1(C0_0,C1_0-1),copy1(C1_0-1,C),copy1(C,C1_0),skip1(C1_0,C5_0),copy1(C5_0,C3_0),skip1(C3_0,C6_0),copy1(C6_0,B)
p167(A,B) :- copy1(A,C0_0),copy1(C0_0,C),copy1(C,C2_0),copy1(C2_0,C3_0-1),copy1(C3_0-1,C1_0),skip1(C1_0,C3_0),skip1(C3_0,C5_0),copy1(C5_0,C7_0),copy1(C7_0,B)
p174(A,B) :- skip1(A,C),copy1(C,C1_0-1),skip1(C1_0-1,C2_0-1),copy1(C2_0-1,C3_0-1),mk_lowercase(C3_0-1,C1_0),skip1(C1_0,C3_0),copy1(C3_0,C2_0),copy1(C2_0,C4_0),copy1(C4_0,B)
p187(A,B) :- copy1(A,C0_0),skip1(C0_0,C1_0-2),copy1(C1_0-2,C1_0-1),skip1(C1_0-1,C2_0-1),copy1(C2_0-1,C),copy1(C,C2_0),skip1(C2_0,C4_0),mk_lowercase(C4_0,C1_0),copy1(C1_0,B)
p194(A,B) :- mk_uppercase(A,C0_0),copy1(C0_0,C),copy1(C,C2_0),copy1(C2_0,C3_0-1),copy1(C3_0-1,C1_0),copy1(C1_0,C3_0),skip1(C3_0,C5_0),skip1(C5_0,C7_0),mk_uppercase(C7_0,B)
p24(A,B) :- skip1(A,C),skip1(C,C1_0-1),skip1(C1_0-1,C2_0-1),skip1(C2_0-1,C3_0),copy1(C3_0,C4_0-1),copy1(C4_0-1,C1_0),skip1(C1_0,C2_0),copy1(C2_0,C4_0),mk_lowercase(C4_0,B)
p107(A,B) :- skip1(A,C0_0),mk_uppercase(C0_0,C),mk_lowercase(C,C1_0),mk_uppercase(C1_0,B)
p107(A,B) :- skip1(A,C0_0),copy1(C0_0,C),p107(C,B)
p157(A,B) :- not_empty(A),mk_lowercase(A,C1_0),mk_uppercase(C1_0,B)
p157(A,B) :- skip1(A,C),p157(C,B)
p159(A,B) :- not_empty(A),mk_uppercase(A,C1_0),copy1(C1_0,B)
p159(A,B) :- skip1(A,C0_0),copy1(C0_0,C),p159(C,B)
