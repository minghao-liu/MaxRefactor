verbgroup(A,B):- hypernym(A,E),haspart(B,F),synsetdomaintopicof(A,D),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(C,D),memberofdomainusage(A,D),derivationallyrelatedform(D,B).
verbgroup(A,B):- haspart(B,F),derivationallyrelatedform(A,D),alsosee(F,C),instancehypernym(E,F).
verbgroup(A,B):- memberofdomainregion(D,B),alsosee(F,E),alsosee(F,C),memberofdomainregion(C,A).
verbgroup(A,B):- instancehypernym(C,D),memberofdomainusage(D,B),hypernym(C,A),similarto(B,C).
verbgroup(A,B):- haspart(A,E),alsosee(F,C),alsosee(B,C),memberofdomainusage(D,A).
verbgroup(A,B):- alsosee(A,B),membermeronym(D,C),haspart(A,D).
verbgroup(A,B):- synsetdomaintopicof(F,D),alsosee(F,C),instancehypernym(A,E),membermeronym(B,D).
verbgroup(A,B):- instancehypernym(D,B),instancehypernym(A,E),instancehypernym(A,C).
verbgroup(A,B):- membermeronym(D,B),similarto(B,C),hypernym(A,D),hypernym(C,B).
verbgroup(A,B):- hypernym(D,A),hypernym(D,B),similarto(B,C),derivationallyrelatedform(A,C).
verbgroup(A,B):- similarto(A,D),synsetdomaintopicof(E,D),similarto(B,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- instancehypernym(D,A),derivationallyrelatedform(A,D),haspart(D,C),similarto(B,C).
verbgroup(A,B):- membermeronym(B,A),similarto(B,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- similarto(A,D),memberofdomainusage(E,C),membermeronym(B,E).
verbgroup(A,B):- similarto(C,D),hypernym(B,C),haspart(D,A).
verbgroup(A,B):- memberofdomainusage(A,E),alsosee(F,C),membermeronym(E,C),alsosee(B,D).
verbgroup(A,B):- hypernym(C,F),hypernym(D,F),membermeronym(A,E),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(A,E),similarto(B,C),haspart(A,D),alsosee(D,A).
verbgroup(A,B):- membermeronym(A,D),hypernym(D,A),similarto(B,C),memberofdomainregion(C,E).
verbgroup(A,B):- synsetdomaintopicof(A,C),hypernym(A,E),membermeronym(D,C),similarto(B,C).
verbgroup(A,B):- similarto(A,F),instancehypernym(E,B),instancehypernym(D,F),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(D,A),memberofdomainusage(C,A),alsosee(B,D).
verbgroup(A,B):- memberofdomainusage(A,D),similarto(E,A),memberofdomainusage(F,A),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(F,E),hypernym(E,D),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- hypernym(B,C),memberofdomainusage(A,D),hypernym(D,E).
verbgroup(A,B):- haspart(A,E),memberofdomainregion(E,D),similarto(B,C),instancehypernym(B,F).
verbgroup(A,B):- alsosee(F,C),alsosee(F,E),memberofdomainregion(B,E),synsetdomaintopicof(D,A).
verbgroup(A,B):- derivationallyrelatedform(A,D),memberofdomainregion(B,A),similarto(B,C),hypernym(E,C).
verbgroup(A,B):- hypernym(E,B),alsosee(F,C),derivationallyrelatedform(A,D),memberofdomainregion(A,F).
verbgroup(A,B):- similarto(A,D),hypernym(E,B),alsosee(F,C),derivationallyrelatedform(E,C).
verbgroup(A,B):- memberofdomainregion(A,B),synsetdomaintopicof(A,D),similarto(B,C),hypernym(C,E).
verbgroup(A,B):- alsosee(D,E),similarto(A,D),alsosee(F,B),similarto(B,C).
verbgroup(A,B):- alsosee(C,B),haspart(D,A),similarto(B,C),hypernym(D,C).
verbgroup(A,B):- alsosee(A,D),alsosee(F,C),instancehypernym(A,E),synsetdomaintopicof(C,B).
verbgroup(A,B):- memberofdomainusage(B,A),similarto(B,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- similarto(E,D),memberofdomainusage(A,D),similarto(B,C),alsosee(A,F).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(F,A),synsetdomaintopicof(B,D),similarto(E,F).
verbgroup(A,B):- alsosee(C,A),haspart(A,B),similarto(A,B).
verbgroup(A,B):- memberofdomainusage(B,C),similarto(D,B),hypernym(E,A).
verbgroup(A,B):- haspart(D,B),alsosee(E,B),derivationallyrelatedform(E,A),similarto(B,C).
verbgroup(A,B):- similarto(B,C),memberofdomainusage(B,E),synsetdomaintopicof(B,A),hypernym(A,D).
verbgroup(A,B):- hypernym(C,F),hypernym(D,A),alsosee(A,E),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(A,D),haspart(D,A),similarto(B,C),memberofdomainusage(E,A).
verbgroup(A,B):- derivationallyrelatedform(D,A),alsosee(F,E),alsosee(F,C),derivationallyrelatedform(E,B).
verbgroup(A,B):- alsosee(F,C),memberofdomainusage(A,F),synsetdomaintopicof(E,D),derivationallyrelatedform(E,B).
verbgroup(A,B):- haspart(D,B),haspart(A,C),alsosee(E,D).
verbgroup(A,B):- memberofdomainregion(F,A),alsosee(F,C),synsetdomaintopicof(F,E),synsetdomaintopicof(D,B).
verbgroup(A,B):- instancehypernym(F,D),alsosee(B,E),alsosee(F,C),hypernym(A,C).
verbgroup(A,B):- alsosee(F,C),alsosee(D,F),instancehypernym(B,E),memberofdomainregion(A,C).
verbgroup(A,B):- membermeronym(E,A),haspart(A,D),similarto(B,C),synsetdomaintopicof(E,F).
verbgroup(A,B):- hypernym(A,E),similarto(B,D),synsetdomaintopicof(C,E).
verbgroup(A,B):- alsosee(A,D),instancehypernym(B,D),alsosee(C,D).
verbgroup(A,B):- haspart(D,B),derivationallyrelatedform(E,B),synsetdomaintopicof(C,A),similarto(B,C).
verbgroup(A,B):- hypernym(B,C),alsosee(F,C),memberofdomainregion(A,D),hypernym(D,E).
verbgroup(A,B):- alsosee(D,E),memberofdomainregion(A,E),derivationallyrelatedform(E,A),similarto(B,C).
verbgroup(A,B):- haspart(D,B),similarto(D,A),hypernym(C,A),similarto(B,C).
verbgroup(A,B):- similarto(E,F),memberofdomainregion(F,A),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- derivationallyrelatedform(B,D),synsetdomaintopicof(B,F),alsosee(F,C),similarto(E,A).
verbgroup(A,B):- similarto(B,D),derivationallyrelatedform(A,C),hypernym(D,C).
