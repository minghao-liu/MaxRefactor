memberofdomainregion(A,B):- verbgroup(B,D),haspart(C,E),membermeronym(F,C),memberofdomainusage(A,C).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),membermeronym(F,C),synsetdomaintopicof(F,A),similarto(E,B).
memberofdomainregion(A,B):- synsetdomaintopicof(C,A),membermeronym(F,C),membermeronym(A,D),verbgroup(B,E).
memberofdomainregion(A,B):- hypernym(A,C),instancehypernym(C,E),similarto(D,B),haspart(B,C).
memberofdomainregion(A,B):- haspart(C,D),similarto(D,A),haspart(B,C),synsetdomaintopicof(A,E).
memberofdomainregion(A,B):- instancehypernym(A,D),membermeronym(D,B),membermeronym(B,E),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),instancehypernym(C,A),derivationallyrelatedform(E,B),verbgroup(D,E).
memberofdomainregion(A,B):- instancehypernym(A,D),membermeronym(F,C),memberofdomainusage(B,E),synsetdomaintopicof(A,F).
memberofdomainregion(A,B):- instancehypernym(A,D),alsosee(A,B),similarto(C,A).
memberofdomainregion(A,B):- haspart(D,B),synsetdomaintopicof(F,C),haspart(B,C),memberofdomainusage(E,A).
memberofdomainregion(A,B):- alsosee(B,F),membermeronym(F,C),haspart(D,A),derivationallyrelatedform(E,C).
memberofdomainregion(A,B):- instancehypernym(A,E),membermeronym(F,C),memberofdomainusage(C,E),haspart(D,B).
memberofdomainregion(A,B):- instancehypernym(B,A),alsosee(C,A),haspart(C,A).
memberofdomainregion(A,B):- membermeronym(A,E),instancehypernym(A,D),haspart(C,E),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(B,C),similarto(A,D),hypernym(C,B),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(E,B),alsosee(C,A),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- similarto(D,A),memberofdomainusage(E,B),membermeronym(C,A).
memberofdomainregion(A,B):- membermeronym(A,E),haspart(B,C),membermeronym(B,D),derivationallyrelatedform(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),similarto(C,B),membermeronym(A,D),hypernym(A,E).
memberofdomainregion(A,B):- similarto(C,B),alsosee(B,A),membermeronym(A,D).
memberofdomainregion(A,B):- alsosee(A,E),haspart(B,C),alsosee(E,F),instancehypernym(D,C).
memberofdomainregion(A,B):- haspart(D,B),similarto(E,C),synsetdomaintopicof(F,A),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(A,D),derivationallyrelatedform(E,D),alsosee(F,B),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,A),memberofdomainusage(A,C),verbgroup(D,B).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),synsetdomaintopicof(E,D),haspart(B,C),verbgroup(C,A).
memberofdomainregion(A,B):- alsosee(B,A),synsetdomaintopicof(D,C),membermeronym(B,D).
memberofdomainregion(A,B):- memberofdomainusage(E,C),hypernym(E,A),derivationallyrelatedform(D,A),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(B,C),membermeronym(A,E),synsetdomaintopicof(C,D),haspart(B,C).
memberofdomainregion(A,B):- hypernym(A,C),derivationallyrelatedform(C,A),verbgroup(A,B).
memberofdomainregion(A,B):- verbgroup(D,F),alsosee(A,E),instancehypernym(E,D),haspart(B,C).
memberofdomainregion(A,B):- hypernym(B,E),membermeronym(F,C),derivationallyrelatedform(D,A),haspart(E,C).
memberofdomainregion(A,B):- instancehypernym(A,E),haspart(D,E),synsetdomaintopicof(F,B),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(E,D),membermeronym(F,C),instancehypernym(C,B),membermeronym(D,A).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),synsetdomaintopicof(C,A),haspart(B,C),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- membermeronym(F,C),instancehypernym(D,E),haspart(A,D),haspart(F,B).
memberofdomainregion(A,B):- instancehypernym(E,F),membermeronym(F,C),derivationallyrelatedform(B,F),memberofdomainusage(D,A).
memberofdomainregion(A,B):- instancehypernym(E,B),alsosee(E,F),haspart(B,C),similarto(D,A).
memberofdomainregion(A,B):- memberofdomainusage(B,C),similarto(B,A),instancehypernym(B,D).
memberofdomainregion(A,B):- instancehypernym(B,F),membermeronym(F,C),verbgroup(A,E),memberofdomainusage(D,A).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),membermeronym(F,C),hypernym(C,D),hypernym(D,B).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),similarto(C,D),haspart(B,C),similarto(C,A).
memberofdomainregion(A,B):- haspart(C,A),derivationallyrelatedform(B,D),hypernym(A,E).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),membermeronym(C,F),alsosee(D,B),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(E,B),memberofdomainusage(C,E),hypernym(A,D).
memberofdomainregion(A,B):- haspart(D,B),derivationallyrelatedform(A,B),haspart(B,C),similarto(D,E).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),instancehypernym(E,D),verbgroup(A,B),haspart(B,C).
memberofdomainregion(A,B):- similarto(A,E),haspart(B,A),derivationallyrelatedform(C,D),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),memberofdomainusage(C,F),membermeronym(D,F),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(C,F),membermeronym(C,E),memberofdomainusage(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,C),alsosee(D,B),instancehypernym(D,C),haspart(A,E).
memberofdomainregion(A,B):- haspart(B,D),verbgroup(C,B),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- instancehypernym(C,B),instancehypernym(A,D),haspart(A,C).
memberofdomainregion(A,B):- membermeronym(B,E),memberofdomainusage(B,E),haspart(A,D),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(C,B),membermeronym(F,C),verbgroup(A,E),haspart(D,E).
memberofdomainregion(A,B):- membermeronym(F,C),alsosee(C,A),membermeronym(B,D),alsosee(E,A).
memberofdomainregion(A,B):- similarto(A,D),haspart(B,C),synsetdomaintopicof(A,C),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- haspart(A,B),membermeronym(B,D),membermeronym(C,D).
memberofdomainregion(A,B):- memberofdomainusage(B,C),membermeronym(A,B),haspart(C,D).
memberofdomainregion(A,B):- hypernym(B,C),derivationallyrelatedform(C,A),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(C,B),synsetdomaintopicof(D,A),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(D,C),derivationallyrelatedform(E,A),haspart(B,C),hypernym(A,E).
memberofdomainregion(A,B):- verbgroup(B,D),memberofdomainusage(A,C),instancehypernym(A,C).
memberofdomainregion(A,B):- membermeronym(A,E),memberofdomainusage(A,C),haspart(B,C),memberofdomainusage(C,D).
memberofdomainregion(A,B):- similarto(A,D),derivationallyrelatedform(F,D),verbgroup(B,E),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(B,E),membermeronym(F,C),similarto(D,B),instancehypernym(A,F).
memberofdomainregion(A,B):- synsetdomaintopicof(E,B),membermeronym(F,C),similarto(C,A),haspart(D,F).
memberofdomainregion(A,B):- hypernym(D,E),synsetdomaintopicof(C,D),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- alsosee(E,A),derivationallyrelatedform(A,D),haspart(B,C),verbgroup(C,A).
memberofdomainregion(A,B):- alsosee(D,C),haspart(A,D),membermeronym(A,B),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(E,B),membermeronym(F,C),instancehypernym(E,D),verbgroup(F,A).
