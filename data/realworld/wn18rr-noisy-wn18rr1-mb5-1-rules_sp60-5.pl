memberofdomainregion(A,B):- hypernym(B,E),membermeronym(F,C),instancehypernym(A,D),synsetdomaintopicof(E,C).
memberofdomainregion(A,B):- membermeronym(F,C),derivationallyrelatedform(E,A),membermeronym(B,D),alsosee(F,D).
memberofdomainregion(A,B):- membermeronym(A,E),similarto(A,D),haspart(B,C),alsosee(E,A).
memberofdomainregion(A,B):- verbgroup(E,D),instancehypernym(D,B),haspart(B,C),membermeronym(A,F).
memberofdomainregion(A,B):- instancehypernym(B,A),instancehypernym(E,D),memberofdomainusage(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(E,D),hypernym(A,C),verbgroup(D,B).
memberofdomainregion(A,B):- instancehypernym(B,E),membermeronym(D,F),membermeronym(F,C),verbgroup(A,C).
memberofdomainregion(A,B):- synsetdomaintopicof(C,E),membermeronym(F,C),similarto(B,D),instancehypernym(A,F).
memberofdomainregion(A,B):- memberofdomainusage(E,C),membermeronym(F,C),similarto(D,B),instancehypernym(A,C).
memberofdomainregion(A,B):- synsetdomaintopicof(E,A),membermeronym(A,B),haspart(B,C),similarto(A,D).
memberofdomainregion(A,B):- membermeronym(F,C),synsetdomaintopicof(F,B),similarto(C,E),verbgroup(A,D).
memberofdomainregion(A,B):- similarto(F,B),membermeronym(D,E),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- synsetdomaintopicof(A,B),haspart(B,C),memberofdomainusage(E,D),hypernym(D,B).
memberofdomainregion(A,B):- memberofdomainusage(D,B),alsosee(D,E),haspart(B,C),haspart(A,C).
memberofdomainregion(A,B):- memberofdomainusage(A,E),synsetdomaintopicof(B,D),hypernym(E,C),haspart(B,C).
memberofdomainregion(A,B):- haspart(F,C),instancehypernym(E,B),alsosee(D,A),haspart(B,C).
memberofdomainregion(A,B):- hypernym(E,D),alsosee(A,D),haspart(B,C),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- similarto(B,E),membermeronym(F,C),memberofdomainusage(F,E),memberofdomainusage(A,D).
memberofdomainregion(A,B):- similarto(A,E),alsosee(E,F),verbgroup(D,F),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(E,B),memberofdomainusage(D,A),haspart(C,B).
memberofdomainregion(A,B):- hypernym(C,D),hypernym(C,B),hypernym(B,A).
memberofdomainregion(A,B):- membermeronym(F,C),synsetdomaintopicof(D,A),alsosee(D,E),instancehypernym(B,C).
memberofdomainregion(A,B):- similarto(D,E),verbgroup(A,C),membermeronym(F,C),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- synsetdomaintopicof(E,B),derivationallyrelatedform(A,D),derivationallyrelatedform(A,F),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(E,A),memberofdomainusage(A,C),verbgroup(D,B).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),membermeronym(F,C),synsetdomaintopicof(C,B),membermeronym(E,A).
memberofdomainregion(A,B):- haspart(C,F),verbgroup(D,B),haspart(B,C),hypernym(A,E).
memberofdomainregion(A,B):- instancehypernym(A,E),hypernym(A,C),haspart(B,C),hypernym(C,D).
memberofdomainregion(A,B):- derivationallyrelatedform(D,F),synsetdomaintopicof(D,B),haspart(B,C),membermeronym(E,A).
memberofdomainregion(A,B):- synsetdomaintopicof(E,B),instancehypernym(A,C),membermeronym(E,D).
memberofdomainregion(A,B):- membermeronym(D,E),instancehypernym(A,C),similarto(E,B).
memberofdomainregion(A,B):- synsetdomaintopicof(E,D),similarto(B,A),hypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(C,D),derivationallyrelatedform(B,E),instancehypernym(C,A).
memberofdomainregion(A,B):- membermeronym(B,C),similarto(B,A),hypernym(D,B).
memberofdomainregion(A,B):- memberofdomainusage(D,B),similarto(B,D),alsosee(D,A),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),similarto(F,D),membermeronym(F,C),instancehypernym(B,C).
memberofdomainregion(A,B):- alsosee(B,D),hypernym(B,A),similarto(A,C).
memberofdomainregion(A,B):- verbgroup(E,D),synsetdomaintopicof(A,D),alsosee(B,A),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),haspart(A,D),haspart(E,A),synsetdomaintopicof(F,B).
memberofdomainregion(A,B):- derivationallyrelatedform(B,D),memberofdomainusage(A,C),hypernym(D,B).
memberofdomainregion(A,B):- alsosee(A,E),synsetdomaintopicof(D,E),membermeronym(F,C),synsetdomaintopicof(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),alsosee(E,F),membermeronym(E,B),alsosee(A,D).
memberofdomainregion(A,B):- membermeronym(F,C),similarto(A,D),similarto(B,C),derivationallyrelatedform(E,C).
memberofdomainregion(A,B):- synsetdomaintopicof(E,B),verbgroup(F,D),membermeronym(F,C),similarto(A,F).
memberofdomainregion(A,B):- verbgroup(A,E),instancehypernym(B,D),haspart(B,C),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- memberofdomainusage(C,F),derivationallyrelatedform(E,D),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- haspart(B,C),similarto(B,C),instancehypernym(A,C),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- membermeronym(D,C),hypernym(E,A),instancehypernym(B,D).
memberofdomainregion(A,B):- instancehypernym(E,A),memberofdomainusage(B,D),similarto(A,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),similarto(C,D),haspart(B,C),verbgroup(D,E).
memberofdomainregion(A,B):- hypernym(C,A),similarto(E,A),hypernym(D,B).
memberofdomainregion(A,B):- hypernym(D,A),haspart(B,C),instancehypernym(F,A),verbgroup(D,E).
memberofdomainregion(A,B):- similarto(E,D),hypernym(A,C),alsosee(D,B).
memberofdomainregion(A,B):- membermeronym(F,C),memberofdomainusage(D,B),instancehypernym(E,A),haspart(F,E).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),verbgroup(A,C),alsosee(C,D).
memberofdomainregion(A,B):- hypernym(D,A),synsetdomaintopicof(E,A),hypernym(A,D),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(C,B),membermeronym(F,C),instancehypernym(D,A),similarto(C,E).
memberofdomainregion(A,B):- instancehypernym(C,B),memberofdomainusage(A,D),haspart(B,C),similarto(D,E).
memberofdomainregion(A,B):- haspart(B,C),hypernym(A,E),memberofdomainusage(E,D),membermeronym(A,F).
memberofdomainregion(A,B):- alsosee(B,F),synsetdomaintopicof(D,E),haspart(A,D),haspart(B,C).
