memberofdomainregion(A,B):- membermeronym(F,C),haspart(D,A),hypernym(C,B),verbgroup(D,E).
memberofdomainregion(A,B):- membermeronym(E,B),memberofdomainusage(D,A),haspart(C,B).
memberofdomainregion(A,B):- hypernym(D,E),memberofdomainusage(A,E),membermeronym(C,B),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(D,A),membermeronym(F,C),synsetdomaintopicof(D,C),verbgroup(B,E).
memberofdomainregion(A,B):- derivationallyrelatedform(C,E),derivationallyrelatedform(E,B),verbgroup(A,D).
memberofdomainregion(A,B):- derivationallyrelatedform(B,A),hypernym(A,B),verbgroup(C,B).
memberofdomainregion(A,B):- verbgroup(D,B),similarto(A,C),haspart(C,B).
memberofdomainregion(A,B):- haspart(D,B),hypernym(C,E),memberofdomainusage(E,A).
memberofdomainregion(A,B):- membermeronym(F,C),synsetdomaintopicof(E,A),synsetdomaintopicof(A,C),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- synsetdomaintopicof(B,A),derivationallyrelatedform(B,D),instancehypernym(D,C).
memberofdomainregion(A,B):- verbgroup(B,D),verbgroup(A,E),alsosee(C,A).
memberofdomainregion(A,B):- membermeronym(A,C),membermeronym(F,C),synsetdomaintopicof(B,D),hypernym(E,B).
memberofdomainregion(A,B):- haspart(C,E),derivationallyrelatedform(D,A),synsetdomaintopicof(F,B),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(C,B),memberofdomainusage(C,B),verbgroup(D,A).
memberofdomainregion(A,B):- verbgroup(D,C),membermeronym(D,B),membermeronym(C,A),haspart(B,C).
memberofdomainregion(A,B):- hypernym(D,E),alsosee(D,B),memberofdomainusage(A,C).
memberofdomainregion(A,B):- hypernym(E,B),derivationallyrelatedform(D,B),membermeronym(F,C),derivationallyrelatedform(C,A).
memberofdomainregion(A,B):- membermeronym(F,C),instancehypernym(A,D),membermeronym(C,A),similarto(E,B).
memberofdomainregion(A,B):- verbgroup(C,D),haspart(B,C),derivationallyrelatedform(D,A),memberofdomainusage(D,A).
memberofdomainregion(A,B):- haspart(B,A),verbgroup(C,B),memberofdomainusage(A,C).
memberofdomainregion(A,B):- synsetdomaintopicof(C,B),synsetdomaintopicof(A,E),haspart(B,C),memberofdomainusage(B,D).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),synsetdomaintopicof(B,F),derivationallyrelatedform(B,D),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(C,D),membermeronym(D,E),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),membermeronym(F,C),hypernym(D,A),memberofdomainusage(F,E).
memberofdomainregion(A,B):- similarto(A,E),derivationallyrelatedform(D,B),haspart(B,C),verbgroup(F,B).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(D,B),derivationallyrelatedform(F,E),alsosee(A,F).
memberofdomainregion(A,B):- verbgroup(B,D),memberofdomainusage(A,E),membermeronym(F,C),instancehypernym(D,C).
memberofdomainregion(A,B):- membermeronym(F,C),instancehypernym(C,A),instancehypernym(E,B),alsosee(E,D).
memberofdomainregion(A,B):- alsosee(A,E),hypernym(F,D),similarto(F,E),haspart(B,C).
memberofdomainregion(A,B):- hypernym(C,D),membermeronym(D,E),haspart(B,C),haspart(A,C).
memberofdomainregion(A,B):- alsosee(A,C),hypernym(A,C),membermeronym(B,D).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),membermeronym(C,A),haspart(A,C).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),hypernym(D,A),similarto(E,C).
memberofdomainregion(A,B):- verbgroup(E,A),membermeronym(F,C),synsetdomaintopicof(D,E),similarto(B,C).
memberofdomainregion(A,B):- haspart(E,B),haspart(A,D),similarto(B,D),haspart(B,C).
memberofdomainregion(A,B):- similarto(F,A),membermeronym(F,C),instancehypernym(B,D),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- instancehypernym(B,E),memberofdomainusage(C,B),instancehypernym(D,A).
memberofdomainregion(A,B):- haspart(B,C),haspart(A,D),verbgroup(C,F),memberofdomainusage(E,D).
memberofdomainregion(A,B):- alsosee(D,E),hypernym(A,D),alsosee(A,D),haspart(B,C).
memberofdomainregion(A,B):- alsosee(E,D),haspart(B,C),derivationallyrelatedform(C,D),instancehypernym(A,C).
memberofdomainregion(A,B):- hypernym(C,D),hypernym(A,C),hypernym(C,B).
memberofdomainregion(A,B):- synsetdomaintopicof(B,C),memberofdomainusage(D,E),alsosee(D,A).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),verbgroup(B,E),haspart(B,C),memberofdomainusage(A,B).
memberofdomainregion(A,B):- verbgroup(D,C),derivationallyrelatedform(D,A),similarto(D,B).
memberofdomainregion(A,B):- membermeronym(A,E),haspart(B,C),derivationallyrelatedform(B,F),membermeronym(F,D).
memberofdomainregion(A,B):- haspart(E,A),hypernym(D,A),membermeronym(F,C),verbgroup(C,B).
memberofdomainregion(A,B):- synsetdomaintopicof(B,A),similarto(E,A),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- membermeronym(C,B),derivationallyrelatedform(A,D),haspart(B,C),similarto(D,A).
memberofdomainregion(A,B):- derivationallyrelatedform(D,A),derivationallyrelatedform(E,A),haspart(B,C),hypernym(A,D).
memberofdomainregion(A,B):- instancehypernym(A,E),hypernym(A,C),haspart(B,C),membermeronym(E,D).
memberofdomainregion(A,B):- haspart(B,E),instancehypernym(D,A),verbgroup(C,A).
memberofdomainregion(A,B):- hypernym(B,D),instancehypernym(E,B),haspart(D,A),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(D,B),instancehypernym(B,A),instancehypernym(C,A),haspart(B,C).
memberofdomainregion(A,B):- haspart(D,A),memberofdomainusage(B,E),memberofdomainusage(C,D).
memberofdomainregion(A,B):- membermeronym(F,C),instancehypernym(F,E),similarto(B,D),derivationallyrelatedform(E,A).
memberofdomainregion(A,B):- hypernym(E,A),instancehypernym(B,D),derivationallyrelatedform(D,C).
memberofdomainregion(A,B):- instancehypernym(D,E),synsetdomaintopicof(F,D),instancehypernym(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,C),hypernym(A,E),membermeronym(E,D),haspart(C,B).
memberofdomainregion(A,B):- verbgroup(D,A),synsetdomaintopicof(A,D),synsetdomaintopicof(C,B).
memberofdomainregion(A,B):- derivationallyrelatedform(E,D),alsosee(C,A),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- memberofdomainusage(E,B),membermeronym(D,E),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- membermeronym(B,C),memberofdomainusage(D,B),instancehypernym(E,A),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(B,F),synsetdomaintopicof(A,E),derivationallyrelatedform(B,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),hypernym(E,A),membermeronym(B,D),alsosee(D,F).
memberofdomainregion(A,B):- derivationallyrelatedform(A,D),verbgroup(A,B),haspart(B,C),alsosee(C,D).
memberofdomainregion(A,B):- verbgroup(F,D),memberofdomainusage(A,E),hypernym(E,D),haspart(B,C).
memberofdomainregion(A,B):- similarto(C,D),alsosee(C,A),memberofdomainusage(A,B).
memberofdomainregion(A,B):- verbgroup(B,D),similarto(E,A),membermeronym(F,C),derivationallyrelatedform(D,C).
memberofdomainregion(A,B):- instancehypernym(A,E),similarto(A,D),alsosee(F,E),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(D,A),hypernym(C,E),haspart(B,C),instancehypernym(C,F).
memberofdomainregion(A,B):- memberofdomainusage(C,B),alsosee(D,E),verbgroup(A,D).
memberofdomainregion(A,B):- haspart(D,B),synsetdomaintopicof(C,A),similarto(B,C).
memberofdomainregion(A,B):- haspart(D,B),verbgroup(E,A),membermeronym(F,C),synsetdomaintopicof(B,C).
memberofdomainregion(A,B):- instancehypernym(C,E),instancehypernym(A,D),memberofdomainusage(C,E),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,A),haspart(B,C),memberofdomainusage(A,C),instancehypernym(A,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,C),verbgroup(D,B),haspart(A,B).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),derivationallyrelatedform(C,A),memberofdomainusage(A,D),haspart(B,C).
memberofdomainregion(A,B):- hypernym(D,E),verbgroup(A,E),haspart(B,F),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(C,B),derivationallyrelatedform(A,D),memberofdomainusage(B,A).
memberofdomainregion(A,B):- derivationallyrelatedform(A,B),alsosee(B,C),synsetdomaintopicof(A,B).
memberofdomainregion(A,B):- instancehypernym(D,B),verbgroup(A,E),haspart(B,C),haspart(A,C).
memberofdomainregion(A,B):- membermeronym(A,E),membermeronym(B,D),derivationallyrelatedform(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(B,A),hypernym(D,C),similarto(B,D).
memberofdomainregion(A,B):- membermeronym(F,C),instancehypernym(D,A),hypernym(B,F),memberofdomainusage(E,D).
memberofdomainregion(A,B):- hypernym(B,C),similarto(B,A),memberofdomainusage(C,A).
memberofdomainregion(A,B):- alsosee(E,D),haspart(F,E),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- alsosee(B,F),alsosee(E,C),membermeronym(F,C),haspart(A,D).
memberofdomainregion(A,B):- instancehypernym(E,D),derivationallyrelatedform(A,F),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- similarto(C,D),alsosee(E,F),verbgroup(A,E),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(F,A),membermeronym(F,C),membermeronym(E,B),memberofdomainusage(D,A).
