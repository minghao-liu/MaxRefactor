memberofdomainregion(A,B):- haspart(C,D),verbgroup(A,B),haspart(B,C),alsosee(A,D).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),instancehypernym(A,B),similarto(A,D),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(E,A),similarto(A,D),synsetdomaintopicof(B,C),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(E,B),haspart(B,C),instancehypernym(D,A),instancehypernym(B,F).
memberofdomainregion(A,B):- similarto(D,A),verbgroup(D,B),haspart(A,C).
memberofdomainregion(A,B):- hypernym(B,D),similarto(A,E),membermeronym(F,C),haspart(F,D).
memberofdomainregion(A,B):- membermeronym(A,C),synsetdomaintopicof(E,D),membermeronym(D,B).
memberofdomainregion(A,B):- hypernym(C,B),memberofdomainusage(A,D),haspart(B,C),hypernym(A,E).
memberofdomainregion(A,B):- instancehypernym(E,B),derivationallyrelatedform(A,D),derivationallyrelatedform(F,E),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(D,B),synsetdomaintopicof(D,C),membermeronym(A,D).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),membermeronym(F,C),haspart(D,C),hypernym(A,E).
memberofdomainregion(A,B):- haspart(B,C),similarto(D,C),haspart(A,D),instancehypernym(A,C).
memberofdomainregion(A,B):- membermeronym(D,B),synsetdomaintopicof(A,B),membermeronym(C,D).
memberofdomainregion(A,B):- verbgroup(E,A),membermeronym(F,C),synsetdomaintopicof(D,C),haspart(C,B).
memberofdomainregion(A,B):- alsosee(B,C),similarto(C,A),haspart(B,C),haspart(A,C).
memberofdomainregion(A,B):- membermeronym(F,C),derivationallyrelatedform(F,B),haspart(E,A),similarto(B,D).
memberofdomainregion(A,B):- hypernym(B,D),membermeronym(F,C),instancehypernym(A,F),memberofdomainusage(E,A).
memberofdomainregion(A,B):- alsosee(A,C),similarto(A,D),synsetdomaintopicof(D,C),haspart(B,C).
memberofdomainregion(A,B):- hypernym(C,A),verbgroup(B,C),alsosee(C,D).
memberofdomainregion(A,B):- haspart(B,C),derivationallyrelatedform(C,A),memberofdomainusage(B,D),haspart(A,E).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),membermeronym(F,C),derivationallyrelatedform(A,D),alsosee(F,B).
memberofdomainregion(A,B):- verbgroup(A,D),membermeronym(F,C),verbgroup(F,E),instancehypernym(B,C).
memberofdomainregion(A,B):- similarto(F,B),membermeronym(F,C),alsosee(D,B),membermeronym(E,A).
memberofdomainregion(A,B):- alsosee(B,C),verbgroup(A,E),derivationallyrelatedform(D,C).
memberofdomainregion(A,B):- hypernym(E,B),derivationallyrelatedform(D,A),hypernym(C,F),haspart(B,C).
memberofdomainregion(A,B):- alsosee(B,F),membermeronym(F,C),hypernym(A,E),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- haspart(C,D),hypernym(C,B),memberofdomainusage(E,A).
memberofdomainregion(A,B):- haspart(A,D),similarto(E,C),synsetdomaintopicof(C,F),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(E,B),alsosee(A,E),alsosee(D,A),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),haspart(B,C),verbgroup(E,B),membermeronym(F,D).
memberofdomainregion(A,B):- membermeronym(F,C),similarto(A,D),memberofdomainusage(E,B),synsetdomaintopicof(D,C).
memberofdomainregion(A,B):- haspart(A,D),verbgroup(C,B),synsetdomaintopicof(E,C).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),membermeronym(F,C),haspart(D,A),alsosee(C,E).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),memberofdomainusage(C,B),haspart(D,B),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(B,E),hypernym(F,D),membermeronym(D,A).
memberofdomainregion(A,B):- instancehypernym(E,B),alsosee(A,B),synsetdomaintopicof(D,A),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,A),memberofdomainusage(D,B),haspart(B,C),instancehypernym(D,C).
memberofdomainregion(A,B):- hypernym(B,E),membermeronym(F,C),alsosee(A,D),derivationallyrelatedform(E,C).
memberofdomainregion(A,B):- instancehypernym(D,B),alsosee(A,E),haspart(B,C),derivationallyrelatedform(F,A).
memberofdomainregion(A,B):- memberofdomainusage(A,E),similarto(A,D),haspart(B,C),haspart(D,F).
memberofdomainregion(A,B):- derivationallyrelatedform(E,F),derivationallyrelatedform(F,D),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- membermeronym(C,B),hypernym(E,A),synsetdomaintopicof(D,A).
memberofdomainregion(A,B):- membermeronym(B,C),instancehypernym(A,B),similarto(C,D).
memberofdomainregion(A,B):- membermeronym(F,C),synsetdomaintopicof(D,A),membermeronym(F,B),derivationallyrelatedform(E,B).
memberofdomainregion(A,B):- synsetdomaintopicof(D,A),synsetdomaintopicof(C,D),hypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(C,D),haspart(A,D),similarto(C,B).
memberofdomainregion(A,B):- hypernym(D,A),alsosee(B,E),membermeronym(C,E).
memberofdomainregion(A,B):- instancehypernym(A,B),haspart(A,D),similarto(E,B),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),instancehypernym(D,A),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- alsosee(C,B),membermeronym(F,C),hypernym(D,C),haspart(A,E).
memberofdomainregion(A,B):- alsosee(E,D),similarto(A,D),haspart(B,C),similarto(D,E).
memberofdomainregion(A,B):- haspart(B,E),verbgroup(E,C),alsosee(A,D).
memberofdomainregion(A,B):- derivationallyrelatedform(C,E),derivationallyrelatedform(C,A),memberofdomainusage(A,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(A,E),instancehypernym(F,B),derivationallyrelatedform(F,D),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(E,A),similarto(B,D),instancehypernym(D,C).
memberofdomainregion(A,B):- membermeronym(B,C),membermeronym(F,C),haspart(E,A),similarto(B,D).
memberofdomainregion(A,B):- similarto(B,F),hypernym(E,A),hypernym(A,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(D,C),similarto(A,E),membermeronym(F,C),synsetdomaintopicof(B,F).
memberofdomainregion(A,B):- membermeronym(F,C),alsosee(B,E),similarto(D,F),alsosee(D,A).
memberofdomainregion(A,B):- alsosee(E,D),membermeronym(B,A),hypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(B,E),memberofdomainusage(A,D),haspart(B,C),membermeronym(C,D).
memberofdomainregion(A,B):- memberofdomainusage(B,F),membermeronym(F,C),instancehypernym(E,A),verbgroup(D,C).
memberofdomainregion(A,B):- verbgroup(B,D),memberofdomainusage(A,C),haspart(A,B).
memberofdomainregion(A,B):- verbgroup(D,A),memberofdomainusage(C,B),synsetdomaintopicof(E,D).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),membermeronym(F,C),synsetdomaintopicof(E,C),membermeronym(B,D).
memberofdomainregion(A,B):- instancehypernym(C,B),hypernym(D,A),membermeronym(F,C),similarto(A,E).
memberofdomainregion(A,B):- haspart(E,D),membermeronym(F,C),instancehypernym(A,C),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- membermeronym(A,C),hypernym(D,A),membermeronym(A,E),haspart(B,C).
memberofdomainregion(A,B):- similarto(B,F),instancehypernym(B,D),hypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(F,E),similarto(D,B),haspart(B,C),memberofdomainusage(A,F).
memberofdomainregion(A,B):- membermeronym(E,C),derivationallyrelatedform(D,A),memberofdomainusage(D,E),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(C,B),hypernym(C,E),derivationallyrelatedform(D,A),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,C),hypernym(D,B),instancehypernym(B,F),haspart(A,E).
memberofdomainregion(A,B):- alsosee(B,C),membermeronym(F,C),hypernym(D,B),memberofdomainusage(E,A).
memberofdomainregion(A,B):- membermeronym(F,C),derivationallyrelatedform(E,A),derivationallyrelatedform(B,F),hypernym(D,F).
memberofdomainregion(A,B):- membermeronym(F,C),synsetdomaintopicof(A,F),synsetdomaintopicof(B,D),synsetdomaintopicof(F,E).
memberofdomainregion(A,B):- haspart(D,A),verbgroup(D,B),haspart(B,C),hypernym(E,A).
memberofdomainregion(A,B):- alsosee(E,C),memberofdomainusage(A,E),verbgroup(D,B),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(B,C),membermeronym(A,E),haspart(D,E).
memberofdomainregion(A,B):- haspart(B,F),memberofdomainusage(A,D),haspart(B,C),membermeronym(E,A).
memberofdomainregion(A,B):- synsetdomaintopicof(E,B),haspart(B,C),instancehypernym(D,C),memberofdomainusage(A,F).
memberofdomainregion(A,B):- verbgroup(F,D),alsosee(A,D),haspart(B,C),similarto(E,B).
memberofdomainregion(A,B):- instancehypernym(A,E),synsetdomaintopicof(C,E),similarto(D,B).
memberofdomainregion(A,B):- similarto(A,D),derivationallyrelatedform(F,B),haspart(B,C),similarto(E,D).
memberofdomainregion(A,B):- membermeronym(F,C),verbgroup(B,E),membermeronym(D,A),haspart(C,A).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),synsetdomaintopicof(B,D),haspart(A,D).
memberofdomainregion(A,B):- similarto(D,C),memberofdomainusage(C,F),alsosee(A,E),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(E,D),similarto(C,D),haspart(B,C),haspart(A,C).
memberofdomainregion(A,B):- memberofdomainusage(C,B),haspart(A,D),synsetdomaintopicof(B,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(A,C),derivationallyrelatedform(A,D),memberofdomainusage(B,A),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),memberofdomainusage(C,E),memberofdomainusage(F,B),memberofdomainusage(D,A).
memberofdomainregion(A,B):- haspart(D,B),hypernym(C,B),similarto(A,C).
memberofdomainregion(A,B):- membermeronym(F,C),instancehypernym(D,A),memberofdomainusage(F,B),memberofdomainusage(E,A).
memberofdomainregion(A,B):- haspart(B,C),memberofdomainusage(D,B),derivationallyrelatedform(D,A),membermeronym(B,D).
memberofdomainregion(A,B):- similarto(E,A),verbgroup(D,B),haspart(B,C),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- memberofdomainusage(A,E),membermeronym(F,C),verbgroup(D,B),derivationallyrelatedform(A,F).
memberofdomainregion(A,B):- hypernym(D,A),similarto(C,A),hypernym(D,B).
memberofdomainregion(A,B):- similarto(B,C),membermeronym(A,D),haspart(B,C),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- haspart(B,D),hypernym(B,A),haspart(C,B).
memberofdomainregion(A,B):- verbgroup(D,B),alsosee(C,A),haspart(C,B).
