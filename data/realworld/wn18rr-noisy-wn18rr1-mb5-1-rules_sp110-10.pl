memberofdomainregion(A,B):- verbgroup(B,D),similarto(A,B),derivationallyrelatedform(D,A),haspart(B,C).
memberofdomainregion(A,B):- similarto(D,F),verbgroup(A,E),hypernym(B,F),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(B,C),instancehypernym(C,D),alsosee(C,A).
memberofdomainregion(A,B):- derivationallyrelatedform(F,C),similarto(D,C),alsosee(A,E),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),similarto(D,B),haspart(B,C),similarto(C,A).
memberofdomainregion(A,B):- verbgroup(D,B),alsosee(D,A),haspart(A,C).
memberofdomainregion(A,B):- derivationallyrelatedform(E,A),memberofdomainusage(D,B),verbgroup(A,B),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(B,D),alsosee(A,D),instancehypernym(B,C).
memberofdomainregion(A,B):- haspart(E,B),membermeronym(F,C),instancehypernym(C,A),derivationallyrelatedform(C,D).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),membermeronym(C,B),derivationallyrelatedform(A,D).
memberofdomainregion(A,B):- hypernym(E,A),memberofdomainusage(A,D),haspart(B,C),memberofdomainusage(F,D).
memberofdomainregion(A,B):- derivationallyrelatedform(D,A),alsosee(D,E),haspart(B,C),haspart(C,B).
memberofdomainregion(A,B):- membermeronym(F,C),instancehypernym(F,B),derivationallyrelatedform(D,A),verbgroup(D,E).
memberofdomainregion(A,B):- hypernym(C,D),similarto(A,B),alsosee(B,D).
memberofdomainregion(A,B):- membermeronym(B,C),synsetdomaintopicof(C,D),memberofdomainusage(D,A).
memberofdomainregion(A,B):- membermeronym(D,C),hypernym(B,A),hypernym(B,D).
memberofdomainregion(A,B):- similarto(E,D),instancehypernym(A,C),haspart(B,C),membermeronym(B,D).
memberofdomainregion(A,B):- instancehypernym(A,D),similarto(E,F),haspart(B,C),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),hypernym(B,F),hypernym(E,C),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),membermeronym(F,C),derivationallyrelatedform(D,E),hypernym(A,F).
memberofdomainregion(A,B):- haspart(E,B),alsosee(C,B),verbgroup(A,D).
memberofdomainregion(A,B):- derivationallyrelatedform(E,D),memberofdomainusage(F,E),memberofdomainusage(A,D),haspart(B,C).
memberofdomainregion(A,B):- similarto(E,D),alsosee(A,E),alsosee(E,B),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(A,D),memberofdomainusage(A,D),haspart(B,C),derivationallyrelatedform(B,C).
memberofdomainregion(A,B):- instancehypernym(B,E),membermeronym(F,C),hypernym(D,A),memberofdomainusage(C,A).
memberofdomainregion(A,B):- similarto(A,D),hypernym(E,C),haspart(B,C),alsosee(A,F).
memberofdomainregion(A,B):- verbgroup(B,C),derivationallyrelatedform(C,A),synsetdomaintopicof(A,B).
memberofdomainregion(A,B):- verbgroup(D,A),synsetdomaintopicof(A,E),membermeronym(D,E),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(E,B),synsetdomaintopicof(D,A),haspart(B,C),membermeronym(E,A).
memberofdomainregion(A,B):- instancehypernym(C,A),memberofdomainusage(E,B),membermeronym(D,A).
memberofdomainregion(A,B):- derivationallyrelatedform(B,A),verbgroup(B,C),derivationallyrelatedform(B,D).
memberofdomainregion(A,B):- membermeronym(F,C),instancehypernym(E,A),similarto(A,C),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- haspart(E,B),haspart(A,D),haspart(A,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),hypernym(D,A),membermeronym(D,B),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(C,B),haspart(B,C),instancehypernym(A,C),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- haspart(B,A),similarto(A,D),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(F,E),alsosee(A,D),haspart(B,C),synsetdomaintopicof(F,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),derivationallyrelatedform(A,D),verbgroup(C,B),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(D,B),membermeronym(F,C),hypernym(C,E),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- verbgroup(F,D),instancehypernym(A,D),memberofdomainusage(F,E),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(D,A),alsosee(E,C),membermeronym(F,C),hypernym(C,B).
memberofdomainregion(A,B):- instancehypernym(D,F),membermeronym(F,C),derivationallyrelatedform(E,B),alsosee(A,F).
memberofdomainregion(A,B):- similarto(C,F),memberofdomainusage(A,E),memberofdomainusage(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(D,A),membermeronym(B,E),alsosee(B,C).
memberofdomainregion(A,B):- verbgroup(E,A),haspart(B,C),memberofdomainusage(A,D),derivationallyrelatedform(E,F).
memberofdomainregion(A,B):- haspart(A,D),membermeronym(F,E),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- synsetdomaintopicof(D,B),synsetdomaintopicof(A,C),haspart(A,E).
memberofdomainregion(A,B):- membermeronym(F,C),similarto(F,E),memberofdomainusage(B,D),alsosee(E,A).
memberofdomainregion(A,B):- haspart(B,E),haspart(B,C),alsosee(A,D),memberofdomainusage(E,D).
memberofdomainregion(A,B):- instancehypernym(C,B),membermeronym(F,C),derivationallyrelatedform(A,E),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- verbgroup(D,A),haspart(B,C),hypernym(A,D),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- instancehypernym(C,E),derivationallyrelatedform(A,D),hypernym(C,B).
memberofdomainregion(A,B):- membermeronym(F,C),memberofdomainusage(E,B),instancehypernym(E,D),derivationallyrelatedform(F,A).
memberofdomainregion(A,B):- synsetdomaintopicof(D,E),membermeronym(F,C),derivationallyrelatedform(E,A),instancehypernym(B,C).
memberofdomainregion(A,B):- verbgroup(A,F),memberofdomainusage(A,E),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(A,D),hypernym(C,E),synsetdomaintopicof(F,A),haspart(B,C).
memberofdomainregion(A,B):- alsosee(A,E),synsetdomaintopicof(B,D),verbgroup(D,B),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(E,D),similarto(B,F),haspart(B,C),derivationallyrelatedform(A,E).
memberofdomainregion(A,B):- synsetdomaintopicof(E,D),membermeronym(D,B),verbgroup(C,A).
memberofdomainregion(A,B):- synsetdomaintopicof(C,B),derivationallyrelatedform(D,C),verbgroup(B,A).
memberofdomainregion(A,B):- haspart(C,D),verbgroup(B,C),verbgroup(A,B).
memberofdomainregion(A,B):- instancehypernym(A,B),membermeronym(A,D),derivationallyrelatedform(B,C).
memberofdomainregion(A,B):- memberofdomainusage(E,B),membermeronym(A,D),haspart(B,C),instancehypernym(B,D).
memberofdomainregion(A,B):- instancehypernym(D,B),membermeronym(A,B),haspart(B,C),verbgroup(C,E).
memberofdomainregion(A,B):- verbgroup(D,A),membermeronym(F,C),haspart(B,F),hypernym(A,E).
memberofdomainregion(A,B):- synsetdomaintopicof(B,A),membermeronym(C,B),similarto(D,B).
memberofdomainregion(A,B):- haspart(E,D),haspart(A,D),haspart(B,C),membermeronym(F,D).
memberofdomainregion(A,B):- similarto(A,D),membermeronym(E,F),haspart(B,C),haspart(D,F).
memberofdomainregion(A,B):- hypernym(E,D),haspart(B,C),verbgroup(A,E),memberofdomainusage(B,D).
memberofdomainregion(A,B):- alsosee(A,E),haspart(D,C),haspart(B,C),hypernym(A,E).
memberofdomainregion(A,B):- membermeronym(D,C),derivationallyrelatedform(A,D),membermeronym(C,A),haspart(B,C).
memberofdomainregion(A,B):- hypernym(C,E),derivationallyrelatedform(A,D),haspart(F,B),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(A,C),membermeronym(F,C),verbgroup(E,C),similarto(D,B).
memberofdomainregion(A,B):- hypernym(B,D),similarto(D,C),membermeronym(B,A).
memberofdomainregion(A,B):- membermeronym(F,C),alsosee(E,F),instancehypernym(D,A),haspart(B,C).
memberofdomainregion(A,B):- similarto(A,E),similarto(B,F),memberofdomainusage(A,D),haspart(B,C).
memberofdomainregion(A,B):- alsosee(B,C),membermeronym(F,C),instancehypernym(D,E),memberofdomainusage(A,D).
memberofdomainregion(A,B):- instancehypernym(C,B),membermeronym(B,C),haspart(B,C),instancehypernym(A,C).
memberofdomainregion(A,B):- instancehypernym(A,E),membermeronym(F,C),similarto(D,F),alsosee(F,B).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),haspart(F,E),hypernym(F,D),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(A,E),haspart(E,B),alsosee(B,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(D,C),verbgroup(E,A),membermeronym(A,E),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(B,E),instancehypernym(F,A),verbgroup(A,D).
memberofdomainregion(A,B):- derivationallyrelatedform(C,E),verbgroup(B,E),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- hypernym(E,D),haspart(B,C),derivationallyrelatedform(D,C),haspart(A,C).
memberofdomainregion(A,B):- similarto(E,A),membermeronym(F,C),synsetdomaintopicof(B,F),memberofdomainusage(B,D).
memberofdomainregion(A,B):- haspart(D,B),membermeronym(C,A),haspart(B,C),synsetdomaintopicof(A,B).
memberofdomainregion(A,B):- verbgroup(A,E),synsetdomaintopicof(C,F),haspart(B,C),verbgroup(D,E).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),haspart(D,A),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- membermeronym(B,F),haspart(C,D),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),haspart(B,C),memberofdomainusage(C,A),memberofdomainusage(E,D).
memberofdomainregion(A,B):- verbgroup(E,A),synsetdomaintopicof(C,F),verbgroup(D,B),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(C,B),hypernym(D,A),membermeronym(F,C),similarto(E,C).
memberofdomainregion(A,B):- haspart(D,B),verbgroup(E,A),membermeronym(F,C),memberofdomainusage(F,D).
memberofdomainregion(A,B):- haspart(A,E),haspart(B,C),memberofdomainusage(D,A),membermeronym(F,D).
memberofdomainregion(A,B):- membermeronym(F,C),memberofdomainusage(B,E),verbgroup(D,F),similarto(C,A).
memberofdomainregion(A,B):- verbgroup(D,A),membermeronym(F,C),derivationallyrelatedform(E,D),derivationallyrelatedform(C,B).
memberofdomainregion(A,B):- alsosee(D,C),synsetdomaintopicof(B,C),haspart(B,C),haspart(A,C).
memberofdomainregion(A,B):- haspart(D,B),membermeronym(F,C),alsosee(E,F),alsosee(A,F).
memberofdomainregion(A,B):- synsetdomaintopicof(D,E),membermeronym(F,C),similarto(A,F),alsosee(B,D).
memberofdomainregion(A,B):- memberofdomainusage(E,C),verbgroup(C,F),hypernym(A,D),haspart(B,C).
memberofdomainregion(A,B):- hypernym(A,F),verbgroup(A,E),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),membermeronym(A,E),membermeronym(F,C),memberofdomainusage(A,D).
memberofdomainregion(A,B):- synsetdomaintopicof(C,A),membermeronym(F,C),alsosee(B,E),memberofdomainusage(A,D).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),synsetdomaintopicof(E,D),similarto(F,D),haspart(B,C).
memberofdomainregion(A,B):- hypernym(E,D),instancehypernym(B,A),memberofdomainusage(D,B),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(D,A),similarto(F,A),membermeronym(F,C),similarto(B,E).
memberofdomainregion(A,B):- membermeronym(B,F),instancehypernym(E,D),memberofdomainusage(A,D),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(A,E),haspart(B,C),synsetdomaintopicof(B,F),memberofdomainusage(D,A).
memberofdomainregion(A,B):- alsosee(C,F),haspart(B,C),verbgroup(A,E),memberofdomainusage(E,D).
