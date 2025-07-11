memberofdomainregion(A,B):- alsosee(E,B),hypernym(D,A),membermeronym(F,C),verbgroup(D,F).
memberofdomainregion(A,B):- membermeronym(F,C),memberofdomainusage(A,C),verbgroup(E,B),verbgroup(A,D).
memberofdomainregion(A,B):- synsetdomaintopicof(E,B),similarto(F,A),membermeronym(F,C),haspart(D,C).
memberofdomainregion(A,B):- memberofdomainusage(C,B),membermeronym(D,B),synsetdomaintopicof(D,A),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),membermeronym(F,C),hypernym(A,F),synsetdomaintopicof(C,D).
memberofdomainregion(A,B):- haspart(B,A),similarto(C,B),hypernym(D,C).
memberofdomainregion(A,B):- instancehypernym(D,B),alsosee(D,A),hypernym(D,E),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(A,E),haspart(B,D),alsosee(D,C).
memberofdomainregion(A,B):- hypernym(B,C),membermeronym(F,C),similarto(D,A),membermeronym(D,E).
memberofdomainregion(A,B):- verbgroup(E,D),hypernym(C,A),hypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- similarto(A,D),derivationallyrelatedform(E,A),haspart(B,C),verbgroup(C,A).
memberofdomainregion(A,B):- instancehypernym(B,A),haspart(A,B),similarto(A,C).
memberofdomainregion(A,B):- haspart(B,C),hypernym(D,C),verbgroup(E,B),memberofdomainusage(A,F).
memberofdomainregion(A,B):- memberofdomainusage(D,C),membermeronym(F,C),alsosee(B,D),membermeronym(E,A).
memberofdomainregion(A,B):- haspart(F,A),haspart(E,B),memberofdomainusage(D,F),membermeronym(F,C).
memberofdomainregion(A,B):- membermeronym(A,C),haspart(C,D),membermeronym(D,B),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(A,E),haspart(C,F),verbgroup(D,B),haspart(B,C).
memberofdomainregion(A,B):- alsosee(A,C),membermeronym(B,D),memberofdomainusage(C,D).
memberofdomainregion(A,B):- haspart(E,D),membermeronym(F,C),alsosee(F,B),haspart(A,E).
memberofdomainregion(A,B):- membermeronym(D,C),haspart(B,C),instancehypernym(A,C),membermeronym(C,D).
memberofdomainregion(A,B):- memberofdomainusage(A,E),haspart(B,C),instancehypernym(B,F),haspart(D,F).
memberofdomainregion(A,B):- hypernym(B,D),membermeronym(F,C),synsetdomaintopicof(F,A),alsosee(E,D).
memberofdomainregion(A,B):- instancehypernym(C,E),haspart(B,C),instancehypernym(D,A),instancehypernym(F,A).
memberofdomainregion(A,B):- synsetdomaintopicof(D,E),similarto(F,C),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),memberofdomainusage(D,A),membermeronym(C,D).
memberofdomainregion(A,B):- alsosee(A,E),memberofdomainusage(E,B),haspart(B,C),memberofdomainusage(C,D).
memberofdomainregion(A,B):- instancehypernym(E,F),instancehypernym(A,D),haspart(B,C),instancehypernym(F,A).
memberofdomainregion(A,B):- synsetdomaintopicof(C,B),haspart(B,C),instancehypernym(A,C),derivationallyrelatedform(B,C).
memberofdomainregion(A,B):- memberofdomainusage(D,C),synsetdomaintopicof(C,B),haspart(A,B).
memberofdomainregion(A,B):- memberofdomainusage(B,F),membermeronym(A,E),synsetdomaintopicof(C,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(C,A),synsetdomaintopicof(D,A),verbgroup(B,E).
memberofdomainregion(A,B):- memberofdomainusage(B,F),membermeronym(F,C),instancehypernym(D,A),haspart(E,C).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),membermeronym(F,C),similarto(C,B),haspart(E,D).
memberofdomainregion(A,B):- similarto(E,D),memberofdomainusage(D,B),instancehypernym(A,F),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(D,B),membermeronym(F,C),hypernym(D,F),alsosee(E,A).
memberofdomainregion(A,B):- memberofdomainusage(C,B),instancehypernym(D,A),haspart(A,B).
memberofdomainregion(A,B):- verbgroup(A,C),membermeronym(F,C),derivationallyrelatedform(A,D),verbgroup(E,B).
memberofdomainregion(A,B):- similarto(D,A),memberofdomainusage(C,A),haspart(C,B).
memberofdomainregion(A,B):- membermeronym(F,C),haspart(B,D),derivationallyrelatedform(A,F),memberofdomainusage(E,A).
memberofdomainregion(A,B):- instancehypernym(B,E),membermeronym(F,C),verbgroup(D,B),similarto(A,C).
memberofdomainregion(A,B):- verbgroup(B,D),instancehypernym(A,C),similarto(B,C).
memberofdomainregion(A,B):- membermeronym(E,D),membermeronym(F,C),membermeronym(B,D),instancehypernym(F,A).
memberofdomainregion(A,B):- similarto(E,D),membermeronym(B,C),membermeronym(F,C),derivationallyrelatedform(A,D).
memberofdomainregion(A,B):- membermeronym(F,C),derivationallyrelatedform(D,E),membermeronym(F,B),hypernym(A,E).
memberofdomainregion(A,B):- memberofdomainusage(A,E),hypernym(F,D),membermeronym(F,C),memberofdomainusage(F,B).
memberofdomainregion(A,B):- alsosee(A,C),derivationallyrelatedform(D,B),membermeronym(C,B),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(E,D),instancehypernym(D,B),verbgroup(A,C),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(E,F),haspart(B,C),instancehypernym(F,A),haspart(C,D).
memberofdomainregion(A,B):- instancehypernym(C,B),hypernym(E,A),membermeronym(E,D).
memberofdomainregion(A,B):- membermeronym(A,B),derivationallyrelatedform(D,C),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- membermeronym(A,C),memberofdomainusage(A,E),haspart(B,C),hypernym(D,B).
memberofdomainregion(A,B):- verbgroup(A,C),alsosee(D,B),similarto(E,B),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),verbgroup(A,E),instancehypernym(E,D),verbgroup(F,B).
memberofdomainregion(A,B):- membermeronym(C,A),membermeronym(A,D),verbgroup(D,B).
memberofdomainregion(A,B):- derivationallyrelatedform(D,A),membermeronym(F,C),verbgroup(C,B),membermeronym(E,D).
memberofdomainregion(A,B):- haspart(B,C),instancehypernym(B,A),haspart(A,D),verbgroup(E,B).
memberofdomainregion(A,B):- memberofdomainusage(E,F),verbgroup(D,B),haspart(B,C),memberofdomainusage(A,F).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),derivationallyrelatedform(D,A),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- instancehypernym(B,E),membermeronym(F,C),similarto(D,F),hypernym(F,A).
memberofdomainregion(A,B):- memberofdomainusage(A,E),verbgroup(B,C),instancehypernym(B,D).
memberofdomainregion(A,B):- haspart(D,B),alsosee(B,A),memberofdomainusage(C,E),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),similarto(D,A),verbgroup(E,F),hypernym(B,F).
memberofdomainregion(A,B):- synsetdomaintopicof(B,D),haspart(B,C),verbgroup(E,F),instancehypernym(F,A).
memberofdomainregion(A,B):- verbgroup(A,E),instancehypernym(F,D),haspart(B,C),haspart(F,B).
memberofdomainregion(A,B):- derivationallyrelatedform(B,D),memberofdomainusage(D,F),membermeronym(F,C),synsetdomaintopicof(A,E).
memberofdomainregion(A,B):- verbgroup(B,D),membermeronym(F,C),membermeronym(C,A),similarto(C,E).
memberofdomainregion(A,B):- instancehypernym(A,B),derivationallyrelatedform(A,D),alsosee(C,A).
memberofdomainregion(A,B):- alsosee(E,C),membermeronym(F,C),similarto(D,A),instancehypernym(B,C).
memberofdomainregion(A,B):- verbgroup(A,C),instancehypernym(E,D),hypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(A,E),haspart(B,C),verbgroup(F,E),derivationallyrelatedform(D,C).
memberofdomainregion(A,B):- alsosee(A,E),haspart(A,D),haspart(B,C),memberofdomainusage(F,D).
memberofdomainregion(A,B):- instancehypernym(C,A),haspart(B,D),verbgroup(D,B).
memberofdomainregion(A,B):- derivationallyrelatedform(D,A),instancehypernym(E,B),verbgroup(C,B),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),similarto(D,F),derivationallyrelatedform(B,D),alsosee(E,A).
memberofdomainregion(A,B):- verbgroup(A,B),synsetdomaintopicof(C,B),similarto(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(E,B),memberofdomainusage(C,A),membermeronym(B,D).
memberofdomainregion(A,B):- instancehypernym(D,B),alsosee(C,A),haspart(B,C),similarto(E,B).
memberofdomainregion(A,B):- instancehypernym(C,A),hypernym(A,D),haspart(B,C),similarto(D,A).
memberofdomainregion(A,B):- haspart(B,C),alsosee(D,E),verbgroup(E,B),verbgroup(A,D).
memberofdomainregion(A,B):- membermeronym(A,C),similarto(C,D),membermeronym(F,C),similarto(B,E).
memberofdomainregion(A,B):- instancehypernym(A,E),memberofdomainusage(E,F),memberofdomainusage(D,E),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(E,C),memberofdomainusage(A,E),membermeronym(D,B),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(B,C),derivationallyrelatedform(A,D),alsosee(B,D),haspart(B,C).
memberofdomainregion(A,B):- alsosee(A,E),hypernym(D,C),memberofdomainusage(F,B),haspart(B,C).
memberofdomainregion(A,B):- alsosee(E,B),instancehypernym(D,B),membermeronym(F,C),verbgroup(A,F).
memberofdomainregion(A,B):- membermeronym(E,C),memberofdomainusage(E,F),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- haspart(D,B),hypernym(B,C),similarto(A,D).
memberofdomainregion(A,B):- synsetdomaintopicof(D,E),memberofdomainusage(E,B),memberofdomainusage(A,D),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(A,E),alsosee(D,B),haspart(B,C),memberofdomainusage(A,F).
memberofdomainregion(A,B):- similarto(A,E),membermeronym(F,C),memberofdomainusage(E,F),alsosee(D,B).
memberofdomainregion(A,B):- similarto(F,D),hypernym(E,A),alsosee(D,B),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(D,A),synsetdomaintopicof(E,D),haspart(B,C),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- verbgroup(D,A),membermeronym(F,C),alsosee(F,B),haspart(E,C).
memberofdomainregion(A,B):- memberofdomainusage(F,A),alsosee(D,F),hypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(E,C),hypernym(F,B),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(A,E),hypernym(F,D),derivationallyrelatedform(A,F),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(A,E),haspart(B,C),membermeronym(E,D),instancehypernym(D,C).
memberofdomainregion(A,B):- memberofdomainusage(D,B),verbgroup(A,E),verbgroup(C,A).
memberofdomainregion(A,B):- membermeronym(B,C),membermeronym(F,C),verbgroup(A,E),derivationallyrelatedform(F,D).
memberofdomainregion(A,B):- haspart(B,C),membermeronym(D,E),verbgroup(E,F),verbgroup(A,D).
memberofdomainregion(A,B):- alsosee(E,C),membermeronym(F,C),derivationallyrelatedform(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(A,D),derivationallyrelatedform(E,D),hypernym(E,C),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(B,C),membermeronym(F,C),verbgroup(E,A),verbgroup(F,D).
memberofdomainregion(A,B):- synsetdomaintopicof(E,A),synsetdomaintopicof(B,F),alsosee(A,D),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(C,A),alsosee(B,C),memberofdomainusage(A,B).
memberofdomainregion(A,B):- haspart(D,B),haspart(E,A),haspart(B,C),membermeronym(F,D).
memberofdomainregion(A,B):- similarto(F,D),haspart(F,E),verbgroup(A,E),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(E,D),derivationallyrelatedform(F,E),haspart(B,C),derivationallyrelatedform(A,E).
memberofdomainregion(A,B):- similarto(E,D),similarto(D,C),hypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(E,A),derivationallyrelatedform(A,D),hypernym(F,B),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(A,B),hypernym(A,B),haspart(A,C).
memberofdomainregion(A,B):- similarto(C,D),similarto(A,D),haspart(B,C),similarto(A,C).
memberofdomainregion(A,B):- haspart(E,D),similarto(D,C),haspart(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,C),memberofdomainusage(B,E),membermeronym(B,D),memberofdomainusage(A,F).
memberofdomainregion(A,B):- haspart(E,F),membermeronym(F,C),instancehypernym(D,A),synsetdomaintopicof(C,B).
memberofdomainregion(A,B):- similarto(A,B),synsetdomaintopicof(E,D),alsosee(D,B),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(C,A),derivationallyrelatedform(A,D),membermeronym(E,B),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(A,D),haspart(B,C),instancehypernym(E,C).
memberofdomainregion(A,B):- membermeronym(A,C),derivationallyrelatedform(C,E),synsetdomaintopicof(B,D).
memberofdomainregion(A,B):- hypernym(D,B),alsosee(A,B),haspart(B,C),memberofdomainusage(A,B).
memberofdomainregion(A,B):- instancehypernym(C,B),similarto(E,A),membermeronym(F,C),haspart(A,D).
memberofdomainregion(A,B):- membermeronym(F,A),memberofdomainusage(F,E),haspart(B,C),hypernym(D,B).
memberofdomainregion(A,B):- haspart(C,A),haspart(A,D),hypernym(D,C),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(F,A),hypernym(A,D),haspart(B,C),similarto(E,D).
memberofdomainregion(A,B):- membermeronym(A,C),instancehypernym(A,E),membermeronym(D,E),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,C),synsetdomaintopicof(D,B),memberofdomainusage(E,D),verbgroup(A,D).
memberofdomainregion(A,B):- alsosee(D,C),instancehypernym(A,D),derivationallyrelatedform(D,A),haspart(B,C).
memberofdomainregion(A,B):- hypernym(A,E),instancehypernym(D,C),hypernym(D,B).
memberofdomainregion(A,B):- haspart(B,C),membermeronym(C,A),membermeronym(D,A),hypernym(A,E).
memberofdomainregion(A,B):- instancehypernym(C,E),memberofdomainusage(A,D),haspart(B,C),memberofdomainusage(A,B).
memberofdomainregion(A,B):- synsetdomaintopicof(C,E),derivationallyrelatedform(E,B),membermeronym(D,A).
memberofdomainregion(A,B):- alsosee(A,C),haspart(A,D),memberofdomainusage(D,E),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(C,B),synsetdomaintopicof(A,D),membermeronym(F,C),haspart(F,E).
memberofdomainregion(A,B):- memberofdomainusage(A,E),hypernym(F,A),haspart(B,C),alsosee(D,F).
memberofdomainregion(A,B):- verbgroup(B,D),verbgroup(A,C),similarto(B,E).
memberofdomainregion(A,B):- membermeronym(F,C),verbgroup(D,B),membermeronym(E,D),memberofdomainusage(A,F).
memberofdomainregion(A,B):- verbgroup(A,C),membermeronym(B,E),derivationallyrelatedform(B,D).
memberofdomainregion(A,B):- haspart(B,E),haspart(D,A),hypernym(E,C).
memberofdomainregion(A,B):- memberofdomainusage(F,E),membermeronym(F,C),memberofdomainusage(E,B),membermeronym(A,D).
memberofdomainregion(A,B):- similarto(A,B),synsetdomaintopicof(A,B),verbgroup(C,A).
