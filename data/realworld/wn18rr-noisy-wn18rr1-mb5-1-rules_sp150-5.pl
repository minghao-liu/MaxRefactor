memberofdomainregion(A,B):- derivationallyrelatedform(D,A),memberofdomainusage(E,B),haspart(E,C),haspart(B,C).
memberofdomainregion(A,B):- similarto(D,E),verbgroup(B,F),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- hypernym(B,E),membermeronym(F,C),derivationallyrelatedform(A,D),hypernym(F,A).
memberofdomainregion(A,B):- synsetdomaintopicof(B,D),membermeronym(F,C),haspart(E,A),synsetdomaintopicof(A,C).
memberofdomainregion(A,B):- alsosee(C,B),haspart(B,C),verbgroup(C,B),instancehypernym(A,C).
memberofdomainregion(A,B):- memberofdomainusage(D,C),memberofdomainusage(B,A),derivationallyrelatedform(D,A).
memberofdomainregion(A,B):- verbgroup(A,B),membermeronym(D,A),similarto(C,A).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),haspart(D,B),hypernym(B,A).
memberofdomainregion(A,B):- alsosee(B,F),alsosee(E,D),hypernym(A,D),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(B,D),verbgroup(A,E),haspart(B,C),membermeronym(A,F).
memberofdomainregion(A,B):- hypernym(B,D),alsosee(B,C),alsosee(D,A).
memberofdomainregion(A,B):- membermeronym(F,C),memberofdomainusage(D,B),haspart(A,F),hypernym(E,F).
memberofdomainregion(A,B):- hypernym(E,D),haspart(B,C),similarto(E,C),instancehypernym(F,A).
memberofdomainregion(A,B):- membermeronym(E,B),memberofdomainusage(A,D),instancehypernym(D,C).
memberofdomainregion(A,B):- similarto(D,B),hypernym(D,A),verbgroup(A,B),haspart(B,C).
memberofdomainregion(A,B):- haspart(C,E),derivationallyrelatedform(B,D),alsosee(E,A).
memberofdomainregion(A,B):- membermeronym(B,F),similarto(A,E),membermeronym(F,C),alsosee(F,D).
memberofdomainregion(A,B):- synsetdomaintopicof(D,E),alsosee(A,E),haspart(B,C),verbgroup(D,E).
memberofdomainregion(A,B):- instancehypernym(E,B),derivationallyrelatedform(D,E),alsosee(B,A),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(A,E),haspart(D,C),haspart(B,C),alsosee(E,A).
memberofdomainregion(A,B):- membermeronym(A,C),haspart(B,E),verbgroup(B,D).
memberofdomainregion(A,B):- instancehypernym(B,E),membermeronym(F,C),instancehypernym(F,A),synsetdomaintopicof(D,F).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),membermeronym(F,C),derivationallyrelatedform(A,D),derivationallyrelatedform(C,E).
memberofdomainregion(A,B):- memberofdomainusage(C,B),memberofdomainusage(C,E),hypernym(A,D).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),derivationallyrelatedform(D,A),verbgroup(E,F),haspart(B,C).
memberofdomainregion(A,B):- hypernym(B,D),alsosee(B,C),memberofdomainusage(C,A).
memberofdomainregion(A,B):- memberofdomainusage(E,C),membermeronym(F,C),instancehypernym(A,D),similarto(B,C).
memberofdomainregion(A,B):- hypernym(B,D),similarto(C,D),membermeronym(B,A).
memberofdomainregion(A,B):- hypernym(C,A),similarto(D,B),verbgroup(C,A).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),alsosee(A,E),similarto(F,C),haspart(B,C).
memberofdomainregion(A,B):- alsosee(D,C),membermeronym(F,C),alsosee(E,B),membermeronym(D,A).
memberofdomainregion(A,B):- derivationallyrelatedform(D,A),synsetdomaintopicof(E,B),memberofdomainusage(C,E).
memberofdomainregion(A,B):- haspart(D,B),haspart(A,D),hypernym(C,D).
memberofdomainregion(A,B):- membermeronym(F,A),similarto(A,E),haspart(B,C),derivationallyrelatedform(D,C).
memberofdomainregion(A,B):- hypernym(E,B),alsosee(D,B),membermeronym(C,A).
memberofdomainregion(A,B):- similarto(A,E),haspart(D,E),memberofdomainusage(C,A),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(E,B),haspart(A,D),haspart(B,C),haspart(D,F).
memberofdomainregion(A,B):- haspart(D,B),alsosee(A,C),similarto(C,E),haspart(B,C).
memberofdomainregion(A,B):- alsosee(A,E),membermeronym(F,C),haspart(B,F),similarto(E,D).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),hypernym(D,A),memberofdomainusage(A,C),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(C,B),membermeronym(C,A),memberofdomainusage(A,D).
memberofdomainregion(A,B):- alsosee(E,A),alsosee(C,A),hypernym(D,B).
memberofdomainregion(A,B):- alsosee(B,A),instancehypernym(D,A),instancehypernym(D,C).
memberofdomainregion(A,B):- membermeronym(A,E),hypernym(F,C),haspart(B,C),alsosee(A,D).
memberofdomainregion(A,B):- memberofdomainusage(D,C),haspart(B,C),instancehypernym(F,A),memberofdomainusage(E,A).
memberofdomainregion(A,B):- verbgroup(A,C),membermeronym(D,B),alsosee(A,B),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,B),instancehypernym(D,C),instancehypernym(B,C).
memberofdomainregion(A,B):- similarto(F,D),similarto(A,F),hypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(A,C),alsosee(A,C),verbgroup(B,D).
memberofdomainregion(A,B):- similarto(C,D),hypernym(D,A),similarto(A,D),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(B,F),membermeronym(F,C),membermeronym(D,E),membermeronym(D,A).
memberofdomainregion(A,B):- synsetdomaintopicof(C,A),similarto(D,C),memberofdomainusage(D,B).
memberofdomainregion(A,B):- hypernym(D,E),synsetdomaintopicof(D,C),alsosee(A,D),haspart(B,C).
memberofdomainregion(A,B):- similarto(A,E),membermeronym(F,C),similarto(C,B),synsetdomaintopicof(D,F).
memberofdomainregion(A,B):- membermeronym(B,A),instancehypernym(D,C),verbgroup(A,D).
memberofdomainregion(A,B):- similarto(A,E),membermeronym(B,C),haspart(D,E),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),instancehypernym(F,E),synsetdomaintopicof(B,D),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(E,B),instancehypernym(A,D),verbgroup(C,B),haspart(B,C).
memberofdomainregion(A,B):- similarto(A,D),similarto(C,B),derivationallyrelatedform(C,D).
memberofdomainregion(A,B):- instancehypernym(B,E),membermeronym(F,C),alsosee(F,D),verbgroup(F,A).
memberofdomainregion(A,B):- membermeronym(A,E),derivationallyrelatedform(F,B),synsetdomaintopicof(D,A),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(A,B),memberofdomainusage(C,A),verbgroup(A,D).
memberofdomainregion(A,B):- alsosee(D,B),derivationallyrelatedform(D,A),synsetdomaintopicof(A,C).
memberofdomainregion(A,B):- verbgroup(D,A),hypernym(A,C),similarto(B,E).
memberofdomainregion(A,B):- haspart(B,E),membermeronym(F,C),similarto(E,F),memberofdomainusage(D,A).
memberofdomainregion(A,B):- alsosee(B,F),derivationallyrelatedform(E,A),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- memberofdomainusage(C,F),alsosee(A,E),instancehypernym(F,D),haspart(B,C).
memberofdomainregion(A,B):- alsosee(E,B),membermeronym(F,C),instancehypernym(D,A),instancehypernym(F,D).
memberofdomainregion(A,B):- hypernym(D,A),membermeronym(C,B),synsetdomaintopicof(D,E).
memberofdomainregion(A,B):- verbgroup(D,C),instancehypernym(B,D),hypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(B,F),membermeronym(F,C),memberofdomainusage(D,B),haspart(E,A).
memberofdomainregion(A,B):- instancehypernym(D,E),derivationallyrelatedform(D,A),verbgroup(C,F),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(C,B),hypernym(C,E),membermeronym(F,C),hypernym(A,D).
memberofdomainregion(A,B):- memberofdomainusage(F,C),derivationallyrelatedform(C,D),haspart(B,C),hypernym(A,E).
memberofdomainregion(A,B):- verbgroup(A,C),instancehypernym(A,D),haspart(B,C),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- hypernym(E,B),instancehypernym(E,D),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- instancehypernym(C,E),synsetdomaintopicof(B,C),haspart(B,C),alsosee(A,D).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),memberofdomainusage(A,E),hypernym(F,D),membermeronym(F,C).
memberofdomainregion(A,B):- synsetdomaintopicof(D,A),synsetdomaintopicof(F,D),verbgroup(A,E),haspart(B,C).
memberofdomainregion(A,B):- similarto(E,C),hypernym(A,E),hypernym(D,B).
memberofdomainregion(A,B):- haspart(D,B),verbgroup(A,D),membermeronym(C,D).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),membermeronym(F,C),similarto(D,F),memberofdomainusage(E,B).
memberofdomainregion(A,B):- instancehypernym(C,B),instancehypernym(C,A),verbgroup(B,D).
memberofdomainregion(A,B):- instancehypernym(B,E),instancehypernym(C,A),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- derivationallyrelatedform(A,D),similarto(F,E),haspart(B,C),verbgroup(D,E).
memberofdomainregion(A,B):- similarto(F,A),haspart(D,A),membermeronym(F,C),memberofdomainusage(B,E).
memberofdomainregion(A,B):- membermeronym(A,C),verbgroup(B,A),similarto(B,C).
memberofdomainregion(A,B):- alsosee(C,B),verbgroup(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- synsetdomaintopicof(C,A),similarto(B,E),alsosee(D,A).
memberofdomainregion(A,B):- derivationallyrelatedform(F,C),membermeronym(E,C),haspart(A,D),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(F,E),alsosee(F,C),alsosee(A,D),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),hypernym(A,C),instancehypernym(C,E),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(A,C),haspart(B,C),hypernym(D,C),membermeronym(D,A).
memberofdomainregion(A,B):- derivationallyrelatedform(E,D),verbgroup(F,C),memberofdomainusage(A,D),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(F,E),alsosee(A,D),haspart(B,C),memberofdomainusage(A,F).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),synsetdomaintopicof(A,D),hypernym(E,C),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(D,C),haspart(B,D),alsosee(B,A).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),membermeronym(B,C),alsosee(C,A),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(E,A),instancehypernym(A,D),instancehypernym(E,A),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(A,C),derivationallyrelatedform(D,B),haspart(C,E),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(A,C),haspart(B,C),derivationallyrelatedform(A,E),memberofdomainusage(C,D).
memberofdomainregion(A,B):- verbgroup(C,D),hypernym(A,E),haspart(B,C),hypernym(D,B).
memberofdomainregion(A,B):- similarto(C,D),alsosee(A,B),synsetdomaintopicof(C,B).
memberofdomainregion(A,B):- verbgroup(F,A),hypernym(A,D),verbgroup(E,F),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(C,B),derivationallyrelatedform(B,A),derivationallyrelatedform(C,A).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),alsosee(D,A),hypernym(E,C),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(E,A),membermeronym(F,C),derivationallyrelatedform(B,D),instancehypernym(A,F).
memberofdomainregion(A,B):- similarto(A,D),synsetdomaintopicof(F,A),alsosee(D,E),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,E),membermeronym(F,C),instancehypernym(D,A),alsosee(F,E).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),membermeronym(F,C),verbgroup(B,C),alsosee(A,D).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),instancehypernym(F,B),membermeronym(F,E),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(C,B),memberofdomainusage(D,B),hypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),alsosee(C,A),verbgroup(A,B),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),derivationallyrelatedform(A,D),haspart(B,C),membermeronym(F,D).
memberofdomainregion(A,B):- membermeronym(A,E),synsetdomaintopicof(C,D),synsetdomaintopicof(B,C).
memberofdomainregion(A,B):- verbgroup(C,D),haspart(B,C),derivationallyrelatedform(D,A),memberofdomainusage(B,D).
memberofdomainregion(A,B):- haspart(E,D),membermeronym(A,E),haspart(B,C),membermeronym(E,A).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),memberofdomainusage(C,F),instancehypernym(D,E),haspart(B,C).
memberofdomainregion(A,B):- hypernym(B,E),hypernym(C,B),memberofdomainusage(D,A).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),haspart(B,D),hypernym(C,D).
memberofdomainregion(A,B):- membermeronym(F,C),instancehypernym(E,D),verbgroup(D,B),similarto(C,A).
memberofdomainregion(A,B):- alsosee(C,E),membermeronym(B,D),similarto(A,C).
memberofdomainregion(A,B):- membermeronym(F,C),haspart(B,D),instancehypernym(C,E),synsetdomaintopicof(A,F).
memberofdomainregion(A,B):- alsosee(C,E),alsosee(A,D),haspart(B,C),membermeronym(F,D).
memberofdomainregion(A,B):- haspart(E,D),haspart(F,E),verbgroup(A,E),haspart(B,C).
memberofdomainregion(A,B):- alsosee(D,E),derivationallyrelatedform(A,C),similarto(E,B).
memberofdomainregion(A,B):- similarto(A,D),alsosee(A,B),alsosee(D,B),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(D,B),membermeronym(C,B),alsosee(A,B),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(B,D),haspart(C,A),alsosee(B,D).
memberofdomainregion(A,B):- hypernym(C,D),alsosee(A,E),haspart(B,C),membermeronym(F,D).
memberofdomainregion(A,B):- similarto(A,D),memberofdomainusage(C,E),haspart(E,C),haspart(B,C).
memberofdomainregion(A,B):- similarto(E,A),membermeronym(D,B),derivationallyrelatedform(B,D),haspart(B,C).
memberofdomainregion(A,B):- similarto(A,D),membermeronym(A,E),instancehypernym(F,E),haspart(B,C).
memberofdomainregion(A,B):- haspart(A,D),haspart(A,F),haspart(B,C),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- similarto(E,D),derivationallyrelatedform(B,D),verbgroup(C,A).
memberofdomainregion(A,B):- similarto(A,D),instancehypernym(D,E),haspart(B,C),memberofdomainusage(C,D).
memberofdomainregion(A,B):- synsetdomaintopicof(E,D),alsosee(B,A),haspart(B,C),hypernym(D,B).
memberofdomainregion(A,B):- haspart(B,E),synsetdomaintopicof(C,A),membermeronym(F,C),alsosee(B,D).
memberofdomainregion(A,B):- hypernym(E,B),membermeronym(F,C),instancehypernym(C,D),memberofdomainusage(D,A).
memberofdomainregion(A,B):- instancehypernym(E,F),similarto(A,F),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(C,B),verbgroup(A,E),instancehypernym(E,D),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(D,A),alsosee(A,C),hypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- haspart(E,D),memberofdomainusage(A,E),derivationallyrelatedform(D,E),haspart(B,C).
memberofdomainregion(A,B):- alsosee(F,A),synsetdomaintopicof(A,E),haspart(B,C),memberofdomainusage(E,D).
memberofdomainregion(A,B):- hypernym(E,D),haspart(B,C),alsosee(E,B),instancehypernym(A,C).
memberofdomainregion(A,B):- derivationallyrelatedform(E,D),membermeronym(F,C),instancehypernym(D,A),haspart(C,B).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),memberofdomainusage(E,C),haspart(B,C),instancehypernym(E,F).
memberofdomainregion(A,B):- instancehypernym(D,B),alsosee(C,A),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- hypernym(E,A),similarto(B,D),derivationallyrelatedform(C,D).
memberofdomainregion(A,B):- haspart(C,A),similarto(B,E),synsetdomaintopicof(D,B).
