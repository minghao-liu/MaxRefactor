memberofdomainregion(A,B):- haspart(D,E),haspart(E,A),verbgroup(D,B),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(E,A),derivationallyrelatedform(C,D),haspart(B,C),memberofdomainusage(A,F).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),derivationallyrelatedform(B,D),similarto(E,B),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(E,C),memberofdomainusage(A,D),haspart(B,C),membermeronym(E,A).
memberofdomainregion(A,B):- verbgroup(A,E),hypernym(D,F),haspart(B,C),alsosee(A,F).
memberofdomainregion(A,B):- instancehypernym(A,E),instancehypernym(E,F),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(D,A),membermeronym(F,C),hypernym(D,C),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- instancehypernym(A,B),membermeronym(A,B),memberofdomainusage(A,B).
memberofdomainregion(A,B):- haspart(C,D),membermeronym(A,E),haspart(B,C),instancehypernym(C,F).
memberofdomainregion(A,B):- membermeronym(B,F),membermeronym(F,C),derivationallyrelatedform(D,E),hypernym(A,E).
memberofdomainregion(A,B):- membermeronym(D,C),hypernym(B,E),membermeronym(F,C),membermeronym(C,A).
memberofdomainregion(A,B):- hypernym(C,B),memberofdomainusage(A,D),memberofdomainusage(E,D).
memberofdomainregion(A,B):- hypernym(E,B),instancehypernym(B,F),membermeronym(F,C),membermeronym(D,A).
memberofdomainregion(A,B):- membermeronym(D,C),instancehypernym(D,A),synsetdomaintopicof(C,B).
memberofdomainregion(A,B):- hypernym(E,A),synsetdomaintopicof(D,B),haspart(B,C),hypernym(D,B).
memberofdomainregion(A,B):- memberofdomainusage(D,C),memberofdomainusage(A,E),synsetdomaintopicof(C,B),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(A,E),synsetdomaintopicof(F,A),alsosee(A,D),haspart(B,C).
memberofdomainregion(A,B):- hypernym(C,A),membermeronym(D,B),derivationallyrelatedform(C,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),derivationallyrelatedform(B,D),hypernym(B,F),membermeronym(E,A).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),membermeronym(F,C),haspart(F,E),derivationallyrelatedform(D,A).
memberofdomainregion(A,B):- membermeronym(D,C),membermeronym(F,C),haspart(B,E),verbgroup(A,D).
memberofdomainregion(A,B):- similarto(A,E),derivationallyrelatedform(D,B),hypernym(B,C).
memberofdomainregion(A,B):- instancehypernym(A,D),verbgroup(A,E),haspart(B,C),verbgroup(C,A).
memberofdomainregion(A,B):- membermeronym(D,B),memberofdomainusage(C,A),haspart(B,C),similarto(D,A).
memberofdomainregion(A,B):- memberofdomainusage(D,C),membermeronym(A,E),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- alsosee(D,B),memberofdomainusage(B,A),haspart(B,C),haspart(A,C).
memberofdomainregion(A,B):- membermeronym(A,E),membermeronym(E,F),verbgroup(D,B),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),alsosee(C,F),haspart(B,C),memberofdomainusage(E,D).
memberofdomainregion(A,B):- membermeronym(F,C),synsetdomaintopicof(D,B),derivationallyrelatedform(E,A),derivationallyrelatedform(C,E).
memberofdomainregion(A,B):- verbgroup(E,A),membermeronym(F,C),haspart(B,D),similarto(F,B).
memberofdomainregion(A,B):- membermeronym(F,C),hypernym(A,F),synsetdomaintopicof(D,B),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- instancehypernym(A,E),membermeronym(F,C),haspart(B,C),memberofdomainusage(E,D).
memberofdomainregion(A,B):- instancehypernym(A,B),verbgroup(A,C),verbgroup(C,B).
memberofdomainregion(A,B):- instancehypernym(B,E),synsetdomaintopicof(B,D),derivationallyrelatedform(A,D),haspart(B,C).
memberofdomainregion(A,B):- hypernym(C,A),membermeronym(F,C),verbgroup(B,E),alsosee(D,F).
memberofdomainregion(A,B):- verbgroup(E,A),membermeronym(F,C),alsosee(E,C),alsosee(B,D).
memberofdomainregion(A,B):- membermeronym(F,C),memberofdomainusage(B,E),derivationallyrelatedform(C,A),alsosee(D,E).
memberofdomainregion(A,B):- hypernym(F,E),haspart(B,D),hypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- hypernym(C,D),membermeronym(B,E),verbgroup(A,E),haspart(B,C).
memberofdomainregion(A,B):- hypernym(E,B),similarto(D,A),similarto(E,C).
memberofdomainregion(A,B):- derivationallyrelatedform(B,C),haspart(A,E),haspart(B,C),membermeronym(C,D).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),hypernym(D,A),similarto(F,D),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(A,E),instancehypernym(A,D),memberofdomainusage(C,B).
memberofdomainregion(A,B):- synsetdomaintopicof(B,D),verbgroup(A,E),haspart(B,C),alsosee(C,D).
memberofdomainregion(A,B):- instancehypernym(E,B),derivationallyrelatedform(B,D),haspart(B,C),haspart(A,C).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),membermeronym(F,C),haspart(D,A),synsetdomaintopicof(A,C).
memberofdomainregion(A,B):- membermeronym(F,C),memberofdomainusage(B,E),haspart(F,D),hypernym(A,F).
memberofdomainregion(A,B):- hypernym(B,E),membermeronym(C,A),membermeronym(E,D).
memberofdomainregion(A,B):- alsosee(C,E),alsosee(A,D),haspart(B,C),alsosee(E,A).
memberofdomainregion(A,B):- verbgroup(B,F),membermeronym(F,C),memberofdomainusage(D,E),alsosee(A,E).
memberofdomainregion(A,B):- hypernym(E,D),membermeronym(A,E),haspart(B,C),verbgroup(C,E).
memberofdomainregion(A,B):- instancehypernym(A,E),instancehypernym(D,E),alsosee(A,B),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),haspart(B,C),verbgroup(C,E),alsosee(E,A).
memberofdomainregion(A,B):- instancehypernym(A,E),derivationallyrelatedform(A,D),verbgroup(C,B).
memberofdomainregion(A,B):- alsosee(A,E),hypernym(B,C),membermeronym(F,C),memberofdomainusage(B,D).
memberofdomainregion(A,B):- similarto(D,C),similarto(B,D),memberofdomainusage(E,A).
memberofdomainregion(A,B):- similarto(D,B),membermeronym(F,C),synsetdomaintopicof(C,D),hypernym(A,E).
memberofdomainregion(A,B):- instancehypernym(B,E),alsosee(D,B),haspart(B,C),similarto(D,A).
memberofdomainregion(A,B):- instancehypernym(A,E),verbgroup(C,D),membermeronym(D,E),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(D,C),memberofdomainusage(D,B),instancehypernym(E,A).
memberofdomainregion(A,B):- alsosee(A,E),membermeronym(F,C),haspart(F,E),instancehypernym(B,D).
memberofdomainregion(A,B):- instancehypernym(F,E),derivationallyrelatedform(F,D),haspart(B,C),memberofdomainusage(A,F).
memberofdomainregion(A,B):- verbgroup(E,D),instancehypernym(A,D),haspart(B,F),haspart(B,C).
memberofdomainregion(A,B):- alsosee(E,A),hypernym(C,B),haspart(B,C),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- synsetdomaintopicof(E,B),hypernym(A,D),haspart(B,C),hypernym(E,F).
memberofdomainregion(A,B):- similarto(A,E),alsosee(C,F),instancehypernym(B,D),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(D,E),instancehypernym(A,D),derivationallyrelatedform(D,A),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(C,B),instancehypernym(A,B),hypernym(C,B).
memberofdomainregion(A,B):- alsosee(D,C),similarto(C,B),synsetdomaintopicof(A,C).
memberofdomainregion(A,B):- haspart(D,B),synsetdomaintopicof(E,D),memberofdomainusage(C,A),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(A,D),membermeronym(E,D),haspart(C,B).
memberofdomainregion(A,B):- haspart(E,A),memberofdomainusage(A,E),derivationallyrelatedform(E,D),haspart(B,C).
memberofdomainregion(A,B):- alsosee(B,D),memberofdomainusage(B,D),verbgroup(C,A).
memberofdomainregion(A,B):- memberofdomainusage(E,C),haspart(B,C),alsosee(A,D),verbgroup(B,A).
memberofdomainregion(A,B):- haspart(E,A),membermeronym(F,C),verbgroup(B,C),verbgroup(D,F).
memberofdomainregion(A,B):- instancehypernym(D,B),instancehypernym(E,B),membermeronym(A,B),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(D,E),membermeronym(A,D),instancehypernym(B,C).
memberofdomainregion(A,B):- verbgroup(A,F),membermeronym(F,C),alsosee(B,D),haspart(E,B).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(D,B),similarto(F,E),hypernym(A,F).
memberofdomainregion(A,B):- haspart(E,B),similarto(A,F),alsosee(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(D,B),synsetdomaintopicof(F,B),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- haspart(A,D),membermeronym(D,B),haspart(B,C),memberofdomainusage(E,A).
memberofdomainregion(A,B):- similarto(D,B),derivationallyrelatedform(B,A),verbgroup(D,B),haspart(B,C).
memberofdomainregion(A,B):- hypernym(B,D),hypernym(D,E),membermeronym(F,C),synsetdomaintopicof(A,C).
memberofdomainregion(A,B):- verbgroup(B,D),similarto(D,A),similarto(D,B),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(A,B),alsosee(B,C),haspart(C,D).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(D,B),alsosee(C,A),hypernym(E,A).
memberofdomainregion(A,B):- verbgroup(B,F),membermeronym(A,E),instancehypernym(D,A),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(A,B),alsosee(D,A),alsosee(A,D),haspart(B,C).
memberofdomainregion(A,B):- hypernym(E,B),membermeronym(B,C),membermeronym(F,C),memberofdomainusage(A,D).
memberofdomainregion(A,B):- instancehypernym(A,E),verbgroup(A,C),derivationallyrelatedform(C,D),haspart(B,C).
memberofdomainregion(A,B):- hypernym(C,A),hypernym(B,C),derivationallyrelatedform(D,A).
memberofdomainregion(A,B):- similarto(A,E),synsetdomaintopicof(A,E),haspart(B,C),membermeronym(E,D).
memberofdomainregion(A,B):- derivationallyrelatedform(A,B),hypernym(B,C),membermeronym(B,D).
memberofdomainregion(A,B):- verbgroup(D,A),haspart(B,C),alsosee(A,D),haspart(A,B).
memberofdomainregion(A,B):- hypernym(B,D),membermeronym(F,C),derivationallyrelatedform(A,F),hypernym(A,E).
memberofdomainregion(A,B):- instancehypernym(B,E),verbgroup(D,C),haspart(A,D).
memberofdomainregion(A,B):- instancehypernym(A,E),similarto(D,A),haspart(B,C),similarto(C,A).
memberofdomainregion(A,B):- membermeronym(F,C),hypernym(E,A),memberofdomainusage(B,D),verbgroup(C,A).
memberofdomainregion(A,B):- alsosee(E,F),membermeronym(F,C),haspart(D,A),membermeronym(F,B).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),memberofdomainusage(B,C),hypernym(A,D).
memberofdomainregion(A,B):- memberofdomainusage(B,C),synsetdomaintopicof(D,A),membermeronym(E,C).
memberofdomainregion(A,B):- membermeronym(F,C),synsetdomaintopicof(A,F),alsosee(B,E),hypernym(D,F).
memberofdomainregion(A,B):- membermeronym(A,C),hypernym(A,B),synsetdomaintopicof(B,C).
memberofdomainregion(A,B):- similarto(D,B),membermeronym(F,C),similarto(E,C),memberofdomainusage(C,A).
memberofdomainregion(A,B):- verbgroup(D,C),similarto(A,D),synsetdomaintopicof(B,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(E,D),memberofdomainusage(A,E),alsosee(B,D),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(B,D),verbgroup(C,B),verbgroup(A,B).
memberofdomainregion(A,B):- similarto(A,E),similarto(F,D),alsosee(F,E),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),instancehypernym(E,B),membermeronym(C,A),hypernym(A,D).
memberofdomainregion(A,B):- membermeronym(F,C),instancehypernym(F,E),haspart(B,D),instancehypernym(A,F).
memberofdomainregion(A,B):- synsetdomaintopicof(E,B),hypernym(D,E),membermeronym(F,C),similarto(C,A).
memberofdomainregion(A,B):- hypernym(B,E),membermeronym(F,C),alsosee(A,D),synsetdomaintopicof(C,A).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),verbgroup(A,B),hypernym(B,A).
memberofdomainregion(A,B):- similarto(E,C),hypernym(A,E),haspart(B,C),hypernym(D,B).
memberofdomainregion(A,B):- synsetdomaintopicof(B,A),derivationallyrelatedform(E,D),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- membermeronym(F,C),verbgroup(C,B),similarto(E,B),memberofdomainusage(D,A).
memberofdomainregion(A,B):- instancehypernym(A,B),haspart(A,D),derivationallyrelatedform(C,D),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(E,D),memberofdomainusage(A,E),verbgroup(B,C),membermeronym(F,C).
memberofdomainregion(A,B):- membermeronym(C,F),verbgroup(F,D),haspart(B,C),synsetdomaintopicof(A,E).
memberofdomainregion(A,B):- alsosee(A,C),verbgroup(B,C),verbgroup(D,B).
memberofdomainregion(A,B):- alsosee(F,A),instancehypernym(D,B),memberofdomainusage(B,E),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(E,D),membermeronym(F,C),verbgroup(B,C),alsosee(A,D).
memberofdomainregion(A,B):- alsosee(E,D),membermeronym(A,E),haspart(B,C),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- membermeronym(B,F),hypernym(F,D),hypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(E,C),haspart(C,A),membermeronym(D,B),haspart(B,C).
memberofdomainregion(A,B):- haspart(D,E),hypernym(D,E),membermeronym(A,E),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,C),memberofdomainusage(A,D),instancehypernym(D,C),hypernym(E,A).
memberofdomainregion(A,B):- membermeronym(F,A),instancehypernym(E,B),instancehypernym(F,D),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),instancehypernym(D,A),synsetdomaintopicof(E,C),haspart(B,C).
memberofdomainregion(A,B):- similarto(A,E),membermeronym(F,C),alsosee(D,B),memberofdomainusage(C,A).
memberofdomainregion(A,B):- verbgroup(A,C),memberofdomainusage(B,D),verbgroup(A,D).
memberofdomainregion(A,B):- instancehypernym(A,E),synsetdomaintopicof(A,D),derivationallyrelatedform(D,A),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(D,C),hypernym(D,A),derivationallyrelatedform(E,B).
memberofdomainregion(A,B):- membermeronym(D,B),memberofdomainusage(B,E),synsetdomaintopicof(F,A),haspart(B,C).
memberofdomainregion(A,B):- haspart(D,B),instancehypernym(B,D),alsosee(C,A),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,E),derivationallyrelatedform(D,B),membermeronym(F,C),membermeronym(C,A).
memberofdomainregion(A,B):- synsetdomaintopicof(D,A),similarto(C,B),synsetdomaintopicof(E,C).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),verbgroup(D,C),alsosee(C,A),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(C,B),synsetdomaintopicof(B,D),haspart(B,C),alsosee(A,E).
memberofdomainregion(A,B):- hypernym(E,B),alsosee(D,F),hypernym(A,D),haspart(B,C).
memberofdomainregion(A,B):- similarto(A,D),memberofdomainusage(B,E),haspart(B,C),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- alsosee(B,D),hypernym(E,C),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- instancehypernym(C,B),verbgroup(D,C),instancehypernym(A,C).
memberofdomainregion(A,B):- membermeronym(F,A),membermeronym(B,E),haspart(D,B),haspart(B,C).
memberofdomainregion(A,B):- similarto(A,E),instancehypernym(D,E),synsetdomaintopicof(F,E),haspart(B,C).
memberofdomainregion(A,B):- hypernym(C,D),synsetdomaintopicof(E,A),similarto(D,B).
memberofdomainregion(A,B):- instancehypernym(D,B),synsetdomaintopicof(D,E),instancehypernym(A,C).
memberofdomainregion(A,B):- membermeronym(A,C),haspart(B,C),derivationallyrelatedform(A,D),verbgroup(B,A).
memberofdomainregion(A,B):- verbgroup(E,D),synsetdomaintopicof(A,C),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- instancehypernym(B,E),membermeronym(F,C),hypernym(A,C),membermeronym(A,D).
memberofdomainregion(A,B):- membermeronym(A,C),synsetdomaintopicof(E,D),hypernym(B,D).
memberofdomainregion(A,B):- similarto(E,A),membermeronym(F,C),instancehypernym(A,D),verbgroup(C,B).
memberofdomainregion(A,B):- synsetdomaintopicof(E,B),derivationallyrelatedform(D,B),derivationallyrelatedform(D,A),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(A,C),hypernym(D,A),instancehypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(D,A),membermeronym(F,C),synsetdomaintopicof(F,A),verbgroup(B,E).
memberofdomainregion(A,B):- derivationallyrelatedform(E,F),alsosee(A,E),haspart(B,C),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(E,B),memberofdomainusage(D,A),synsetdomaintopicof(A,C).
memberofdomainregion(A,B):- haspart(B,C),derivationallyrelatedform(D,C),memberofdomainusage(E,F),instancehypernym(F,A).
memberofdomainregion(A,B):- hypernym(C,E),instancehypernym(E,B),hypernym(A,D).
memberofdomainregion(A,B):- instancehypernym(D,B),haspart(E,A),similarto(C,D),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(B,D),verbgroup(A,B),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- similarto(B,E),alsosee(C,E),alsosee(A,D).
memberofdomainregion(A,B):- membermeronym(F,C),derivationallyrelatedform(A,D),similarto(B,C),haspart(A,E).
memberofdomainregion(A,B):- membermeronym(D,C),memberofdomainusage(D,B),haspart(B,C),memberofdomainusage(E,A).
memberofdomainregion(A,B):- alsosee(A,C),instancehypernym(D,B),instancehypernym(E,C).
memberofdomainregion(A,B):- alsosee(B,F),membermeronym(F,C),derivationallyrelatedform(A,D),alsosee(E,A).
memberofdomainregion(A,B):- haspart(D,A),memberofdomainusage(B,D),similarto(C,A).
memberofdomainregion(A,B):- verbgroup(B,D),alsosee(C,F),membermeronym(A,E),haspart(B,C).
memberofdomainregion(A,B):- similarto(A,D),alsosee(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(D,B),memberofdomainusage(B,A),haspart(B,C),memberofdomainusage(A,B).
memberofdomainregion(A,B):- instancehypernym(A,D),alsosee(C,A),haspart(B,C),alsosee(E,A).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),similarto(C,B),instancehypernym(E,D).
memberofdomainregion(A,B):- memberofdomainusage(E,B),membermeronym(A,D),instancehypernym(D,C).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),membermeronym(F,C),haspart(E,A),haspart(F,B).
memberofdomainregion(A,B):- membermeronym(F,C),similarto(C,B),synsetdomaintopicof(D,A),derivationallyrelatedform(E,B).
memberofdomainregion(A,B):- verbgroup(B,D),synsetdomaintopicof(C,A),similarto(A,C).
memberofdomainregion(A,B):- hypernym(D,E),similarto(D,B),alsosee(C,A).
memberofdomainregion(A,B):- instancehypernym(C,B),haspart(D,C),membermeronym(E,A).
memberofdomainregion(A,B):- hypernym(C,D),memberofdomainusage(A,E),instancehypernym(F,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(A,C),membermeronym(F,C),membermeronym(B,E),memberofdomainusage(E,D).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),membermeronym(F,C),membermeronym(E,F),derivationallyrelatedform(F,B).
memberofdomainregion(A,B):- alsosee(E,C),alsosee(A,D),haspart(B,C),verbgroup(F,B).
memberofdomainregion(A,B):- similarto(A,E),membermeronym(F,C),haspart(F,E),hypernym(D,B).
memberofdomainregion(A,B):- instancehypernym(A,B),haspart(A,D),haspart(E,C),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,C),memberofdomainusage(C,E),instancehypernym(F,A),hypernym(A,D).
memberofdomainregion(A,B):- similarto(A,D),verbgroup(F,E),haspart(B,C),instancehypernym(B,F).
memberofdomainregion(A,B):- membermeronym(D,C),similarto(F,B),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- similarto(A,D),similarto(C,A),haspart(B,C),membermeronym(E,A).
memberofdomainregion(A,B):- instancehypernym(D,B),haspart(C,D),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- membermeronym(A,C),instancehypernym(D,B),verbgroup(C,E).
memberofdomainregion(A,B):- verbgroup(D,A),similarto(E,B),haspart(B,C),memberofdomainusage(A,F).
memberofdomainregion(A,B):- haspart(B,C),derivationallyrelatedform(B,D),memberofdomainusage(A,D),membermeronym(E,D).
memberofdomainregion(A,B):- alsosee(C,E),memberofdomainusage(C,E),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- derivationallyrelatedform(A,B),alsosee(A,E),derivationallyrelatedform(E,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),verbgroup(E,B),instancehypernym(A,C),verbgroup(D,E).
memberofdomainregion(A,B):- alsosee(B,D),memberofdomainusage(A,C),membermeronym(D,A).
memberofdomainregion(A,B):- derivationallyrelatedform(F,E),hypernym(A,F),memberofdomainusage(A,D),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(C,A),similarto(D,B),membermeronym(D,A).
memberofdomainregion(A,B):- similarto(A,B),synsetdomaintopicof(A,C).
