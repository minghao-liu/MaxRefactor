memberofdomainregion(A,B):- similarto(A,D),haspart(C,D),instancehypernym(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(A,D),instancehypernym(C,A),synsetdomaintopicof(B,D),haspart(B,C).
memberofdomainregion(A,B):- similarto(B,F),haspart(E,B),membermeronym(F,C),synsetdomaintopicof(D,A).
memberofdomainregion(A,B):- haspart(F,D),instancehypernym(A,D),haspart(B,C),hypernym(E,F).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),haspart(B,C),alsosee(C,E),verbgroup(E,B).
memberofdomainregion(A,B):- instancehypernym(A,E),verbgroup(E,D),haspart(B,C),memberofdomainusage(A,F).
memberofdomainregion(A,B):- hypernym(A,F),haspart(B,D),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- verbgroup(B,D),memberofdomainusage(B,C),similarto(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(D,B),instancehypernym(C,D),alsosee(C,A).
memberofdomainregion(A,B):- membermeronym(F,C),hypernym(A,F),memberofdomainusage(E,D),memberofdomainusage(B,D).
memberofdomainregion(A,B):- alsosee(A,E),hypernym(B,C),membermeronym(F,C),memberofdomainusage(A,D).
memberofdomainregion(A,B):- similarto(C,D),hypernym(A,B),derivationallyrelatedform(A,D),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(A,E),verbgroup(A,F),haspart(B,C),instancehypernym(D,C).
memberofdomainregion(A,B):- membermeronym(A,E),memberofdomainusage(D,B),membermeronym(F,C),instancehypernym(D,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),membermeronym(F,C),haspart(D,E),similarto(B,C).
memberofdomainregion(A,B):- instancehypernym(D,B),membermeronym(F,C),synsetdomaintopicof(A,C),similarto(C,E).
memberofdomainregion(A,B):- haspart(E,B),memberofdomainusage(A,C),memberofdomainusage(B,D).
memberofdomainregion(A,B):- similarto(A,D),instancehypernym(D,E),instancehypernym(D,A),haspart(B,C).
memberofdomainregion(A,B):- hypernym(F,B),derivationallyrelatedform(A,D),haspart(B,C),synsetdomaintopicof(A,E).
memberofdomainregion(A,B):- memberofdomainusage(A,E),alsosee(A,D),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- haspart(E,D),alsosee(A,E),haspart(B,C),similarto(F,B).
memberofdomainregion(A,B):- hypernym(D,C),verbgroup(A,E),haspart(B,C),membermeronym(C,D).
memberofdomainregion(A,B):- instancehypernym(A,E),similarto(A,D),derivationallyrelatedform(C,B).
memberofdomainregion(A,B):- alsosee(C,D),haspart(C,A),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- instancehypernym(B,E),similarto(D,A),synsetdomaintopicof(C,A).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),haspart(D,C),haspart(B,C),similarto(C,A).
memberofdomainregion(A,B):- instancehypernym(A,D),membermeronym(C,E),hypernym(F,C),haspart(B,C).
memberofdomainregion(A,B):- similarto(F,E),hypernym(C,F),haspart(B,C),alsosee(A,D).
memberofdomainregion(A,B):- alsosee(A,D),instancehypernym(A,C),haspart(C,B).
memberofdomainregion(A,B):- hypernym(B,E),haspart(D,A),verbgroup(C,E).
memberofdomainregion(A,B):- membermeronym(D,B),memberofdomainusage(A,C),haspart(B,D),haspart(B,C).
memberofdomainregion(A,B):- alsosee(D,C),synsetdomaintopicof(D,A),instancehypernym(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(D,E),verbgroup(E,F),haspart(B,C),hypernym(A,E).
memberofdomainregion(A,B):- memberofdomainusage(D,C),similarto(C,B),derivationallyrelatedform(D,A).
memberofdomainregion(A,B):- membermeronym(F,C),verbgroup(E,C),synsetdomaintopicof(B,D),instancehypernym(A,C).
memberofdomainregion(A,B):- memberofdomainusage(B,C),membermeronym(F,C),memberofdomainusage(E,F),haspart(A,D).
memberofdomainregion(A,B):- verbgroup(F,D),derivationallyrelatedform(E,D),haspart(B,C),memberofdomainusage(A,F).
memberofdomainregion(A,B):- hypernym(B,D),synsetdomaintopicof(E,B),memberofdomainusage(A,C).
memberofdomainregion(A,B):- alsosee(C,F),synsetdomaintopicof(D,B),haspart(B,C),membermeronym(E,A).
memberofdomainregion(A,B):- haspart(B,C),memberofdomainusage(B,E),haspart(D,A),instancehypernym(A,C).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),alsosee(F,E),haspart(B,C),alsosee(A,F).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),instancehypernym(B,E),membermeronym(F,C),synsetdomaintopicof(C,A).
memberofdomainregion(A,B):- haspart(D,E),similarto(A,D),alsosee(F,B),haspart(B,C).
memberofdomainregion(A,B):- similarto(A,E),similarto(B,D),verbgroup(A,B),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,C),synsetdomaintopicof(F,B),memberofdomainusage(B,D),haspart(A,E).
memberofdomainregion(A,B):- similarto(E,A),similarto(D,C),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(A,E),haspart(B,C),hypernym(C,E),instancehypernym(D,C).
memberofdomainregion(A,B):- haspart(E,D),membermeronym(F,C),hypernym(D,B),membermeronym(A,F).
memberofdomainregion(A,B):- derivationallyrelatedform(A,B),verbgroup(B,C),derivationallyrelatedform(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),memberofdomainusage(A,C),verbgroup(A,B).
memberofdomainregion(A,B):- alsosee(A,E),derivationallyrelatedform(D,B),membermeronym(F,C),instancehypernym(A,F).
memberofdomainregion(A,B):- similarto(B,A),synsetdomaintopicof(A,C),memberofdomainusage(A,B).
memberofdomainregion(A,B):- haspart(E,B),membermeronym(F,C),instancehypernym(D,E),memberofdomainusage(A,F).
memberofdomainregion(A,B):- hypernym(A,C),hypernym(A,B),haspart(B,C),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- instancehypernym(C,B),haspart(B,A),alsosee(B,A).
memberofdomainregion(A,B):- memberofdomainusage(D,B),verbgroup(D,B),haspart(B,C),similarto(D,A).
memberofdomainregion(A,B):- derivationallyrelatedform(B,A),hypernym(A,B),similarto(B,A).
memberofdomainregion(A,B):- hypernym(D,E),alsosee(A,E),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(E,A),membermeronym(C,B),membermeronym(F,C),synsetdomaintopicof(D,F).
memberofdomainregion(A,B):- haspart(B,C),alsosee(F,E),memberofdomainusage(B,D),memberofdomainusage(A,F).
memberofdomainregion(A,B):- hypernym(D,B),similarto(C,A),haspart(B,C),memberofdomainusage(C,D).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),haspart(D,A),similarto(C,E).
memberofdomainregion(A,B):- similarto(D,A),hypernym(D,C),haspart(B,C),haspart(A,C).
memberofdomainregion(A,B):- hypernym(B,C),membermeronym(F,C),membermeronym(D,E),alsosee(D,A).
memberofdomainregion(A,B):- derivationallyrelatedform(D,A),memberofdomainusage(C,B),membermeronym(F,C),haspart(E,D).
memberofdomainregion(A,B):- memberofdomainusage(B,C),instancehypernym(A,D),hypernym(C,E),haspart(B,C).
memberofdomainregion(A,B):- similarto(D,C),membermeronym(F,C),derivationallyrelatedform(A,D),instancehypernym(E,B).
memberofdomainregion(A,B):- hypernym(B,E),instancehypernym(A,D),verbgroup(D,F),haspart(B,C).
memberofdomainregion(A,B):- haspart(E,A),derivationallyrelatedform(C,D),synsetdomaintopicof(C,B).
memberofdomainregion(A,B):- instancehypernym(A,D),hypernym(F,A),similarto(E,F),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(E,D),haspart(A,D),instancehypernym(F,D),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(A,E),membermeronym(F,C),synsetdomaintopicof(B,D),membermeronym(A,F).
memberofdomainregion(A,B):- alsosee(B,C),memberofdomainusage(D,B),synsetdomaintopicof(A,C),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(D,E),haspart(E,A),haspart(B,C).
memberofdomainregion(A,B):- hypernym(B,E),haspart(B,C),verbgroup(A,E),instancehypernym(D,C).
memberofdomainregion(A,B):- instancehypernym(A,E),instancehypernym(D,E),membermeronym(D,B),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(A,C),instancehypernym(A,E),alsosee(A,D),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(A,E),membermeronym(E,A),haspart(B,C),membermeronym(C,D).
memberofdomainregion(A,B):- instancehypernym(D,B),instancehypernym(C,A),haspart(B,C),derivationallyrelatedform(D,B).
memberofdomainregion(A,B):- instancehypernym(A,E),membermeronym(E,F),verbgroup(E,D),haspart(B,C).
memberofdomainregion(A,B):- similarto(A,D),memberofdomainusage(D,B),instancehypernym(B,D),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(C,E),memberofdomainusage(A,D),haspart(B,C),synsetdomaintopicof(E,F).
memberofdomainregion(A,B):- synsetdomaintopicof(C,E),hypernym(D,A),membermeronym(F,C),membermeronym(F,B).
memberofdomainregion(A,B):- verbgroup(D,C),instancehypernym(C,A),similarto(D,B),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(A,C),haspart(B,D),similarto(D,B),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(B,C),similarto(A,D),haspart(A,E).
memberofdomainregion(A,B):- instancehypernym(A,E),haspart(B,C),haspart(C,E),membermeronym(B,D).
memberofdomainregion(A,B):- synsetdomaintopicof(E,C),alsosee(F,C),memberofdomainusage(A,D),haspart(B,C).
memberofdomainregion(A,B):- hypernym(E,C),similarto(D,B),memberofdomainusage(C,A).
memberofdomainregion(A,B):- membermeronym(B,E),hypernym(A,D),memberofdomainusage(C,D).
memberofdomainregion(A,B):- instancehypernym(D,B),memberofdomainusage(A,E),instancehypernym(A,C).
memberofdomainregion(A,B):- verbgroup(E,A),memberofdomainusage(C,B),membermeronym(D,B),membermeronym(F,C).
memberofdomainregion(A,B):- memberofdomainusage(C,B),hypernym(E,A),membermeronym(F,C),instancehypernym(D,A).
memberofdomainregion(A,B):- verbgroup(E,D),membermeronym(F,C),derivationallyrelatedform(C,B),memberofdomainusage(A,D).
memberofdomainregion(A,B):- membermeronym(F,A),hypernym(D,E),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- similarto(A,E),haspart(B,C),hypernym(C,E),membermeronym(B,D).
memberofdomainregion(A,B):- verbgroup(A,E),memberofdomainusage(F,E),haspart(B,C),alsosee(F,D).
memberofdomainregion(A,B):- similarto(C,D),instancehypernym(E,B),haspart(B,C),alsosee(E,A).
memberofdomainregion(A,B):- alsosee(A,C),memberofdomainusage(B,C),haspart(D,A).
memberofdomainregion(A,B):- synsetdomaintopicof(C,A),memberofdomainusage(B,E),haspart(B,D).
memberofdomainregion(A,B):- membermeronym(F,C),synsetdomaintopicof(C,D),derivationallyrelatedform(E,A),memberofdomainusage(B,D).
memberofdomainregion(A,B):- verbgroup(B,D),verbgroup(A,E),synsetdomaintopicof(C,B),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),hypernym(A,D),derivationallyrelatedform(C,B).
memberofdomainregion(A,B):- alsosee(A,B),memberofdomainusage(B,D),similarto(A,C).
memberofdomainregion(A,B):- verbgroup(D,A),membermeronym(F,C),memberofdomainusage(E,F),alsosee(E,B).
memberofdomainregion(A,B):- hypernym(C,A),memberofdomainusage(E,B),haspart(B,C),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- alsosee(D,F),membermeronym(A,E),haspart(B,C),memberofdomainusage(A,F).
memberofdomainregion(A,B):- instancehypernym(E,B),memberofdomainusage(B,E),derivationallyrelatedform(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(C,A),membermeronym(A,D),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- similarto(A,F),alsosee(F,E),verbgroup(D,B),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),haspart(F,D),derivationallyrelatedform(B,D),instancehypernym(E,A).
memberofdomainregion(A,B):- alsosee(F,A),similarto(A,E),haspart(B,C),alsosee(F,D).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),hypernym(E,A),instancehypernym(D,C).
memberofdomainregion(A,B):- verbgroup(D,A),haspart(B,C),haspart(A,B),verbgroup(A,D).
memberofdomainregion(A,B):- instancehypernym(B,D),synsetdomaintopicof(B,C),verbgroup(C,A).
memberofdomainregion(A,B):- similarto(A,B),hypernym(E,D),similarto(A,D),haspart(B,C).
memberofdomainregion(A,B):- alsosee(C,B),instancehypernym(C,D),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- hypernym(B,D),instancehypernym(C,A),haspart(D,C).
memberofdomainregion(A,B):- haspart(E,B),memberofdomainusage(D,B),derivationallyrelatedform(D,A),haspart(B,C).
memberofdomainregion(A,B):- similarto(A,D),membermeronym(F,C),derivationallyrelatedform(F,E),membermeronym(F,B).
memberofdomainregion(A,B):- membermeronym(D,B),verbgroup(A,E),verbgroup(B,C).
memberofdomainregion(A,B):- hypernym(E,B),haspart(B,C),hypernym(D,C),instancehypernym(A,C).
memberofdomainregion(A,B):- membermeronym(A,C),haspart(B,E),alsosee(D,A).
memberofdomainregion(A,B):- hypernym(A,C),derivationallyrelatedform(B,A),verbgroup(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,F),verbgroup(A,E),haspart(B,C),alsosee(C,D).
memberofdomainregion(A,B):- memberofdomainusage(D,B),membermeronym(E,A),haspart(B,C),memberofdomainusage(E,A).
memberofdomainregion(A,B):- similarto(A,E),haspart(E,C),memberofdomainusage(D,E),haspart(B,C).
memberofdomainregion(A,B):- similarto(A,E),alsosee(C,F),haspart(B,C),membermeronym(E,D).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),membermeronym(F,C),synsetdomaintopicof(A,C),verbgroup(D,E).
memberofdomainregion(A,B):- alsosee(C,B),memberofdomainusage(E,B),memberofdomainusage(A,D),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(A,C),alsosee(B,D),hypernym(B,A).
memberofdomainregion(A,B):- membermeronym(D,C),alsosee(B,C),similarto(A,C).
memberofdomainregion(A,B):- similarto(A,D),haspart(B,C),membermeronym(D,E),instancehypernym(A,C).
memberofdomainregion(A,B):- alsosee(A,E),haspart(B,C),verbgroup(C,E),memberofdomainusage(E,D).
memberofdomainregion(A,B):- verbgroup(B,D),haspart(B,A),hypernym(A,C).
memberofdomainregion(A,B):- verbgroup(D,C),membermeronym(D,B),alsosee(A,B).
memberofdomainregion(A,B):- haspart(D,E),hypernym(A,F),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- memberofdomainusage(B,C),memberofdomainusage(A,E),memberofdomainusage(D,B),haspart(B,C).
memberofdomainregion(A,B):- similarto(A,E),haspart(F,B),hypernym(D,F),haspart(B,C).
memberofdomainregion(A,B):- alsosee(E,C),memberofdomainusage(D,B),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(C,E),alsosee(A,D),haspart(B,C),memberofdomainusage(F,D).
memberofdomainregion(A,B):- instancehypernym(D,B),membermeronym(F,C),alsosee(F,E),memberofdomainusage(C,A).
memberofdomainregion(A,B):- hypernym(C,A),verbgroup(D,C),verbgroup(C,B).
memberofdomainregion(A,B):- hypernym(A,C),membermeronym(F,C),memberofdomainusage(E,F),derivationallyrelatedform(B,D).
memberofdomainregion(A,B):- alsosee(C,E),membermeronym(F,C),haspart(A,D),synsetdomaintopicof(B,F).
memberofdomainregion(A,B):- membermeronym(E,D),membermeronym(F,C),memberofdomainusage(D,A),haspart(C,B).
memberofdomainregion(A,B):- haspart(A,D),haspart(E,C),alsosee(D,A),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(A,E),instancehypernym(F,D),haspart(B,C),similarto(D,E).
memberofdomainregion(A,B):- membermeronym(C,B),instancehypernym(A,D),haspart(A,C).
memberofdomainregion(A,B):- verbgroup(E,B),memberofdomainusage(D,A),haspart(A,C).
memberofdomainregion(A,B):- verbgroup(D,A),membermeronym(B,C),haspart(D,A).
memberofdomainregion(A,B):- memberofdomainusage(B,F),memberofdomainusage(A,D),haspart(B,C),hypernym(A,E).
memberofdomainregion(A,B):- haspart(B,C),membermeronym(C,E),instancehypernym(A,C),instancehypernym(B,D).
memberofdomainregion(A,B):- membermeronym(D,F),membermeronym(F,C),similarto(E,B),similarto(A,C).
memberofdomainregion(A,B):- membermeronym(D,C),membermeronym(F,C),synsetdomaintopicof(B,D),haspart(A,E).
memberofdomainregion(A,B):- synsetdomaintopicof(E,D),membermeronym(F,C),membermeronym(D,B),haspart(C,A).
memberofdomainregion(A,B):- verbgroup(A,C),membermeronym(E,B),alsosee(C,D).
memberofdomainregion(A,B):- membermeronym(A,C),hypernym(A,B),alsosee(C,A).
memberofdomainregion(A,B):- alsosee(C,B),memberofdomainusage(D,B),verbgroup(A,B),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),membermeronym(F,C),synsetdomaintopicof(A,F),similarto(D,B).
memberofdomainregion(A,B):- hypernym(A,C),hypernym(A,D),hypernym(D,B).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),synsetdomaintopicof(B,C),membermeronym(C,A),haspart(B,C).
memberofdomainregion(A,B):- similarto(E,A),membermeronym(F,C),synsetdomaintopicof(B,F),membermeronym(E,D).
memberofdomainregion(A,B):- instancehypernym(F,E),verbgroup(A,E),haspart(D,C),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),hypernym(B,A),hypernym(C,B),haspart(B,C).
memberofdomainregion(A,B):- hypernym(B,C),hypernym(D,A),hypernym(A,D).
memberofdomainregion(A,B):- haspart(B,C),membermeronym(C,B),verbgroup(B,C),instancehypernym(A,C).
memberofdomainregion(A,B):- memberofdomainusage(B,C),membermeronym(B,A),haspart(A,B).
memberofdomainregion(A,B):- membermeronym(F,C),hypernym(A,F),similarto(B,E),instancehypernym(D,C).
memberofdomainregion(A,B):- hypernym(A,B),alsosee(D,B),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- hypernym(C,E),instancehypernym(B,D),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- haspart(D,C),verbgroup(B,E),haspart(B,C),alsosee(A,D).
memberofdomainregion(A,B):- synsetdomaintopicof(E,D),membermeronym(F,C),verbgroup(B,C),haspart(E,A).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),hypernym(D,A),synsetdomaintopicof(B,C).
memberofdomainregion(A,B):- verbgroup(D,C),instancehypernym(D,A),haspart(C,B).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),membermeronym(B,E),derivationallyrelatedform(D,A),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(D,B),derivationallyrelatedform(E,A),haspart(B,C),instancehypernym(E,C).
memberofdomainregion(A,B):- synsetdomaintopicof(C,D),derivationallyrelatedform(A,D),haspart(B,C),hypernym(E,A).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),membermeronym(F,C),verbgroup(D,F),similarto(C,A).
memberofdomainregion(A,B):- similarto(A,E),alsosee(E,D),synsetdomaintopicof(C,D),haspart(B,C).
