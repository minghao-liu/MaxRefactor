memberofdomainregion(A,B):- alsosee(A,E),similarto(C,D),membermeronym(F,C),derivationallyrelatedform(B,C).
memberofdomainregion(A,B):- membermeronym(C,B),alsosee(B,E),membermeronym(F,C),memberofdomainusage(D,A).
memberofdomainregion(A,B):- verbgroup(A,C),membermeronym(B,E),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- verbgroup(B,C),membermeronym(F,C),membermeronym(B,E),memberofdomainusage(A,D).
memberofdomainregion(A,B):- synsetdomaintopicof(D,B),instancehypernym(E,A),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- derivationallyrelatedform(A,B),hypernym(D,C),memberofdomainusage(D,A).
memberofdomainregion(A,B):- similarto(A,E),instancehypernym(B,E),hypernym(D,E),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(E,A),hypernym(A,D),haspart(B,C),memberofdomainusage(A,B).
memberofdomainregion(A,B):- similarto(A,B),instancehypernym(B,A),memberofdomainusage(A,D),haspart(B,C).
memberofdomainregion(A,B):- hypernym(D,E),verbgroup(F,A),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- membermeronym(B,F),membermeronym(F,C),verbgroup(E,B),verbgroup(D,A).
memberofdomainregion(A,B):- memberofdomainusage(D,B),instancehypernym(E,D),haspart(B,C),alsosee(A,F).
memberofdomainregion(A,B):- membermeronym(F,A),haspart(D,A),hypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(E,B),membermeronym(F,C),haspart(D,A),hypernym(F,A).
memberofdomainregion(A,B):- instancehypernym(F,C),memberofdomainusage(E,C),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- similarto(E,D),membermeronym(E,B),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- alsosee(E,C),synsetdomaintopicof(A,E),haspart(D,A),haspart(B,C).
memberofdomainregion(A,B):- hypernym(E,B),membermeronym(F,C),hypernym(F,A),similarto(D,E).
memberofdomainregion(A,B):- haspart(D,B),alsosee(E,B),similarto(C,A).
memberofdomainregion(A,B):- hypernym(A,B),membermeronym(A,D),haspart(B,C),memberofdomainusage(C,D).
memberofdomainregion(A,B):- haspart(D,B),verbgroup(E,A),haspart(B,C),memberofdomainusage(A,B).
memberofdomainregion(A,B):- haspart(D,B),alsosee(C,B),membermeronym(C,A).
memberofdomainregion(A,B):- haspart(E,A),alsosee(C,A),alsosee(B,D).
memberofdomainregion(A,B):- similarto(B,A),synsetdomaintopicof(C,D),haspart(C,B).
memberofdomainregion(A,B):- membermeronym(F,C),alsosee(D,B),verbgroup(A,E),alsosee(C,D).
memberofdomainregion(A,B):- membermeronym(D,B),membermeronym(C,A),membermeronym(D,A).
memberofdomainregion(A,B):- memberofdomainusage(D,F),haspart(A,D),alsosee(C,E),haspart(B,C).
memberofdomainregion(A,B):- similarto(A,D),memberofdomainusage(A,E),hypernym(E,A),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(B,C),membermeronym(D,A),membermeronym(C,D).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),alsosee(B,D),memberofdomainusage(B,A),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,C),hypernym(A,E),memberofdomainusage(E,D),similarto(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),memberofdomainusage(B,E),hypernym(A,D),instancehypernym(F,D).
memberofdomainregion(A,B):- synsetdomaintopicof(E,D),haspart(B,C),alsosee(A,D),membermeronym(E,D).
memberofdomainregion(A,B):- synsetdomaintopicof(B,D),instancehypernym(C,A),derivationallyrelatedform(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(D,A),memberofdomainusage(A,D),haspart(B,C),similarto(D,E).
memberofdomainregion(A,B):- derivationallyrelatedform(B,D),alsosee(C,A),instancehypernym(E,C).
memberofdomainregion(A,B):- alsosee(A,C),membermeronym(B,C),instancehypernym(C,D).
memberofdomainregion(A,B):- verbgroup(B,A),instancehypernym(B,C).
memberofdomainregion(A,B):- hypernym(B,E),haspart(A,D),memberofdomainusage(A,C),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(E,C),membermeronym(F,C),similarto(D,A),hypernym(B,F).
memberofdomainregion(A,B):- similarto(D,C),alsosee(A,E),synsetdomaintopicof(B,C).
memberofdomainregion(A,B):- verbgroup(A,C),verbgroup(D,B),synsetdomaintopicof(A,E).
memberofdomainregion(A,B):- membermeronym(A,C),instancehypernym(C,B),membermeronym(D,A).
memberofdomainregion(A,B):- haspart(B,A),instancehypernym(B,D),instancehypernym(C,D).
memberofdomainregion(A,B):- haspart(B,C),membermeronym(A,D),verbgroup(E,F),hypernym(F,D).
memberofdomainregion(A,B):- instancehypernym(A,E),alsosee(B,C),membermeronym(F,C),membermeronym(F,D).
memberofdomainregion(A,B):- haspart(D,B),membermeronym(F,C),synsetdomaintopicof(E,D),derivationallyrelatedform(A,F).
memberofdomainregion(A,B):- hypernym(B,C),membermeronym(F,C),alsosee(A,D),membermeronym(E,D).
memberofdomainregion(A,B):- synsetdomaintopicof(E,D),derivationallyrelatedform(A,D),haspart(B,C),membermeronym(A,F).
memberofdomainregion(A,B):- membermeronym(B,C),verbgroup(A,D),haspart(B,C),instancehypernym(B,C).
memberofdomainregion(A,B):- haspart(B,C),haspart(D,C),instancehypernym(F,A),hypernym(E,A).
memberofdomainregion(A,B):- hypernym(C,D),membermeronym(F,C),instancehypernym(E,A),instancehypernym(B,F).
memberofdomainregion(A,B):- verbgroup(C,D),memberofdomainusage(E,F),haspart(B,C),memberofdomainusage(A,F).
memberofdomainregion(A,B):- verbgroup(A,C),alsosee(B,A),alsosee(C,A).
memberofdomainregion(A,B):- alsosee(F,A),similarto(F,D),membermeronym(F,C),similarto(E,B).
memberofdomainregion(A,B):- derivationallyrelatedform(D,F),haspart(E,B),membermeronym(F,C),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- alsosee(B,D),derivationallyrelatedform(E,D),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- derivationallyrelatedform(E,D),derivationallyrelatedform(D,A),synsetdomaintopicof(B,C).
memberofdomainregion(A,B):- haspart(E,D),instancehypernym(A,D),synsetdomaintopicof(B,C),haspart(B,C).
memberofdomainregion(A,B):- haspart(E,B),membermeronym(F,C),verbgroup(B,C),derivationallyrelatedform(D,A).
memberofdomainregion(A,B):- instancehypernym(A,E),haspart(B,C),verbgroup(C,B),memberofdomainusage(B,D).
memberofdomainregion(A,B):- instancehypernym(A,D),synsetdomaintopicof(B,C),haspart(B,C),alsosee(C,D).
memberofdomainregion(A,B):- haspart(D,C),haspart(A,D),memberofdomainusage(C,A),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(E,B),membermeronym(A,B),alsosee(D,A),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(A,E),membermeronym(E,D),instancehypernym(B,C).
memberofdomainregion(A,B):- haspart(C,D),hypernym(B,E),memberofdomainusage(A,D).
memberofdomainregion(A,B):- similarto(B,F),similarto(C,D),membermeronym(F,C),verbgroup(A,E).
memberofdomainregion(A,B):- synsetdomaintopicof(C,D),alsosee(B,D),alsosee(A,D),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(C,B),instancehypernym(E,A),membermeronym(F,C),membermeronym(D,E).
memberofdomainregion(A,B):- verbgroup(D,C),instancehypernym(A,C),instancehypernym(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),derivationallyrelatedform(A,B),haspart(B,C),synsetdomaintopicof(C,A).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),hypernym(B,C),similarto(E,A),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),memberofdomainusage(A,E),haspart(B,C),haspart(C,D).
memberofdomainregion(A,B):- memberofdomainusage(A,E),instancehypernym(F,B),membermeronym(F,C),alsosee(D,A).
memberofdomainregion(A,B):- verbgroup(E,D),instancehypernym(D,E),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(D,B),hypernym(D,C),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- synsetdomaintopicof(C,B),instancehypernym(A,D),alsosee(A,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(A,C),similarto(A,B),alsosee(C,A).
memberofdomainregion(A,B):- verbgroup(C,D),haspart(A,C),haspart(B,C),memberofdomainusage(E,A).
memberofdomainregion(A,B):- similarto(A,D),membermeronym(C,F),instancehypernym(D,E),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(D,C),haspart(B,C),hypernym(A,E),memberofdomainusage(B,D).
memberofdomainregion(A,B):- similarto(D,C),memberofdomainusage(A,E),membermeronym(D,E),haspart(B,C).
memberofdomainregion(A,B):- alsosee(F,D),memberofdomainusage(A,D),haspart(B,C),hypernym(A,E).
memberofdomainregion(A,B):- alsosee(A,C),membermeronym(F,C),memberofdomainusage(D,B),haspart(F,E).
memberofdomainregion(A,B):- derivationallyrelatedform(B,C),membermeronym(F,C),haspart(A,D),memberofdomainusage(E,A).
memberofdomainregion(A,B):- synsetdomaintopicof(C,E),haspart(E,B),membermeronym(F,C),membermeronym(A,D).
memberofdomainregion(A,B):- membermeronym(F,C),derivationallyrelatedform(B,D),instancehypernym(A,F),hypernym(A,E).
memberofdomainregion(A,B):- alsosee(F,A),synsetdomaintopicof(A,D),alsosee(E,C),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(B,C),similarto(D,B),instancehypernym(A,C).
memberofdomainregion(A,B):- verbgroup(E,D),similarto(E,B),haspart(B,C),memberofdomainusage(A,F).
memberofdomainregion(A,B):- membermeronym(B,F),instancehypernym(A,D),verbgroup(E,F),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(A,C),verbgroup(C,B),haspart(D,B).
memberofdomainregion(A,B):- verbgroup(E,A),membermeronym(F,C),similarto(D,B),verbgroup(C,E).
memberofdomainregion(A,B):- membermeronym(F,C),memberofdomainusage(D,B),alsosee(C,E),alsosee(C,A).
memberofdomainregion(A,B):- hypernym(E,A),membermeronym(E,B),alsosee(A,D),haspart(B,C).
memberofdomainregion(A,B):- alsosee(A,E),hypernym(B,F),haspart(B,C),synsetdomaintopicof(D,F).
memberofdomainregion(A,B):- verbgroup(D,A),instancehypernym(E,B),derivationallyrelatedform(C,B).
memberofdomainregion(A,B):- similarto(C,F),hypernym(A,E),haspart(B,C),verbgroup(D,E).
memberofdomainregion(A,B):- verbgroup(E,A),haspart(B,C),memberofdomainusage(A,D),derivationallyrelatedform(D,B).
memberofdomainregion(A,B):- verbgroup(D,A),alsosee(D,B),synsetdomaintopicof(E,C),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(B,F),membermeronym(F,C),similarto(D,A),alsosee(D,E).
memberofdomainregion(A,B):- haspart(E,D),similarto(A,E),haspart(B,C),similarto(C,A).
memberofdomainregion(A,B):- instancehypernym(A,E),instancehypernym(C,E),haspart(B,C),similarto(E,D).
memberofdomainregion(A,B):- synsetdomaintopicof(D,E),haspart(C,A),membermeronym(B,D).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),membermeronym(F,C),derivationallyrelatedform(A,D),synsetdomaintopicof(E,F).
memberofdomainregion(A,B):- membermeronym(F,C),derivationallyrelatedform(A,D),similarto(E,B),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(C,B),memberofdomainusage(A,C),haspart(B,C),haspart(A,C).
memberofdomainregion(A,B):- instancehypernym(A,E),haspart(C,F),derivationallyrelatedform(E,D),haspart(B,C).
memberofdomainregion(A,B):- similarto(D,C),membermeronym(F,C),membermeronym(D,A),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- membermeronym(C,B),instancehypernym(D,A),synsetdomaintopicof(E,C).
memberofdomainregion(A,B):- hypernym(E,B),haspart(B,C),membermeronym(B,D),memberofdomainusage(A,F).
memberofdomainregion(A,B):- haspart(E,D),derivationallyrelatedform(D,E),verbgroup(A,E),haspart(B,C).
memberofdomainregion(A,B):- alsosee(D,C),membermeronym(F,C),hypernym(E,A),haspart(C,B).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),memberofdomainusage(B,C),haspart(B,C),instancehypernym(A,C).
memberofdomainregion(A,B):- synsetdomaintopicof(C,D),memberofdomainusage(D,B),verbgroup(C,A).
memberofdomainregion(A,B):- verbgroup(D,C),memberofdomainusage(B,A),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(C,D),haspart(B,C),verbgroup(B,A),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),hypernym(A,C),verbgroup(C,B).
memberofdomainregion(A,B):- instancehypernym(B,E),membermeronym(F,C),derivationallyrelatedform(D,A),hypernym(D,F).
memberofdomainregion(A,B):- haspart(B,E),membermeronym(D,B),haspart(B,C),alsosee(A,F).
memberofdomainregion(A,B):- verbgroup(B,F),membermeronym(F,C),verbgroup(B,E),membermeronym(D,A).
memberofdomainregion(A,B):- synsetdomaintopicof(C,A),membermeronym(F,C),memberofdomainusage(D,B),verbgroup(F,E).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),similarto(C,D),haspart(B,C),similarto(A,C).
memberofdomainregion(A,B):- similarto(D,C),alsosee(A,E),synsetdomaintopicof(C,F),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),synsetdomaintopicof(F,D),membermeronym(B,D),haspart(A,E).
memberofdomainregion(A,B):- haspart(B,E),synsetdomaintopicof(B,D),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(C,A),membermeronym(D,B),verbgroup(C,B),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(D,C),haspart(A,D),haspart(B,C),synsetdomaintopicof(A,B).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),membermeronym(A,E),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- haspart(C,D),membermeronym(F,C),membermeronym(D,B),haspart(A,E).
memberofdomainregion(A,B):- alsosee(D,C),instancehypernym(B,A),alsosee(C,A).
memberofdomainregion(A,B):- hypernym(B,E),similarto(D,A),similarto(B,C).
memberofdomainregion(A,B):- verbgroup(E,D),similarto(A,D),verbgroup(D,F),haspart(B,C).
memberofdomainregion(A,B):- haspart(E,F),similarto(F,D),memberofdomainusage(A,E),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(B,D),similarto(F,D),verbgroup(A,E),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),hypernym(E,A),instancehypernym(D,A),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(A,E),instancehypernym(D,E),hypernym(F,C),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),hypernym(D,E),haspart(B,C),haspart(D,F).
memberofdomainregion(A,B):- alsosee(A,E),derivationallyrelatedform(D,C),haspart(B,C),membermeronym(B,D).
memberofdomainregion(A,B):- verbgroup(C,D),memberofdomainusage(A,E),membermeronym(F,C),alsosee(B,D).
memberofdomainregion(A,B):- instancehypernym(A,E),membermeronym(F,C),alsosee(E,F),verbgroup(D,B).
memberofdomainregion(A,B):- hypernym(A,E),verbgroup(D,B),haspart(B,C),verbgroup(C,A).
memberofdomainregion(A,B):- memberofdomainusage(E,A),instancehypernym(B,D),memberofdomainusage(C,D).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),membermeronym(D,F),haspart(B,C),memberofdomainusage(A,F).
memberofdomainregion(A,B):- hypernym(B,D),membermeronym(E,C),membermeronym(F,C),haspart(A,E).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),membermeronym(F,C),alsosee(C,A),membermeronym(F,D).
memberofdomainregion(A,B):- membermeronym(F,C),hypernym(D,B),synsetdomaintopicof(A,F),derivationallyrelatedform(C,E).
memberofdomainregion(A,B):- instancehypernym(A,D),membermeronym(B,E),verbgroup(C,B),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(D,F),membermeronym(F,C),synsetdomaintopicof(A,F),membermeronym(E,B).
memberofdomainregion(A,B):- membermeronym(F,C),synsetdomaintopicof(A,C),similarto(B,D),memberofdomainusage(E,D).
memberofdomainregion(A,B):- hypernym(B,C),haspart(A,D),memberofdomainusage(E,B),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),hypernym(D,A),haspart(A,C).
memberofdomainregion(A,B):- haspart(E,B),membermeronym(A,E),synsetdomaintopicof(D,A),haspart(B,C).
memberofdomainregion(A,B):- hypernym(E,B),membermeronym(D,B),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),similarto(E,C),alsosee(A,D),instancehypernym(B,F).
memberofdomainregion(A,B):- instancehypernym(A,B),instancehypernym(C,A),membermeronym(C,D).
memberofdomainregion(A,B):- derivationallyrelatedform(A,D),alsosee(C,E),haspart(B,C),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- memberofdomainusage(D,C),similarto(D,B),instancehypernym(A,C).
memberofdomainregion(A,B):- similarto(E,D),membermeronym(F,C),hypernym(A,F),instancehypernym(E,B).
memberofdomainregion(A,B):- alsosee(F,A),instancehypernym(D,B),haspart(B,C),similarto(E,D).
memberofdomainregion(A,B):- synsetdomaintopicof(C,E),verbgroup(A,C),similarto(B,D).
memberofdomainregion(A,B):- similarto(C,B),hypernym(A,D),verbgroup(A,D).
memberofdomainregion(A,B):- hypernym(B,D),alsosee(E,C),membermeronym(F,C),hypernym(E,A).
memberofdomainregion(A,B):- similarto(E,D),haspart(B,C),instancehypernym(F,A),synsetdomaintopicof(E,F).
memberofdomainregion(A,B):- haspart(F,A),similarto(A,D),alsosee(C,E),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(D,F),memberofdomainusage(A,E),haspart(B,C),instancehypernym(F,A).
memberofdomainregion(A,B):- memberofdomainusage(D,C),membermeronym(F,C),verbgroup(A,E),haspart(F,B).
memberofdomainregion(A,B):- verbgroup(E,C),hypernym(F,D),haspart(B,C),alsosee(A,D).
memberofdomainregion(A,B):- membermeronym(F,C),synsetdomaintopicof(E,A),alsosee(B,D),haspart(E,C).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),memberofdomainusage(D,F),hypernym(A,F),membermeronym(F,C).
memberofdomainregion(A,B):- haspart(E,F),derivationallyrelatedform(A,D),membermeronym(D,E),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(B,D),membermeronym(F,C),membermeronym(F,E),haspart(A,E).
memberofdomainregion(A,B):- haspart(D,B),membermeronym(F,C),haspart(F,E),instancehypernym(A,F).
memberofdomainregion(A,B):- verbgroup(A,C),membermeronym(D,B),similarto(B,E).
memberofdomainregion(A,B):- alsosee(C,E),instancehypernym(B,D),verbgroup(C,A).
memberofdomainregion(A,B):- hypernym(C,A),instancehypernym(B,E),memberofdomainusage(C,D).
memberofdomainregion(A,B):- haspart(B,E),synsetdomaintopicof(D,A),instancehypernym(A,D),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(B,A),membermeronym(B,C),instancehypernym(C,D).
memberofdomainregion(A,B):- hypernym(E,C),membermeronym(F,C),haspart(A,D),memberofdomainusage(F,B).
memberofdomainregion(A,B):- similarto(E,A),similarto(A,D),haspart(B,C),hypernym(E,F).
