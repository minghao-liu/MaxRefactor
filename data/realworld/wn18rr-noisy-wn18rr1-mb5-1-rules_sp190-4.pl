memberofdomainregion(A,B):- alsosee(B,C),derivationallyrelatedform(E,A),verbgroup(D,B),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(D,F),alsosee(F,E),alsosee(A,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),instancehypernym(D,A),membermeronym(D,E),synsetdomaintopicof(B,F).
memberofdomainregion(A,B):- hypernym(E,D),haspart(C,A),membermeronym(B,D).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),membermeronym(B,E),derivationallyrelatedform(D,A),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(B,A),membermeronym(D,A),haspart(C,B).
memberofdomainregion(A,B):- haspart(C,D),derivationallyrelatedform(C,A),haspart(C,B).
memberofdomainregion(A,B):- membermeronym(F,C),similarto(B,D),verbgroup(B,E),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- similarto(A,E),haspart(B,C),memberofdomainusage(D,A),membermeronym(C,D).
memberofdomainregion(A,B):- alsosee(D,C),verbgroup(C,B),verbgroup(A,E),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),derivationallyrelatedform(A,D),verbgroup(B,E),hypernym(D,F).
memberofdomainregion(A,B):- alsosee(A,E),verbgroup(D,C),derivationallyrelatedform(C,D),haspart(B,C).
memberofdomainregion(A,B):- similarto(B,A),membermeronym(B,D),similarto(B,C).
memberofdomainregion(A,B):- similarto(A,B),membermeronym(A,E),instancehypernym(D,E),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(A,D),alsosee(B,E),similarto(A,C).
memberofdomainregion(A,B):- alsosee(C,B),membermeronym(F,C),synsetdomaintopicof(C,D),haspart(A,E).
memberofdomainregion(A,B):- synsetdomaintopicof(C,E),membermeronym(F,C),haspart(D,A),hypernym(B,F).
memberofdomainregion(A,B):- alsosee(D,C),similarto(E,D),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- haspart(B,C),haspart(A,D),verbgroup(E,C),memberofdomainusage(B,D).
memberofdomainregion(A,B):- similarto(A,E),memberofdomainusage(F,E),haspart(B,C),hypernym(A,D).
memberofdomainregion(A,B):- memberofdomainusage(A,E),instancehypernym(E,D),haspart(B,C),alsosee(E,A).
memberofdomainregion(A,B):- memberofdomainusage(D,B),derivationallyrelatedform(A,D),haspart(B,C),similarto(A,C).
memberofdomainregion(A,B):- derivationallyrelatedform(A,B),haspart(B,C),haspart(C,B).
memberofdomainregion(A,B):- hypernym(E,B),synsetdomaintopicof(D,E),haspart(C,A).
memberofdomainregion(A,B):- hypernym(B,C),memberofdomainusage(E,B),verbgroup(A,D).
memberofdomainregion(A,B):- membermeronym(D,B),alsosee(B,D),instancehypernym(A,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),similarto(F,A),membermeronym(E,F),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(C,D),membermeronym(F,C),instancehypernym(F,B),haspart(A,E).
memberofdomainregion(A,B):- verbgroup(D,A),instancehypernym(B,E),membermeronym(F,C),synsetdomaintopicof(F,A).
memberofdomainregion(A,B):- membermeronym(F,C),memberofdomainusage(E,B),membermeronym(A,D),derivationallyrelatedform(F,A).
memberofdomainregion(A,B):- instancehypernym(B,E),membermeronym(F,C),derivationallyrelatedform(A,D),verbgroup(C,E).
memberofdomainregion(A,B):- instancehypernym(C,E),memberofdomainusage(A,D),haspart(B,C),verbgroup(F,B).
memberofdomainregion(A,B):- similarto(E,F),hypernym(D,A),membermeronym(F,C),haspart(B,F).
memberofdomainregion(A,B):- memberofdomainusage(E,C),instancehypernym(A,D),similarto(E,B).
memberofdomainregion(A,B):- alsosee(A,E),haspart(C,F),haspart(B,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,A),instancehypernym(E,B),membermeronym(D,B),haspart(B,C).
memberofdomainregion(A,B):- hypernym(B,C),memberofdomainusage(A,D),haspart(C,B).
memberofdomainregion(A,B):- similarto(A,E),alsosee(D,B),similarto(E,C).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),membermeronym(E,B),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- verbgroup(A,C),membermeronym(F,C),haspart(B,D),instancehypernym(E,C).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),similarto(D,A),hypernym(C,B),haspart(B,C).
memberofdomainregion(A,B):- haspart(E,D),membermeronym(F,C),derivationallyrelatedform(F,B),haspart(A,D).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),alsosee(B,C),derivationallyrelatedform(D,E),haspart(B,C).
memberofdomainregion(A,B):- alsosee(B,F),memberofdomainusage(E,C),membermeronym(F,C),memberofdomainusage(D,A).
memberofdomainregion(A,B):- synsetdomaintopicof(D,A),similarto(A,C),alsosee(C,B).
memberofdomainregion(A,B):- instancehypernym(E,B),haspart(B,C),membermeronym(D,E),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- memberofdomainusage(A,E),instancehypernym(C,E),memberofdomainusage(B,D).
memberofdomainregion(A,B):- haspart(A,D),membermeronym(A,B),haspart(B,C),alsosee(C,D).
memberofdomainregion(A,B):- membermeronym(F,C),similarto(F,E),alsosee(A,D),synsetdomaintopicof(C,B).
memberofdomainregion(A,B):- verbgroup(E,D),haspart(B,C),derivationallyrelatedform(D,A),verbgroup(C,E).
memberofdomainregion(A,B):- membermeronym(A,C),instancehypernym(C,B),similarto(C,A).
memberofdomainregion(A,B):- hypernym(C,D),membermeronym(F,C),haspart(E,A),verbgroup(F,B).
memberofdomainregion(A,B):- membermeronym(F,C),alsosee(E,F),verbgroup(A,E),memberofdomainusage(B,D).
memberofdomainregion(A,B):- verbgroup(D,A),similarto(A,E),haspart(B,C),derivationallyrelatedform(F,A).
memberofdomainregion(A,B):- hypernym(B,D),derivationallyrelatedform(E,B),hypernym(C,A).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),instancehypernym(D,B),memberofdomainusage(E,B),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(A,E),membermeronym(F,C),synsetdomaintopicof(C,D),alsosee(F,B).
memberofdomainregion(A,B):- derivationallyrelatedform(D,F),membermeronym(A,E),hypernym(F,C),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),verbgroup(A,C),membermeronym(F,C),instancehypernym(B,D).
memberofdomainregion(A,B):- verbgroup(F,A),haspart(B,C),hypernym(A,E),instancehypernym(D,C).
memberofdomainregion(A,B):- synsetdomaintopicof(C,D),similarto(B,D),instancehypernym(A,C).
memberofdomainregion(A,B):- hypernym(F,E),haspart(B,C),hypernym(F,D),instancehypernym(F,A).
memberofdomainregion(A,B):- hypernym(E,D),haspart(B,C),alsosee(B,D),instancehypernym(F,A).
memberofdomainregion(A,B):- verbgroup(E,D),verbgroup(A,C),memberofdomainusage(E,B).
memberofdomainregion(A,B):- similarto(E,D),membermeronym(D,F),similarto(A,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(E,B),instancehypernym(F,D),haspart(A,C).
memberofdomainregion(A,B):- instancehypernym(D,B),similarto(A,D),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- membermeronym(E,C),membermeronym(F,C),similarto(E,A),derivationallyrelatedform(D,B).
memberofdomainregion(A,B):- similarto(D,B),instancehypernym(A,D),alsosee(D,A),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(E,B),memberofdomainusage(A,D),haspart(B,C),similarto(C,A).
memberofdomainregion(A,B):- instancehypernym(D,B),synsetdomaintopicof(F,A),hypernym(E,C),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(A,F),alsosee(D,B),instancehypernym(E,D),haspart(B,C).
memberofdomainregion(A,B):- hypernym(C,D),synsetdomaintopicof(B,A),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- verbgroup(B,C),hypernym(A,D),alsosee(B,D).
memberofdomainregion(A,B):- synsetdomaintopicof(F,B),membermeronym(A,D),haspart(B,C),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- synsetdomaintopicof(B,A),synsetdomaintopicof(A,E),hypernym(E,D),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),alsosee(A,F),haspart(B,C),derivationallyrelatedform(E,C).
memberofdomainregion(A,B):- membermeronym(F,C),synsetdomaintopicof(E,A),alsosee(A,D),haspart(C,B).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),membermeronym(D,F),haspart(B,C),membermeronym(E,D).
memberofdomainregion(A,B):- membermeronym(F,A),derivationallyrelatedform(B,E),membermeronym(F,C),verbgroup(D,B).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),synsetdomaintopicof(C,D),haspart(B,C),haspart(C,B).
memberofdomainregion(A,B):- haspart(C,E),derivationallyrelatedform(D,A),verbgroup(D,B),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,C),instancehypernym(A,D),derivationallyrelatedform(B,D),derivationallyrelatedform(D,C).
memberofdomainregion(A,B):- haspart(B,A),haspart(C,D),verbgroup(A,D).
memberofdomainregion(A,B):- similarto(A,E),derivationallyrelatedform(A,D),hypernym(A,D),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(C,B),haspart(B,C),instancehypernym(A,C),verbgroup(C,A).
memberofdomainregion(A,B):- membermeronym(A,E),alsosee(F,C),haspart(B,C),verbgroup(D,C).
memberofdomainregion(A,B):- derivationallyrelatedform(D,A),derivationallyrelatedform(D,F),verbgroup(A,E),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(B,A),synsetdomaintopicof(B,D),derivationallyrelatedform(C,D).
memberofdomainregion(A,B):- hypernym(E,D),haspart(A,D),hypernym(D,C),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(E,A),membermeronym(F,C),instancehypernym(F,B),memberofdomainusage(D,A).
memberofdomainregion(A,B):- memberofdomainusage(A,E),similarto(E,C),instancehypernym(E,D),haspart(B,C).
memberofdomainregion(A,B):- hypernym(E,B),membermeronym(F,C),synsetdomaintopicof(C,D),synsetdomaintopicof(A,C).
memberofdomainregion(A,B):- hypernym(C,A),membermeronym(F,C),verbgroup(C,E),memberofdomainusage(B,D).
memberofdomainregion(A,B):- derivationallyrelatedform(A,B),synsetdomaintopicof(D,B),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- similarto(A,E),hypernym(B,C),memberofdomainusage(D,E),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),instancehypernym(C,A),derivationallyrelatedform(B,D),haspart(F,E).
memberofdomainregion(A,B):- instancehypernym(A,D),synsetdomaintopicof(C,A),membermeronym(F,C),membermeronym(B,E).
memberofdomainregion(A,B):- haspart(D,B),membermeronym(A,E),instancehypernym(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,D),similarto(E,C),alsosee(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,C),memberofdomainusage(B,E),instancehypernym(F,D),instancehypernym(F,A).
memberofdomainregion(A,B):- alsosee(D,C),haspart(B,A),membermeronym(D,B),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),membermeronym(F,C),similarto(A,D),synsetdomaintopicof(B,C).
memberofdomainregion(A,B):- similarto(F,A),membermeronym(F,C),alsosee(B,E),similarto(D,E).
memberofdomainregion(A,B):- membermeronym(B,A),haspart(A,B),synsetdomaintopicof(A,C).
memberofdomainregion(A,B):- alsosee(E,A),similarto(D,A),haspart(B,C),instancehypernym(C,F).
memberofdomainregion(A,B):- synsetdomaintopicof(B,D),membermeronym(E,B),similarto(A,C).
memberofdomainregion(A,B):- hypernym(B,C),alsosee(C,A),instancehypernym(B,C).
memberofdomainregion(A,B):- verbgroup(A,C),alsosee(D,B),memberofdomainusage(E,D).
memberofdomainregion(A,B):- alsosee(B,F),membermeronym(F,C),membermeronym(F,E),alsosee(D,A).
memberofdomainregion(A,B):- similarto(E,D),haspart(B,A),similarto(A,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(D,B),derivationallyrelatedform(E,C),verbgroup(C,A).
memberofdomainregion(A,B):- membermeronym(F,C),verbgroup(D,F),membermeronym(A,D),verbgroup(B,E).
memberofdomainregion(A,B):- synsetdomaintopicof(C,B),derivationallyrelatedform(D,A),haspart(B,C),similarto(B,C).
memberofdomainregion(A,B):- similarto(F,E),alsosee(D,E),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- alsosee(B,F),membermeronym(F,C),haspart(A,D),verbgroup(D,E).
memberofdomainregion(A,B):- similarto(C,D),haspart(C,B),memberofdomainusage(A,B).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),membermeronym(F,C),synsetdomaintopicof(E,D),synsetdomaintopicof(A,C).
memberofdomainregion(A,B):- instancehypernym(C,B),similarto(D,C),instancehypernym(D,A).
memberofdomainregion(A,B):- synsetdomaintopicof(C,A),memberofdomainusage(B,E),similarto(D,E).
memberofdomainregion(A,B):- synsetdomaintopicof(C,E),membermeronym(F,C),hypernym(D,B),verbgroup(F,A).
memberofdomainregion(A,B):- synsetdomaintopicof(C,A),similarto(E,C),membermeronym(B,D).
memberofdomainregion(A,B):- membermeronym(B,C),haspart(D,E),hypernym(A,D).
memberofdomainregion(A,B):- hypernym(B,D),haspart(E,A),verbgroup(D,B),haspart(B,C).
memberofdomainregion(A,B):- hypernym(F,B),membermeronym(F,C),hypernym(A,E),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- synsetdomaintopicof(B,A),instancehypernym(B,A),instancehypernym(C,A).
memberofdomainregion(A,B):- synsetdomaintopicof(D,E),derivationallyrelatedform(B,D),membermeronym(C,A).
memberofdomainregion(A,B):- verbgroup(E,A),membermeronym(F,C),membermeronym(F,E),derivationallyrelatedform(B,D).
memberofdomainregion(A,B):- alsosee(C,D),verbgroup(A,F),haspart(B,C),synsetdomaintopicof(A,E).
memberofdomainregion(A,B):- membermeronym(B,F),haspart(C,D),membermeronym(F,C),derivationallyrelatedform(E,A).
memberofdomainregion(A,B):- instancehypernym(D,B),haspart(B,C),haspart(D,C),memberofdomainusage(D,A).
memberofdomainregion(A,B):- membermeronym(F,C),instancehypernym(D,E),similarto(A,F),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- haspart(E,B),haspart(C,A),memberofdomainusage(D,A).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),derivationallyrelatedform(E,B),derivationallyrelatedform(D,E),haspart(B,C).
memberofdomainregion(A,B):- hypernym(C,D),hypernym(A,E),haspart(B,C),similarto(D,E).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),synsetdomaintopicof(F,D),haspart(B,C),membermeronym(C,D).
memberofdomainregion(A,B):- membermeronym(F,C),memberofdomainusage(B,E),hypernym(C,B),membermeronym(A,D).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),haspart(D,C),haspart(B,C),instancehypernym(E,C).
memberofdomainregion(A,B):- membermeronym(F,C),hypernym(A,D),hypernym(E,C),hypernym(B,F).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),haspart(D,E),alsosee(C,E),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(D,B),alsosee(C,A),haspart(B,C),synsetdomaintopicof(A,B).
memberofdomainregion(A,B):- similarto(C,D),similarto(B,D),verbgroup(A,D).
memberofdomainregion(A,B):- instancehypernym(A,D),membermeronym(C,A),haspart(B,C),memberofdomainusage(E,A).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),alsosee(D,E),synsetdomaintopicof(F,E),haspart(B,C).
memberofdomainregion(A,B):- hypernym(B,D),similarto(A,E),alsosee(A,D),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(C,D),membermeronym(A,E),verbgroup(D,F),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,C),synsetdomaintopicof(D,E),derivationallyrelatedform(A,D),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- membermeronym(F,C),instancehypernym(C,A),memberofdomainusage(C,E),alsosee(B,D).
memberofdomainregion(A,B):- derivationallyrelatedform(C,E),similarto(A,D),derivationallyrelatedform(E,D),haspart(B,C).
memberofdomainregion(A,B):- hypernym(E,D),derivationallyrelatedform(C,A),alsosee(E,B).
memberofdomainregion(A,B):- synsetdomaintopicof(E,A),instancehypernym(A,D),haspart(B,C),membermeronym(E,A).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),memberofdomainusage(A,C),alsosee(D,E),haspart(B,C).
memberofdomainregion(A,B):- alsosee(B,C),haspart(D,C),membermeronym(A,D).
memberofdomainregion(A,B):- similarto(D,A),membermeronym(F,C),alsosee(B,E),haspart(C,B).
memberofdomainregion(A,B):- verbgroup(C,D),membermeronym(F,C),membermeronym(E,B),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- haspart(E,D),instancehypernym(C,A),instancehypernym(B,D).
memberofdomainregion(A,B):- membermeronym(E,C),derivationallyrelatedform(D,A),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- verbgroup(E,D),hypernym(A,C),instancehypernym(B,D).
memberofdomainregion(A,B):- hypernym(C,A),derivationallyrelatedform(C,E),memberofdomainusage(D,B).
memberofdomainregion(A,B):- synsetdomaintopicof(D,A),hypernym(A,D),haspart(B,C),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- memberofdomainusage(F,A),synsetdomaintopicof(D,E),membermeronym(F,C),memberofdomainusage(B,E).
memberofdomainregion(A,B):- membermeronym(D,C),instancehypernym(F,C),instancehypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(D,C),similarto(A,D),haspart(B,C),similarto(C,A).
memberofdomainregion(A,B):- haspart(C,D),similarto(A,D),alsosee(C,A),haspart(B,C).
memberofdomainregion(A,B):- alsosee(A,E),membermeronym(F,C),memberofdomainusage(F,B),verbgroup(A,D).
memberofdomainregion(A,B):- synsetdomaintopicof(C,E),derivationallyrelatedform(D,A),synsetdomaintopicof(F,E),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),memberofdomainusage(B,C),hypernym(C,A).
memberofdomainregion(A,B):- instancehypernym(B,A),instancehypernym(E,B),haspart(D,C),haspart(B,C).
memberofdomainregion(A,B):- haspart(D,B),membermeronym(F,C),synsetdomaintopicof(A,F),membermeronym(D,E).
memberofdomainregion(A,B):- instancehypernym(D,B),haspart(B,C),similarto(E,C),instancehypernym(A,C).
memberofdomainregion(A,B):- haspart(D,A),haspart(B,C),instancehypernym(D,C),verbgroup(A,D).
memberofdomainregion(A,B):- haspart(D,B),membermeronym(F,C),hypernym(E,A),synsetdomaintopicof(F,A).
memberofdomainregion(A,B):- similarto(E,A),memberofdomainusage(D,B),similarto(F,D),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(C,D),synsetdomaintopicof(D,A),haspart(B,C),hypernym(D,B).
memberofdomainregion(A,B):- hypernym(E,D),derivationallyrelatedform(C,A),derivationallyrelatedform(B,D).
memberofdomainregion(A,B):- membermeronym(A,C),memberofdomainusage(C,B),haspart(B,D).
memberofdomainregion(A,B):- alsosee(B,F),instancehypernym(A,D),memberofdomainusage(C,E),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(B,D),instancehypernym(C,A),instancehypernym(B,D).
memberofdomainregion(A,B):- instancehypernym(E,F),haspart(A,D),haspart(B,C),hypernym(A,F).
memberofdomainregion(A,B):- derivationallyrelatedform(C,A),instancehypernym(B,D),memberofdomainusage(D,E).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),similarto(F,E),derivationallyrelatedform(F,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),haspart(E,A),verbgroup(D,B),membermeronym(A,F).
memberofdomainregion(A,B):- haspart(B,A),verbgroup(C,B),similarto(B,D).
memberofdomainregion(A,B):- similarto(A,E),memberofdomainusage(B,C),membermeronym(F,C),verbgroup(D,C).
memberofdomainregion(A,B):- instancehypernym(F,E),membermeronym(F,B),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- hypernym(C,A),haspart(D,A),memberofdomainusage(B,E).
memberofdomainregion(A,B):- membermeronym(C,B),derivationallyrelatedform(C,A),similarto(C,B).
memberofdomainregion(A,B):- verbgroup(F,E),membermeronym(F,C),membermeronym(D,A),haspart(C,B).
memberofdomainregion(A,B):- similarto(D,A),membermeronym(E,D),instancehypernym(B,C).
memberofdomainregion(A,B):- instancehypernym(B,E),membermeronym(F,C),hypernym(F,B),membermeronym(A,D).
