memberofdomainregion(A,B):- membermeronym(F,C),similarto(D,A),derivationallyrelatedform(F,D),derivationallyrelatedform(E,B).
memberofdomainregion(A,B):- memberofdomainusage(A,E),verbgroup(B,C),hypernym(D,C),haspart(B,C).
memberofdomainregion(A,B):- similarto(F,A),haspart(D,E),verbgroup(A,E),haspart(B,C).
memberofdomainregion(A,B):- hypernym(B,C),synsetdomaintopicof(D,C),verbgroup(B,A).
memberofdomainregion(A,B):- memberofdomainusage(B,C),alsosee(A,B),instancehypernym(A,C).
memberofdomainregion(A,B):- similarto(A,E),synsetdomaintopicof(A,D),alsosee(A,D),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(F,A),synsetdomaintopicof(E,A),haspart(B,C),hypernym(D,B).
memberofdomainregion(A,B):- alsosee(A,E),membermeronym(D,F),haspart(B,C),memberofdomainusage(B,D).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),haspart(D,A),instancehypernym(B,C).
memberofdomainregion(A,B):- similarto(A,B),synsetdomaintopicof(D,A),verbgroup(C,A).
memberofdomainregion(A,B):- verbgroup(F,D),membermeronym(F,C),synsetdomaintopicof(F,B),memberofdomainusage(E,A).
memberofdomainregion(A,B):- hypernym(B,D),hypernym(E,B),membermeronym(F,C),haspart(C,A).
memberofdomainregion(A,B):- instancehypernym(A,E),similarto(B,F),synsetdomaintopicof(D,A),haspart(B,C).
memberofdomainregion(A,B):- haspart(D,B),synsetdomaintopicof(C,D),hypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),haspart(E,A),similarto(B,D),membermeronym(C,D).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),hypernym(E,D),synsetdomaintopicof(B,C),haspart(B,C).
memberofdomainregion(A,B):- haspart(D,A),instancehypernym(E,B),verbgroup(E,C).
memberofdomainregion(A,B):- hypernym(C,A),membermeronym(F,C),synsetdomaintopicof(E,A),synsetdomaintopicof(B,D).
memberofdomainregion(A,B):- instancehypernym(A,E),haspart(B,C),verbgroup(B,C),instancehypernym(D,C).
memberofdomainregion(A,B):- similarto(E,D),hypernym(A,E),haspart(B,C),membermeronym(E,A).
memberofdomainregion(A,B):- haspart(F,A),derivationallyrelatedform(D,B),membermeronym(F,C),hypernym(E,D).
memberofdomainregion(A,B):- synsetdomaintopicof(B,A),verbgroup(E,C),haspart(B,C),hypernym(D,B).
memberofdomainregion(A,B):- synsetdomaintopicof(E,B),membermeronym(F,C),haspart(F,E),verbgroup(A,D).
memberofdomainregion(A,B):- membermeronym(F,C),synsetdomaintopicof(B,C),derivationallyrelatedform(E,A),alsosee(D,E).
memberofdomainregion(A,B):- derivationallyrelatedform(A,B),synsetdomaintopicof(E,C),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- haspart(A,E),verbgroup(B,F),haspart(B,C),verbgroup(D,E).
memberofdomainregion(A,B):- hypernym(A,B),memberofdomainusage(B,A),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- hypernym(B,D),memberofdomainusage(E,B),verbgroup(C,A).
memberofdomainregion(A,B):- memberofdomainusage(C,B),instancehypernym(A,D),membermeronym(F,C),alsosee(D,E).
memberofdomainregion(A,B):- verbgroup(F,D),membermeronym(F,C),hypernym(D,A),alsosee(E,B).
memberofdomainregion(A,B):- verbgroup(C,B),haspart(B,C),memberofdomainusage(B,A),instancehypernym(A,C).
memberofdomainregion(A,B):- similarto(D,C),memberofdomainusage(A,D),haspart(B,C),instancehypernym(B,C).
memberofdomainregion(A,B):- similarto(C,D),memberofdomainusage(A,E),similarto(B,D).
memberofdomainregion(A,B):- hypernym(C,A),membermeronym(D,B),verbgroup(C,A).
memberofdomainregion(A,B):- alsosee(B,A),hypernym(D,C),membermeronym(C,A).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),derivationallyrelatedform(A,B),instancehypernym(A,D),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(E,B),membermeronym(F,C),synsetdomaintopicof(D,F),alsosee(A,F).
memberofdomainregion(A,B):- similarto(B,A),membermeronym(D,B),haspart(B,C),similarto(A,C).
memberofdomainregion(A,B):- similarto(A,D),synsetdomaintopicof(B,F),synsetdomaintopicof(E,C),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(A,F),membermeronym(F,C),alsosee(E,B),memberofdomainusage(A,D).
memberofdomainregion(A,B):- alsosee(E,A),membermeronym(B,D),instancehypernym(E,C).
memberofdomainregion(A,B):- instancehypernym(C,B),synsetdomaintopicof(A,E),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- membermeronym(A,C),derivationallyrelatedform(D,B),synsetdomaintopicof(A,C),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),alsosee(D,B),similarto(D,F),memberofdomainusage(E,A).
memberofdomainregion(A,B):- hypernym(F,B),membermeronym(F,C),alsosee(C,E),instancehypernym(D,A).
memberofdomainregion(A,B):- haspart(D,A),similarto(A,C),derivationallyrelatedform(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(E,F),membermeronym(B,D),haspart(A,E).
memberofdomainregion(A,B):- memberofdomainusage(D,C),instancehypernym(A,D),alsosee(D,B),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(C,E),alsosee(C,B),instancehypernym(D,A).
memberofdomainregion(A,B):- haspart(B,E),similarto(B,F),membermeronym(F,C),haspart(A,D).
memberofdomainregion(A,B):- derivationallyrelatedform(A,D),derivationallyrelatedform(E,A),haspart(B,C),similarto(F,B).
memberofdomainregion(A,B):- memberofdomainusage(C,B),haspart(E,A),memberofdomainusage(B,D).
memberofdomainregion(A,B):- verbgroup(B,D),membermeronym(F,C),verbgroup(B,E),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- membermeronym(B,C),alsosee(A,E),hypernym(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(C,D),memberofdomainusage(B,A),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- synsetdomaintopicof(C,A),membermeronym(F,C),alsosee(E,C),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- membermeronym(F,C),alsosee(D,B),similarto(E,F),instancehypernym(F,A).
memberofdomainregion(A,B):- hypernym(F,E),membermeronym(F,C),membermeronym(E,B),membermeronym(A,D).
memberofdomainregion(A,B):- instancehypernym(A,E),membermeronym(F,C),derivationallyrelatedform(B,D),alsosee(B,F).
memberofdomainregion(A,B):- synsetdomaintopicof(C,A),haspart(E,A),hypernym(D,B).
memberofdomainregion(A,B):- hypernym(D,C),hypernym(B,A),instancehypernym(B,C).
memberofdomainregion(A,B):- verbgroup(D,A),similarto(A,E),synsetdomaintopicof(F,B),haspart(B,C).
memberofdomainregion(A,B):- haspart(E,C),verbgroup(A,B),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- membermeronym(A,C),similarto(D,B),alsosee(E,A).
memberofdomainregion(A,B):- haspart(A,D),synsetdomaintopicof(B,F),alsosee(E,F),haspart(B,C).
memberofdomainregion(A,B):- hypernym(B,C),synsetdomaintopicof(B,E),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- synsetdomaintopicof(C,A),haspart(B,C),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- verbgroup(D,C),derivationallyrelatedform(A,D),alsosee(D,A),haspart(B,C).
memberofdomainregion(A,B):- hypernym(D,E),memberofdomainusage(D,B),alsosee(C,A),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(E,B),alsosee(D,A),similarto(C,A).
memberofdomainregion(A,B):- haspart(C,A),instancehypernym(A,D),memberofdomainusage(E,B).
memberofdomainregion(A,B):- similarto(B,E),memberofdomainusage(A,D),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- similarto(A,E),haspart(B,C),hypernym(F,A),memberofdomainusage(D,A).
memberofdomainregion(A,B):- membermeronym(F,C),synsetdomaintopicof(B,F),alsosee(D,E),haspart(A,E).
memberofdomainregion(A,B):- hypernym(B,D),haspart(B,C),instancehypernym(A,C),memberofdomainusage(A,B).
memberofdomainregion(A,B):- instancehypernym(D,B),hypernym(E,A),haspart(B,C),synsetdomaintopicof(C,A).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),verbgroup(D,C),hypernym(F,C),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(A,C),similarto(A,B),verbgroup(C,A).
memberofdomainregion(A,B):- memberofdomainusage(B,C),synsetdomaintopicof(D,C),similarto(A,B).
memberofdomainregion(A,B):- synsetdomaintopicof(C,A),memberofdomainusage(C,B),instancehypernym(D,A).
memberofdomainregion(A,B):- haspart(D,B),alsosee(E,C),instancehypernym(C,A).
memberofdomainregion(A,B):- instancehypernym(C,A),alsosee(B,D),haspart(B,C),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- haspart(D,B),similarto(F,A),instancehypernym(D,E),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(C,D),synsetdomaintopicof(A,C),verbgroup(B,A).
memberofdomainregion(A,B):- derivationallyrelatedform(B,D),verbgroup(B,A),instancehypernym(A,C).
memberofdomainregion(A,B):- similarto(A,B),haspart(A,D),memberofdomainusage(C,A),haspart(B,C).
memberofdomainregion(A,B):- alsosee(B,D),derivationallyrelatedform(A,C),instancehypernym(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),haspart(B,C),derivationallyrelatedform(A,C),verbgroup(B,A).
memberofdomainregion(A,B):- alsosee(D,C),membermeronym(F,C),synsetdomaintopicof(A,E),derivationallyrelatedform(B,C).
memberofdomainregion(A,B):- haspart(B,C),haspart(E,C),membermeronym(D,A),hypernym(A,D).
memberofdomainregion(A,B):- hypernym(E,D),derivationallyrelatedform(D,A),haspart(B,C),memberofdomainusage(A,F).
memberofdomainregion(A,B):- memberofdomainusage(B,C),similarto(A,C),memberofdomainusage(C,D).
memberofdomainregion(A,B):- membermeronym(D,C),verbgroup(A,E),instancehypernym(C,D),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(F,D),membermeronym(F,C),synsetdomaintopicof(B,D),alsosee(E,A).
memberofdomainregion(A,B):- instancehypernym(A,D),verbgroup(B,A),instancehypernym(B,C).
memberofdomainregion(A,B):- similarto(A,E),membermeronym(F,C),haspart(B,D),synsetdomaintopicof(F,D).
memberofdomainregion(A,B):- verbgroup(D,A),similarto(C,D),membermeronym(F,C),derivationallyrelatedform(E,B).
memberofdomainregion(A,B):- haspart(C,D),haspart(A,D),verbgroup(D,B),haspart(B,C).
memberofdomainregion(A,B):- alsosee(A,C),synsetdomaintopicof(A,D),haspart(B,C),verbgroup(C,E).
memberofdomainregion(A,B):- instancehypernym(D,B),haspart(B,C),memberofdomainusage(A,C),membermeronym(E,D).
memberofdomainregion(A,B):- synsetdomaintopicof(E,A),hypernym(F,B),membermeronym(F,C),derivationallyrelatedform(A,D).
memberofdomainregion(A,B):- memberofdomainusage(B,F),derivationallyrelatedform(A,D),synsetdomaintopicof(E,C),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(F,A),membermeronym(F,C),haspart(D,B),similarto(D,E).
memberofdomainregion(A,B):- instancehypernym(D,E),hypernym(C,B),hypernym(E,A).
memberofdomainregion(A,B):- memberofdomainusage(D,C),instancehypernym(B,A),membermeronym(D,A).
memberofdomainregion(A,B):- verbgroup(C,D),similarto(A,D),membermeronym(B,D).
memberofdomainregion(A,B):- derivationallyrelatedform(F,C),haspart(B,C),hypernym(A,E),membermeronym(B,D).
memberofdomainregion(A,B):- verbgroup(B,D),derivationallyrelatedform(D,A),alsosee(A,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(A,C),instancehypernym(B,E),membermeronym(F,C),hypernym(D,B).
memberofdomainregion(A,B):- membermeronym(B,A),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- haspart(C,B),membermeronym(F,C),derivationallyrelatedform(C,D),membermeronym(E,A).
memberofdomainregion(A,B):- verbgroup(D,C),verbgroup(B,C),derivationallyrelatedform(A,D).
memberofdomainregion(A,B):- alsosee(D,C),instancehypernym(D,A),haspart(C,B).
memberofdomainregion(A,B):- haspart(B,C),similarto(E,B),membermeronym(D,A).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),alsosee(A,D),verbgroup(B,A).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),haspart(A,D),haspart(B,C),memberofdomainusage(E,A).
memberofdomainregion(A,B):- verbgroup(E,D),synsetdomaintopicof(B,E),haspart(B,C),memberofdomainusage(A,F).
memberofdomainregion(A,B):- similarto(E,D),membermeronym(A,E),haspart(B,C),derivationallyrelatedform(E,C).
memberofdomainregion(A,B):- similarto(B,F),synsetdomaintopicof(A,D),membermeronym(F,C),derivationallyrelatedform(E,C).
memberofdomainregion(A,B):- verbgroup(D,E),haspart(B,C),membermeronym(B,D),verbgroup(A,D).
memberofdomainregion(A,B):- similarto(E,A),membermeronym(F,C),synsetdomaintopicof(E,D),membermeronym(F,B).
memberofdomainregion(A,B):- membermeronym(F,C),similarto(A,F),similarto(E,B),memberofdomainusage(F,D).
memberofdomainregion(A,B):- hypernym(B,E),membermeronym(F,C),memberofdomainusage(A,D),synsetdomaintopicof(C,B).
memberofdomainregion(A,B):- derivationallyrelatedform(E,F),memberofdomainusage(A,E),instancehypernym(C,D),haspart(B,C).
memberofdomainregion(A,B):- hypernym(A,D),hypernym(A,E),haspart(C,B).
memberofdomainregion(A,B):- haspart(E,F),membermeronym(A,D),haspart(B,C),verbgroup(B,E).
memberofdomainregion(A,B):- instancehypernym(A,B),alsosee(E,B),memberofdomainusage(A,D),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(A,E),verbgroup(C,D),haspart(B,C),alsosee(F,D).
memberofdomainregion(A,B):- verbgroup(C,B),haspart(A,B),memberofdomainusage(A,B).
memberofdomainregion(A,B):- verbgroup(D,A),similarto(C,D),haspart(B,E).
memberofdomainregion(A,B):- memberofdomainusage(A,E),haspart(A,D),haspart(B,C),alsosee(C,D).
memberofdomainregion(A,B):- verbgroup(E,A),similarto(B,A),memberofdomainusage(A,D),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(A,F),alsosee(A,E),instancehypernym(E,D),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(C,B),derivationallyrelatedform(B,D),instancehypernym(A,C).
memberofdomainregion(A,B):- alsosee(C,A),alsosee(A,D),haspart(B,C),haspart(A,C).
memberofdomainregion(A,B):- memberofdomainusage(C,B),hypernym(E,A),membermeronym(F,C),memberofdomainusage(C,D).
memberofdomainregion(A,B):- similarto(A,E),alsosee(C,A),haspart(B,C),alsosee(C,D).
memberofdomainregion(A,B):- hypernym(E,B),haspart(B,C),derivationallyrelatedform(D,A),memberofdomainusage(B,D).
memberofdomainregion(A,B):- hypernym(E,B),membermeronym(D,B),verbgroup(C,A).
memberofdomainregion(A,B):- instancehypernym(A,E),derivationallyrelatedform(D,E),haspart(B,C),hypernym(A,F).
memberofdomainregion(A,B):- instancehypernym(D,B),hypernym(A,C),similarto(D,B).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),similarto(A,D),similarto(D,A).
memberofdomainregion(A,B):- membermeronym(A,E),haspart(B,C),synsetdomaintopicof(F,A),memberofdomainusage(D,A).
memberofdomainregion(A,B):- haspart(A,D),similarto(C,B),membermeronym(B,D).
memberofdomainregion(A,B):- haspart(D,B),memberofdomainusage(E,C),haspart(B,C),memberofdomainusage(D,A).
memberofdomainregion(A,B):- instancehypernym(B,E),instancehypernym(E,B),derivationallyrelatedform(A,D),haspart(B,C).
memberofdomainregion(A,B):- hypernym(B,C),membermeronym(C,A),memberofdomainusage(B,D).
memberofdomainregion(A,B):- memberofdomainusage(E,C),similarto(B,A),haspart(B,C),derivationallyrelatedform(D,B).
memberofdomainregion(A,B):- hypernym(B,C),haspart(E,C),membermeronym(D,A).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),verbgroup(A,E),haspart(B,C),synsetdomaintopicof(A,C).
memberofdomainregion(A,B):- verbgroup(C,D),membermeronym(A,D),haspart(B,C),haspart(C,B).
memberofdomainregion(A,B):- alsosee(F,A),alsosee(A,E),haspart(B,C),derivationallyrelatedform(D,C).
memberofdomainregion(A,B):- membermeronym(B,C),synsetdomaintopicof(D,A),haspart(B,C).
memberofdomainregion(A,B):- alsosee(A,E),synsetdomaintopicof(D,B),haspart(B,C),verbgroup(D,E).
memberofdomainregion(A,B):- verbgroup(B,D),membermeronym(F,C),hypernym(A,F),derivationallyrelatedform(E,C).
memberofdomainregion(A,B):- verbgroup(B,F),membermeronym(F,C),membermeronym(F,E),verbgroup(A,D).
memberofdomainregion(A,B):- verbgroup(D,A),membermeronym(F,C),hypernym(C,B),membermeronym(E,D).
memberofdomainregion(A,B):- haspart(B,C),hypernym(A,E),membermeronym(B,D),haspart(F,E).
memberofdomainregion(A,B):- similarto(D,B),verbgroup(F,C),hypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(D,C),instancehypernym(D,B),derivationallyrelatedform(C,A).
memberofdomainregion(A,B):- membermeronym(A,E),synsetdomaintopicof(C,D),haspart(B,C),haspart(C,A).
memberofdomainregion(A,B):- synsetdomaintopicof(E,D),derivationallyrelatedform(A,D),memberofdomainusage(F,E),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),similarto(D,C),membermeronym(F,C),verbgroup(D,B).
memberofdomainregion(A,B):- alsosee(E,A),membermeronym(F,C),memberofdomainusage(D,B),synsetdomaintopicof(E,F).
memberofdomainregion(A,B):- memberofdomainusage(D,F),memberofdomainusage(A,E),membermeronym(F,C),memberofdomainusage(F,B).
memberofdomainregion(A,B):- verbgroup(E,C),membermeronym(A,D),haspart(B,C),similarto(F,B).
memberofdomainregion(A,B):- similarto(B,A),alsosee(A,B),similarto(C,A).
memberofdomainregion(A,B):- derivationallyrelatedform(E,F),membermeronym(F,C),similarto(B,E),verbgroup(A,D).
memberofdomainregion(A,B):- haspart(C,D),membermeronym(F,C),memberofdomainusage(B,E),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- hypernym(C,D),haspart(B,C),membermeronym(A,D),instancehypernym(D,C).
memberofdomainregion(A,B):- derivationallyrelatedform(D,A),verbgroup(C,B),hypernym(E,C),haspart(B,C).
memberofdomainregion(A,B):- hypernym(C,A),similarto(B,A),memberofdomainusage(B,D).
memberofdomainregion(A,B):- membermeronym(A,C),membermeronym(F,C),memberofdomainusage(B,E),synsetdomaintopicof(D,C).
memberofdomainregion(A,B):- verbgroup(C,D),alsosee(A,E),hypernym(F,D),haspart(B,C).
memberofdomainregion(A,B):- alsosee(B,C),memberofdomainusage(A,E),membermeronym(F,C),similarto(B,D).
memberofdomainregion(A,B):- alsosee(F,D),membermeronym(F,C),memberofdomainusage(E,B),verbgroup(A,D).
memberofdomainregion(A,B):- haspart(B,E),memberofdomainusage(A,E),similarto(B,D),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(F,B),derivationallyrelatedform(D,E),verbgroup(A,E),haspart(B,C).
memberofdomainregion(A,B):- hypernym(E,B),haspart(D,A),membermeronym(F,C),instancehypernym(F,B).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),hypernym(D,E),haspart(B,C),alsosee(E,A).
memberofdomainregion(A,B):- verbgroup(E,C),memberofdomainusage(B,A),derivationallyrelatedform(A,D),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(D,C),hypernym(B,A),derivationallyrelatedform(B,C).
memberofdomainregion(A,B):- memberofdomainusage(B,F),synsetdomaintopicof(A,D),membermeronym(F,C),hypernym(E,A).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),haspart(B,C),verbgroup(A,B),memberofdomainusage(B,D).
memberofdomainregion(A,B):- memberofdomainusage(C,B),verbgroup(B,C),derivationallyrelatedform(D,A),haspart(B,C).
memberofdomainregion(A,B):- haspart(D,E),similarto(D,B),similarto(A,C).
memberofdomainregion(A,B):- haspart(B,C),membermeronym(F,B),membermeronym(E,D),verbgroup(A,D).
memberofdomainregion(A,B):- instancehypernym(A,B),similarto(D,B),haspart(B,C),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- instancehypernym(D,A),synsetdomaintopicof(D,C),memberofdomainusage(B,D).
memberofdomainregion(A,B):- haspart(C,B),membermeronym(F,C),verbgroup(B,E),verbgroup(A,D).
memberofdomainregion(A,B):- instancehypernym(D,E),instancehypernym(A,D),haspart(B,C),memberofdomainusage(C,D).
memberofdomainregion(A,B):- haspart(B,A),instancehypernym(A,C),verbgroup(C,A).
memberofdomainregion(A,B):- derivationallyrelatedform(E,D),memberofdomainusage(B,A),verbgroup(D,B),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(A,E),haspart(A,D),haspart(B,C),membermeronym(A,F).
memberofdomainregion(A,B):- verbgroup(C,D),verbgroup(A,B),derivationallyrelatedform(D,B).
memberofdomainregion(A,B):- synsetdomaintopicof(B,D),memberofdomainusage(A,E),instancehypernym(F,E),membermeronym(F,C).
memberofdomainregion(A,B):- haspart(C,D),haspart(A,D),haspart(B,C),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- alsosee(A,C),similarto(C,B),synsetdomaintopicof(A,B).
memberofdomainregion(A,B):- membermeronym(A,E),instancehypernym(B,D),hypernym(B,F),haspart(B,C).
memberofdomainregion(A,B):- similarto(A,E),derivationallyrelatedform(D,B),haspart(B,C),similarto(F,B).
