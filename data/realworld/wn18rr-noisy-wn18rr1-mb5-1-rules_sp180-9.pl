memberofdomainregion(A,B):- synsetdomaintopicof(A,D),haspart(B,C),instancehypernym(C,A),memberofdomainusage(D,A).
memberofdomainregion(A,B):- synsetdomaintopicof(E,B),haspart(A,C),verbgroup(D,E).
memberofdomainregion(A,B):- haspart(E,F),hypernym(F,B),membermeronym(F,C),synsetdomaintopicof(A,D).
memberofdomainregion(A,B):- alsosee(A,E),membermeronym(D,E),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(D,A),instancehypernym(E,B),hypernym(D,C),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),alsosee(D,A),verbgroup(E,B),derivationallyrelatedform(E,C).
memberofdomainregion(A,B):- derivationallyrelatedform(A,D),alsosee(C,A),haspart(B,C),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- synsetdomaintopicof(B,A),instancehypernym(A,D),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- membermeronym(F,C),derivationallyrelatedform(E,B),similarto(D,B),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- similarto(D,C),synsetdomaintopicof(A,C),alsosee(A,D),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(A,E),synsetdomaintopicof(A,D),derivationallyrelatedform(C,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,C),haspart(A,D),hypernym(C,E),derivationallyrelatedform(F,A).
memberofdomainregion(A,B):- hypernym(E,B),hypernym(E,D),membermeronym(F,C),memberofdomainusage(C,A).
memberofdomainregion(A,B):- hypernym(C,A),hypernym(B,C),synsetdomaintopicof(A,D),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(E,C),synsetdomaintopicof(D,C),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- instancehypernym(B,A),haspart(D,A),memberofdomainusage(A,C).
memberofdomainregion(A,B):- synsetdomaintopicof(D,A),hypernym(A,E),haspart(B,C),derivationallyrelatedform(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),membermeronym(F,C),instancehypernym(B,D),derivationallyrelatedform(F,D).
memberofdomainregion(A,B):- alsosee(C,B),membermeronym(A,B),verbgroup(D,B).
memberofdomainregion(A,B):- verbgroup(E,D),verbgroup(E,A),membermeronym(F,C),similarto(C,B).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),haspart(B,C),membermeronym(C,E),memberofdomainusage(D,A).
memberofdomainregion(A,B):- membermeronym(A,E),membermeronym(C,B),haspart(B,C),memberofdomainusage(C,D).
memberofdomainregion(A,B):- instancehypernym(B,A),similarto(C,B),verbgroup(A,D).
memberofdomainregion(A,B):- verbgroup(D,A),memberofdomainusage(C,B),instancehypernym(D,E).
memberofdomainregion(A,B):- memberofdomainusage(B,E),synsetdomaintopicof(D,B),haspart(B,C),membermeronym(A,F).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),derivationallyrelatedform(E,D),similarto(D,B),haspart(B,C).
memberofdomainregion(A,B):- hypernym(C,B),derivationallyrelatedform(D,A),similarto(B,C).
memberofdomainregion(A,B):- instancehypernym(A,E),instancehypernym(D,F),haspart(B,C),hypernym(E,F).
memberofdomainregion(A,B):- instancehypernym(A,D),membermeronym(A,E),memberofdomainusage(D,B),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(E,B),haspart(A,F),haspart(B,C),memberofdomainusage(C,D).
memberofdomainregion(A,B):- haspart(F,C),membermeronym(A,E),haspart(B,C),instancehypernym(D,C).
memberofdomainregion(A,B):- hypernym(E,B),memberofdomainusage(C,B),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,C),membermeronym(E,B),instancehypernym(D,A),verbgroup(A,D).
memberofdomainregion(A,B):- instancehypernym(A,E),haspart(A,D),alsosee(A,B),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),derivationallyrelatedform(E,A),membermeronym(D,E),haspart(C,B).
memberofdomainregion(A,B):- haspart(E,D),membermeronym(F,C),membermeronym(C,A),hypernym(D,B).
memberofdomainregion(A,B):- verbgroup(D,B),instancehypernym(D,C),verbgroup(C,A).
memberofdomainregion(A,B):- hypernym(D,E),membermeronym(A,E),haspart(B,C),verbgroup(C,A).
memberofdomainregion(A,B):- haspart(E,D),similarto(A,E),haspart(B,C),membermeronym(E,D).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),synsetdomaintopicof(F,D),haspart(D,C),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(E,B),membermeronym(E,D),similarto(A,C).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),similarto(C,D),verbgroup(D,F),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),verbgroup(B,E),haspart(B,C),synsetdomaintopicof(A,B).
memberofdomainregion(A,B):- similarto(D,E),hypernym(E,A),haspart(B,C),haspart(A,C).
memberofdomainregion(A,B):- memberofdomainusage(E,C),derivationallyrelatedform(A,D),haspart(E,B).
memberofdomainregion(A,B):- memberofdomainusage(A,E),memberofdomainusage(C,A),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),membermeronym(C,B),membermeronym(F,C),hypernym(C,D).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(B,E),haspart(D,C),membermeronym(A,F).
memberofdomainregion(A,B):- similarto(B,F),membermeronym(F,C),memberofdomainusage(E,D),membermeronym(E,A).
memberofdomainregion(A,B):- membermeronym(A,C),instancehypernym(A,D),verbgroup(C,B),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),similarto(D,C),verbgroup(A,B),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(D,E),haspart(B,C),alsosee(F,E),instancehypernym(F,A).
memberofdomainregion(A,B):- membermeronym(F,C),verbgroup(C,B),hypernym(A,E),alsosee(C,D).
memberofdomainregion(A,B):- instancehypernym(A,D),instancehypernym(A,C),hypernym(D,B).
memberofdomainregion(A,B):- memberofdomainusage(D,B),derivationallyrelatedform(E,A),membermeronym(C,D).
memberofdomainregion(A,B):- derivationallyrelatedform(A,B),membermeronym(D,E),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(B,E),derivationallyrelatedform(D,A),verbgroup(C,F),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(E,B),memberofdomainusage(D,F),instancehypernym(A,D),membermeronym(F,C).
memberofdomainregion(A,B):- verbgroup(E,A),alsosee(F,C),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),similarto(A,D),instancehypernym(D,C).
memberofdomainregion(A,B):- membermeronym(B,C),derivationallyrelatedform(C,A),alsosee(A,D).
memberofdomainregion(A,B):- haspart(B,C),alsosee(D,B),membermeronym(C,A),membermeronym(D,A).
memberofdomainregion(A,B):- synsetdomaintopicof(B,D),derivationallyrelatedform(C,A),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),synsetdomaintopicof(D,A),memberofdomainusage(A,E),membermeronym(F,C).
memberofdomainregion(A,B):- alsosee(A,E),hypernym(F,B),membermeronym(F,C),memberofdomainusage(C,D).
memberofdomainregion(A,B):- verbgroup(A,C),synsetdomaintopicof(D,A),memberofdomainusage(B,D).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),similarto(E,A),derivationallyrelatedform(F,D),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(C,B),similarto(A,B),alsosee(B,D).
memberofdomainregion(A,B):- similarto(F,A),membermeronym(F,C),membermeronym(B,E),verbgroup(A,D).
memberofdomainregion(A,B):- synsetdomaintopicof(D,B),synsetdomaintopicof(F,A),haspart(B,C),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- membermeronym(A,C),derivationallyrelatedform(B,D),similarto(D,B),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(C,E),verbgroup(D,B),haspart(B,C),synsetdomaintopicof(A,B).
memberofdomainregion(A,B):- membermeronym(A,E),alsosee(D,B),membermeronym(F,C),instancehypernym(A,F).
memberofdomainregion(A,B):- hypernym(A,C),membermeronym(B,E),verbgroup(D,B).
memberofdomainregion(A,B):- similarto(B,E),membermeronym(F,C),alsosee(A,D),derivationallyrelatedform(F,A).
memberofdomainregion(A,B):- membermeronym(B,E),memberofdomainusage(A,D),haspart(B,C),haspart(D,F).
memberofdomainregion(A,B):- memberofdomainusage(A,E),alsosee(D,A),synsetdomaintopicof(D,C),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),hypernym(E,D),haspart(B,C),verbgroup(C,E).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),membermeronym(F,C),similarto(B,D),derivationallyrelatedform(F,E).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),derivationallyrelatedform(B,A),alsosee(D,A).
memberofdomainregion(A,B):- memberofdomainusage(D,B),verbgroup(C,F),haspart(B,C),hypernym(E,A).
memberofdomainregion(A,B):- similarto(B,E),derivationallyrelatedform(C,D),verbgroup(A,D).
memberofdomainregion(A,B):- hypernym(C,D),synsetdomaintopicof(B,D),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- verbgroup(C,D),verbgroup(B,C),derivationallyrelatedform(C,A).
memberofdomainregion(A,B):- haspart(B,A),hypernym(A,B),alsosee(A,B).
memberofdomainregion(A,B):- derivationallyrelatedform(C,A),alsosee(B,A),verbgroup(C,A).
memberofdomainregion(A,B):- synsetdomaintopicof(D,E),membermeronym(F,C),memberofdomainusage(B,E),verbgroup(F,A).
memberofdomainregion(A,B):- verbgroup(A,F),memberofdomainusage(E,F),derivationallyrelatedform(D,A),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(C,A),instancehypernym(B,D),similarto(D,B),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(F,D),membermeronym(F,C),instancehypernym(E,B),memberofdomainusage(A,D).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(B,E),memberofdomainusage(D,A),alsosee(D,F).
memberofdomainregion(A,B):- haspart(B,C),haspart(A,D),instancehypernym(D,C),hypernym(E,A).
memberofdomainregion(A,B):- similarto(C,D),hypernym(A,E),synsetdomaintopicof(C,B).
memberofdomainregion(A,B):- membermeronym(F,C),memberofdomainusage(B,E),derivationallyrelatedform(D,A),synsetdomaintopicof(E,F).
memberofdomainregion(A,B):- alsosee(A,E),memberofdomainusage(E,B),verbgroup(D,B),haspart(B,C).
memberofdomainregion(A,B):- hypernym(D,E),membermeronym(E,F),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- hypernym(B,C),membermeronym(F,C),verbgroup(D,F),alsosee(E,A).
memberofdomainregion(A,B):- instancehypernym(E,F),alsosee(D,A),haspart(B,C),memberofdomainusage(A,F).
memberofdomainregion(A,B):- instancehypernym(A,E),memberofdomainusage(D,F),haspart(B,C),instancehypernym(B,F).
memberofdomainregion(A,B):- hypernym(C,D),synsetdomaintopicof(A,D),derivationallyrelatedform(E,A),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(D,C),haspart(B,C),instancehypernym(A,E),instancehypernym(D,C).
memberofdomainregion(A,B):- alsosee(D,C),hypernym(A,C),alsosee(D,B).
memberofdomainregion(A,B):- haspart(E,F),haspart(B,C),membermeronym(A,D),derivationallyrelatedform(A,F).
memberofdomainregion(A,B):- haspart(E,D),verbgroup(A,B),haspart(B,C),hypernym(D,B).
memberofdomainregion(A,B):- memberofdomainusage(D,C),alsosee(A,E),haspart(B,C),hypernym(B,D).
memberofdomainregion(A,B):- haspart(E,D),membermeronym(C,B),membermeronym(F,C),hypernym(A,E).
memberofdomainregion(A,B):- verbgroup(D,A),membermeronym(F,C),haspart(E,A),synsetdomaintopicof(B,C).
memberofdomainregion(A,B):- alsosee(D,B),memberofdomainusage(B,A),haspart(B,C),instancehypernym(B,C).
memberofdomainregion(A,B):- instancehypernym(A,C),memberofdomainusage(B,D),similarto(C,A).
memberofdomainregion(A,B):- verbgroup(B,F),membermeronym(F,C),memberofdomainusage(E,F),synsetdomaintopicof(D,A).
memberofdomainregion(A,B):- haspart(D,C),instancehypernym(E,A),alsosee(B,D).
memberofdomainregion(A,B):- hypernym(B,A),similarto(A,D),haspart(B,C),alsosee(E,A).
memberofdomainregion(A,B):- similarto(A,E),synsetdomaintopicof(D,E),alsosee(D,A),haspart(B,C).
memberofdomainregion(A,B):- haspart(E,B),memberofdomainusage(D,F),membermeronym(F,C),hypernym(A,D).
memberofdomainregion(A,B):- similarto(A,B),hypernym(A,D),alsosee(C,A).
memberofdomainregion(A,B):- instancehypernym(D,B),instancehypernym(D,E),haspart(B,C),verbgroup(B,A).
memberofdomainregion(A,B):- membermeronym(F,C),synsetdomaintopicof(F,D),hypernym(F,A),derivationallyrelatedform(E,B).
memberofdomainregion(A,B):- verbgroup(E,A),synsetdomaintopicof(D,A),synsetdomaintopicof(C,B).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),membermeronym(F,C),membermeronym(F,B),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- similarto(D,B),verbgroup(A,E),derivationallyrelatedform(A,F),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,C),memberofdomainusage(D,E),haspart(A,B),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- verbgroup(E,A),synsetdomaintopicof(B,D),synsetdomaintopicof(A,C).
memberofdomainregion(A,B):- membermeronym(B,A),haspart(E,C),haspart(B,C),hypernym(D,B).
memberofdomainregion(A,B):- hypernym(C,D),hypernym(B,E),membermeronym(F,C),alsosee(A,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),similarto(D,C),haspart(B,C),membermeronym(D,A).
memberofdomainregion(A,B):- derivationallyrelatedform(A,D),memberofdomainusage(A,C),synsetdomaintopicof(E,C),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(E,C),verbgroup(B,E),verbgroup(A,D).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),membermeronym(F,C),derivationallyrelatedform(A,D),similarto(C,D).
memberofdomainregion(A,B):- alsosee(D,E),memberofdomainusage(F,B),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- instancehypernym(A,E),hypernym(C,B),alsosee(C,D).
memberofdomainregion(A,B):- synsetdomaintopicof(C,A),similarto(A,D),haspart(B,C),verbgroup(D,E).
memberofdomainregion(A,B):- alsosee(E,B),memberofdomainusage(C,B),membermeronym(F,C),membermeronym(A,D).
memberofdomainregion(A,B):- similarto(A,E),memberofdomainusage(D,F),memberofdomainusage(E,F),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(A,B),similarto(C,A).
memberofdomainregion(A,B):- instancehypernym(A,E),membermeronym(B,D),haspart(B,C),memberofdomainusage(E,D).
memberofdomainregion(A,B):- haspart(F,A),hypernym(E,D),hypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- alsosee(A,C),hypernym(C,B),synsetdomaintopicof(A,C).
memberofdomainregion(A,B):- haspart(B,C),instancehypernym(A,D),hypernym(E,C),membermeronym(B,D).
memberofdomainregion(A,B):- derivationallyrelatedform(A,D),instancehypernym(B,D),haspart(B,D),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(D,E),alsosee(D,B),alsosee(D,A),haspart(B,C).
memberofdomainregion(A,B):- hypernym(B,E),membermeronym(F,C),alsosee(A,D),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- membermeronym(A,E),alsosee(D,B),alsosee(C,D).
memberofdomainregion(A,B):- membermeronym(A,E),instancehypernym(D,E),hypernym(F,A),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),haspart(C,A),similarto(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),similarto(C,B),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),similarto(E,C),haspart(B,C),hypernym(D,B).
memberofdomainregion(A,B):- synsetdomaintopicof(E,A),hypernym(D,E),haspart(A,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(D,B),instancehypernym(A,F),haspart(A,E).
memberofdomainregion(A,B):- hypernym(C,D),derivationallyrelatedform(D,B),membermeronym(F,C),similarto(E,A).
memberofdomainregion(A,B):- alsosee(A,E),membermeronym(F,C),alsosee(D,C),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(C,A),derivationallyrelatedform(E,B),similarto(A,D),haspart(B,C).
memberofdomainregion(A,B):- alsosee(A,B),membermeronym(A,D),memberofdomainusage(C,D).
memberofdomainregion(A,B):- alsosee(D,C),membermeronym(A,E),haspart(F,E),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(B,F),instancehypernym(E,F),membermeronym(F,C),synsetdomaintopicof(D,A).
memberofdomainregion(A,B):- haspart(B,C),derivationallyrelatedform(D,C),memberofdomainusage(D,B),membermeronym(D,A).
memberofdomainregion(A,B):- haspart(E,B),membermeronym(F,C),verbgroup(D,F),membermeronym(A,F).
memberofdomainregion(A,B):- hypernym(C,A),haspart(B,C),hypernym(A,D),verbgroup(E,B).
memberofdomainregion(A,B):- derivationallyrelatedform(A,B),memberofdomainusage(A,C),instancehypernym(B,D).
memberofdomainregion(A,B):- similarto(A,E),haspart(B,C),derivationallyrelatedform(E,D),verbgroup(B,A).
memberofdomainregion(A,B):- haspart(B,C),similarto(E,C),verbgroup(D,B),derivationallyrelatedform(F,A).
memberofdomainregion(A,B):- haspart(D,A),memberofdomainusage(E,B),hypernym(D,C).
memberofdomainregion(A,B):- haspart(C,D),synsetdomaintopicof(E,A),verbgroup(D,B).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(D,B),instancehypernym(E,B),synsetdomaintopicof(A,F).
memberofdomainregion(A,B):- derivationallyrelatedform(A,B),membermeronym(C,E),alsosee(A,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(D,B),hypernym(D,C),verbgroup(A,B).
memberofdomainregion(A,B):- membermeronym(B,C),derivationallyrelatedform(A,D),similarto(A,C).
memberofdomainregion(A,B):- membermeronym(F,C),derivationallyrelatedform(A,D),synsetdomaintopicof(F,B),haspart(F,E).
memberofdomainregion(A,B):- hypernym(E,A),memberofdomainusage(A,D),haspart(B,C),similarto(D,E).
memberofdomainregion(A,B):- similarto(A,B),synsetdomaintopicof(A,C),membermeronym(A,D).
memberofdomainregion(A,B):- memberofdomainusage(B,C),derivationallyrelatedform(C,A),haspart(C,B).
memberofdomainregion(A,B):- membermeronym(D,F),verbgroup(A,E),haspart(B,C),membermeronym(A,F).
memberofdomainregion(A,B):- instancehypernym(A,D),hypernym(C,E),synsetdomaintopicof(E,C),haspart(B,C).
memberofdomainregion(A,B):- haspart(D,B),derivationallyrelatedform(B,A),similarto(D,A),haspart(B,C).
memberofdomainregion(A,B):- alsosee(E,D),membermeronym(F,C),memberofdomainusage(D,B),hypernym(A,F).
memberofdomainregion(A,B):- verbgroup(F,D),alsosee(A,E),instancehypernym(A,F),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(C,A),membermeronym(F,C),synsetdomaintopicof(E,D),similarto(B,D).
memberofdomainregion(A,B):- hypernym(E,B),verbgroup(C,D),membermeronym(F,C),haspart(A,F).
memberofdomainregion(A,B):- similarto(A,C),derivationallyrelatedform(D,A),haspart(B,C),synsetdomaintopicof(A,B).
memberofdomainregion(A,B):- hypernym(E,B),membermeronym(F,C),haspart(F,B),membermeronym(D,A).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(B,E),hypernym(D,C),haspart(A,C).
