memberofdomainregion(A,B):- memberofdomainusage(D,C),membermeronym(F,C),memberofdomainusage(F,B),alsosee(E,A).
memberofdomainregion(A,B):- synsetdomaintopicof(C,A),haspart(A,D),hypernym(C,B).
memberofdomainregion(A,B):- verbgroup(B,D),alsosee(D,E),verbgroup(C,A).
memberofdomainregion(A,B):- synsetdomaintopicof(D,E),membermeronym(F,C),memberofdomainusage(E,B),similarto(A,F).
memberofdomainregion(A,B):- verbgroup(B,D),synsetdomaintopicof(A,D),haspart(B,C),hypernym(E,B).
memberofdomainregion(A,B):- membermeronym(C,B),derivationallyrelatedform(A,D),alsosee(C,A).
memberofdomainregion(A,B):- synsetdomaintopicof(C,B),memberofdomainusage(A,B).
memberofdomainregion(A,B):- similarto(D,C),alsosee(E,B),verbgroup(A,D).
memberofdomainregion(A,B):- similarto(A,D),verbgroup(B,C),haspart(B,C),similarto(A,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),instancehypernym(B,E),membermeronym(F,C),verbgroup(C,D).
memberofdomainregion(A,B):- instancehypernym(A,E),membermeronym(F,C),haspart(B,D),synsetdomaintopicof(D,F).
memberofdomainregion(A,B):- haspart(E,B),membermeronym(F,C),membermeronym(C,A),memberofdomainusage(D,A).
memberofdomainregion(A,B):- membermeronym(F,C),haspart(A,D),membermeronym(C,A),derivationallyrelatedform(E,B).
memberofdomainregion(A,B):- synsetdomaintopicof(E,A),instancehypernym(B,D),similarto(C,A).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),verbgroup(B,C),alsosee(D,E),haspart(B,C).
memberofdomainregion(A,B):- alsosee(A,E),membermeronym(F,C),alsosee(F,E),hypernym(D,B).
memberofdomainregion(A,B):- similarto(D,A),alsosee(E,B),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- memberofdomainusage(B,F),membermeronym(F,C),membermeronym(E,F),hypernym(A,D).
memberofdomainregion(A,B):- instancehypernym(F,C),verbgroup(A,E),haspart(B,C),memberofdomainusage(F,D).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),haspart(B,C),instancehypernym(A,C),alsosee(C,D).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),membermeronym(F,C),derivationallyrelatedform(B,F),membermeronym(E,A).
memberofdomainregion(A,B):- similarto(E,D),haspart(E,A),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- alsosee(F,A),haspart(E,B),verbgroup(D,B),haspart(B,C).
memberofdomainregion(A,B):- hypernym(C,A),hypernym(C,D),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- verbgroup(D,A),alsosee(A,D),haspart(B,C),alsosee(D,C).
memberofdomainregion(A,B):- memberofdomainusage(B,C),instancehypernym(A,D),haspart(B,C),verbgroup(B,A).
memberofdomainregion(A,B):- memberofdomainusage(B,F),membermeronym(F,C),synsetdomaintopicof(D,A),alsosee(E,A).
memberofdomainregion(A,B):- instancehypernym(A,C),haspart(B,C),memberofdomainusage(D,A),memberofdomainusage(B,D).
memberofdomainregion(A,B):- instancehypernym(A,D),instancehypernym(C,D),haspart(B,C),memberofdomainusage(E,A).
memberofdomainregion(A,B):- verbgroup(C,D),alsosee(A,D),haspart(B,C),haspart(E,B).
memberofdomainregion(A,B):- verbgroup(C,D),membermeronym(A,E),haspart(B,C),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- hypernym(A,C),membermeronym(F,C),similarto(D,B),synsetdomaintopicof(A,E).
memberofdomainregion(A,B):- instancehypernym(C,A),membermeronym(A,D),haspart(B,C),similarto(E,B).
memberofdomainregion(A,B):- membermeronym(F,C),similarto(D,F),similarto(E,B),membermeronym(D,A).
memberofdomainregion(A,B):- verbgroup(E,D),alsosee(C,B),instancehypernym(A,D).
memberofdomainregion(A,B):- membermeronym(A,D),memberofdomainusage(E,C),memberofdomainusage(D,E),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(A,E),instancehypernym(C,D),haspart(B,C),verbgroup(B,E).
memberofdomainregion(A,B):- alsosee(D,C),haspart(A,D),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),verbgroup(E,F),haspart(B,C),membermeronym(A,F).
memberofdomainregion(A,B):- alsosee(E,A),membermeronym(D,B),haspart(B,C),membermeronym(A,F).
memberofdomainregion(A,B):- haspart(E,F),membermeronym(C,B),similarto(D,A),membermeronym(F,C).
memberofdomainregion(A,B):- instancehypernym(E,F),membermeronym(F,C),verbgroup(A,C),alsosee(B,D).
memberofdomainregion(A,B):- synsetdomaintopicof(E,D),haspart(D,A),membermeronym(F,C),verbgroup(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(C,E),similarto(A,D),similarto(B,A),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),similarto(E,A),haspart(B,C),verbgroup(C,A).
memberofdomainregion(A,B):- alsosee(A,E),haspart(B,C),derivationallyrelatedform(B,D),verbgroup(F,E).
memberofdomainregion(A,B):- similarto(C,F),memberofdomainusage(E,C),derivationallyrelatedform(A,D),haspart(B,C).
memberofdomainregion(A,B):- alsosee(B,C),derivationallyrelatedform(D,E),verbgroup(A,D).
memberofdomainregion(A,B):- verbgroup(E,D),memberofdomainusage(E,C),haspart(B,C),instancehypernym(F,A).
memberofdomainregion(A,B):- similarto(F,B),membermeronym(D,E),haspart(B,C),alsosee(A,D).
memberofdomainregion(A,B):- hypernym(C,D),verbgroup(A,E),haspart(B,C),similarto(C,F).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),haspart(E,C),verbgroup(A,D).
memberofdomainregion(A,B):- hypernym(F,C),memberofdomainusage(A,D),haspart(B,C),memberofdomainusage(E,A).
memberofdomainregion(A,B):- similarto(E,D),synsetdomaintopicof(C,A),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- hypernym(B,D),membermeronym(F,C),synsetdomaintopicof(A,C),synsetdomaintopicof(F,E).
memberofdomainregion(A,B):- verbgroup(D,A),haspart(E,B),membermeronym(F,C),alsosee(C,E).
memberofdomainregion(A,B):- membermeronym(D,C),membermeronym(F,C),memberofdomainusage(F,B),hypernym(A,E).
memberofdomainregion(A,B):- derivationallyrelatedform(E,D),instancehypernym(D,B),membermeronym(B,A),haspart(B,C).
memberofdomainregion(A,B):- hypernym(B,D),derivationallyrelatedform(B,E),membermeronym(F,C),similarto(F,A).
memberofdomainregion(A,B):- memberofdomainusage(D,C),haspart(B,C),synsetdomaintopicof(A,B).
memberofdomainregion(A,B):- instancehypernym(E,A),membermeronym(A,D),similarto(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),instancehypernym(C,A),synsetdomaintopicof(D,C),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- haspart(B,C),instancehypernym(C,A),instancehypernym(A,D),membermeronym(D,A).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(F,B),membermeronym(A,D),hypernym(E,F).
memberofdomainregion(A,B):- instancehypernym(C,B),similarto(A,D),derivationallyrelatedform(D,A),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),alsosee(D,A),alsosee(A,D),haspart(B,C).
memberofdomainregion(A,B):- similarto(A,E),haspart(B,C),memberofdomainusage(A,D),derivationallyrelatedform(B,F).
memberofdomainregion(A,B):- haspart(E,D),derivationallyrelatedform(B,E),membermeronym(F,C),synsetdomaintopicof(C,A).
memberofdomainregion(A,B):- membermeronym(D,B),haspart(E,C),haspart(B,C),hypernym(A,F).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),instancehypernym(D,A),haspart(B,C),membermeronym(F,D).
memberofdomainregion(A,B):- verbgroup(D,A),hypernym(F,B),membermeronym(F,C),haspart(B,E).
memberofdomainregion(A,B):- verbgroup(F,D),derivationallyrelatedform(A,D),similarto(E,A),haspart(B,C).
memberofdomainregion(A,B):- hypernym(C,A),haspart(C,E),similarto(D,B),haspart(B,C).
memberofdomainregion(A,B):- hypernym(A,C),alsosee(C,B),haspart(B,C),hypernym(D,B).
memberofdomainregion(A,B):- similarto(E,A),haspart(B,C),memberofdomainusage(E,D),memberofdomainusage(A,F).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),hypernym(A,C),haspart(B,C),hypernym(D,B).
memberofdomainregion(A,B):- memberofdomainusage(B,C),membermeronym(F,C),synsetdomaintopicof(D,C),membermeronym(E,A).
memberofdomainregion(A,B):- haspart(D,A),membermeronym(F,C),membermeronym(B,E),verbgroup(C,A).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(F,E),similarto(B,D),haspart(C,A).
memberofdomainregion(A,B):- instancehypernym(C,B),verbgroup(A,C),haspart(B,C).
memberofdomainregion(A,B):- hypernym(D,A),memberofdomainusage(F,C),instancehypernym(E,B),haspart(B,C).
memberofdomainregion(A,B):- haspart(E,B),alsosee(A,B),similarto(D,B),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(C,F),memberofdomainusage(A,E),hypernym(A,D),haspart(B,C).
memberofdomainregion(A,B):- similarto(A,E),memberofdomainusage(E,C),synsetdomaintopicof(B,D),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),derivationallyrelatedform(B,D),derivationallyrelatedform(A,F),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(B,A),membermeronym(C,A),similarto(A,C).
memberofdomainregion(A,B):- instancehypernym(D,B),verbgroup(E,A),haspart(B,C),haspart(C,D).
memberofdomainregion(A,B):- instancehypernym(A,B),similarto(A,B),haspart(B,C),hypernym(D,B).
memberofdomainregion(A,B):- instancehypernym(C,B),alsosee(B,A),haspart(B,C),haspart(A,C).
memberofdomainregion(A,B):- membermeronym(B,C),synsetdomaintopicof(E,A),alsosee(E,D).
memberofdomainregion(A,B):- haspart(F,A),instancehypernym(E,B),hypernym(D,F),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),membermeronym(E,C),alsosee(A,D).
memberofdomainregion(A,B):- instancehypernym(E,F),membermeronym(F,C),haspart(A,D),synsetdomaintopicof(F,B).
memberofdomainregion(A,B):- membermeronym(A,C),haspart(D,A),instancehypernym(B,D).
memberofdomainregion(A,B):- haspart(C,A),hypernym(A,E),membermeronym(B,D).
memberofdomainregion(A,B):- memberofdomainusage(B,C),instancehypernym(C,A),membermeronym(B,D).
memberofdomainregion(A,B):- instancehypernym(D,F),verbgroup(A,C),membermeronym(F,C),membermeronym(E,B).
memberofdomainregion(A,B):- alsosee(B,C),membermeronym(A,B),memberofdomainusage(A,D).
memberofdomainregion(A,B):- instancehypernym(F,E),instancehypernym(A,F),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(D,A),memberofdomainusage(A,E),haspart(B,C),hypernym(E,B).
memberofdomainregion(A,B):- memberofdomainusage(C,B),haspart(A,D),hypernym(B,A),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(B,E),membermeronym(F,C),derivationallyrelatedform(A,D),synsetdomaintopicof(A,F).
memberofdomainregion(A,B):- similarto(E,A),haspart(A,D),alsosee(D,A),haspart(B,C).
memberofdomainregion(A,B):- haspart(C,D),membermeronym(F,C),instancehypernym(E,B),alsosee(A,F).
memberofdomainregion(A,B):- instancehypernym(C,B),similarto(E,D),haspart(A,E).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),membermeronym(F,C),memberofdomainusage(B,E),derivationallyrelatedform(E,C).
memberofdomainregion(A,B):- membermeronym(B,C),hypernym(E,D),instancehypernym(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,C),hypernym(C,E),verbgroup(D,B),memberofdomainusage(D,A).
memberofdomainregion(A,B):- hypernym(E,B),instancehypernym(D,E),haspart(B,C),haspart(A,C).
memberofdomainregion(A,B):- similarto(E,D),similarto(B,A),memberofdomainusage(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(C,D),synsetdomaintopicof(D,A),verbgroup(C,B).
memberofdomainregion(A,B):- derivationallyrelatedform(A,B),synsetdomaintopicof(C,D),similarto(C,B).
memberofdomainregion(A,B):- synsetdomaintopicof(D,E),instancehypernym(E,A),haspart(B,C),memberofdomainusage(A,F).
memberofdomainregion(A,B):- similarto(E,D),membermeronym(F,C),alsosee(D,A),alsosee(C,B).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(B,E),memberofdomainusage(A,D),verbgroup(C,E).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),synsetdomaintopicof(D,B),haspart(B,C),derivationallyrelatedform(E,C).
memberofdomainregion(A,B):- hypernym(B,E),verbgroup(D,C),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- similarto(A,E),instancehypernym(C,A),hypernym(D,C),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),memberofdomainusage(E,F),alsosee(D,A),verbgroup(F,B).
memberofdomainregion(A,B):- memberofdomainusage(E,C),membermeronym(F,C),hypernym(F,B),membermeronym(A,D).
memberofdomainregion(A,B):- memberofdomainusage(B,C),membermeronym(F,C),synsetdomaintopicof(E,A),hypernym(A,D).
memberofdomainregion(A,B):- synsetdomaintopicof(E,A),membermeronym(F,C),hypernym(F,D),alsosee(C,B).
memberofdomainregion(A,B):- instancehypernym(A,E),memberofdomainusage(B,C),haspart(B,C),membermeronym(E,D).
memberofdomainregion(A,B):- instancehypernym(E,B),verbgroup(A,E),haspart(B,C),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- derivationallyrelatedform(F,E),instancehypernym(F,B),alsosee(A,D),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(F,C),similarto(A,E),haspart(B,C),synsetdomaintopicof(D,F).
memberofdomainregion(A,B):- synsetdomaintopicof(D,A),alsosee(E,D),instancehypernym(B,C).
memberofdomainregion(A,B):- haspart(B,A),instancehypernym(C,A),membermeronym(A,B).
memberofdomainregion(A,B):- haspart(B,C),derivationallyrelatedform(A,D),instancehypernym(B,F),hypernym(E,A).
memberofdomainregion(A,B):- similarto(A,B),derivationallyrelatedform(B,D),instancehypernym(D,C).
memberofdomainregion(A,B):- verbgroup(D,A),haspart(B,C),memberofdomainusage(E,D),instancehypernym(C,F).
memberofdomainregion(A,B):- instancehypernym(A,B),similarto(B,A),memberofdomainusage(A,C).
memberofdomainregion(A,B):- haspart(B,E),synsetdomaintopicof(A,D),synsetdomaintopicof(E,A),haspart(B,C).
memberofdomainregion(A,B):- alsosee(F,A),membermeronym(F,C),derivationallyrelatedform(B,D),similarto(C,E).
memberofdomainregion(A,B):- hypernym(C,A),membermeronym(F,C),membermeronym(D,B),alsosee(F,E).
memberofdomainregion(A,B):- haspart(C,D),hypernym(D,A),similarto(B,E).
memberofdomainregion(A,B):- verbgroup(D,A),membermeronym(F,C),hypernym(E,A),memberofdomainusage(F,B).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),haspart(D,E),synsetdomaintopicof(A,C),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),haspart(D,A),synsetdomaintopicof(B,F),verbgroup(F,E).
memberofdomainregion(A,B):- similarto(F,A),membermeronym(F,C),memberofdomainusage(E,B),alsosee(D,A).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),membermeronym(F,C),memberofdomainusage(D,E),instancehypernym(B,C).
memberofdomainregion(A,B):- memberofdomainusage(B,E),verbgroup(D,F),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- membermeronym(D,C),hypernym(D,E),haspart(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(E,D),alsosee(A,E),haspart(B,C),membermeronym(C,D).
memberofdomainregion(A,B):- verbgroup(D,A),membermeronym(F,C),memberofdomainusage(E,D),similarto(B,C).
memberofdomainregion(A,B):- alsosee(A,E),instancehypernym(F,D),haspart(B,C),membermeronym(C,D).
memberofdomainregion(A,B):- membermeronym(A,E),instancehypernym(B,D),haspart(B,C),hypernym(D,B).
memberofdomainregion(A,B):- alsosee(B,C),membermeronym(F,C),alsosee(E,B),alsosee(D,A).
memberofdomainregion(A,B):- derivationallyrelatedform(E,B),similarto(D,B),verbgroup(C,A).
memberofdomainregion(A,B):- synsetdomaintopicof(E,B),instancehypernym(C,E),alsosee(D,A).
memberofdomainregion(A,B):- membermeronym(C,B),similarto(B,D),derivationallyrelatedform(E,A).
memberofdomainregion(A,B):- membermeronym(F,C),instancehypernym(A,D),memberofdomainusage(E,B),instancehypernym(D,C).
memberofdomainregion(A,B):- instancehypernym(C,B),derivationallyrelatedform(A,E),hypernym(C,D).
memberofdomainregion(A,B):- haspart(C,F),instancehypernym(D,A),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- similarto(A,E),derivationallyrelatedform(A,D),haspart(B,C),alsosee(E,A).
memberofdomainregion(A,B):- membermeronym(F,A),synsetdomaintopicof(A,E),similarto(D,C),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(B,A),derivationallyrelatedform(A,D),instancehypernym(B,D),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(E,C),membermeronym(F,C),hypernym(C,B),instancehypernym(D,A).
memberofdomainregion(A,B):- membermeronym(A,B),alsosee(A,D),membermeronym(C,D).
memberofdomainregion(A,B):- verbgroup(E,A),verbgroup(C,B),memberofdomainusage(D,A).
memberofdomainregion(A,B):- haspart(D,E),haspart(B,C),membermeronym(A,D),derivationallyrelatedform(B,F).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),instancehypernym(B,D),hypernym(C,F),haspart(B,C).
memberofdomainregion(A,B):- similarto(E,A),similarto(A,D),verbgroup(C,B).
memberofdomainregion(A,B):- instancehypernym(B,A),instancehypernym(D,C),haspart(A,C).
memberofdomainregion(A,B):- haspart(B,C),memberofdomainusage(D,A),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- haspart(B,C),verbgroup(D,B),derivationallyrelatedform(A,F),hypernym(E,F).
memberofdomainregion(A,B):- memberofdomainusage(B,C),instancehypernym(A,D),membermeronym(C,E),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(E,C),membermeronym(F,C),membermeronym(D,B),verbgroup(A,F).
memberofdomainregion(A,B):- hypernym(A,B),derivationallyrelatedform(D,A),synsetdomaintopicof(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),instancehypernym(B,D),instancehypernym(E,A),similarto(F,B).
memberofdomainregion(A,B):- instancehypernym(B,D),haspart(A,B),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- alsosee(A,E),haspart(C,F),haspart(B,C),memberofdomainusage(D,A).
memberofdomainregion(A,B):- alsosee(A,C),membermeronym(F,C),memberofdomainusage(E,B),memberofdomainusage(F,D).
memberofdomainregion(A,B):- hypernym(C,D),alsosee(A,E),derivationallyrelatedform(E,A),haspart(B,C).
memberofdomainregion(A,B):- alsosee(A,C),derivationallyrelatedform(D,B),hypernym(E,D).
memberofdomainregion(A,B):- verbgroup(E,A),membermeronym(F,C),verbgroup(E,C),hypernym(D,B).
memberofdomainregion(A,B):- haspart(B,E),derivationallyrelatedform(E,D),memberofdomainusage(A,D),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),instancehypernym(B,E),instancehypernym(B,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),hypernym(D,C),derivationallyrelatedform(E,B),synsetdomaintopicof(A,C).
memberofdomainregion(A,B):- derivationallyrelatedform(A,D),synsetdomaintopicof(A,C),memberofdomainusage(A,B).
