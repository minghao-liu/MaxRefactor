memberofdomainregion(A,B):- similarto(E,A),memberofdomainusage(D,B),alsosee(D,E),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(D,B),instancehypernym(B,A),alsosee(B,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),haspart(D,A),alsosee(E,B),derivationallyrelatedform(C,E).
memberofdomainregion(A,B):- alsosee(B,C),membermeronym(A,E),membermeronym(F,C),alsosee(F,D).
memberofdomainregion(A,B):- similarto(D,E),membermeronym(F,C),membermeronym(B,D),verbgroup(F,A).
memberofdomainregion(A,B):- membermeronym(F,C),memberofdomainusage(E,F),derivationallyrelatedform(D,A),instancehypernym(B,F).
memberofdomainregion(A,B):- membermeronym(F,C),memberofdomainusage(A,D),alsosee(E,D),similarto(F,B).
memberofdomainregion(A,B):- membermeronym(F,C),memberofdomainusage(A,D),haspart(B,C),similarto(D,E).
memberofdomainregion(A,B):- similarto(A,B),hypernym(C,B),derivationallyrelatedform(D,A).
memberofdomainregion(A,B):- verbgroup(B,F),synsetdomaintopicof(A,D),membermeronym(F,C),alsosee(D,E).
memberofdomainregion(A,B):- instancehypernym(A,E),hypernym(F,B),membermeronym(F,C),alsosee(D,A).
memberofdomainregion(A,B):- hypernym(B,D),membermeronym(F,C),alsosee(A,E),alsosee(F,D).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),instancehypernym(E,B),synsetdomaintopicof(F,A),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(B,A),memberofdomainusage(B,D),haspart(C,B).
memberofdomainregion(A,B):- haspart(B,C),verbgroup(A,E),instancehypernym(D,C),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- similarto(D,B),hypernym(B,A),verbgroup(C,A).
memberofdomainregion(A,B):- verbgroup(B,D),membermeronym(B,C),derivationallyrelatedform(A,B).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),similarto(A,D),haspart(B,C),verbgroup(F,B).
memberofdomainregion(A,B):- haspart(E,B),verbgroup(A,E),verbgroup(D,B),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(D,B),similarto(A,F),haspart(B,C),alsosee(E,A).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),membermeronym(A,E),synsetdomaintopicof(D,A),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(A,E),membermeronym(D,E),haspart(B,C),synsetdomaintopicof(E,F).
memberofdomainregion(A,B):- membermeronym(F,C),synsetdomaintopicof(F,A),similarto(B,E),membermeronym(E,D).
memberofdomainregion(A,B):- membermeronym(F,C),synsetdomaintopicof(B,E),haspart(A,C),verbgroup(D,E).
memberofdomainregion(A,B):- similarto(A,E),hypernym(B,C),memberofdomainusage(B,D).
memberofdomainregion(A,B):- alsosee(A,C),similarto(C,E),alsosee(B,D).
memberofdomainregion(A,B):- similarto(B,F),synsetdomaintopicof(A,D),membermeronym(F,C),haspart(E,C).
memberofdomainregion(A,B):- synsetdomaintopicof(C,E),haspart(D,E),haspart(A,D),haspart(B,C).
memberofdomainregion(A,B):- similarto(D,C),membermeronym(C,B),verbgroup(A,E),membermeronym(F,C).
memberofdomainregion(A,B):- alsosee(E,B),membermeronym(F,C),synsetdomaintopicof(B,D),verbgroup(F,A).
memberofdomainregion(A,B):- membermeronym(F,C),derivationallyrelatedform(B,D),verbgroup(B,E),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- hypernym(D,B),alsosee(E,B),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- hypernym(C,A),membermeronym(A,D),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- verbgroup(D,A),similarto(C,B),similarto(B,E).
memberofdomainregion(A,B):- verbgroup(F,D),membermeronym(F,C),similarto(A,D),hypernym(B,E).
memberofdomainregion(A,B):- membermeronym(F,C),verbgroup(B,C),verbgroup(A,E),haspart(D,E).
memberofdomainregion(A,B):- membermeronym(F,C),verbgroup(C,B),instancehypernym(F,D),memberofdomainusage(E,A).
memberofdomainregion(A,B):- similarto(D,A),memberofdomainusage(C,A),instancehypernym(B,C).
memberofdomainregion(A,B):- verbgroup(B,D),alsosee(A,E),synsetdomaintopicof(E,C).
memberofdomainregion(A,B):- haspart(E,D),membermeronym(F,C),verbgroup(B,C),derivationallyrelatedform(D,A).
memberofdomainregion(A,B):- alsosee(B,F),membermeronym(F,C),instancehypernym(D,C),alsosee(E,A).
memberofdomainregion(A,B):- memberofdomainusage(A,E),similarto(F,E),haspart(B,C),verbgroup(D,E).
memberofdomainregion(A,B):- hypernym(B,D),synsetdomaintopicof(C,D),instancehypernym(A,D).
memberofdomainregion(A,B):- membermeronym(F,C),hypernym(D,B),derivationallyrelatedform(E,A),membermeronym(C,D).
memberofdomainregion(A,B):- membermeronym(B,F),membermeronym(F,C),synsetdomaintopicof(E,D),membermeronym(E,A).
memberofdomainregion(A,B):- synsetdomaintopicof(D,B),synsetdomaintopicof(C,F),haspart(B,C),memberofdomainusage(E,A).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),membermeronym(F,C),instancehypernym(C,A),verbgroup(A,E).
memberofdomainregion(A,B):- derivationallyrelatedform(C,E),haspart(B,C),derivationallyrelatedform(F,A),hypernym(D,B).
memberofdomainregion(A,B):- hypernym(C,B),verbgroup(C,B),similarto(D,A).
memberofdomainregion(A,B):- alsosee(C,B),membermeronym(A,B),synsetdomaintopicof(A,C).
memberofdomainregion(A,B):- memberofdomainusage(E,C),membermeronym(F,C),similarto(A,D),similarto(B,E).
memberofdomainregion(A,B):- membermeronym(B,C),haspart(B,C),instancehypernym(D,B),memberofdomainusage(A,B).
memberofdomainregion(A,B):- instancehypernym(C,E),hypernym(C,B),memberofdomainusage(D,A).
memberofdomainregion(A,B):- synsetdomaintopicof(C,E),hypernym(F,A),verbgroup(D,B),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(D,B),verbgroup(D,B),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- alsosee(E,C),haspart(A,D),haspart(B,C),verbgroup(F,B).
memberofdomainregion(A,B):- similarto(D,B),membermeronym(F,C),alsosee(C,A),memberofdomainusage(E,D).
memberofdomainregion(A,B):- membermeronym(F,C),instancehypernym(F,E),membermeronym(C,A),hypernym(D,B).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),synsetdomaintopicof(C,D),haspart(B,C),similarto(C,A).
memberofdomainregion(A,B):- verbgroup(C,D),alsosee(A,E),instancehypernym(E,A),haspart(B,C).
memberofdomainregion(A,B):- similarto(A,D),haspart(B,C),synsetdomaintopicof(C,F),verbgroup(C,E).
memberofdomainregion(A,B):- similarto(A,E),memberofdomainusage(E,C),haspart(B,C),memberofdomainusage(B,D).
memberofdomainregion(A,B):- hypernym(F,E),derivationallyrelatedform(A,D),synsetdomaintopicof(F,B),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(B,D),membermeronym(F,C),memberofdomainusage(E,F),alsosee(F,A).
memberofdomainregion(A,B):- haspart(B,C),alsosee(D,A),haspart(A,B),haspart(A,C).
memberofdomainregion(A,B):- memberofdomainusage(B,C),memberofdomainusage(C,A),alsosee(C,A).
memberofdomainregion(A,B):- memberofdomainusage(A,E),synsetdomaintopicof(A,F),membermeronym(F,C),alsosee(D,B).
memberofdomainregion(A,B):- similarto(A,D),alsosee(A,D),haspart(B,C),instancehypernym(E,C).
memberofdomainregion(A,B):- instancehypernym(C,B),membermeronym(F,C),derivationallyrelatedform(D,E),alsosee(A,D).
memberofdomainregion(A,B):- membermeronym(F,C),similarto(D,F),alsosee(E,B),verbgroup(A,D).
memberofdomainregion(A,B):- verbgroup(A,E),similarto(A,F),haspart(B,C),alsosee(C,D).
memberofdomainregion(A,B):- hypernym(B,C),alsosee(B,C),memberofdomainusage(A,D).
memberofdomainregion(A,B):- hypernym(B,E),memberofdomainusage(B,D),similarto(A,C).
memberofdomainregion(A,B):- instancehypernym(C,B),haspart(D,A).
memberofdomainregion(A,B):- membermeronym(C,E),memberofdomainusage(A,D),haspart(B,C),haspart(A,C).
memberofdomainregion(A,B):- hypernym(B,D),membermeronym(E,F),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- haspart(D,A),membermeronym(F,C),memberofdomainusage(E,F),hypernym(B,E).
memberofdomainregion(A,B):- membermeronym(A,C),derivationallyrelatedform(B,A),instancehypernym(C,A).
memberofdomainregion(A,B):- haspart(A,D),derivationallyrelatedform(E,D),haspart(B,C),memberofdomainusage(A,F).
memberofdomainregion(A,B):- membermeronym(F,C),synsetdomaintopicof(F,D),derivationallyrelatedform(F,A),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- hypernym(F,E),membermeronym(D,F),haspart(B,C),memberofdomainusage(A,F).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),haspart(A,D),haspart(B,C),hypernym(A,F).
memberofdomainregion(A,B):- haspart(A,C),instancehypernym(D,C),instancehypernym(B,C).
memberofdomainregion(A,B):- instancehypernym(A,B),alsosee(E,B),haspart(B,C),hypernym(D,B).
memberofdomainregion(A,B):- alsosee(F,A),derivationallyrelatedform(E,D),similarto(D,B),haspart(B,C).
memberofdomainregion(A,B):- hypernym(B,D),instancehypernym(E,A),alsosee(C,A).
memberofdomainregion(A,B):- haspart(E,D),synsetdomaintopicof(A,D),haspart(C,A),haspart(B,C).
memberofdomainregion(A,B):- haspart(D,E),membermeronym(A,D),haspart(B,C),alsosee(F,D).
memberofdomainregion(A,B):- membermeronym(E,C),derivationallyrelatedform(A,D),synsetdomaintopicof(B,E).
memberofdomainregion(A,B):- haspart(E,F),membermeronym(F,C),membermeronym(E,B),membermeronym(D,A).
memberofdomainregion(A,B):- synsetdomaintopicof(B,D),hypernym(C,B),haspart(E,A).
memberofdomainregion(A,B):- similarto(E,A),haspart(D,E),instancehypernym(B,C).
memberofdomainregion(A,B):- membermeronym(A,C),membermeronym(E,B),alsosee(E,D).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),similarto(A,C),haspart(B,C),hypernym(D,B).
memberofdomainregion(A,B):- verbgroup(A,C),instancehypernym(B,A),hypernym(B,A).
memberofdomainregion(A,B):- haspart(E,B),synsetdomaintopicof(A,C),instancehypernym(D,C).
memberofdomainregion(A,B):- instancehypernym(A,E),hypernym(D,A),membermeronym(F,C),hypernym(F,B).
memberofdomainregion(A,B):- instancehypernym(C,B),haspart(B,E),memberofdomainusage(A,D),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(B,C),instancehypernym(A,D),memberofdomainusage(B,A),haspart(B,C).
memberofdomainregion(A,B):- verbgroup(B,F),membermeronym(F,C),alsosee(D,B),haspart(E,A).
memberofdomainregion(A,B):- hypernym(A,C),verbgroup(D,B),instancehypernym(E,C).
memberofdomainregion(A,B):- similarto(A,E),hypernym(D,A),haspart(B,C),alsosee(A,F).
memberofdomainregion(A,B):- alsosee(A,C),membermeronym(F,C),verbgroup(A,E),alsosee(B,D).
memberofdomainregion(A,B):- alsosee(B,F),haspart(B,C),instancehypernym(A,D),verbgroup(C,E).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),membermeronym(F,C),synsetdomaintopicof(D,E),instancehypernym(A,C).
memberofdomainregion(A,B):- haspart(B,C),instancehypernym(A,D),similarto(E,B),verbgroup(C,E).
memberofdomainregion(A,B):- hypernym(C,D),memberofdomainusage(A,E),verbgroup(A,B),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),synsetdomaintopicof(A,F),verbgroup(A,E),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),haspart(C,F),synsetdomaintopicof(E,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),synsetdomaintopicof(E,A),haspart(B,F),alsosee(E,D).
memberofdomainregion(A,B):- derivationallyrelatedform(B,C),similarto(E,A),membermeronym(F,C),verbgroup(D,E).
memberofdomainregion(A,B):- instancehypernym(D,B),alsosee(C,A),haspart(B,C),similarto(A,C).
memberofdomainregion(A,B):- synsetdomaintopicof(A,E),memberofdomainusage(B,A),verbgroup(D,B),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,C),memberofdomainusage(D,B),hypernym(A,E),instancehypernym(B,F).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),instancehypernym(A,D),derivationallyrelatedform(E,D),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(E,B),membermeronym(F,C),hypernym(A,D),derivationallyrelatedform(F,D).
memberofdomainregion(A,B):- similarto(A,B),instancehypernym(C,A),membermeronym(A,D).
memberofdomainregion(A,B):- haspart(E,A),instancehypernym(C,F),haspart(B,C),membermeronym(C,D).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),hypernym(E,A),similarto(B,D),haspart(B,C).
memberofdomainregion(A,B):- similarto(C,A),synsetdomaintopicof(C,B),similarto(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(B,A),hypernym(C,E),similarto(D,B),haspart(B,C).
memberofdomainregion(A,B):- similarto(B,D),verbgroup(A,B),haspart(A,C).
memberofdomainregion(A,B):- haspart(F,A),hypernym(E,D),memberofdomainusage(D,B),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,C),hypernym(A,D),derivationallyrelatedform(E,A),verbgroup(F,E).
memberofdomainregion(A,B):- synsetdomaintopicof(D,B),derivationallyrelatedform(C,D),haspart(B,C),verbgroup(C,A).
memberofdomainregion(A,B):- haspart(C,E),membermeronym(C,B),similarto(A,D),membermeronym(F,C).
memberofdomainregion(A,B):- similarto(C,D),alsosee(B,A),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- synsetdomaintopicof(C,B),membermeronym(F,C),instancehypernym(F,D),hypernym(A,E).
memberofdomainregion(A,B):- memberofdomainusage(B,C),membermeronym(B,E),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- instancehypernym(A,E),membermeronym(F,C),instancehypernym(F,B),derivationallyrelatedform(B,D).
memberofdomainregion(A,B):- alsosee(A,C),verbgroup(C,D),membermeronym(F,C),similarto(E,B).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),membermeronym(F,C),alsosee(D,A),verbgroup(F,A).
memberofdomainregion(A,B):- alsosee(A,C),similarto(A,D),alsosee(B,A),haspart(B,C).
memberofdomainregion(A,B):- alsosee(D,C),derivationallyrelatedform(B,E),instancehypernym(A,D).
memberofdomainregion(A,B):- membermeronym(B,E),instancehypernym(C,D),haspart(B,C),haspart(A,E).
memberofdomainregion(A,B):- verbgroup(C,A),membermeronym(F,C),alsosee(B,E),memberofdomainusage(C,D).
memberofdomainregion(A,B):- verbgroup(D,A),membermeronym(F,C),synsetdomaintopicof(E,A),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(D,C),similarto(A,F),membermeronym(F,C),verbgroup(B,E).
memberofdomainregion(A,B):- membermeronym(B,C),haspart(C,A),hypernym(D,B).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(E,B),instancehypernym(C,D),instancehypernym(F,A).
memberofdomainregion(A,B):- haspart(D,B),membermeronym(C,B),verbgroup(A,E),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(B,C),instancehypernym(E,B),similarto(A,D).
memberofdomainregion(A,B):- memberofdomainusage(A,E),membermeronym(D,E),haspart(B,C),verbgroup(D,E).
memberofdomainregion(A,B):- synsetdomaintopicof(D,A),memberofdomainusage(F,C),instancehypernym(E,B),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(C,B),instancehypernym(C,D),derivationallyrelatedform(B,A).
memberofdomainregion(A,B):- derivationallyrelatedform(D,E),synsetdomaintopicof(A,E),membermeronym(E,F),haspart(B,C).
memberofdomainregion(A,B):- hypernym(A,C),verbgroup(B,C),derivationallyrelatedform(B,D).
memberofdomainregion(A,B):- synsetdomaintopicof(C,A),derivationallyrelatedform(A,D),verbgroup(E,B).
memberofdomainregion(A,B):- hypernym(E,D),membermeronym(A,E),hypernym(E,A),haspart(B,C).
memberofdomainregion(A,B):- hypernym(B,D),alsosee(E,D),haspart(B,C),haspart(A,C).
memberofdomainregion(A,B):- alsosee(E,B),memberofdomainusage(D,F),membermeronym(F,C),alsosee(A,D).
memberofdomainregion(A,B):- alsosee(F,A),instancehypernym(D,B),membermeronym(F,C),haspart(A,E).
memberofdomainregion(A,B):- membermeronym(F,C),hypernym(D,F),hypernym(B,F),memberofdomainusage(E,A).
memberofdomainregion(A,B):- memberofdomainusage(A,E),similarto(D,A),similarto(A,F),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(A,C),instancehypernym(E,D),memberofdomainusage(B,D).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),membermeronym(F,C),derivationallyrelatedform(E,D),instancehypernym(B,C).
memberofdomainregion(A,B):- alsosee(D,C),similarto(A,E),haspart(B,C),derivationallyrelatedform(E,C).
memberofdomainregion(A,B):- instancehypernym(B,E),membermeronym(F,C),verbgroup(D,B),memberofdomainusage(A,F).
memberofdomainregion(A,B):- verbgroup(E,D),derivationallyrelatedform(A,E),haspart(B,C),membermeronym(D,A).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(E,F),derivationallyrelatedform(D,A),haspart(F,B).
memberofdomainregion(A,B):- hypernym(D,A),derivationallyrelatedform(D,A),synsetdomaintopicof(D,C),haspart(B,C).
memberofdomainregion(A,B):- hypernym(C,A),derivationallyrelatedform(D,B),hypernym(B,A).
memberofdomainregion(A,B):- haspart(B,D),alsosee(C,A),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- instancehypernym(A,D),membermeronym(A,D),haspart(B,C),similarto(D,A).
memberofdomainregion(A,B):- hypernym(F,E),membermeronym(A,D),haspart(B,C),synsetdomaintopicof(F,C).
memberofdomainregion(A,B):- membermeronym(C,B),instancehypernym(A,D),synsetdomaintopicof(E,C).
memberofdomainregion(A,B):- memberofdomainusage(E,C),hypernym(A,C),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- similarto(D,C),derivationallyrelatedform(A,D),instancehypernym(B,D),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(A,C),membermeronym(F,C),synsetdomaintopicof(B,D),synsetdomaintopicof(E,F).
memberofdomainregion(A,B):- alsosee(A,E),membermeronym(F,C),verbgroup(D,F),synsetdomaintopicof(F,B).
memberofdomainregion(A,B):- similarto(A,E),membermeronym(F,C),verbgroup(B,C),derivationallyrelatedform(F,D).
memberofdomainregion(A,B):- similarto(A,D),hypernym(C,E),haspart(B,C),memberofdomainusage(E,A).
memberofdomainregion(A,B):- membermeronym(A,C),memberofdomainusage(A,E),membermeronym(F,C),memberofdomainusage(B,D).
memberofdomainregion(A,B):- verbgroup(B,D),hypernym(A,B),haspart(B,C),instancehypernym(A,C).
memberofdomainregion(A,B):- similarto(A,D),similarto(E,A),haspart(B,D),haspart(B,C).
memberofdomainregion(A,B):- similarto(C,D),instancehypernym(E,B),instancehypernym(D,A).
memberofdomainregion(A,B):- membermeronym(F,C),membermeronym(D,B),verbgroup(A,E),hypernym(E,F).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),alsosee(D,B),verbgroup(C,A).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),derivationallyrelatedform(B,E),similarto(A,D).
memberofdomainregion(A,B):- instancehypernym(D,B),alsosee(B,D),instancehypernym(D,A),haspart(B,C).
memberofdomainregion(A,B):- hypernym(B,A),synsetdomaintopicof(D,B),haspart(B,C),membermeronym(C,D).
memberofdomainregion(A,B):- derivationallyrelatedform(D,F),similarto(B,F),verbgroup(A,E),haspart(B,C).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),verbgroup(C,F),haspart(B,C),membermeronym(F,D).
memberofdomainregion(A,B):- hypernym(C,A),synsetdomaintopicof(B,A),alsosee(C,D).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),membermeronym(F,C),similarto(A,C),haspart(C,D).
memberofdomainregion(A,B):- instancehypernym(D,B),membermeronym(F,C),derivationallyrelatedform(C,A),instancehypernym(E,A).
memberofdomainregion(A,B):- alsosee(C,D),similarto(A,E),haspart(B,C),hypernym(D,B).
memberofdomainregion(A,B):- verbgroup(B,D),hypernym(A,C),instancehypernym(C,D).
memberofdomainregion(A,B):- membermeronym(F,C),haspart(E,A),membermeronym(A,D),alsosee(F,B).
memberofdomainregion(A,B):- membermeronym(F,C),haspart(A,D),alsosee(F,E),synsetdomaintopicof(C,B).
memberofdomainregion(A,B):- memberofdomainusage(A,E),similarto(F,E),synsetdomaintopicof(D,C),haspart(B,C).
memberofdomainregion(A,B):- alsosee(D,F),membermeronym(F,C),haspart(B,C),memberofdomainusage(E,A).
memberofdomainregion(A,B):- instancehypernym(A,E),hypernym(F,B),memberofdomainusage(D,F),membermeronym(F,C).
memberofdomainregion(A,B):- hypernym(B,C),similarto(A,C).
memberofdomainregion(A,B):- hypernym(B,A),hypernym(C,E),membermeronym(A,D),haspart(B,C).
memberofdomainregion(A,B):- haspart(E,F),membermeronym(F,C),membermeronym(B,D),alsosee(E,A).
memberofdomainregion(A,B):- membermeronym(E,C),derivationallyrelatedform(A,D),hypernym(F,C),haspart(B,C).
memberofdomainregion(A,B):- similarto(E,F),hypernym(F,D),hypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- instancehypernym(E,B),hypernym(D,C),memberofdomainusage(A,D),haspart(B,C).
memberofdomainregion(A,B):- memberofdomainusage(B,F),haspart(C,D),memberofdomainusage(A,E),membermeronym(F,C).
