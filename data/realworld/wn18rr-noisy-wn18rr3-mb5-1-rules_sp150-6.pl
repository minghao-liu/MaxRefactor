verbgroup(A,B):- alsosee(D,E),hypernym(A,E),alsosee(F,C),haspart(B,F).
verbgroup(A,B):- memberofdomainregion(A,C),alsosee(B,C),hypernym(A,B).
verbgroup(A,B):- synsetdomaintopicof(C,D),synsetdomaintopicof(B,D),alsosee(E,A).
verbgroup(A,B):- synsetdomaintopicof(A,C),instancehypernym(A,D),derivationallyrelatedform(E,B),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(C,F),similarto(B,C),hypernym(A,D),hypernym(C,E).
verbgroup(A,B):- memberofdomainusage(B,C),alsosee(F,C),memberofdomainusage(A,D),instancehypernym(F,E).
verbgroup(A,B):- alsosee(D,B),similarto(A,E),derivationallyrelatedform(C,A).
verbgroup(A,B):- memberofdomainusage(E,B),synsetdomaintopicof(A,D),membermeronym(D,C).
verbgroup(A,B):- hypernym(C,D),alsosee(B,C),similarto(E,A).
verbgroup(A,B):- derivationallyrelatedform(E,A),synsetdomaintopicof(A,D),similarto(B,C),membermeronym(B,D).
verbgroup(A,B):- derivationallyrelatedform(E,C),instancehypernym(A,D),similarto(B,C),memberofdomainusage(C,D).
verbgroup(A,B):- memberofdomainregion(C,B),synsetdomaintopicof(C,D),haspart(A,D).
verbgroup(A,B):- memberofdomainregion(E,F),hypernym(D,B),synsetdomaintopicof(E,A),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(D,C),alsosee(F,C),memberofdomainregion(E,A),synsetdomaintopicof(C,B).
verbgroup(A,B):- derivationallyrelatedform(E,A),hypernym(B,F),memberofdomainusage(D,B),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(E,C),hypernym(A,C),haspart(D,A),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(B,C),synsetdomaintopicof(A,D),similarto(B,C),alsosee(E,A).
verbgroup(A,B):- alsosee(D,E),membermeronym(E,F),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- similarto(C,D),memberofdomainregion(A,D),similarto(B,C),derivationallyrelatedform(D,C).
verbgroup(A,B):- membermeronym(A,D),haspart(C,B),instancehypernym(C,B).
verbgroup(A,B):- derivationallyrelatedform(A,F),alsosee(F,C),derivationallyrelatedform(B,E),instancehypernym(D,C).
verbgroup(A,B):- memberofdomainregion(C,B),alsosee(F,C),memberofdomainusage(A,D),hypernym(E,C).
verbgroup(A,B):- membermeronym(D,E),derivationallyrelatedform(D,B),synsetdomaintopicof(B,A),similarto(B,C).
verbgroup(A,B):- similarto(D,E),derivationallyrelatedform(A,D),similarto(B,C),alsosee(F,D).
verbgroup(A,B):- membermeronym(C,A),memberofdomainusage(E,B),haspart(D,A),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(B,D),memberofdomainusage(A,D),synsetdomaintopicof(C,B).
verbgroup(A,B):- synsetdomaintopicof(B,C),similarto(B,D),memberofdomainregion(E,A).
verbgroup(A,B):- membermeronym(E,B),similarto(D,B),similarto(B,C),hypernym(A,B).
verbgroup(A,B):- alsosee(F,C),hypernym(A,C),hypernym(B,E),alsosee(F,D).
verbgroup(A,B):- instancehypernym(D,A),synsetdomaintopicof(B,D),membermeronym(A,E),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(B,C),membermeronym(B,A),membermeronym(D,C).
verbgroup(A,B):- similarto(A,D),memberofdomainregion(E,B),similarto(B,C),similarto(A,C).
verbgroup(A,B):- similarto(D,A),membermeronym(E,C),alsosee(F,C),hypernym(F,B).
verbgroup(A,B):- derivationallyrelatedform(A,E),alsosee(F,C),alsosee(B,C),similarto(D,B).
verbgroup(A,B):- alsosee(F,C),hypernym(A,C),haspart(B,D),alsosee(E,D).
verbgroup(A,B):- similarto(A,D),similarto(B,C),haspart(A,D),membermeronym(B,D).
verbgroup(A,B):- derivationallyrelatedform(E,C),alsosee(F,C),hypernym(B,D),memberofdomainusage(E,A).
verbgroup(A,B):- memberofdomainregion(B,A),instancehypernym(C,B),similarto(B,C),similarto(A,C).
verbgroup(A,B):- membermeronym(D,B),similarto(A,E),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(D,B),memberofdomainregion(B,D),instancehypernym(A,C).
verbgroup(A,B):- memberofdomainregion(A,C),derivationallyrelatedform(D,B),memberofdomainregion(B,A).
verbgroup(A,B):- alsosee(A,D),alsosee(C,E),instancehypernym(B,E).
verbgroup(A,B):- hypernym(B,A),memberofdomainregion(D,B),haspart(C,B),similarto(B,C).
verbgroup(A,B):- instancehypernym(F,B),similarto(B,C),hypernym(A,D),similarto(F,E).
verbgroup(A,B):- alsosee(E,B),similarto(A,D),alsosee(F,C),similarto(A,C).
verbgroup(A,B):- memberofdomainregion(A,B),instancehypernym(B,A),similarto(C,B).
verbgroup(A,B):- similarto(B,D),derivationallyrelatedform(C,A),alsosee(F,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- synsetdomaintopicof(D,C),similarto(A,C),haspart(E,B).
verbgroup(A,B):- synsetdomaintopicof(A,C),alsosee(D,B),alsosee(F,C),memberofdomainregion(F,E).
verbgroup(A,B):- similarto(B,C),membermeronym(C,D),instancehypernym(C,B),haspart(A,D).
verbgroup(A,B):- hypernym(A,E),hypernym(B,D),similarto(A,C).
verbgroup(A,B):- instancehypernym(D,A),memberofdomainregion(C,B),haspart(B,A).
verbgroup(A,B):- haspart(D,A),instancehypernym(E,C),similarto(E,B).
verbgroup(A,B):- haspart(E,D),alsosee(F,C),derivationallyrelatedform(C,B),memberofdomainregion(A,E).
verbgroup(A,B):- alsosee(F,C),memberofdomainregion(E,B),derivationallyrelatedform(B,C),membermeronym(D,A).
verbgroup(A,B):- alsosee(B,A),alsosee(A,B),memberofdomainusage(C,A).
verbgroup(A,B):- synsetdomaintopicof(A,C),instancehypernym(D,E),similarto(D,B).
verbgroup(A,B):- derivationallyrelatedform(E,A),derivationallyrelatedform(D,A),alsosee(C,B).
verbgroup(A,B):- instancehypernym(D,A),similarto(A,B),similarto(A,C).
verbgroup(A,B):- memberofdomainregion(C,D),memberofdomainregion(D,A),synsetdomaintopicof(C,B).
verbgroup(A,B):- instancehypernym(A,C),alsosee(A,C),alsosee(B,D).
verbgroup(A,B):- similarto(B,C),synsetdomaintopicof(C,A),synsetdomaintopicof(E,B),haspart(A,D).
verbgroup(A,B):- alsosee(A,E),synsetdomaintopicof(B,D),derivationallyrelatedform(F,E),similarto(B,C).
verbgroup(A,B):- similarto(A,F),alsosee(F,C),synsetdomaintopicof(A,D),hypernym(B,E).
verbgroup(A,B):- memberofdomainusage(B,F),derivationallyrelatedform(A,D),alsosee(F,C),membermeronym(E,A).
verbgroup(A,B):- derivationallyrelatedform(B,C),memberofdomainusage(D,C),haspart(C,A).
verbgroup(A,B):- instancehypernym(E,A),hypernym(D,B),derivationallyrelatedform(C,B).
verbgroup(A,B):- similarto(B,C),instancehypernym(B,D),synsetdomaintopicof(C,E),hypernym(A,D).
verbgroup(A,B):- hypernym(B,C),alsosee(D,B),similarto(A,C).
verbgroup(A,B):- alsosee(F,C),memberofdomainusage(E,F),synsetdomaintopicof(B,D),derivationallyrelatedform(A,F).
verbgroup(A,B):- instancehypernym(E,F),alsosee(E,B),alsosee(F,C),synsetdomaintopicof(A,D).
verbgroup(A,B):- synsetdomaintopicof(A,C),alsosee(F,C),memberofdomainusage(B,D),similarto(C,E).
verbgroup(A,B):- alsosee(A,E),instancehypernym(D,B),memberofdomainusage(C,F),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(A,D),alsosee(F,C),instancehypernym(E,F),membermeronym(B,F).
verbgroup(A,B):- haspart(B,E),alsosee(C,E),synsetdomaintopicof(D,A).
verbgroup(A,B):- hypernym(C,F),instancehypernym(A,D),similarto(B,C),synsetdomaintopicof(E,F).
verbgroup(A,B):- hypernym(D,A),instancehypernym(C,B),derivationallyrelatedform(E,C).
verbgroup(A,B):- instancehypernym(A,B),similarto(B,C),haspart(A,D),memberofdomainregion(E,B).
verbgroup(A,B):- instancehypernym(B,D),memberofdomainusage(A,C),similarto(E,D).
verbgroup(A,B):- haspart(A,B),memberofdomainregion(B,D),derivationallyrelatedform(A,C).
verbgroup(A,B):- derivationallyrelatedform(B,C),memberofdomainusage(D,B),memberofdomainregion(E,A),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(D,C),alsosee(F,C),membermeronym(C,B),hypernym(E,A).
verbgroup(A,B):- membermeronym(C,E),memberofdomainregion(C,F),similarto(B,C),hypernym(A,D).
verbgroup(A,B):- derivationallyrelatedform(A,D),memberofdomainusage(C,E),similarto(B,C),similarto(F,B).
verbgroup(A,B):- haspart(B,C),synsetdomaintopicof(A,D),synsetdomaintopicof(C,E),similarto(B,C).
verbgroup(A,B):- similarto(A,D),synsetdomaintopicof(D,A),similarto(B,E),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(D,F),derivationallyrelatedform(A,D),alsosee(F,C),instancehypernym(E,B).
verbgroup(A,B):- derivationallyrelatedform(C,E),instancehypernym(C,B),haspart(D,A).
verbgroup(A,B):- derivationallyrelatedform(A,D),memberofdomainregion(B,A),similarto(B,C),haspart(B,A).
verbgroup(A,B):- hypernym(D,B),alsosee(F,C),memberofdomainusage(A,E),haspart(E,C).
verbgroup(A,B):- memberofdomainusage(F,B),membermeronym(F,E),alsosee(F,C),memberofdomainusage(A,D).
verbgroup(A,B):- instancehypernym(C,D),haspart(A,E),derivationallyrelatedform(B,A),similarto(B,C).
verbgroup(A,B):- similarto(A,B),alsosee(D,C),instancehypernym(A,C).
verbgroup(A,B):- alsosee(E,A),alsosee(F,D),similarto(B,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(A,F),alsosee(D,F),hypernym(B,E).
verbgroup(A,B):- synsetdomaintopicof(A,C),similarto(D,B),alsosee(D,A).
verbgroup(A,B):- membermeronym(D,B),membermeronym(A,C),alsosee(E,A).
verbgroup(A,B):- membermeronym(C,A),synsetdomaintopicof(D,A),derivationallyrelatedform(B,C).
verbgroup(A,B):- alsosee(F,C),hypernym(B,E),hypernym(A,D),membermeronym(F,A).
verbgroup(A,B):- synsetdomaintopicof(D,A),membermeronym(E,C),hypernym(B,E).
verbgroup(A,B):- membermeronym(E,B),alsosee(D,C),similarto(B,C),instancehypernym(A,C).
verbgroup(A,B):- hypernym(A,E),haspart(D,F),similarto(B,C),derivationallyrelatedform(B,F).
verbgroup(A,B):- alsosee(B,E),synsetdomaintopicof(E,D),derivationallyrelatedform(A,D),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(A,F),derivationallyrelatedform(E,B),similarto(B,C),memberofdomainusage(D,A).
verbgroup(A,B):- alsosee(E,B),alsosee(F,C),hypernym(C,A),synsetdomaintopicof(D,F).
verbgroup(A,B):- instancehypernym(C,A),similarto(D,B),similarto(B,C),memberofdomainusage(C,D).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(B,F),alsosee(A,E),hypernym(E,D).
verbgroup(A,B):- instancehypernym(A,D),derivationallyrelatedform(C,E),similarto(B,C),membermeronym(B,D).
verbgroup(A,B):- derivationallyrelatedform(D,A),alsosee(F,C),membermeronym(B,C),derivationallyrelatedform(E,C).
verbgroup(A,B):- synsetdomaintopicof(B,D),memberofdomainusage(C,A).
verbgroup(A,B):- hypernym(D,A),alsosee(F,C),derivationallyrelatedform(E,B),memberofdomainusage(F,E).
verbgroup(A,B):- alsosee(A,D),synsetdomaintopicof(E,A),alsosee(F,C),similarto(C,B).
verbgroup(A,B):- haspart(B,E),memberofdomainusage(A,C),alsosee(F,C),hypernym(D,E).
verbgroup(A,B):- memberofdomainusage(B,C),similarto(A,D),haspart(A,C).
verbgroup(A,B):- hypernym(D,A),haspart(B,D),derivationallyrelatedform(A,C).
verbgroup(A,B):- alsosee(B,E),alsosee(F,C),alsosee(B,C),membermeronym(D,A).
verbgroup(A,B):- derivationallyrelatedform(C,A),memberofdomainusage(B,D),haspart(D,E).
verbgroup(A,B):- alsosee(F,C),derivationallyrelatedform(F,E),instancehypernym(B,C),membermeronym(D,A).
verbgroup(A,B):- haspart(A,E),derivationallyrelatedform(E,C),memberofdomainregion(D,A),similarto(B,C).
verbgroup(A,B):- alsosee(C,E),synsetdomaintopicof(A,F),membermeronym(F,D),similarto(B,C).
verbgroup(A,B):- alsosee(C,E),synsetdomaintopicof(A,D),membermeronym(D,C),similarto(B,C).
verbgroup(A,B):- hypernym(B,A),similarto(A,D),membermeronym(A,C).
verbgroup(A,B):- instancehypernym(D,B),instancehypernym(B,A),synsetdomaintopicof(C,A),similarto(B,C).
verbgroup(A,B):- alsosee(E,B),alsosee(A,E),hypernym(B,D),similarto(B,C).
verbgroup(A,B):- instancehypernym(D,B),memberofdomainregion(E,B),similarto(A,C).
verbgroup(A,B):- instancehypernym(C,A),synsetdomaintopicof(A,D),synsetdomaintopicof(C,B).
verbgroup(A,B):- derivationallyrelatedform(D,B),similarto(E,A),derivationallyrelatedform(A,C).
verbgroup(A,B):- membermeronym(D,F),similarto(B,C),instancehypernym(E,C),instancehypernym(F,A).
verbgroup(A,B):- memberofdomainusage(A,F),memberofdomainusage(A,D),similarto(E,D),similarto(B,C).
verbgroup(A,B):- alsosee(D,B),synsetdomaintopicof(F,B),hypernym(E,A),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(C,B),alsosee(F,C),haspart(A,D),memberofdomainregion(E,B).
verbgroup(A,B):- memberofdomainusage(A,C),instancehypernym(A,D),similarto(B,C),haspart(C,E).
verbgroup(A,B):- synsetdomaintopicof(F,C),haspart(D,C),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- membermeronym(A,C),memberofdomainusage(D,B),synsetdomaintopicof(C,E).
verbgroup(A,B):- memberofdomainregion(C,A),similarto(B,C),haspart(A,D),instancehypernym(A,C).
verbgroup(A,B):- hypernym(A,C),memberofdomainregion(D,A),synsetdomaintopicof(C,B).
verbgroup(A,B):- derivationallyrelatedform(B,D),alsosee(F,C),hypernym(A,F),synsetdomaintopicof(A,E).
verbgroup(A,B):- membermeronym(F,B),instancehypernym(D,B),similarto(B,C),memberofdomainregion(E,A).
verbgroup(A,B):- memberofdomainusage(B,D),memberofdomainusage(E,C),similarto(B,C),instancehypernym(A,C).
verbgroup(A,B):- synsetdomaintopicof(F,D),alsosee(F,C),haspart(E,A),instancehypernym(C,B).
verbgroup(A,B):- derivationallyrelatedform(A,F),synsetdomaintopicof(C,D),derivationallyrelatedform(A,E),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(B,C),alsosee(B,A),synsetdomaintopicof(B,A).
verbgroup(A,B):- haspart(F,D),memberofdomainusage(A,D),similarto(B,C),haspart(C,E).
verbgroup(A,B):- instancehypernym(E,A),alsosee(A,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- hypernym(D,F),memberofdomainusage(F,A),instancehypernym(A,E),similarto(B,C).
verbgroup(A,B):- similarto(D,E),memberofdomainusage(D,B),memberofdomainusage(B,A),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(D,C),similarto(D,B),memberofdomainregion(D,A),similarto(B,C).
verbgroup(A,B):- similarto(A,F),haspart(A,E),derivationallyrelatedform(D,E),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(D,E),derivationallyrelatedform(C,B),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- membermeronym(A,D),memberofdomainusage(B,E),alsosee(F,C),alsosee(F,D).
