verbgroup(A,B):- instancehypernym(A,D),membermeronym(C,B),membermeronym(A,C),similarto(B,C).
verbgroup(A,B):- similarto(B,C),haspart(A,B),haspart(A,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- memberofdomainregion(E,A),memberofdomainregion(D,A),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- synsetdomaintopicof(E,A),alsosee(F,C),instancehypernym(C,B),derivationallyrelatedform(D,F).
verbgroup(A,B):- similarto(A,D),alsosee(C,B),derivationallyrelatedform(A,C).
verbgroup(A,B):- memberofdomainregion(C,A),instancehypernym(D,A),alsosee(F,C),hypernym(B,E).
verbgroup(A,B):- memberofdomainregion(D,B),haspart(C,B),memberofdomainusage(A,B).
verbgroup(A,B):- derivationallyrelatedform(F,D),memberofdomainregion(A,E),similarto(B,C),memberofdomainusage(D,A).
verbgroup(A,B):- membermeronym(A,D),memberofdomainusage(A,D),similarto(B,C),derivationallyrelatedform(D,C).
verbgroup(A,B):- alsosee(E,F),alsosee(F,C),derivationallyrelatedform(C,B),memberofdomainregion(A,D).
verbgroup(A,B):- alsosee(A,D),membermeronym(C,E),memberofdomainregion(C,D),similarto(B,C).
verbgroup(A,B):- similarto(E,F),memberofdomainusage(A,F),similarto(D,B),similarto(B,C).
verbgroup(A,B):- alsosee(C,A),haspart(B,D),memberofdomainusage(B,E).
verbgroup(A,B):- derivationallyrelatedform(E,C),similarto(A,C),similarto(B,C),instancehypernym(D,C).
verbgroup(A,B):- alsosee(C,A),alsosee(B,E),alsosee(F,C),membermeronym(A,D).
verbgroup(A,B):- hypernym(E,B),memberofdomainregion(B,C),haspart(A,D).
verbgroup(A,B):- derivationallyrelatedform(D,A),alsosee(F,C),similarto(F,D),hypernym(B,E).
verbgroup(A,B):- membermeronym(A,D),haspart(C,B),similarto(A,E),similarto(B,C).
verbgroup(A,B):- hypernym(E,C),alsosee(D,A),synsetdomaintopicof(C,B).
verbgroup(A,B):- membermeronym(B,A),synsetdomaintopicof(A,D),instancehypernym(D,C).
verbgroup(A,B):- instancehypernym(D,E),derivationallyrelatedform(D,B),similarto(B,C),memberofdomainregion(B,A).
verbgroup(A,B):- instancehypernym(F,E),alsosee(F,C),alsosee(A,F),membermeronym(B,D).
verbgroup(A,B):- memberofdomainusage(C,A),haspart(D,A),synsetdomaintopicof(C,B).
verbgroup(A,B):- hypernym(B,F),hypernym(E,A),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- similarto(B,C),haspart(B,D),haspart(A,D).
verbgroup(A,B):- synsetdomaintopicof(B,C),synsetdomaintopicof(D,A),instancehypernym(D,B),similarto(B,C).
verbgroup(A,B):- alsosee(A,D),membermeronym(D,B),memberofdomainregion(C,D),similarto(B,C).
verbgroup(A,B):- haspart(F,D),memberofdomainusage(A,E),alsosee(F,C),haspart(F,B).
verbgroup(A,B):- hypernym(B,F),alsosee(F,C),haspart(D,A),memberofdomainusage(C,E).
verbgroup(A,B):- alsosee(C,A),membermeronym(D,B),similarto(B,C),hypernym(B,A).
verbgroup(A,B):- instancehypernym(B,D),hypernym(B,C),haspart(D,A),similarto(B,C).
verbgroup(A,B):- haspart(D,B),membermeronym(A,E),membermeronym(E,C),similarto(B,C).
verbgroup(A,B):- membermeronym(D,B),derivationallyrelatedform(B,A),memberofdomainregion(E,C),similarto(B,C).
verbgroup(A,B):- alsosee(A,D),alsosee(F,C),instancehypernym(B,E),instancehypernym(D,F).
verbgroup(A,B):- alsosee(F,C),membermeronym(C,B),hypernym(E,A),memberofdomainregion(D,E).
verbgroup(A,B):- derivationallyrelatedform(A,D),membermeronym(B,C),memberofdomainusage(D,A).
verbgroup(A,B):- hypernym(D,A),derivationallyrelatedform(A,E),synsetdomaintopicof(C,E),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(A,D),instancehypernym(C,B),membermeronym(C,D).
verbgroup(A,B):- alsosee(F,B),alsosee(F,C),memberofdomainusage(B,E),memberofdomainregion(A,D).
verbgroup(A,B):- haspart(D,B),membermeronym(D,E),derivationallyrelatedform(A,C).
verbgroup(A,B):- alsosee(A,D),memberofdomainusage(D,E),similarto(C,F),similarto(B,C).
verbgroup(A,B):- instancehypernym(D,E),alsosee(F,C),alsosee(B,C),haspart(A,D).
verbgroup(A,B):- alsosee(F,E),derivationallyrelatedform(C,A),alsosee(F,C),memberofdomainregion(B,D).
verbgroup(A,B):- alsosee(A,D),membermeronym(C,B),derivationallyrelatedform(C,B).
verbgroup(A,B):- hypernym(A,E),instancehypernym(C,B),alsosee(B,D).
verbgroup(A,B):- haspart(B,F),alsosee(F,C),derivationallyrelatedform(A,E),hypernym(D,C).
verbgroup(A,B):- alsosee(F,C),similarto(F,E),alsosee(A,F),alsosee(B,D).
verbgroup(A,B):- memberofdomainregion(F,C),similarto(B,C),haspart(D,E),memberofdomainusage(A,E).
verbgroup(A,B):- hypernym(B,D),derivationallyrelatedform(D,A),instancehypernym(A,E),similarto(B,C).
verbgroup(A,B):- similarto(C,D),instancehypernym(B,E),hypernym(A,D).
verbgroup(A,B):- hypernym(D,A),similarto(A,C),similarto(B,C),haspart(C,E).
verbgroup(A,B):- derivationallyrelatedform(B,D),derivationallyrelatedform(D,E),alsosee(F,C),similarto(A,C).
verbgroup(A,B):- hypernym(B,A),membermeronym(D,B),similarto(B,C),memberofdomainusage(D,A).
verbgroup(A,B):- instancehypernym(D,A),instancehypernym(D,E),instancehypernym(A,E),similarto(B,C).
verbgroup(A,B):- membermeronym(E,B),alsosee(F,C),memberofdomainusage(A,C),memberofdomainregion(B,D).
verbgroup(A,B):- membermeronym(A,F),instancehypernym(E,B),derivationallyrelatedform(D,F),similarto(B,C).
verbgroup(A,B):- membermeronym(A,D),derivationallyrelatedform(E,C),haspart(E,A),similarto(B,C).
verbgroup(A,B):- hypernym(B,A),membermeronym(D,B),derivationallyrelatedform(D,C).
verbgroup(A,B):- similarto(F,A),alsosee(F,C),synsetdomaintopicof(F,E),haspart(B,D).
verbgroup(A,B):- alsosee(C,E),memberofdomainusage(C,D),derivationallyrelatedform(A,E),similarto(B,C).
verbgroup(A,B):- similarto(B,D),alsosee(F,C),memberofdomainusage(B,E),similarto(A,C).
verbgroup(A,B):- alsosee(C,A),memberofdomainregion(C,E),membermeronym(B,D).
verbgroup(A,B):- memberofdomainregion(E,C),instancehypernym(D,F),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- instancehypernym(A,D),synsetdomaintopicof(D,A),hypernym(E,A),similarto(B,C).
verbgroup(A,B):- membermeronym(C,A),hypernym(C,D),memberofdomainusage(B,C).
verbgroup(A,B):- memberofdomainusage(A,D),hypernym(E,A),synsetdomaintopicof(E,B),similarto(B,C).
verbgroup(A,B):- membermeronym(B,A),membermeronym(C,E),memberofdomainusage(D,B),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(D,B),alsosee(F,C),haspart(A,C),memberofdomainusage(B,E).
verbgroup(A,B):- synsetdomaintopicof(D,C),hypernym(A,E),haspart(F,C),similarto(B,C).
verbgroup(A,B):- haspart(D,C),synsetdomaintopicof(A,D),similarto(B,C),haspart(D,E).
verbgroup(A,B):- alsosee(A,D),memberofdomainusage(C,D),memberofdomainregion(D,B).
verbgroup(A,B):- synsetdomaintopicof(E,C),memberofdomainusage(A,C),membermeronym(D,B),alsosee(F,C).
verbgroup(A,B):- derivationallyrelatedform(B,D),hypernym(A,E),alsosee(F,C),derivationallyrelatedform(D,C).
verbgroup(A,B):- membermeronym(F,B),membermeronym(D,B),alsosee(F,C),memberofdomainusage(E,A).
verbgroup(A,B):- alsosee(F,C),haspart(D,C),synsetdomaintopicof(B,E),similarto(A,C).
verbgroup(A,B):- haspart(A,E),hypernym(E,D),similarto(B,C),derivationallyrelatedform(D,C).
verbgroup(A,B):- membermeronym(D,B),alsosee(F,C),derivationallyrelatedform(A,E),haspart(C,E).
verbgroup(A,B):- memberofdomainusage(D,E),haspart(A,B),similarto(B,C),hypernym(A,D).
verbgroup(A,B):- membermeronym(A,D),membermeronym(E,A),similarto(B,C),derivationallyrelatedform(E,F).
verbgroup(A,B):- similarto(A,F),membermeronym(E,F),alsosee(F,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- similarto(D,A),hypernym(B,C),memberofdomainregion(B,A).
verbgroup(A,B):- memberofdomainusage(D,C),memberofdomainusage(D,B),hypernym(E,A),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(C,A),alsosee(B,D),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- haspart(D,F),synsetdomaintopicof(F,E),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- memberofdomainregion(A,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- similarto(C,D),memberofdomainregion(C,B),memberofdomainregion(D,A).
verbgroup(A,B):- memberofdomainusage(B,E),derivationallyrelatedform(C,B),haspart(A,D).
verbgroup(A,B):- derivationallyrelatedform(E,C),memberofdomainusage(A,D),instancehypernym(B,C).
verbgroup(A,B):- haspart(C,D),membermeronym(A,E),similarto(D,B),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(C,F),memberofdomainusage(E,F),similarto(B,C),hypernym(A,D).
verbgroup(A,B):- memberofdomainregion(D,E),haspart(D,A),similarto(B,C),memberofdomainusage(D,A).
verbgroup(A,B):- derivationallyrelatedform(E,A),alsosee(D,F),similarto(B,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- instancehypernym(E,B),memberofdomainregion(C,D),memberofdomainusage(D,A).
verbgroup(A,B):- hypernym(A,C),derivationallyrelatedform(E,B),synsetdomaintopicof(A,D).
verbgroup(A,B):- instancehypernym(B,D),alsosee(F,C),instancehypernym(B,C),memberofdomainusage(E,A).
verbgroup(A,B):- memberofdomainusage(B,C),alsosee(C,E),haspart(D,A).
verbgroup(A,B):- instancehypernym(D,E),alsosee(F,C),memberofdomainusage(A,F),alsosee(B,D).
verbgroup(A,B):- memberofdomainusage(E,B),synsetdomaintopicof(A,D),similarto(B,C),memberofdomainusage(F,E).
verbgroup(A,B):- alsosee(F,C),haspart(C,B),membermeronym(A,E),memberofdomainusage(E,D).
verbgroup(A,B):- membermeronym(E,B),similarto(E,C),alsosee(F,C),memberofdomainusage(D,A).
verbgroup(A,B):- haspart(B,F),alsosee(F,C),similarto(D,B),derivationallyrelatedform(A,E).
verbgroup(A,B):- alsosee(D,B),alsosee(F,C),memberofdomainregion(D,E),derivationallyrelatedform(A,C).
verbgroup(A,B):- membermeronym(F,E),similarto(A,D),memberofdomainregion(E,A),similarto(B,C).
verbgroup(A,B):- alsosee(F,C),memberofdomainusage(E,B),synsetdomaintopicof(E,D),similarto(F,A).
verbgroup(A,B):- membermeronym(A,E),similarto(A,E),similarto(B,C),instancehypernym(D,C).
verbgroup(A,B):- memberofdomainregion(A,B),membermeronym(D,B),similarto(B,C),memberofdomainusage(E,D).
verbgroup(A,B):- alsosee(C,E),alsosee(B,E),hypernym(D,A).
verbgroup(A,B):- instancehypernym(A,B),derivationallyrelatedform(C,B),synsetdomaintopicof(C,B).
verbgroup(A,B):- instancehypernym(F,D),hypernym(B,C),alsosee(F,C),similarto(E,A).
verbgroup(A,B):- haspart(A,B),alsosee(B,C),membermeronym(C,B).
verbgroup(A,B):- memberofdomainregion(A,E),instancehypernym(D,E),alsosee(F,C),haspart(C,B).
verbgroup(A,B):- memberofdomainusage(B,C),derivationallyrelatedform(B,A),synsetdomaintopicof(A,D).
verbgroup(A,B):- membermeronym(D,B),derivationallyrelatedform(C,E),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- hypernym(B,F),alsosee(F,C),memberofdomainregion(D,A),memberofdomainregion(A,E).
verbgroup(A,B):- memberofdomainregion(A,C),memberofdomainregion(A,D),hypernym(C,B).
verbgroup(A,B):- instancehypernym(F,B),alsosee(F,C),memberofdomainusage(A,D),derivationallyrelatedform(B,E).
verbgroup(A,B):- membermeronym(B,C),synsetdomaintopicof(C,D),alsosee(A,B).
verbgroup(A,B):- instancehypernym(E,A),derivationallyrelatedform(B,D),alsosee(F,C),derivationallyrelatedform(A,F).
verbgroup(A,B):- derivationallyrelatedform(E,A),hypernym(B,F),alsosee(F,C),memberofdomainregion(E,D).
verbgroup(A,B):- alsosee(F,C),instancehypernym(A,D),alsosee(D,F),haspart(E,B).
verbgroup(A,B):- instancehypernym(E,B),similarto(B,C),hypernym(A,B),instancehypernym(D,C).
verbgroup(A,B):- instancehypernym(E,A),synsetdomaintopicof(B,F),memberofdomainregion(D,C),alsosee(F,C).
verbgroup(A,B):- membermeronym(A,D),memberofdomainregion(F,A),hypernym(E,B),alsosee(F,C).
verbgroup(A,B):- memberofdomainregion(B,C),alsosee(F,C),similarto(D,B),hypernym(E,A).
verbgroup(A,B):- memberofdomainusage(A,E),alsosee(D,F),similarto(B,C),similarto(F,B).
verbgroup(A,B):- hypernym(D,A),memberofdomainusage(E,B),instancehypernym(A,C).
verbgroup(A,B):- memberofdomainusage(A,D),similarto(C,B),derivationallyrelatedform(A,C).
verbgroup(A,B):- memberofdomainregion(B,F),alsosee(F,C),memberofdomainusage(E,C),hypernym(A,D).
verbgroup(A,B):- synsetdomaintopicof(E,A),haspart(B,D),haspart(A,C).
verbgroup(A,B):- memberofdomainusage(F,E),hypernym(D,B),alsosee(F,C),hypernym(A,F).
verbgroup(A,B):- memberofdomainusage(E,B),alsosee(F,C),derivationallyrelatedform(D,B),membermeronym(A,C).
verbgroup(A,B):- memberofdomainusage(A,E),alsosee(F,C),similarto(D,F),hypernym(C,B).
verbgroup(A,B):- membermeronym(C,E),hypernym(E,A),synsetdomaintopicof(D,B).
verbgroup(A,B):- memberofdomainusage(E,A),haspart(D,C),similarto(B,C),instancehypernym(A,C).
verbgroup(A,B):- synsetdomaintopicof(D,C),derivationallyrelatedform(D,B),haspart(D,A).
verbgroup(A,B):- memberofdomainregion(D,C),membermeronym(F,D),similarto(A,E),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(E,B),haspart(B,F),synsetdomaintopicof(A,D),similarto(B,C).
verbgroup(A,B):- membermeronym(D,B),hypernym(A,C),memberofdomainregion(C,E).
verbgroup(A,B):- alsosee(D,B),alsosee(F,C),membermeronym(C,B),memberofdomainregion(E,A).
verbgroup(A,B):- alsosee(A,B),derivationallyrelatedform(A,D),similarto(C,B).
verbgroup(A,B):- derivationallyrelatedform(A,F),memberofdomainusage(D,B),alsosee(F,C),derivationallyrelatedform(F,E).
verbgroup(A,B):- derivationallyrelatedform(A,D),alsosee(F,C),synsetdomaintopicof(D,E),derivationallyrelatedform(F,B).
verbgroup(A,B):- similarto(B,F),alsosee(F,C),memberofdomainusage(D,A),haspart(C,E).
verbgroup(A,B):- hypernym(A,B),instancehypernym(D,B),similarto(B,C),instancehypernym(E,C).
verbgroup(A,B):- membermeronym(A,E),memberofdomainregion(C,E),similarto(B,C),similarto(D,C).
verbgroup(A,B):- alsosee(B,A),memberofdomainregion(B,C),memberofdomainregion(D,C).
verbgroup(A,B):- synsetdomaintopicof(E,C),derivationallyrelatedform(A,D),synsetdomaintopicof(C,E),similarto(B,C).
verbgroup(A,B):- similarto(D,E),haspart(B,F),memberofdomainusage(A,D),similarto(B,C).
verbgroup(A,B):- membermeronym(D,B),memberofdomainregion(E,C),similarto(B,C),alsosee(D,A).
verbgroup(A,B):- instancehypernym(B,D),synsetdomaintopicof(D,A),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(A,F),memberofdomainregion(B,E),alsosee(F,C),derivationallyrelatedform(C,D).
verbgroup(A,B):- hypernym(B,A),memberofdomainusage(A,D),similarto(B,C),hypernym(E,C).
verbgroup(A,B):- hypernym(B,C),alsosee(F,C),memberofdomainusage(D,A),synsetdomaintopicof(A,E).
verbgroup(A,B):- haspart(F,A),alsosee(F,C),instancehypernym(B,E),membermeronym(B,D).
verbgroup(A,B):- derivationallyrelatedform(D,A),instancehypernym(E,B),similarto(B,C),alsosee(D,A).
verbgroup(A,B):- memberofdomainusage(B,C),memberofdomainregion(D,C),memberofdomainregion(D,A).
verbgroup(A,B):- alsosee(F,C),haspart(E,A),hypernym(E,D),similarto(B,F).
verbgroup(A,B):- alsosee(F,B),alsosee(F,C),hypernym(E,A),memberofdomainusage(E,D).
verbgroup(A,B):- similarto(D,E),similarto(E,C),synsetdomaintopicof(A,D),similarto(B,C).
verbgroup(A,B):- haspart(E,D),derivationallyrelatedform(A,E),similarto(B,C),alsosee(D,A).
verbgroup(A,B):- alsosee(D,E),hypernym(B,F),alsosee(F,C),similarto(A,E).
verbgroup(A,B):- memberofdomainusage(D,B),memberofdomainusage(C,A),synsetdomaintopicof(C,E),similarto(B,C).
verbgroup(A,B):- membermeronym(C,A),memberofdomainregion(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- instancehypernym(C,A),alsosee(F,C),memberofdomainregion(A,D),haspart(E,B).
verbgroup(A,B):- membermeronym(D,A),haspart(F,B),alsosee(F,C),haspart(E,B).
verbgroup(A,B):- hypernym(D,A),haspart(B,D),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- derivationallyrelatedform(A,D),synsetdomaintopicof(D,E),similarto(B,C),haspart(A,D).
verbgroup(A,B):- membermeronym(C,A),membermeronym(C,D),hypernym(A,B).
verbgroup(A,B):- memberofdomainusage(B,D),membermeronym(E,A),derivationallyrelatedform(D,C).
verbgroup(A,B):- memberofdomainregion(A,B),hypernym(A,E),derivationallyrelatedform(D,B),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(A,E),synsetdomaintopicof(D,E),similarto(A,E),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(B,C),derivationallyrelatedform(D,E),alsosee(F,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(A,C),synsetdomaintopicof(E,D),memberofdomainregion(E,B).
verbgroup(A,B):- memberofdomainregion(B,D),similarto(D,B),alsosee(A,C),similarto(B,C).
verbgroup(A,B):- alsosee(D,F),memberofdomainregion(A,F),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- synsetdomaintopicof(E,C),alsosee(D,B),haspart(A,C).
verbgroup(A,B):- derivationallyrelatedform(B,D),alsosee(F,C),derivationallyrelatedform(F,A),synsetdomaintopicof(A,E).
verbgroup(A,B):- instancehypernym(E,A),alsosee(F,C),memberofdomainregion(B,D),derivationallyrelatedform(B,C).
verbgroup(A,B):- synsetdomaintopicof(E,A),alsosee(F,C),memberofdomainregion(B,D),instancehypernym(F,A).
verbgroup(A,B):- synsetdomaintopicof(B,C),memberofdomainregion(A,D),alsosee(D,A).
