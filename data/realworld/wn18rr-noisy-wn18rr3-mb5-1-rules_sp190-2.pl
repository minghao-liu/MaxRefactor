verbgroup(A,B):- synsetdomaintopicof(A,C),haspart(B,D),synsetdomaintopicof(A,E).
verbgroup(A,B):- memberofdomainregion(B,F),alsosee(E,F),alsosee(F,C),derivationallyrelatedform(A,D).
verbgroup(A,B):- derivationallyrelatedform(A,F),alsosee(F,C),alsosee(F,D),haspart(E,B).
verbgroup(A,B):- memberofdomainregion(B,C),alsosee(F,C),haspart(A,D),hypernym(B,E).
verbgroup(A,B):- derivationallyrelatedform(E,B),memberofdomainusage(E,D),instancehypernym(A,C).
verbgroup(A,B):- alsosee(C,A),derivationallyrelatedform(E,D),alsosee(F,C),hypernym(B,D).
verbgroup(A,B):- haspart(E,D),instancehypernym(A,D),derivationallyrelatedform(C,E),similarto(B,C).
verbgroup(A,B):- hypernym(E,B),alsosee(F,C),haspart(A,F),alsosee(F,D).
verbgroup(A,B):- hypernym(E,F),alsosee(D,C),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- derivationallyrelatedform(A,D),similarto(D,B),memberofdomainregion(B,D),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(E,B),synsetdomaintopicof(A,D),similarto(B,C),instancehypernym(E,C).
verbgroup(A,B):- synsetdomaintopicof(A,C),membermeronym(C,D),synsetdomaintopicof(C,B).
verbgroup(A,B):- derivationallyrelatedform(B,D),synsetdomaintopicof(A,D),similarto(B,C),similarto(D,C).
verbgroup(A,B):- derivationallyrelatedform(B,D),memberofdomainregion(A,C),instancehypernym(A,E).
verbgroup(A,B):- instancehypernym(B,E),synsetdomaintopicof(A,D),membermeronym(A,C).
verbgroup(A,B):- memberofdomainusage(D,B),similarto(B,C),synsetdomaintopicof(D,B),memberofdomainregion(B,A).
verbgroup(A,B):- derivationallyrelatedform(D,A),alsosee(B,E),alsosee(F,C),memberofdomainregion(B,C).
verbgroup(A,B):- similarto(D,E),alsosee(B,E),alsosee(F,C),hypernym(A,F).
verbgroup(A,B):- membermeronym(A,D),instancehypernym(B,D),alsosee(A,E),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(D,A),membermeronym(A,E),memberofdomainusage(C,F),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(F,D),synsetdomaintopicof(D,E),similarto(B,C),haspart(A,D).
verbgroup(A,B):- alsosee(D,E),memberofdomainregion(D,F),membermeronym(A,E),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(E,A),derivationallyrelatedform(A,D),hypernym(A,F),similarto(B,C).
verbgroup(A,B):- instancehypernym(D,E),membermeronym(A,E),memberofdomainregion(B,C).
verbgroup(A,B):- alsosee(A,D),memberofdomainusage(B,D),similarto(B,C).
verbgroup(A,B):- instancehypernym(F,B),membermeronym(A,E),similarto(B,C),haspart(A,D).
verbgroup(A,B):- instancehypernym(D,A),hypernym(D,B),memberofdomainregion(B,C),similarto(B,C).
verbgroup(A,B):- similarto(A,E),alsosee(D,C),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(B,C),haspart(A,D),hypernym(D,C).
verbgroup(A,B):- memberofdomainusage(F,E),memberofdomainusage(A,F),alsosee(F,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- similarto(A,F),alsosee(E,B),alsosee(F,C),synsetdomaintopicof(A,D).
verbgroup(A,B):- derivationallyrelatedform(C,D),alsosee(B,A),derivationallyrelatedform(C,A).
verbgroup(A,B):- alsosee(C,A),derivationallyrelatedform(D,B),similarto(B,C),synsetdomaintopicof(B,E).
verbgroup(A,B):- similarto(A,D),hypernym(B,C),similarto(B,C),hypernym(B,E).
verbgroup(A,B):- alsosee(A,D),similarto(D,E),similarto(B,C),membermeronym(D,A).
verbgroup(A,B):- memberofdomainregion(B,E),alsosee(F,C),alsosee(F,A),membermeronym(F,D).
verbgroup(A,B):- haspart(D,B),synsetdomaintopicof(A,F),alsosee(F,C),derivationallyrelatedform(D,E).
verbgroup(A,B):- alsosee(C,A),haspart(D,B),hypernym(B,D).
verbgroup(A,B):- memberofdomainregion(D,B),synsetdomaintopicof(A,C),similarto(B,C),hypernym(C,E).
verbgroup(A,B):- haspart(C,B),alsosee(B,C),similarto(B,C),similarto(A,C).
verbgroup(A,B):- memberofdomainregion(C,B),membermeronym(C,B),memberofdomainusage(D,A).
verbgroup(A,B):- alsosee(F,C),derivationallyrelatedform(B,E),membermeronym(F,A),membermeronym(B,D).
verbgroup(A,B):- haspart(C,D),alsosee(F,C),similarto(E,A),hypernym(C,B).
verbgroup(A,B):- similarto(D,A),memberofdomainusage(D,B),derivationallyrelatedform(E,D),similarto(B,C).
verbgroup(A,B):- alsosee(A,E),synsetdomaintopicof(F,B),membermeronym(D,F),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(B,C),hypernym(C,A),memberofdomainusage(C,B).
verbgroup(A,B):- similarto(B,C),similarto(A,E),haspart(F,E),memberofdomainregion(A,D).
verbgroup(A,B):- instancehypernym(E,A),derivationallyrelatedform(C,A),alsosee(F,C),memberofdomainusage(B,D).
verbgroup(A,B):- similarto(C,D),hypernym(D,B),similarto(B,C),alsosee(D,A).
verbgroup(A,B):- derivationallyrelatedform(E,D),membermeronym(E,A),similarto(B,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- memberofdomainusage(D,F),hypernym(E,B),alsosee(F,C),memberofdomainusage(F,A).
verbgroup(A,B):- instancehypernym(D,B),membermeronym(E,A),haspart(C,E).
verbgroup(A,B):- alsosee(F,C),memberofdomainregion(B,E),alsosee(D,F),hypernym(A,F).
verbgroup(A,B):- memberofdomainusage(C,E),instancehypernym(A,D),hypernym(B,D),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(C,A),membermeronym(D,B),membermeronym(A,C),similarto(B,C).
verbgroup(A,B):- hypernym(B,F),similarto(A,D),similarto(C,E),similarto(B,C).
verbgroup(A,B):- haspart(A,E),hypernym(C,D),similarto(C,F),similarto(B,C).
verbgroup(A,B):- instancehypernym(B,D),similarto(B,C),hypernym(A,D),derivationallyrelatedform(A,C).
verbgroup(A,B):- similarto(A,D),alsosee(F,C),similarto(B,E),haspart(F,E).
verbgroup(A,B):- derivationallyrelatedform(A,D),instancehypernym(C,E),similarto(B,C),memberofdomainusage(C,B).
verbgroup(A,B):- similarto(A,E),memberofdomainregion(D,F),alsosee(D,C),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(E,B),alsosee(F,C),membermeronym(F,A),hypernym(D,C).
verbgroup(A,B):- hypernym(A,C),hypernym(D,B),alsosee(F,C),alsosee(E,C).
verbgroup(A,B):- derivationallyrelatedform(A,D),similarto(A,B),similarto(B,C),similarto(E,B).
verbgroup(A,B):- membermeronym(B,A),memberofdomainusage(C,D),memberofdomainregion(A,E),similarto(B,C).
verbgroup(A,B):- alsosee(C,A),memberofdomainregion(B,E),alsosee(F,C),memberofdomainregion(A,D).
verbgroup(A,B):- alsosee(F,B),alsosee(F,C),membermeronym(E,A),hypernym(D,C).
verbgroup(A,B):- instancehypernym(E,A),alsosee(F,C),similarto(F,D),similarto(B,C).
verbgroup(A,B):- hypernym(A,E),similarto(B,C),haspart(A,D),membermeronym(D,C).
verbgroup(A,B):- derivationallyrelatedform(A,F),alsosee(F,C),memberofdomainregion(D,B),memberofdomainusage(E,D).
verbgroup(A,B):- hypernym(A,C),haspart(B,D),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(B,C),instancehypernym(A,D),similarto(B,C),alsosee(C,D).
verbgroup(A,B):- memberofdomainregion(D,B),synsetdomaintopicof(A,C),memberofdomainregion(A,C),similarto(B,C).
verbgroup(A,B):- alsosee(F,C),alsosee(D,B),alsosee(A,E),haspart(D,C).
verbgroup(A,B):- membermeronym(C,E),instancehypernym(A,D),alsosee(B,C).
verbgroup(A,B):- alsosee(D,E),derivationallyrelatedform(A,E),similarto(B,C),memberofdomainusage(C,B).
verbgroup(A,B):- membermeronym(B,A),derivationallyrelatedform(C,A),membermeronym(D,A).
verbgroup(A,B):- similarto(B,C),derivationallyrelatedform(B,D),instancehypernym(A,E),alsosee(A,F).
verbgroup(A,B):- memberofdomainregion(C,B),memberofdomainusage(C,A),memberofdomainusage(B,A).
verbgroup(A,B):- membermeronym(D,A),memberofdomainregion(A,E),similarto(B,C),synsetdomaintopicof(D,F).
verbgroup(A,B):- memberofdomainregion(D,B),hypernym(D,B),memberofdomainusage(B,A),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(A,C),synsetdomaintopicof(B,D),similarto(B,C).
verbgroup(A,B):- similarto(E,F),memberofdomainregion(A,E),similarto(B,C),memberofdomainusage(D,A).
verbgroup(A,B):- similarto(E,C),haspart(D,A),similarto(E,B).
verbgroup(A,B):- alsosee(F,C),memberofdomainregion(F,D),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- hypernym(F,D),haspart(B,F),similarto(A,E),similarto(B,C).
verbgroup(A,B):- similarto(E,D),alsosee(F,C),hypernym(C,A),hypernym(B,D).
verbgroup(A,B):- derivationallyrelatedform(D,A),alsosee(F,C),derivationallyrelatedform(E,B),hypernym(C,E).
verbgroup(A,B):- derivationallyrelatedform(B,C),alsosee(F,C),memberofdomainusage(F,D),memberofdomainusage(A,E).
verbgroup(A,B):- derivationallyrelatedform(A,F),derivationallyrelatedform(E,D),alsosee(F,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- haspart(C,B),instancehypernym(D,B),haspart(A,C),similarto(B,C).
verbgroup(A,B):- alsosee(A,C),haspart(D,E),similarto(E,B).
verbgroup(A,B):- synsetdomaintopicof(E,C),instancehypernym(A,D),similarto(B,E).
verbgroup(A,B):- synsetdomaintopicof(A,C),haspart(E,D),memberofdomainregion(E,B).
verbgroup(A,B):- instancehypernym(B,D),hypernym(D,F),alsosee(F,C),memberofdomainusage(E,A).
verbgroup(A,B):- memberofdomainregion(F,A),memberofdomainusage(D,B),alsosee(F,C),haspart(D,E).
verbgroup(A,B):- memberofdomainregion(B,C),membermeronym(E,A),haspart(D,E).
verbgroup(A,B):- instancehypernym(A,D),alsosee(A,E),haspart(B,C).
verbgroup(A,B):- haspart(D,B),haspart(A,E),membermeronym(C,E),alsosee(F,C).
verbgroup(A,B):- instancehypernym(F,D),alsosee(B,E),membermeronym(A,D),similarto(B,C).
verbgroup(A,B):- hypernym(D,A),memberofdomainusage(A,F),alsosee(F,C),memberofdomainusage(E,B).
verbgroup(A,B):- memberofdomainregion(E,F),alsosee(F,C),similarto(B,E),haspart(D,A).
verbgroup(A,B):- haspart(A,D),derivationallyrelatedform(C,B),instancehypernym(E,C).
verbgroup(A,B):- alsosee(C,B),synsetdomaintopicof(C,A),membermeronym(D,A).
verbgroup(A,B):- alsosee(A,B),haspart(D,A),similarto(B,C),membermeronym(D,C).
verbgroup(A,B):- alsosee(F,C),memberofdomainregion(D,A),instancehypernym(E,B),membermeronym(F,D).
verbgroup(A,B):- instancehypernym(C,E),haspart(B,D),membermeronym(E,A).
verbgroup(A,B):- alsosee(F,E),synsetdomaintopicof(A,D),similarto(B,C),instancehypernym(F,A).
verbgroup(A,B):- similarto(B,D),alsosee(D,C),haspart(B,A).
verbgroup(A,B):- alsosee(F,C),alsosee(D,F),haspart(C,B),synsetdomaintopicof(A,E).
verbgroup(A,B):- haspart(B,E),memberofdomainusage(D,B),derivationallyrelatedform(A,D),similarto(B,C).
verbgroup(A,B):- instancehypernym(E,A),memberofdomainregion(A,D),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- synsetdomaintopicof(B,C),memberofdomainusage(C,D),alsosee(A,C).
verbgroup(A,B):- alsosee(A,D),instancehypernym(E,B),haspart(E,A),similarto(B,C).
verbgroup(A,B):- instancehypernym(C,A),alsosee(F,C),memberofdomainregion(D,A),synsetdomaintopicof(B,E).
verbgroup(A,B):- derivationallyrelatedform(A,E),similarto(C,B),similarto(B,C),alsosee(D,A).
verbgroup(A,B):- synsetdomaintopicof(B,C),membermeronym(B,A),alsosee(D,B).
verbgroup(A,B):- alsosee(A,D),hypernym(B,F),memberofdomainusage(D,E),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(D,A),haspart(B,D),similarto(D,C).
verbgroup(A,B):- derivationallyrelatedform(D,A),haspart(A,E),alsosee(F,C),derivationallyrelatedform(C,B).
verbgroup(A,B):- alsosee(D,E),memberofdomainregion(B,F),alsosee(F,C),alsosee(D,A).
verbgroup(A,B):- haspart(D,B),instancehypernym(D,A),alsosee(B,E),similarto(B,C).
verbgroup(A,B):- instancehypernym(E,F),alsosee(F,C),synsetdomaintopicof(A,D),hypernym(F,B).
verbgroup(A,B):- memberofdomainusage(A,C),similarto(D,B),membermeronym(A,C).
verbgroup(A,B):- memberofdomainusage(B,C),membermeronym(A,B),alsosee(B,C).
verbgroup(A,B):- alsosee(D,E),instancehypernym(E,F),similarto(B,C),haspart(A,D).
verbgroup(A,B):- haspart(D,F),similarto(D,E),similarto(B,C),haspart(A,D).
verbgroup(A,B):- similarto(B,A),synsetdomaintopicof(B,A),haspart(C,A).
verbgroup(A,B):- membermeronym(B,C),instancehypernym(B,A),instancehypernym(D,B),similarto(B,C).
verbgroup(A,B):- instancehypernym(D,E),alsosee(A,E),haspart(C,B),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(A,B),similarto(C,B),synsetdomaintopicof(A,B).
verbgroup(A,B):- instancehypernym(E,A),alsosee(F,C),derivationallyrelatedform(D,B),hypernym(C,D).
verbgroup(A,B):- membermeronym(A,E),derivationallyrelatedform(D,B),memberofdomainusage(C,E),similarto(B,C).
verbgroup(A,B):- membermeronym(A,E),membermeronym(B,C),similarto(B,C),membermeronym(D,A).
verbgroup(A,B):- alsosee(A,D),similarto(C,A),derivationallyrelatedform(C,B),similarto(B,C).
verbgroup(A,B):- membermeronym(B,E),alsosee(F,C),hypernym(A,F),alsosee(F,D).
verbgroup(A,B):- derivationallyrelatedform(C,D),similarto(C,A),hypernym(A,B).
verbgroup(A,B):- memberofdomainusage(B,C),memberofdomainregion(E,A),haspart(A,D).
verbgroup(A,B):- memberofdomainusage(A,D),similarto(E,A),derivationallyrelatedform(B,C).
verbgroup(A,B):- alsosee(B,A),hypernym(A,C).
verbgroup(A,B):- memberofdomainusage(E,B),similarto(B,C),hypernym(A,D),synsetdomaintopicof(D,F).
verbgroup(A,B):- hypernym(E,F),haspart(B,F),alsosee(F,C),memberofdomainregion(D,A).
verbgroup(A,B):- alsosee(C,A),alsosee(F,C),memberofdomainregion(B,D),memberofdomainregion(E,F).
verbgroup(A,B):- alsosee(D,E),instancehypernym(A,D),similarto(B,C),haspart(E,C).
verbgroup(A,B):- instancehypernym(D,A),alsosee(F,C),haspart(C,B),memberofdomainusage(C,E).
verbgroup(A,B):- memberofdomainregion(D,B),hypernym(E,A),similarto(A,C).
verbgroup(A,B):- similarto(D,B),membermeronym(A,C),hypernym(C,B).
verbgroup(A,B):- haspart(B,E),alsosee(F,C),memberofdomainregion(D,A),derivationallyrelatedform(A,C).
verbgroup(A,B):- memberofdomainusage(B,C),similarto(C,A),similarto(B,A).
verbgroup(A,B):- hypernym(A,C),synsetdomaintopicof(C,D),instancehypernym(D,B).
verbgroup(A,B):- alsosee(C,A),alsosee(D,B),membermeronym(B,D).
verbgroup(A,B):- hypernym(D,B),haspart(F,A),similarto(B,C),haspart(C,E).
verbgroup(A,B):- similarto(D,E),alsosee(F,C),synsetdomaintopicof(B,E),hypernym(F,A).
verbgroup(A,B):- synsetdomaintopicof(E,A),similarto(B,C),hypernym(A,D),instancehypernym(F,A).
verbgroup(A,B):- hypernym(A,E),memberofdomainusage(D,A),similarto(B,C),haspart(E,B).
verbgroup(A,B):- derivationallyrelatedform(D,B),derivationallyrelatedform(C,E),haspart(E,A).
verbgroup(A,B):- haspart(F,B),memberofdomainregion(D,C),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- synsetdomaintopicof(A,D),memberofdomainusage(B,A),similarto(B,C),derivationallyrelatedform(A,C).
verbgroup(A,B):- hypernym(E,F),memberofdomainusage(B,F),alsosee(F,C),membermeronym(A,D).
verbgroup(A,B):- memberofdomainusage(A,E),memberofdomainregion(B,D),similarto(B,C),haspart(C,E).
verbgroup(A,B):- memberofdomainusage(D,E),alsosee(F,C),haspart(C,B),hypernym(A,D).
verbgroup(A,B):- memberofdomainusage(D,E),memberofdomainusage(D,A),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- memberofdomainusage(D,C),instancehypernym(A,D),instancehypernym(A,E),similarto(B,C).
verbgroup(A,B):- similarto(D,B),haspart(A,F),similarto(B,C),synsetdomaintopicof(B,E).
verbgroup(A,B):- memberofdomainusage(A,E),haspart(B,D),similarto(B,C),similarto(A,C).
verbgroup(A,B):- alsosee(F,C),memberofdomainregion(E,B),hypernym(A,D),hypernym(F,A).
verbgroup(A,B):- synsetdomaintopicof(B,C),synsetdomaintopicof(E,A),memberofdomainusage(C,D).
verbgroup(A,B):- instancehypernym(A,D),instancehypernym(C,E),similarto(A,E),similarto(B,C).
verbgroup(A,B):- alsosee(E,B),memberofdomainusage(A,D),derivationallyrelatedform(A,B),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(E,A),derivationallyrelatedform(D,A),alsosee(F,C),memberofdomainregion(B,F).
verbgroup(A,B):- hypernym(D,B),alsosee(F,C),alsosee(B,C),similarto(E,A).
verbgroup(A,B):- synsetdomaintopicof(F,A),alsosee(F,C),similarto(F,D),similarto(E,B).
verbgroup(A,B):- derivationallyrelatedform(A,D),haspart(D,C),similarto(C,B).
verbgroup(A,B):- derivationallyrelatedform(E,A),derivationallyrelatedform(E,D),instancehypernym(B,C).
verbgroup(A,B):- derivationallyrelatedform(A,D),derivationallyrelatedform(C,E),instancehypernym(F,C),similarto(B,C).
verbgroup(A,B):- hypernym(C,D),similarto(B,C),hypernym(A,D),memberofdomainregion(C,E).
verbgroup(A,B):- instancehypernym(C,D),instancehypernym(A,D),membermeronym(B,D).
verbgroup(A,B):- alsosee(B,E),memberofdomainusage(B,D),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- alsosee(A,D),haspart(D,A),derivationallyrelatedform(B,C).
verbgroup(A,B):- alsosee(A,D),alsosee(F,C),memberofdomainregion(D,E),memberofdomainusage(C,B).
verbgroup(A,B):- memberofdomainusage(E,B),hypernym(F,D),alsosee(F,C),memberofdomainusage(C,A).
verbgroup(A,B):- membermeronym(A,D),haspart(A,E),similarto(B,C),alsosee(E,D).
verbgroup(A,B):- memberofdomainusage(D,F),alsosee(A,E),memberofdomainregion(A,F),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(B,E),hypernym(A,C),haspart(D,A),similarto(B,C).
verbgroup(A,B):- similarto(E,D),derivationallyrelatedform(A,E),similarto(B,C),alsosee(E,A).
verbgroup(A,B):- synsetdomaintopicof(E,A),memberofdomainusage(D,C),haspart(B,C).
verbgroup(A,B):- membermeronym(A,D),hypernym(E,A),similarto(B,C),memberofdomainusage(E,D).
verbgroup(A,B):- derivationallyrelatedform(D,B),alsosee(F,C),synsetdomaintopicof(D,E),membermeronym(A,F).
verbgroup(A,B):- similarto(C,D),haspart(D,A),hypernym(C,B).
verbgroup(A,B):- membermeronym(A,D),haspart(E,D),derivationallyrelatedform(A,D),similarto(B,C).
