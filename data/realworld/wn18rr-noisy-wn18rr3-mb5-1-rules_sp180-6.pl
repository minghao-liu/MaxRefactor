verbgroup(A,B):- memberofdomainusage(C,D),similarto(D,B),memberofdomainregion(E,A).
verbgroup(A,B):- derivationallyrelatedform(B,C),membermeronym(C,D),haspart(A,D).
verbgroup(A,B):- derivationallyrelatedform(C,D),membermeronym(D,B),alsosee(F,C),instancehypernym(A,E).
verbgroup(A,B):- alsosee(E,B),hypernym(A,E),hypernym(B,D),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(A,E),synsetdomaintopicof(F,B),similarto(B,C),instancehypernym(D,C).
verbgroup(A,B):- instancehypernym(B,A),haspart(D,A),similarto(B,C),alsosee(B,D).
verbgroup(A,B):- derivationallyrelatedform(E,B),memberofdomainregion(D,A),derivationallyrelatedform(B,C).
verbgroup(A,B):- instancehypernym(B,D),similarto(B,D),alsosee(A,C).
verbgroup(A,B):- membermeronym(C,A),alsosee(F,C),hypernym(B,E),memberofdomainregion(A,D).
verbgroup(A,B):- hypernym(D,E),memberofdomainregion(C,D),similarto(B,C),instancehypernym(A,C).
verbgroup(A,B):- derivationallyrelatedform(E,A),hypernym(D,B),alsosee(F,C),derivationallyrelatedform(C,A).
verbgroup(A,B):- instancehypernym(C,B),instancehypernym(B,C),memberofdomainusage(D,A).
verbgroup(A,B):- instancehypernym(B,A),haspart(D,A),similarto(B,C),memberofdomainusage(E,A).
verbgroup(A,B):- memberofdomainregion(E,F),membermeronym(A,E),similarto(E,D),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(B,E),similarto(D,E),similarto(B,C),instancehypernym(A,C).
verbgroup(A,B):- alsosee(A,D),membermeronym(A,E),similarto(B,C),haspart(B,A).
verbgroup(A,B):- membermeronym(E,B),synsetdomaintopicof(B,D),instancehypernym(A,C).
verbgroup(A,B):- synsetdomaintopicof(B,C),derivationallyrelatedform(A,C),similarto(C,D).
verbgroup(A,B):- alsosee(A,D),derivationallyrelatedform(B,A),similarto(B,C),similarto(E,B).
verbgroup(A,B):- alsosee(D,E),memberofdomainregion(A,E),alsosee(F,A),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(A,D),derivationallyrelatedform(A,B),memberofdomainusage(A,B),similarto(B,C).
verbgroup(A,B):- alsosee(F,C),derivationallyrelatedform(E,B),memberofdomainregion(B,D),similarto(A,C).
verbgroup(A,B):- alsosee(A,D),instancehypernym(F,B),synsetdomaintopicof(C,E),similarto(B,C).
verbgroup(A,B):- alsosee(D,E),memberofdomainregion(A,E),similarto(F,A),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(B,E),hypernym(C,A),alsosee(B,D).
verbgroup(A,B):- synsetdomaintopicof(F,D),alsosee(F,C),similarto(E,A),haspart(B,D).
verbgroup(A,B):- membermeronym(E,F),derivationallyrelatedform(A,D),similarto(B,C),alsosee(E,D).
verbgroup(A,B):- alsosee(F,C),hypernym(B,C),alsosee(A,E),derivationallyrelatedform(A,D).
verbgroup(A,B):- haspart(B,C),alsosee(F,C),similarto(E,A),haspart(B,D).
verbgroup(A,B):- derivationallyrelatedform(E,C),instancehypernym(A,D),derivationallyrelatedform(D,F),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(B,E),synsetdomaintopicof(E,A),similarto(D,B),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(A,E),alsosee(F,C),hypernym(A,C),memberofdomainusage(B,D).
verbgroup(A,B):- derivationallyrelatedform(A,D),alsosee(D,F),similarto(B,C),memberofdomainregion(C,E).
verbgroup(A,B):- haspart(D,B),haspart(A,E),instancehypernym(C,A),similarto(B,C).
verbgroup(A,B):- similarto(B,D),memberofdomainusage(A,F),alsosee(F,C),membermeronym(E,C).
verbgroup(A,B):- hypernym(A,E),synsetdomaintopicof(D,E),derivationallyrelatedform(C,B).
verbgroup(A,B):- hypernym(B,A),synsetdomaintopicof(A,B),memberofdomainusage(C,B).
verbgroup(A,B):- alsosee(C,A),alsosee(F,C),synsetdomaintopicof(B,D),memberofdomainregion(E,D).
verbgroup(A,B):- haspart(B,E),alsosee(B,A),instancehypernym(D,B),similarto(B,C).
verbgroup(A,B):- instancehypernym(E,D),similarto(F,A),similarto(B,C),haspart(A,D).
verbgroup(A,B):- alsosee(A,D),membermeronym(E,B),instancehypernym(C,E).
verbgroup(A,B):- membermeronym(D,E),instancehypernym(E,B),alsosee(F,C),alsosee(F,A).
verbgroup(A,B):- memberofdomainusage(A,C),instancehypernym(B,D),instancehypernym(B,E).
verbgroup(A,B):- alsosee(C,E),haspart(F,A),alsosee(F,C),alsosee(B,D).
verbgroup(A,B):- memberofdomainregion(F,A),alsosee(F,C),derivationallyrelatedform(D,B),synsetdomaintopicof(E,B).
verbgroup(A,B):- similarto(D,A),alsosee(F,C),hypernym(B,E),haspart(F,B).
verbgroup(A,B):- synsetdomaintopicof(F,A),instancehypernym(A,D),membermeronym(C,E),similarto(B,C).
verbgroup(A,B):- similarto(A,E),similarto(B,C),instancehypernym(D,F),alsosee(A,F).
verbgroup(A,B):- membermeronym(C,A),hypernym(B,D).
verbgroup(A,B):- derivationallyrelatedform(F,D),haspart(B,F),alsosee(F,C),haspart(E,A).
verbgroup(A,B):- alsosee(F,C),alsosee(D,F),synsetdomaintopicof(B,E),hypernym(F,A).
verbgroup(A,B):- membermeronym(E,B),alsosee(F,C),haspart(A,F),membermeronym(D,A).
verbgroup(A,B):- memberofdomainregion(A,E),instancehypernym(A,D),similarto(E,C),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(B,D),alsosee(B,E),similarto(A,E),similarto(B,C).
verbgroup(A,B):- alsosee(A,B),memberofdomainregion(E,A),similarto(B,C),instancehypernym(A,D).
verbgroup(A,B):- alsosee(A,E),similarto(F,D),similarto(B,C),memberofdomainusage(D,A).
verbgroup(A,B):- derivationallyrelatedform(C,E),haspart(F,A),alsosee(F,C),membermeronym(D,B).
verbgroup(A,B):- similarto(A,D),alsosee(F,C),memberofdomainusage(E,F),similarto(B,C).
verbgroup(A,B):- similarto(C,A),haspart(A,B),membermeronym(B,D).
verbgroup(A,B):- instancehypernym(D,B),synsetdomaintopicof(B,A),similarto(B,C),synsetdomaintopicof(C,B).
verbgroup(A,B):- memberofdomainregion(A,B),memberofdomainregion(D,A),synsetdomaintopicof(C,B).
verbgroup(A,B):- synsetdomaintopicof(C,D),synsetdomaintopicof(E,B),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- alsosee(D,B),synsetdomaintopicof(D,A),similarto(E,D),similarto(B,C).
verbgroup(A,B):- membermeronym(A,D),synsetdomaintopicof(D,C),hypernym(D,B),similarto(B,C).
verbgroup(A,B):- hypernym(D,A),hypernym(D,B),memberofdomainregion(B,C).
verbgroup(A,B):- memberofdomainregion(A,C),instancehypernym(B,D),alsosee(F,C),memberofdomainregion(A,E).
verbgroup(A,B):- derivationallyrelatedform(E,D),alsosee(F,C),memberofdomainregion(F,B),membermeronym(A,E).
verbgroup(A,B):- derivationallyrelatedform(D,B),alsosee(F,A),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- similarto(E,F),hypernym(A,E),memberofdomainusage(D,C),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(B,F),similarto(A,E),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- alsosee(F,C),hypernym(F,E),haspart(A,D),haspart(F,B).
verbgroup(A,B):- memberofdomainusage(D,E),memberofdomainusage(A,E),similarto(B,C),alsosee(E,D).
verbgroup(A,B):- similarto(A,E),memberofdomainusage(D,E),haspart(D,A),similarto(B,C).
verbgroup(A,B):- haspart(A,E),alsosee(F,C),hypernym(E,D),memberofdomainregion(F,B).
verbgroup(A,B):- similarto(D,A),alsosee(F,C),similarto(B,E),hypernym(A,F).
verbgroup(A,B):- hypernym(B,F),alsosee(F,C),haspart(A,D),memberofdomainusage(F,E).
verbgroup(A,B):- alsosee(F,C),hypernym(E,B),synsetdomaintopicof(D,A),instancehypernym(F,E).
verbgroup(A,B):- alsosee(D,B),similarto(C,E),synsetdomaintopicof(A,D),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(D,E),memberofdomainregion(D,A),instancehypernym(B,C).
verbgroup(A,B):- alsosee(A,D),alsosee(C,B),synsetdomaintopicof(B,E).
verbgroup(A,B):- memberofdomainusage(F,D),synsetdomaintopicof(B,D),derivationallyrelatedform(A,E),similarto(B,C).
verbgroup(A,B):- hypernym(D,C),alsosee(F,C),derivationallyrelatedform(E,A),synsetdomaintopicof(C,B).
verbgroup(A,B):- alsosee(D,B),derivationallyrelatedform(A,D),similarto(B,C),haspart(E,B).
verbgroup(A,B):- similarto(B,C),memberofdomainregion(D,B),hypernym(B,E),alsosee(E,A).
verbgroup(A,B):- hypernym(A,E),similarto(B,C),synsetdomaintopicof(D,B),synsetdomaintopicof(C,B).
verbgroup(A,B):- memberofdomainregion(C,A),membermeronym(B,A),memberofdomainusage(A,D),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(B,F),alsosee(F,C),membermeronym(F,D),membermeronym(E,A).
verbgroup(A,B):- alsosee(F,C),derivationallyrelatedform(B,E),derivationallyrelatedform(D,F),memberofdomainregion(A,D).
verbgroup(A,B):- instancehypernym(D,E),haspart(E,F),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- alsosee(A,E),derivationallyrelatedform(D,B),similarto(B,C),membermeronym(B,D).
verbgroup(A,B):- derivationallyrelatedform(E,D),alsosee(F,C),instancehypernym(D,B),membermeronym(A,C).
verbgroup(A,B):- derivationallyrelatedform(D,B),derivationallyrelatedform(D,A),similarto(B,E),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(A,E),instancehypernym(A,E),similarto(B,C),hypernym(D,C).
verbgroup(A,B):- memberofdomainusage(F,D),synsetdomaintopicof(E,D),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- synsetdomaintopicof(D,A),haspart(C,B),memberofdomainusage(B,A).
verbgroup(A,B):- memberofdomainregion(C,A),similarto(D,B),membermeronym(C,D).
verbgroup(A,B):- memberofdomainusage(E,A),derivationallyrelatedform(D,C),similarto(B,C),instancehypernym(A,C).
verbgroup(A,B):- derivationallyrelatedform(A,E),memberofdomainusage(C,E),memberofdomainregion(B,D).
verbgroup(A,B):- haspart(E,D),synsetdomaintopicof(D,E),synsetdomaintopicof(A,D),similarto(B,C).
verbgroup(A,B):- membermeronym(D,B),alsosee(B,F),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- derivationallyrelatedform(D,A),derivationallyrelatedform(C,B),memberofdomainusage(A,E).
verbgroup(A,B):- derivationallyrelatedform(E,A),instancehypernym(B,D),membermeronym(A,C).
verbgroup(A,B):- hypernym(C,F),hypernym(A,E),synsetdomaintopicof(E,D),similarto(B,C).
verbgroup(A,B):- instancehypernym(B,D),derivationallyrelatedform(B,E),haspart(C,A).
verbgroup(A,B):- similarto(D,B),similarto(B,C),haspart(A,D),memberofdomainusage(C,B).
verbgroup(A,B):- hypernym(E,F),similarto(B,C),hypernym(A,D),instancehypernym(B,F).
verbgroup(A,B):- instancehypernym(B,D),alsosee(F,C),instancehypernym(A,E),instancehypernym(F,E).
verbgroup(A,B):- similarto(A,C),hypernym(D,B),alsosee(F,C),hypernym(C,E).
verbgroup(A,B):- haspart(A,B),membermeronym(C,B),similarto(A,C).
verbgroup(A,B):- hypernym(B,A),membermeronym(C,B),synsetdomaintopicof(D,B).
verbgroup(A,B):- alsosee(A,D),memberofdomainusage(B,E),membermeronym(F,A),similarto(B,C).
verbgroup(A,B):- haspart(B,E),alsosee(F,C),instancehypernym(D,F),derivationallyrelatedform(A,C).
verbgroup(A,B):- similarto(B,C),hypernym(C,B),haspart(C,A),instancehypernym(A,C).
verbgroup(A,B):- membermeronym(B,C),derivationallyrelatedform(A,D),similarto(B,E).
verbgroup(A,B):- synsetdomaintopicof(B,C),synsetdomaintopicof(D,C),instancehypernym(A,C).
verbgroup(A,B):- hypernym(C,F),derivationallyrelatedform(A,D),similarto(E,D),similarto(B,C).
verbgroup(A,B):- hypernym(D,A),memberofdomainregion(B,C),alsosee(F,C),instancehypernym(E,C).
verbgroup(A,B):- membermeronym(C,E),haspart(E,C),synsetdomaintopicof(A,D),similarto(B,C).
verbgroup(A,B):- hypernym(B,A),hypernym(A,C),haspart(B,D).
verbgroup(A,B):- instancehypernym(E,A),memberofdomainusage(F,B),similarto(B,C),haspart(A,D).
verbgroup(A,B):- memberofdomainregion(D,B),alsosee(F,C),memberofdomainregion(F,D),memberofdomainusage(E,A).
verbgroup(A,B):- memberofdomainusage(D,C),haspart(D,A),similarto(B,C),instancehypernym(A,C).
verbgroup(A,B):- instancehypernym(D,A),haspart(D,F),alsosee(F,C),instancehypernym(E,B).
verbgroup(A,B):- synsetdomaintopicof(C,D),synsetdomaintopicof(A,F),hypernym(F,E),similarto(B,C).
verbgroup(A,B):- instancehypernym(D,E),alsosee(F,C),instancehypernym(B,E),memberofdomainusage(F,A).
verbgroup(A,B):- memberofdomainusage(A,C),haspart(A,C),instancehypernym(B,C).
verbgroup(A,B):- memberofdomainusage(E,B),alsosee(F,C),memberofdomainusage(A,D),instancehypernym(E,C).
verbgroup(A,B):- hypernym(C,E),hypernym(D,E),similarto(B,C),instancehypernym(F,A).
verbgroup(A,B):- alsosee(F,C),hypernym(E,A),membermeronym(B,F),hypernym(D,C).
verbgroup(A,B):- hypernym(A,E),alsosee(F,C),derivationallyrelatedform(D,B),synsetdomaintopicof(D,F).
verbgroup(A,B):- alsosee(E,F),synsetdomaintopicof(B,D),membermeronym(A,E),similarto(B,C).
verbgroup(A,B):- instancehypernym(A,F),memberofdomainusage(C,D),instancehypernym(A,E),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(B,C),derivationallyrelatedform(D,A),memberofdomainregion(E,C).
verbgroup(A,B):- alsosee(C,D),alsosee(B,E),alsosee(F,C),alsosee(A,F).
verbgroup(A,B):- membermeronym(B,A),membermeronym(D,B),haspart(A,C),similarto(B,C).
verbgroup(A,B):- alsosee(B,E),alsosee(F,C),membermeronym(B,F),haspart(A,D).
verbgroup(A,B):- haspart(F,D),alsosee(F,C),synsetdomaintopicof(B,E),instancehypernym(A,C).
verbgroup(A,B):- derivationallyrelatedform(D,A),memberofdomainusage(D,B),similarto(B,C),memberofdomainregion(C,E).
verbgroup(A,B):- alsosee(C,A),similarto(D,A),hypernym(A,B).
verbgroup(A,B):- instancehypernym(C,D),synsetdomaintopicof(A,F),similarto(B,C),synsetdomaintopicof(E,F).
verbgroup(A,B):- derivationallyrelatedform(D,A),memberofdomainusage(E,B),alsosee(F,C),hypernym(F,B).
verbgroup(A,B):- memberofdomainregion(C,B),derivationallyrelatedform(C,E),alsosee(F,C),memberofdomainregion(A,D).
verbgroup(A,B):- derivationallyrelatedform(C,B),membermeronym(A,C),hypernym(C,B).
verbgroup(A,B):- derivationallyrelatedform(D,A),derivationallyrelatedform(B,A),memberofdomainregion(C,B).
verbgroup(A,B):- synsetdomaintopicof(A,C),derivationallyrelatedform(C,A),instancehypernym(D,B).
verbgroup(A,B):- memberofdomainusage(D,B),instancehypernym(A,B),similarto(B,C),alsosee(B,D).
verbgroup(A,B):- membermeronym(D,E),memberofdomainusage(C,D),similarto(B,C),instancehypernym(F,A).
verbgroup(A,B):- hypernym(A,E),alsosee(F,C),memberofdomainregion(F,B),membermeronym(F,D).
verbgroup(A,B):- membermeronym(A,D),similarto(C,B),similarto(B,C),memberofdomainusage(E,A).
verbgroup(A,B):- memberofdomainregion(F,A),membermeronym(D,B),alsosee(F,C),derivationallyrelatedform(B,E).
verbgroup(A,B):- membermeronym(E,D),haspart(D,A),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- alsosee(C,E),alsosee(A,B),similarto(B,C),instancehypernym(A,D).
verbgroup(A,B):- derivationallyrelatedform(D,E),alsosee(F,C),hypernym(A,C),similarto(D,B).
verbgroup(A,B):- instancehypernym(E,A),instancehypernym(D,B),membermeronym(F,A),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(C,D),alsosee(E,B),alsosee(F,C),membermeronym(F,A).
verbgroup(A,B):- similarto(F,D),memberofdomainusage(C,E),similarto(B,C),instancehypernym(F,A).
verbgroup(A,B):- derivationallyrelatedform(A,D),synsetdomaintopicof(A,D),memberofdomainregion(E,C),similarto(B,C).
verbgroup(A,B):- alsosee(D,F),membermeronym(F,A),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- memberofdomainusage(B,E),similarto(D,B),derivationallyrelatedform(C,A),similarto(B,C).
verbgroup(A,B):- alsosee(A,D),hypernym(B,F),similarto(B,C),haspart(C,E).
verbgroup(A,B):- membermeronym(A,D),membermeronym(C,E),alsosee(F,C),hypernym(F,B).
verbgroup(A,B):- instancehypernym(B,D),instancehypernym(C,A),alsosee(F,C),haspart(A,E).
verbgroup(A,B):- memberofdomainusage(D,B),instancehypernym(A,B),membermeronym(D,C),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(B,A),similarto(A,B),membermeronym(A,C).
verbgroup(A,B):- memberofdomainusage(A,E),hypernym(A,F),similarto(B,C),instancehypernym(D,C).
verbgroup(A,B):- similarto(D,A),memberofdomainregion(F,D),instancehypernym(A,E),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(D,E),memberofdomainregion(B,D),alsosee(A,C).
verbgroup(A,B):- instancehypernym(E,D),memberofdomainregion(E,C),similarto(B,C),similarto(A,C).
verbgroup(A,B):- alsosee(A,D),alsosee(E,C),hypernym(B,E).
verbgroup(A,B):- derivationallyrelatedform(D,B),instancehypernym(A,D),derivationallyrelatedform(A,D),similarto(B,C).
verbgroup(A,B):- similarto(B,C),membermeronym(A,D),similarto(A,E),synsetdomaintopicof(B,E).
verbgroup(A,B):- haspart(D,B),hypernym(C,A),membermeronym(B,C).
verbgroup(A,B):- alsosee(F,C),memberofdomainusage(B,E),synsetdomaintopicof(E,D),membermeronym(A,F).
verbgroup(A,B):- memberofdomainregion(F,E),derivationallyrelatedform(C,E),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- alsosee(C,A),similarto(B,D),alsosee(F,C),memberofdomainregion(F,E).
verbgroup(A,B):- memberofdomainregion(A,E),alsosee(F,C),alsosee(B,F),synsetdomaintopicof(D,B).
verbgroup(A,B):- synsetdomaintopicof(D,A),similarto(C,B),memberofdomainusage(E,A).
verbgroup(A,B):- similarto(A,D),hypernym(B,C),memberofdomainusage(E,A).
verbgroup(A,B):- memberofdomainregion(A,B),haspart(E,D),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- membermeronym(A,D),synsetdomaintopicof(D,A),instancehypernym(D,B),similarto(B,C).
