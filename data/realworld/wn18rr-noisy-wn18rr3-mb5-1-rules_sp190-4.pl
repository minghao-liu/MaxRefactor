verbgroup(A,B):- derivationallyrelatedform(A,E),memberofdomainusage(F,A),similarto(B,C),derivationallyrelatedform(D,C).
verbgroup(A,B):- similarto(A,D),haspart(B,C),similarto(B,C),hypernym(A,B).
verbgroup(A,B):- similarto(E,F),hypernym(D,B),membermeronym(A,E),similarto(B,C).
verbgroup(A,B):- membermeronym(A,D),memberofdomainregion(C,F),derivationallyrelatedform(E,A),similarto(B,C).
verbgroup(A,B):- similarto(A,C),hypernym(D,E),similarto(B,C),alsosee(D,A).
verbgroup(A,B):- derivationallyrelatedform(E,C),synsetdomaintopicof(A,D),similarto(B,C),derivationallyrelatedform(B,F).
verbgroup(A,B):- memberofdomainusage(A,C),derivationallyrelatedform(A,B),instancehypernym(D,C).
verbgroup(A,B):- alsosee(E,B),similarto(D,E),alsosee(F,C),hypernym(A,C).
verbgroup(A,B):- haspart(D,B),memberofdomainusage(D,F),instancehypernym(A,E),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(E,F),haspart(F,D),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- memberofdomainusage(D,E),membermeronym(A,E),derivationallyrelatedform(A,E),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(B,D),memberofdomainusage(A,D),instancehypernym(C,E),similarto(B,C).
verbgroup(A,B):- haspart(D,B),similarto(A,F),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- haspart(A,E),alsosee(F,C),similarto(D,B),haspart(F,B).
verbgroup(A,B):- instancehypernym(F,B),alsosee(E,F),alsosee(F,C),hypernym(D,A).
verbgroup(A,B):- alsosee(A,D),alsosee(D,B),memberofdomainregion(A,C).
verbgroup(A,B):- membermeronym(A,D),haspart(C,D),memberofdomainregion(D,B).
verbgroup(A,B):- hypernym(A,E),derivationallyrelatedform(A,D),instancehypernym(C,B).
verbgroup(A,B):- synsetdomaintopicof(E,C),membermeronym(A,D),derivationallyrelatedform(B,E).
verbgroup(A,B):- membermeronym(D,E),alsosee(B,C),membermeronym(E,A).
verbgroup(A,B):- alsosee(F,B),alsosee(F,C),hypernym(E,A),memberofdomainusage(F,D).
verbgroup(A,B):- haspart(E,D),memberofdomainusage(B,D),similarto(B,C),haspart(A,D).
verbgroup(A,B):- alsosee(A,D),membermeronym(C,D),similarto(B,C),memberofdomainusage(B,D).
verbgroup(A,B):- memberofdomainusage(D,B),derivationallyrelatedform(F,E),membermeronym(F,A),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(D,A),memberofdomainusage(C,A),memberofdomainregion(B,D).
verbgroup(A,B):- similarto(B,C),similarto(A,E),hypernym(F,A),alsosee(D,A).
verbgroup(A,B):- alsosee(A,E),similarto(D,B),memberofdomainregion(B,D),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(D,A),hypernym(E,D),memberofdomainusage(C,B).
verbgroup(A,B):- membermeronym(F,B),alsosee(F,C),similarto(D,F),synsetdomaintopicof(A,E).
verbgroup(A,B):- membermeronym(D,A),similarto(B,E),similarto(B,C),instancehypernym(F,A).
verbgroup(A,B):- memberofdomainregion(A,E),instancehypernym(D,B),instancehypernym(E,C).
verbgroup(A,B):- haspart(D,B),synsetdomaintopicof(C,E),similarto(B,C),similarto(A,C).
verbgroup(A,B):- memberofdomainregion(D,B),similarto(C,A),similarto(B,C),haspart(A,D).
verbgroup(A,B):- instancehypernym(B,A),synsetdomaintopicof(A,D),hypernym(C,B).
verbgroup(A,B):- memberofdomainusage(B,C),memberofdomainusage(A,D),membermeronym(A,C),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(C,D),derivationallyrelatedform(A,D),similarto(B,A).
verbgroup(A,B):- hypernym(E,B),alsosee(F,C),membermeronym(A,C),alsosee(E,D).
verbgroup(A,B):- membermeronym(D,A),derivationallyrelatedform(A,D),similarto(B,C),alsosee(E,D).
verbgroup(A,B):- hypernym(D,A),membermeronym(B,E),haspart(D,C).
verbgroup(A,B):- similarto(A,B),instancehypernym(D,B),instancehypernym(D,C).
verbgroup(A,B):- derivationallyrelatedform(A,D),memberofdomainregion(F,D),derivationallyrelatedform(A,E),similarto(B,C).
verbgroup(A,B):- alsosee(C,A),memberofdomainregion(B,E),synsetdomaintopicof(B,D).
verbgroup(A,B):- synsetdomaintopicof(B,C),hypernym(A,C),synsetdomaintopicof(B,A).
verbgroup(A,B):- memberofdomainregion(D,B),memberofdomainregion(A,E),alsosee(F,C),memberofdomainregion(C,B).
verbgroup(A,B):- synsetdomaintopicof(D,A),similarto(B,C),instancehypernym(F,E),instancehypernym(F,A).
verbgroup(A,B):- hypernym(C,F),instancehypernym(A,E),similarto(B,C),derivationallyrelatedform(D,C).
verbgroup(A,B):- haspart(A,E),hypernym(D,B),memberofdomainregion(E,C),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(F,A),derivationallyrelatedform(A,D),instancehypernym(A,E),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(D,B),memberofdomainregion(F,A),similarto(B,C),memberofdomainusage(E,D).
verbgroup(A,B):- hypernym(D,B),alsosee(F,C),similarto(E,A),memberofdomainregion(F,E).
verbgroup(A,B):- memberofdomainusage(C,D),hypernym(B,D),alsosee(D,A).
verbgroup(A,B):- memberofdomainusage(A,C),membermeronym(B,C),memberofdomainregion(B,A).
verbgroup(A,B):- instancehypernym(A,D),haspart(A,D),memberofdomainusage(C,B).
verbgroup(A,B):- hypernym(B,A),haspart(D,C),memberofdomainusage(A,D).
verbgroup(A,B):- memberofdomainregion(A,C),membermeronym(B,C),similarto(C,B).
verbgroup(A,B):- memberofdomainusage(D,B),alsosee(F,C),synsetdomaintopicof(D,E),haspart(C,A).
verbgroup(A,B):- instancehypernym(A,D),membermeronym(A,C),similarto(B,C),haspart(E,B).
verbgroup(A,B):- memberofdomainregion(A,C),hypernym(B,D),membermeronym(B,D).
verbgroup(A,B):- instancehypernym(D,B),similarto(B,C),alsosee(C,D),haspart(B,A).
verbgroup(A,B):- similarto(D,B),derivationallyrelatedform(A,B),similarto(B,C),instancehypernym(A,C).
verbgroup(A,B):- similarto(B,C),derivationallyrelatedform(C,B),alsosee(A,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- haspart(A,E),alsosee(F,C),derivationallyrelatedform(D,B),memberofdomainregion(C,D).
verbgroup(A,B):- derivationallyrelatedform(C,D),similarto(B,D),derivationallyrelatedform(B,A).
verbgroup(A,B):- memberofdomainregion(D,B),derivationallyrelatedform(C,B),similarto(B,C),alsosee(D,A).
verbgroup(A,B):- derivationallyrelatedform(E,C),membermeronym(D,B),similarto(B,C),memberofdomainusage(E,A).
verbgroup(A,B):- membermeronym(C,A),derivationallyrelatedform(D,B),memberofdomainusage(B,A),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(C,A),instancehypernym(E,C),membermeronym(B,D).
verbgroup(A,B):- synsetdomaintopicof(D,A),alsosee(E,D),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- alsosee(C,A),instancehypernym(A,E),alsosee(B,D).
verbgroup(A,B):- alsosee(B,C),memberofdomainregion(B,D),hypernym(A,D).
verbgroup(A,B):- hypernym(B,C),synsetdomaintopicof(D,A),haspart(B,D).
verbgroup(A,B):- instancehypernym(C,D),similarto(B,A),membermeronym(A,E),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(D,A),instancehypernym(A,E),similarto(B,C),derivationallyrelatedform(D,C).
verbgroup(A,B):- similarto(F,A),alsosee(F,C),derivationallyrelatedform(D,B),haspart(C,E).
verbgroup(A,B):- alsosee(C,A),synsetdomaintopicof(A,D),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- hypernym(A,E),similarto(D,C),similarto(B,C),haspart(B,A).
verbgroup(A,B):- derivationallyrelatedform(D,A),alsosee(F,C),instancehypernym(B,E),membermeronym(C,B).
verbgroup(A,B):- memberofdomainregion(F,A),alsosee(F,C),derivationallyrelatedform(B,E),memberofdomainusage(B,D).
verbgroup(A,B):- instancehypernym(E,A),haspart(D,F),alsosee(F,C),derivationallyrelatedform(B,D).
verbgroup(A,B):- synsetdomaintopicof(D,C),instancehypernym(A,D),derivationallyrelatedform(B,C),similarto(B,C).
verbgroup(A,B):- alsosee(F,B),hypernym(A,E),hypernym(D,F),alsosee(F,C).
verbgroup(A,B):- alsosee(A,D),synsetdomaintopicof(D,E),similarto(B,C),instancehypernym(E,A).
verbgroup(A,B):- hypernym(D,B),haspart(A,B),memberofdomainregion(E,A),similarto(B,C).
verbgroup(A,B):- alsosee(C,E),alsosee(F,C),memberofdomainregion(D,A),similarto(B,F).
verbgroup(A,B):- similarto(B,D),membermeronym(B,E),derivationallyrelatedform(A,D),similarto(B,C).
verbgroup(A,B):- hypernym(A,E),derivationallyrelatedform(D,E),similarto(B,C),synsetdomaintopicof(D,F).
verbgroup(A,B):- membermeronym(B,C),hypernym(A,D),alsosee(B,D).
verbgroup(A,B):- membermeronym(A,C),hypernym(A,D),alsosee(B,D).
verbgroup(A,B):- similarto(E,F),alsosee(C,F),haspart(D,A),similarto(B,C).
verbgroup(A,B):- membermeronym(C,A),hypernym(D,B),synsetdomaintopicof(C,B).
verbgroup(A,B):- similarto(C,D),derivationallyrelatedform(B,D),similarto(B,C),instancehypernym(A,C).
verbgroup(A,B):- memberofdomainregion(D,E),alsosee(A,E),similarto(B,C),similarto(E,B).
verbgroup(A,B):- instancehypernym(B,D),similarto(B,A),haspart(D,A),similarto(B,C).
verbgroup(A,B):- haspart(A,E),synsetdomaintopicof(B,A),similarto(B,C),alsosee(D,A).
verbgroup(A,B):- derivationallyrelatedform(D,B),synsetdomaintopicof(B,D),memberofdomainusage(C,A).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(B,D),derivationallyrelatedform(A,F),instancehypernym(E,C).
verbgroup(A,B):- similarto(A,F),alsosee(F,C),haspart(D,C),hypernym(B,E).
verbgroup(A,B):- similarto(A,E),similarto(C,E),hypernym(E,D),similarto(B,C).
verbgroup(A,B):- alsosee(F,C),hypernym(A,F),memberofdomainregion(B,D),hypernym(C,E).
verbgroup(A,B):- alsosee(D,E),haspart(E,C),instancehypernym(A,E),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(D,F),hypernym(A,E),haspart(B,C),alsosee(F,C).
verbgroup(A,B):- memberofdomainusage(C,E),similarto(D,B),similarto(B,C),hypernym(A,B).
verbgroup(A,B):- hypernym(A,E),memberofdomainusage(E,C),similarto(B,C),derivationallyrelatedform(D,C).
verbgroup(A,B):- haspart(D,F),memberofdomainregion(F,C),instancehypernym(A,E),similarto(B,C).
verbgroup(A,B):- hypernym(B,F),instancehypernym(D,B),similarto(B,C),memberofdomainusage(E,A).
verbgroup(A,B):- hypernym(D,A),similarto(B,E),instancehypernym(A,C).
verbgroup(A,B):- alsosee(F,C),haspart(E,A),memberofdomainregion(B,D),synsetdomaintopicof(E,F).
verbgroup(A,B):- hypernym(A,E),membermeronym(C,D),memberofdomainusage(E,C),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(C,E),similarto(A,D),similarto(B,C),hypernym(A,B).
verbgroup(A,B):- alsosee(C,A),derivationallyrelatedform(B,C),haspart(D,B),similarto(B,C).
verbgroup(A,B):- hypernym(C,D),haspart(C,B),synsetdomaintopicof(A,E).
verbgroup(A,B):- alsosee(A,D),memberofdomainusage(B,F),memberofdomainusage(E,C),similarto(B,C).
verbgroup(A,B):- hypernym(E,F),alsosee(F,C),synsetdomaintopicof(A,D),instancehypernym(E,B).
verbgroup(A,B):- haspart(C,F),instancehypernym(C,E),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- derivationallyrelatedform(D,E),similarto(D,B),similarto(B,C),derivationallyrelatedform(A,C).
verbgroup(A,B):- alsosee(A,D),memberofdomainusage(D,A),similarto(B,C),memberofdomainusage(C,B).
verbgroup(A,B):- alsosee(A,E),synsetdomaintopicof(E,D),similarto(B,C),membermeronym(D,A).
verbgroup(A,B):- hypernym(D,B),instancehypernym(A,E),derivationallyrelatedform(E,C).
verbgroup(A,B):- alsosee(C,B),instancehypernym(A,E),memberofdomainregion(D,E).
verbgroup(A,B):- memberofdomainregion(D,B),membermeronym(B,A),derivationallyrelatedform(C,E),similarto(B,C).
verbgroup(A,B):- similarto(A,D),hypernym(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- instancehypernym(B,D),haspart(E,C),similarto(C,A).
verbgroup(A,B):- memberofdomainusage(A,D),similarto(B,C),hypernym(A,D),synsetdomaintopicof(A,E).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(E,A),synsetdomaintopicof(B,D),alsosee(C,B).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(D,A),instancehypernym(B,E),synsetdomaintopicof(F,E).
verbgroup(A,B):- hypernym(B,C),instancehypernym(B,A),instancehypernym(D,C).
verbgroup(A,B):- similarto(C,A),synsetdomaintopicof(E,B),membermeronym(B,D).
verbgroup(A,B):- membermeronym(B,C),instancehypernym(A,E),hypernym(E,D).
verbgroup(A,B):- similarto(A,D),alsosee(F,C),haspart(C,E),synsetdomaintopicof(C,B).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(C,A),instancehypernym(D,F),similarto(B,E).
verbgroup(A,B):- instancehypernym(E,A),derivationallyrelatedform(B,C),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- membermeronym(F,E),memberofdomainregion(F,A),alsosee(F,C),hypernym(B,D).
verbgroup(A,B):- membermeronym(C,A),similarto(B,C),synsetdomaintopicof(D,B),memberofdomainusage(A,E).
verbgroup(A,B):- synsetdomaintopicof(E,C),instancehypernym(B,D),instancehypernym(A,E).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(F,B),synsetdomaintopicof(C,E),memberofdomainregion(D,A).
verbgroup(A,B):- haspart(A,B),synsetdomaintopicof(A,B),derivationallyrelatedform(A,C).
verbgroup(A,B):- memberofdomainusage(D,B),derivationallyrelatedform(D,B),memberofdomainregion(C,A).
verbgroup(A,B):- similarto(A,C),instancehypernym(C,E),similarto(B,C),instancehypernym(D,C).
verbgroup(A,B):- haspart(C,B),instancehypernym(C,B),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- derivationallyrelatedform(D,B),derivationallyrelatedform(A,C),similarto(A,C).
verbgroup(A,B):- haspart(B,E),hypernym(D,B),alsosee(F,C),derivationallyrelatedform(F,A).
verbgroup(A,B):- membermeronym(A,D),memberofdomainusage(B,E),synsetdomaintopicof(D,E),similarto(B,C).
verbgroup(A,B):- instancehypernym(A,D),hypernym(C,D),instancehypernym(C,B).
verbgroup(A,B):- hypernym(D,A),instancehypernym(E,B),memberofdomainregion(F,D),similarto(B,C).
verbgroup(A,B):- hypernym(B,A),memberofdomainregion(D,B),similarto(B,C),instancehypernym(D,C).
verbgroup(A,B):- derivationallyrelatedform(C,A),haspart(D,C),synsetdomaintopicof(B,A).
verbgroup(A,B):- alsosee(A,D),alsosee(B,E),membermeronym(C,A).
verbgroup(A,B):- similarto(B,D),derivationallyrelatedform(C,E),alsosee(F,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- instancehypernym(E,B),instancehypernym(E,F),similarto(B,C),alsosee(D,A).
verbgroup(A,B):- haspart(F,D),membermeronym(D,B),similarto(A,E),similarto(B,C).
verbgroup(A,B):- haspart(E,B),alsosee(F,C),memberofdomainusage(D,A),synsetdomaintopicof(C,B).
verbgroup(A,B):- haspart(B,C),alsosee(F,C),alsosee(E,C),haspart(A,D).
verbgroup(A,B):- alsosee(A,D),memberofdomainusage(D,B),memberofdomainusage(D,C).
verbgroup(A,B):- membermeronym(D,B),haspart(A,B),similarto(B,C),similarto(D,C).
verbgroup(A,B):- memberofdomainusage(F,B),alsosee(C,E),alsosee(F,C),memberofdomainusage(A,D).
verbgroup(A,B):- hypernym(D,B),hypernym(C,A),similarto(A,E).
verbgroup(A,B):- instancehypernym(B,D),similarto(E,C),alsosee(F,C),memberofdomainusage(F,A).
verbgroup(A,B):- derivationallyrelatedform(A,D),similarto(C,B),similarto(B,C),membermeronym(E,D).
verbgroup(A,B):- memberofdomainregion(D,B),alsosee(F,C),hypernym(C,D),memberofdomainusage(A,E).
verbgroup(A,B):- synsetdomaintopicof(A,C),hypernym(B,C),haspart(D,A),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(C,B),similarto(D,B),derivationallyrelatedform(A,B).
verbgroup(A,B):- instancehypernym(D,A),memberofdomainregion(D,E),memberofdomainregion(A,E),similarto(B,C).
verbgroup(A,B):- similarto(D,E),derivationallyrelatedform(E,F),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- membermeronym(B,C),memberofdomainusage(A,B),memberofdomainregion(B,A).
verbgroup(A,B):- instancehypernym(D,A),memberofdomainregion(D,C),similarto(C,B).
verbgroup(A,B):- alsosee(A,E),synsetdomaintopicof(D,E),hypernym(C,B).
verbgroup(A,B):- haspart(A,E),similarto(B,C),hypernym(F,A),membermeronym(D,A).
verbgroup(A,B):- derivationallyrelatedform(B,D),alsosee(C,B),derivationallyrelatedform(A,C).
verbgroup(A,B):- hypernym(D,A),similarto(B,C),synsetdomaintopicof(C,B).
verbgroup(A,B):- derivationallyrelatedform(B,A),synsetdomaintopicof(D,A),hypernym(D,C).
verbgroup(A,B):- alsosee(A,D),synsetdomaintopicof(F,D),similarto(B,C),hypernym(E,F).
verbgroup(A,B):- haspart(A,E),similarto(B,A),hypernym(B,D),similarto(B,C).
verbgroup(A,B):- alsosee(A,D),haspart(D,C),similarto(B,A).
verbgroup(A,B):- similarto(D,A),haspart(E,C),membermeronym(A,E),similarto(B,C).
verbgroup(A,B):- similarto(D,E),alsosee(F,C),memberofdomainregion(E,A),derivationallyrelatedform(B,F).
verbgroup(A,B):- hypernym(D,A),membermeronym(B,E),alsosee(F,C),haspart(C,D).
verbgroup(A,B):- alsosee(F,C),similarto(E,A),derivationallyrelatedform(C,B),membermeronym(B,D).
verbgroup(A,B):- memberofdomainregion(D,A),haspart(C,B),memberofdomainusage(C,E).
verbgroup(A,B):- synsetdomaintopicof(B,C),membermeronym(B,C),memberofdomainusage(A,B).
verbgroup(A,B):- hypernym(B,F),alsosee(F,C),derivationallyrelatedform(E,F),memberofdomainusage(D,A).
verbgroup(A,B):- instancehypernym(C,D),alsosee(F,C),haspart(B,E),memberofdomainregion(A,D).
verbgroup(A,B):- memberofdomainregion(D,A),derivationallyrelatedform(C,B),memberofdomainusage(C,B).
verbgroup(A,B):- alsosee(A,B),alsosee(D,C),memberofdomainregion(A,D).
verbgroup(A,B):- memberofdomainusage(B,C),memberofdomainusage(A,C),alsosee(D,C).
verbgroup(A,B):- instancehypernym(B,F),synsetdomaintopicof(B,D),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- haspart(B,C),synsetdomaintopicof(A,D),memberofdomainregion(E,C),similarto(B,C).
verbgroup(A,B):- membermeronym(D,C),similarto(A,E),similarto(B,C),hypernym(D,C).
verbgroup(A,B):- haspart(C,B),synsetdomaintopicof(D,E),alsosee(D,A).
verbgroup(A,B):- synsetdomaintopicof(B,C),membermeronym(C,B),haspart(A,C).
verbgroup(A,B):- membermeronym(C,A),hypernym(B,D),similarto(B,C),memberofdomainusage(A,E).
