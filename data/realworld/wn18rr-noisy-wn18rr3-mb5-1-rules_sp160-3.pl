verbgroup(A,B):- instancehypernym(B,D),alsosee(A,C),haspart(B,A).
verbgroup(A,B):- derivationallyrelatedform(C,D),hypernym(A,E),alsosee(B,C).
verbgroup(A,B):- alsosee(D,E),haspart(A,E),memberofdomainregion(D,B),similarto(B,C).
verbgroup(A,B):- instancehypernym(D,A),memberofdomainusage(B,A),hypernym(D,C).
verbgroup(A,B):- derivationallyrelatedform(B,D),alsosee(F,C),derivationallyrelatedform(A,E),haspart(F,B).
verbgroup(A,B):- synsetdomaintopicof(C,F),similarto(A,D),hypernym(F,E),similarto(B,C).
verbgroup(A,B):- similarto(C,D),alsosee(F,C),memberofdomainusage(D,A),haspart(E,B).
verbgroup(A,B):- similarto(B,D),membermeronym(A,E),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- membermeronym(B,A),hypernym(E,B),similarto(B,C),hypernym(A,D).
verbgroup(A,B):- similarto(B,D),alsosee(F,C),alsosee(B,C),similarto(E,A).
verbgroup(A,B):- memberofdomainregion(E,C),alsosee(F,C),derivationallyrelatedform(C,B),membermeronym(D,A).
verbgroup(A,B):- alsosee(A,B),similarto(D,B),similarto(B,C),memberofdomainregion(E,A).
verbgroup(A,B):- instancehypernym(D,B),similarto(B,C),hypernym(A,B),instancehypernym(A,C).
verbgroup(A,B):- similarto(C,D),alsosee(F,C),hypernym(E,A),membermeronym(F,B).
verbgroup(A,B):- membermeronym(A,D),memberofdomainregion(D,A),memberofdomainusage(D,C),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(B,D),hypernym(C,A),instancehypernym(A,C).
verbgroup(A,B):- derivationallyrelatedform(D,A),derivationallyrelatedform(D,B),similarto(B,C),synsetdomaintopicof(B,E).
verbgroup(A,B):- memberofdomainusage(A,C),instancehypernym(E,B),synsetdomaintopicof(D,B).
verbgroup(A,B):- synsetdomaintopicof(D,C),alsosee(F,C),memberofdomainregion(E,A),haspart(B,D).
verbgroup(A,B):- synsetdomaintopicof(F,A),haspart(E,C),alsosee(F,C),membermeronym(B,D).
verbgroup(A,B):- alsosee(C,A),memberofdomainregion(E,D),haspart(D,A),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(B,D),haspart(A,C),hypernym(D,C).
verbgroup(A,B):- memberofdomainusage(A,C),hypernym(A,D),similarto(E,B).
verbgroup(A,B):- memberofdomainregion(A,B),synsetdomaintopicof(B,A),similarto(A,C).
verbgroup(A,B):- similarto(C,A),similarto(A,E),synsetdomaintopicof(D,B).
verbgroup(A,B):- membermeronym(E,B),alsosee(F,C),alsosee(A,C),hypernym(C,D).
verbgroup(A,B):- instancehypernym(F,D),memberofdomainregion(D,E),membermeronym(A,E),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(C,A),synsetdomaintopicof(B,D),memberofdomainregion(C,E).
verbgroup(A,B):- synsetdomaintopicof(A,F),alsosee(F,C),memberofdomainregion(C,D),similarto(E,B).
verbgroup(A,B):- haspart(A,B),membermeronym(A,E),similarto(B,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- alsosee(D,B),hypernym(F,D),derivationallyrelatedform(A,E),similarto(B,C).
verbgroup(A,B):- alsosee(F,C),membermeronym(B,E),synsetdomaintopicof(D,A),memberofdomainusage(C,E).
verbgroup(A,B):- membermeronym(A,E),alsosee(B,C),similarto(E,D).
verbgroup(A,B):- synsetdomaintopicof(E,A),synsetdomaintopicof(E,D),membermeronym(B,C).
verbgroup(A,B):- hypernym(B,C),hypernym(A,C),membermeronym(C,D).
verbgroup(A,B):- haspart(A,E),similarto(B,C),synsetdomaintopicof(D,B),derivationallyrelatedform(D,F).
verbgroup(A,B):- alsosee(A,D),similarto(B,C),hypernym(A,D),hypernym(C,E).
verbgroup(A,B):- instancehypernym(E,B),alsosee(F,C),alsosee(D,C),haspart(C,A).
verbgroup(A,B):- instancehypernym(B,E),synsetdomaintopicof(A,D),memberofdomainusage(A,B),similarto(B,C).
verbgroup(A,B):- hypernym(D,B),synsetdomaintopicof(E,A),hypernym(D,C).
verbgroup(A,B):- alsosee(A,D),similarto(A,C),alsosee(B,D).
verbgroup(A,B):- memberofdomainregion(E,D),haspart(A,F),similarto(B,C),haspart(A,D).
verbgroup(A,B):- membermeronym(D,E),similarto(B,E),synsetdomaintopicof(A,D),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(C,B),alsosee(F,C),memberofdomainusage(A,D),synsetdomaintopicof(A,E).
verbgroup(A,B):- synsetdomaintopicof(E,C),derivationallyrelatedform(E,A),similarto(B,C),hypernym(A,D).
verbgroup(A,B):- memberofdomainregion(D,B),membermeronym(C,F),similarto(E,A),similarto(B,C).
verbgroup(A,B):- instancehypernym(C,A),synsetdomaintopicof(B,D),memberofdomainregion(A,D).
verbgroup(A,B):- memberofdomainregion(D,B),memberofdomainusage(C,A),derivationallyrelatedform(B,C).
verbgroup(A,B):- alsosee(D,E),similarto(A,D),memberofdomainregion(E,C),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(B,A),derivationallyrelatedform(A,E),similarto(B,C),hypernym(A,D).
verbgroup(A,B):- alsosee(A,D),memberofdomainusage(F,C),derivationallyrelatedform(A,E),similarto(B,C).
verbgroup(A,B):- haspart(B,E),alsosee(F,C),membermeronym(D,F),memberofdomainregion(A,C).
verbgroup(A,B):- instancehypernym(A,D),memberofdomainusage(B,E),similarto(B,C),membermeronym(B,D).
verbgroup(A,B):- hypernym(C,A),instancehypernym(A,D),alsosee(F,C),instancehypernym(B,E).
verbgroup(A,B):- derivationallyrelatedform(C,D),alsosee(E,A),memberofdomainusage(C,B).
verbgroup(A,B):- haspart(D,F),hypernym(E,B),alsosee(F,C),membermeronym(A,F).
verbgroup(A,B):- hypernym(B,F),alsosee(F,C),derivationallyrelatedform(F,E),memberofdomainregion(A,D).
verbgroup(A,B):- derivationallyrelatedform(A,D),alsosee(F,C),similarto(B,E),derivationallyrelatedform(E,C).
verbgroup(A,B):- hypernym(D,A),derivationallyrelatedform(D,A),memberofdomainregion(A,E),similarto(B,C).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(D,A),instancehypernym(C,B),memberofdomainusage(E,D).
verbgroup(A,B):- similarto(D,A),haspart(B,A),synsetdomaintopicof(C,B).
verbgroup(A,B):- alsosee(D,B),synsetdomaintopicof(B,D),derivationallyrelatedform(C,A),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(A,D),membermeronym(C,D),synsetdomaintopicof(B,A),similarto(B,C).
verbgroup(A,B):- alsosee(C,A),alsosee(F,C),similarto(D,B),hypernym(E,F).
verbgroup(A,B):- derivationallyrelatedform(A,D),memberofdomainregion(D,A),similarto(B,C),alsosee(B,D).
verbgroup(A,B):- instancehypernym(E,F),similarto(B,C),alsosee(A,F),memberofdomainregion(A,D).
verbgroup(A,B):- hypernym(A,E),derivationallyrelatedform(D,E),haspart(F,C),similarto(B,C).
verbgroup(A,B):- alsosee(F,B),similarto(D,B),similarto(B,C),alsosee(E,A).
verbgroup(A,B):- derivationallyrelatedform(E,B),memberofdomainusage(C,A),haspart(B,D).
verbgroup(A,B):- synsetdomaintopicof(D,B),similarto(B,C),synsetdomaintopicof(A,B),memberofdomainregion(C,E).
verbgroup(A,B):- memberofdomainregion(A,D),similarto(B,C),hypernym(F,A),memberofdomainusage(E,D).
verbgroup(A,B):- hypernym(E,F),hypernym(A,E),alsosee(D,C),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(D,F),hypernym(A,E),similarto(B,C),alsosee(A,F).
verbgroup(A,B):- similarto(B,D),memberofdomainusage(C,A),memberofdomainregion(A,D).
verbgroup(A,B):- derivationallyrelatedform(D,A),haspart(B,F),alsosee(A,E),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(B,A),haspart(A,C),memberofdomainregion(D,A).
verbgroup(A,B):- haspart(A,E),memberofdomainusage(D,B),similarto(B,C),alsosee(D,A).
verbgroup(A,B):- memberofdomainregion(D,B),alsosee(E,F),alsosee(F,C),alsosee(F,A).
verbgroup(A,B):- synsetdomaintopicof(E,A),synsetdomaintopicof(C,A),membermeronym(D,B).
verbgroup(A,B):- alsosee(F,C),derivationallyrelatedform(B,E),synsetdomaintopicof(F,E),alsosee(D,A).
verbgroup(A,B):- hypernym(A,E),synsetdomaintopicof(E,D),similarto(B,C),membermeronym(D,A).
verbgroup(A,B):- alsosee(D,E),alsosee(F,C),instancehypernym(A,E),similarto(F,B).
verbgroup(A,B):- synsetdomaintopicof(F,D),similarto(A,E),similarto(B,C),haspart(C,F).
verbgroup(A,B):- haspart(A,B),membermeronym(D,C),haspart(A,D).
verbgroup(A,B):- membermeronym(B,A),similarto(B,C),hypernym(A,D),haspart(E,B).
verbgroup(A,B):- instancehypernym(A,D),memberofdomainregion(E,A),similarto(B,C),hypernym(D,E).
verbgroup(A,B):- membermeronym(D,B),memberofdomainregion(D,A),similarto(B,C),haspart(B,A).
verbgroup(A,B):- memberofdomainusage(C,D),alsosee(F,C),similarto(C,B),membermeronym(E,A).
verbgroup(A,B):- hypernym(D,B),alsosee(D,C),instancehypernym(A,E).
verbgroup(A,B):- instancehypernym(E,A),membermeronym(C,E),memberofdomainusage(B,D).
verbgroup(A,B):- alsosee(A,D),memberofdomainusage(B,E),memberofdomainusage(A,D),similarto(B,C).
verbgroup(A,B):- instancehypernym(D,A),memberofdomainusage(C,D),derivationallyrelatedform(B,A).
verbgroup(A,B):- instancehypernym(E,D),alsosee(F,C),membermeronym(B,C),hypernym(A,D).
verbgroup(A,B):- synsetdomaintopicof(E,A),haspart(B,D),similarto(D,C).
verbgroup(A,B):- similarto(D,A),alsosee(F,C),membermeronym(C,B),instancehypernym(E,C).
verbgroup(A,B):- memberofdomainregion(D,A),hypernym(C,B),synsetdomaintopicof(C,B).
verbgroup(A,B):- instancehypernym(A,F),hypernym(D,B),alsosee(F,C),memberofdomainregion(E,F).
verbgroup(A,B):- alsosee(F,C),alsosee(A,E),alsosee(A,F),memberofdomainusage(B,D).
verbgroup(A,B):- memberofdomainregion(D,B),instancehypernym(C,A),hypernym(A,C).
verbgroup(A,B):- synsetdomaintopicof(E,C),similarto(B,C),haspart(A,D),derivationallyrelatedform(F,D).
verbgroup(A,B):- hypernym(B,C),synsetdomaintopicof(B,A),similarto(B,C),similarto(A,C).
verbgroup(A,B):- haspart(D,B),synsetdomaintopicof(E,A),similarto(B,C),instancehypernym(A,D).
verbgroup(A,B):- membermeronym(D,B),similarto(B,C),haspart(D,E),memberofdomainusage(D,A).
verbgroup(A,B):- hypernym(B,D),hypernym(C,A),synsetdomaintopicof(B,A).
verbgroup(A,B):- alsosee(F,C),alsosee(C,B),similarto(E,A),haspart(A,D).
verbgroup(A,B):- memberofdomainusage(A,D),similarto(A,E),similarto(B,C),similarto(D,C).
verbgroup(A,B):- synsetdomaintopicof(A,C),derivationallyrelatedform(A,D),similarto(B,C),similarto(E,B).
verbgroup(A,B):- similarto(D,B),hypernym(E,A),similarto(B,C),similarto(B,F).
verbgroup(A,B):- instancehypernym(E,A),alsosee(F,C),haspart(D,B),haspart(F,E).
verbgroup(A,B):- instancehypernym(C,D),hypernym(B,E),memberofdomainregion(A,D).
verbgroup(A,B):- hypernym(D,A),alsosee(F,C),similarto(B,C),memberofdomainusage(E,A).
verbgroup(A,B):- hypernym(B,C),alsosee(F,C),derivationallyrelatedform(A,D),memberofdomainregion(E,D).
verbgroup(A,B):- memberofdomainregion(F,B),alsosee(F,C),memberofdomainusage(D,C),memberofdomainusage(E,A).
verbgroup(A,B):- instancehypernym(B,D),synsetdomaintopicof(C,A),membermeronym(A,C).
verbgroup(A,B):- derivationallyrelatedform(A,D),alsosee(F,C),synsetdomaintopicof(C,E),memberofdomainusage(C,B).
verbgroup(A,B):- alsosee(A,D),memberofdomainusage(B,C),memberofdomainusage(B,A),similarto(B,C).
verbgroup(A,B):- instancehypernym(C,E),similarto(B,C),alsosee(C,D),memberofdomainregion(A,D).
verbgroup(A,B):- similarto(A,D),alsosee(F,C),memberofdomainusage(E,C),instancehypernym(E,B).
verbgroup(A,B):- synsetdomaintopicof(F,A),synsetdomaintopicof(E,D),similarto(B,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- instancehypernym(D,E),alsosee(B,C),memberofdomainregion(D,A).
verbgroup(A,B):- derivationallyrelatedform(D,B),synsetdomaintopicof(D,A),alsosee(B,C),similarto(B,C).
verbgroup(A,B):- alsosee(E,B),memberofdomainregion(D,C),haspart(A,D).
verbgroup(A,B):- memberofdomainusage(F,A),alsosee(F,C),instancehypernym(E,B),alsosee(E,D).
verbgroup(A,B):- haspart(D,B),membermeronym(C,E),similarto(C,A),alsosee(F,C).
verbgroup(A,B):- membermeronym(A,C),instancehypernym(B,D),similarto(A,E),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(C,B),similarto(A,E),similarto(B,C),instancehypernym(D,C).
verbgroup(A,B):- memberofdomainregion(A,C),instancehypernym(D,B),memberofdomainusage(E,D).
verbgroup(A,B):- instancehypernym(A,D),membermeronym(C,D),similarto(B,C),similarto(E,B).
verbgroup(A,B):- memberofdomainregion(A,B),synsetdomaintopicof(A,C),instancehypernym(D,A).
verbgroup(A,B):- derivationallyrelatedform(B,D),similarto(B,C),alsosee(C,D),synsetdomaintopicof(A,E).
verbgroup(A,B):- alsosee(C,B),hypernym(A,C),instancehypernym(D,C).
verbgroup(A,B):- hypernym(D,B),derivationallyrelatedform(C,B),instancehypernym(A,C).
verbgroup(A,B):- synsetdomaintopicof(C,F),synsetdomaintopicof(A,D),hypernym(E,D),similarto(B,C).
verbgroup(A,B):- hypernym(B,D),alsosee(F,C),synsetdomaintopicof(C,E),similarto(A,E).
verbgroup(A,B):- haspart(D,B),memberofdomainusage(A,C),alsosee(F,C),derivationallyrelatedform(B,E).
verbgroup(A,B):- derivationallyrelatedform(D,B),derivationallyrelatedform(A,C),similarto(B,C),hypernym(E,C).
verbgroup(A,B):- synsetdomaintopicof(D,C),memberofdomainregion(B,A),membermeronym(D,A).
verbgroup(A,B):- derivationallyrelatedform(D,A),alsosee(F,C),synsetdomaintopicof(F,B),membermeronym(A,E).
verbgroup(A,B):- memberofdomainusage(F,B),alsosee(F,C),similarto(A,E),memberofdomainusage(E,D).
verbgroup(A,B):- similarto(B,C),memberofdomainregion(A,F),synsetdomaintopicof(C,E),synsetdomaintopicof(D,B).
verbgroup(A,B):- membermeronym(E,C),haspart(D,A),similarto(B,C),synsetdomaintopicof(F,C).
verbgroup(A,B):- membermeronym(C,B),derivationallyrelatedform(A,E),alsosee(B,D).
verbgroup(A,B):- instancehypernym(E,D),similarto(A,D),similarto(B,C),similarto(A,C).
verbgroup(A,B):- instancehypernym(B,D),alsosee(F,C),similarto(F,E),haspart(A,E).
verbgroup(A,B):- derivationallyrelatedform(C,A),alsosee(C,B),memberofdomainregion(B,D).
verbgroup(A,B):- memberofdomainregion(A,E),instancehypernym(D,B),membermeronym(C,D).
verbgroup(A,B):- alsosee(D,E),haspart(E,A),similarto(B,C),instancehypernym(C,F).
verbgroup(A,B):- derivationallyrelatedform(B,C),synsetdomaintopicof(D,E),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- memberofdomainusage(B,C),hypernym(D,A),alsosee(F,C),memberofdomainregion(F,E).
verbgroup(A,B):- hypernym(D,B),instancehypernym(A,B),memberofdomainusage(C,D).
verbgroup(A,B):- synsetdomaintopicof(E,C),similarto(A,D),similarto(B,C),memberofdomainregion(C,A).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(A,D),instancehypernym(E,B),haspart(F,E).
verbgroup(A,B):- instancehypernym(A,B),haspart(D,A),membermeronym(C,D).
verbgroup(A,B):- hypernym(B,A),similarto(D,B),similarto(B,C),alsosee(B,D).
verbgroup(A,B):- synsetdomaintopicof(E,C),membermeronym(A,E),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- memberofdomainregion(D,B),derivationallyrelatedform(B,A),similarto(B,C),hypernym(D,E).
verbgroup(A,B):- memberofdomainregion(B,E),similarto(D,A),memberofdomainregion(A,C).
verbgroup(A,B):- memberofdomainregion(A,C),derivationallyrelatedform(E,D),alsosee(B,E),alsosee(F,C).
verbgroup(A,B):- derivationallyrelatedform(F,B),alsosee(F,C),memberofdomainusage(D,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- similarto(C,B),alsosee(F,C),haspart(D,A),memberofdomainregion(C,E).
