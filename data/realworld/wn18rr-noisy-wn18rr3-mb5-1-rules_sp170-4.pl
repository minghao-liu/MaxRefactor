verbgroup(A,B):- memberofdomainregion(B,E),derivationallyrelatedform(A,D),alsosee(F,C),similarto(D,F).
verbgroup(A,B):- instancehypernym(C,D),membermeronym(F,E),similarto(A,E),similarto(B,C).
verbgroup(A,B):- hypernym(C,D),instancehypernym(C,B),haspart(A,D).
verbgroup(A,B):- memberofdomainusage(A,C),memberofdomainregion(D,A),similarto(B,C),instancehypernym(A,C).
verbgroup(A,B):- derivationallyrelatedform(E,D),alsosee(F,C),instancehypernym(C,B),memberofdomainusage(D,A).
verbgroup(A,B):- alsosee(D,B),similarto(E,C),hypernym(A,C),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(C,E),alsosee(F,C),similarto(D,B),alsosee(A,C).
verbgroup(A,B):- instancehypernym(C,A),memberofdomainregion(D,A),similarto(A,E),similarto(B,C).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(D,A),haspart(B,E),alsosee(D,C).
verbgroup(A,B):- alsosee(C,A),similarto(D,B),haspart(D,B),similarto(B,C).
verbgroup(A,B):- haspart(B,C),similarto(B,C),hypernym(A,D),haspart(E,B).
verbgroup(A,B):- memberofdomainusage(A,E),hypernym(F,B),similarto(B,C),alsosee(B,D).
verbgroup(A,B):- instancehypernym(D,A),haspart(B,C),instancehypernym(E,C).
verbgroup(A,B):- derivationallyrelatedform(E,D),synsetdomaintopicof(C,D),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- memberofdomainusage(E,B),memberofdomainregion(C,D),hypernym(A,D).
verbgroup(A,B):- similarto(B,D),membermeronym(D,B),derivationallyrelatedform(B,A),similarto(B,C).
verbgroup(A,B):- hypernym(A,C),similarto(B,C),instancehypernym(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- synsetdomaintopicof(A,C),hypernym(F,D),alsosee(F,C),haspart(E,B).
verbgroup(A,B):- alsosee(B,C),derivationallyrelatedform(A,E),similarto(B,C),hypernym(D,C).
verbgroup(A,B):- alsosee(B,A),instancehypernym(E,D),similarto(A,E),similarto(B,C).
verbgroup(A,B):- instancehypernym(E,A),synsetdomaintopicof(A,D),similarto(B,C),synsetdomaintopicof(A,B).
verbgroup(A,B):- hypernym(D,A),membermeronym(E,F),alsosee(F,C),similarto(C,B).
verbgroup(A,B):- memberofdomainusage(C,D),similarto(B,C),hypernym(A,D),instancehypernym(D,C).
verbgroup(A,B):- memberofdomainusage(D,B),similarto(B,C),synsetdomaintopicof(B,E),memberofdomainusage(A,E).
verbgroup(A,B):- hypernym(D,B),alsosee(F,C),synsetdomaintopicof(C,A),similarto(E,B).
verbgroup(A,B):- hypernym(D,A),derivationallyrelatedform(F,B),alsosee(F,C),derivationallyrelatedform(B,E).
verbgroup(A,B):- membermeronym(A,D),similarto(C,E),alsosee(F,C),synsetdomaintopicof(C,B).
verbgroup(A,B):- alsosee(F,C),haspart(A,C),synsetdomaintopicof(D,B),hypernym(C,E).
verbgroup(A,B):- alsosee(F,C),memberofdomainusage(A,D),synsetdomaintopicof(F,E),membermeronym(B,F).
verbgroup(A,B):- instancehypernym(D,E),synsetdomaintopicof(C,A),similarto(A,E),similarto(B,C).
verbgroup(A,B):- similarto(E,C),alsosee(D,F),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- alsosee(D,E),membermeronym(A,B),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- derivationallyrelatedform(B,D),memberofdomainregion(E,A),alsosee(D,C).
verbgroup(A,B):- derivationallyrelatedform(A,D),haspart(E,A),similarto(E,A),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(D,B),memberofdomainusage(A,C),instancehypernym(C,B),similarto(B,C).
verbgroup(A,B):- similarto(D,A),alsosee(F,C),memberofdomainregion(E,B),similarto(D,C).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(C,A),instancehypernym(E,B),membermeronym(D,C).
verbgroup(A,B):- haspart(C,D),hypernym(D,B),membermeronym(E,A).
verbgroup(A,B):- alsosee(B,A),memberofdomainusage(A,D),similarto(B,C),haspart(E,B).
verbgroup(A,B):- haspart(A,C),synsetdomaintopicof(D,B),memberofdomainusage(E,A).
verbgroup(A,B):- hypernym(A,C),haspart(C,A),alsosee(B,D).
verbgroup(A,B):- derivationallyrelatedform(C,A),similarto(D,B),memberofdomainusage(D,A).
verbgroup(A,B):- membermeronym(D,A),hypernym(E,A),similarto(B,C),instancehypernym(A,C).
verbgroup(A,B):- memberofdomainregion(C,B),instancehypernym(D,B),memberofdomainusage(D,A).
verbgroup(A,B):- hypernym(A,E),alsosee(F,C),similarto(C,B),memberofdomainusage(B,D).
verbgroup(A,B):- alsosee(F,C),similarto(F,D),memberofdomainusage(B,E),instancehypernym(A,C).
verbgroup(A,B):- synsetdomaintopicof(E,C),synsetdomaintopicof(A,F),derivationallyrelatedform(A,D),similarto(B,C).
verbgroup(A,B):- alsosee(A,D),hypernym(B,F),alsosee(F,C),memberofdomainregion(E,A).
verbgroup(A,B):- membermeronym(C,A),memberofdomainregion(D,A),derivationallyrelatedform(B,C).
verbgroup(A,B):- memberofdomainregion(C,B),membermeronym(D,B),derivationallyrelatedform(B,A).
verbgroup(A,B):- derivationallyrelatedform(B,D),similarto(A,D),memberofdomainregion(D,C),similarto(B,C).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(F,E),haspart(D,A),haspart(F,B).
verbgroup(A,B):- derivationallyrelatedform(F,D),instancehypernym(A,D),alsosee(F,C),hypernym(B,E).
verbgroup(A,B):- similarto(A,D),alsosee(F,C),instancehypernym(B,E),instancehypernym(F,A).
verbgroup(A,B):- membermeronym(D,E),similarto(B,E),instancehypernym(A,E),similarto(B,C).
verbgroup(A,B):- alsosee(F,B),similarto(A,E),similarto(B,C),instancehypernym(F,D).
verbgroup(A,B):- derivationallyrelatedform(B,D),alsosee(F,C),membermeronym(E,C),memberofdomainusage(F,A).
verbgroup(A,B):- memberofdomainregion(A,E),memberofdomainregion(D,A),haspart(D,A),similarto(B,C).
verbgroup(A,B):- instancehypernym(E,D),hypernym(B,C),similarto(B,C),haspart(A,D).
verbgroup(A,B):- memberofdomainusage(F,E),membermeronym(D,B),alsosee(F,C),instancehypernym(A,E).
verbgroup(A,B):- memberofdomainregion(F,C),instancehypernym(D,F),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- similarto(B,C),similarto(A,E),haspart(D,E),membermeronym(D,A).
verbgroup(A,B):- membermeronym(C,E),alsosee(F,C),haspart(D,A),similarto(B,F).
verbgroup(A,B):- derivationallyrelatedform(A,D),alsosee(F,C),instancehypernym(D,F),similarto(E,B).
verbgroup(A,B):- memberofdomainregion(D,C),synsetdomaintopicof(A,F),alsosee(F,C),hypernym(B,E).
verbgroup(A,B):- similarto(C,D),hypernym(D,B),memberofdomainusage(C,A).
verbgroup(A,B):- membermeronym(A,D),membermeronym(B,A),instancehypernym(D,C).
verbgroup(A,B):- memberofdomainregion(D,F),similarto(A,D),alsosee(B,E),alsosee(F,C).
verbgroup(A,B):- memberofdomainregion(B,E),alsosee(D,B),alsosee(F,C),haspart(C,A).
verbgroup(A,B):- alsosee(D,B),alsosee(F,C),synsetdomaintopicof(C,A),similarto(E,B).
verbgroup(A,B):- derivationallyrelatedform(E,A),membermeronym(D,B),alsosee(F,C),haspart(A,F).
verbgroup(A,B):- synsetdomaintopicof(B,C),memberofdomainusage(A,D),derivationallyrelatedform(A,E),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(B,D),haspart(C,D),synsetdomaintopicof(D,A).
verbgroup(A,B):- similarto(B,C),synsetdomaintopicof(F,D),synsetdomaintopicof(F,E),haspart(D,A).
verbgroup(A,B):- alsosee(F,C),membermeronym(A,E),hypernym(B,D),haspart(C,A).
verbgroup(A,B):- derivationallyrelatedform(E,A),alsosee(C,E),memberofdomainregion(D,B),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(D,B),membermeronym(A,E),similarto(B,C),similarto(D,C).
verbgroup(A,B):- instancehypernym(D,B),memberofdomainusage(D,C),membermeronym(D,A).
verbgroup(A,B):- memberofdomainusage(B,C),memberofdomainregion(E,A),alsosee(B,D).
verbgroup(A,B):- membermeronym(B,E),alsosee(F,C),instancehypernym(D,B),membermeronym(A,F).
verbgroup(A,B):- instancehypernym(E,A),haspart(B,F),synsetdomaintopicof(F,D),alsosee(F,C).
verbgroup(A,B):- alsosee(E,B),derivationallyrelatedform(A,E),similarto(B,C),similarto(D,C).
verbgroup(A,B):- membermeronym(A,C),alsosee(E,B),hypernym(D,A).
verbgroup(A,B):- instancehypernym(F,D),alsosee(F,C),similarto(B,E),memberofdomainregion(C,A).
verbgroup(A,B):- memberofdomainusage(E,A),alsosee(F,C),haspart(A,D),similarto(F,B).
verbgroup(A,B):- memberofdomainusage(D,B),memberofdomainusage(C,B),similarto(B,C),instancehypernym(A,C).
verbgroup(A,B):- alsosee(A,D),synsetdomaintopicof(D,E),derivationallyrelatedform(C,B).
verbgroup(A,B):- haspart(B,C),hypernym(C,A),derivationallyrelatedform(A,B).
verbgroup(A,B):- similarto(B,D),haspart(A,C),haspart(B,A).
verbgroup(A,B):- memberofdomainusage(A,C),synsetdomaintopicof(B,D),membermeronym(A,E).
verbgroup(A,B):- memberofdomainregion(E,C),hypernym(D,B),memberofdomainusage(F,A),similarto(B,C).
verbgroup(A,B):- haspart(D,B),memberofdomainusage(D,B),similarto(B,C),membermeronym(D,A).
verbgroup(A,B):- haspart(B,E),alsosee(F,C),similarto(F,A),similarto(D,F).
verbgroup(A,B):- memberofdomainregion(D,B),memberofdomainusage(F,E),haspart(A,F),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(B,F),alsosee(F,C),similarto(E,A),hypernym(A,D).
verbgroup(A,B):- memberofdomainregion(A,C),haspart(A,B),synsetdomaintopicof(A,D).
verbgroup(A,B):- haspart(B,C),similarto(C,B),haspart(A,D).
verbgroup(A,B):- memberofdomainusage(D,F),alsosee(A,E),similarto(B,C),membermeronym(E,D).
verbgroup(A,B):- memberofdomainregion(A,B),instancehypernym(C,B),hypernym(C,B).
verbgroup(A,B):- haspart(E,D),similarto(C,A),haspart(B,D).
verbgroup(A,B):- memberofdomainregion(F,C),instancehypernym(A,D),similarto(B,C),hypernym(B,E).
verbgroup(A,B):- alsosee(E,B),derivationallyrelatedform(C,E),alsosee(F,C),alsosee(D,A).
verbgroup(A,B):- instancehypernym(A,D),similarto(B,C),haspart(B,C),haspart(C,E).
verbgroup(A,B):- synsetdomaintopicof(E,C),alsosee(F,C),derivationallyrelatedform(D,B),hypernym(E,A).
verbgroup(A,B):- synsetdomaintopicof(C,A),synsetdomaintopicof(D,B),memberofdomainusage(D,A).
verbgroup(A,B):- membermeronym(E,A),haspart(C,A),alsosee(B,D).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(B,D),hypernym(C,A),memberofdomainusage(C,E).
verbgroup(A,B):- hypernym(C,D),membermeronym(A,E),similarto(B,C),memberofdomainregion(F,E).
verbgroup(A,B):- similarto(B,C),haspart(A,E),hypernym(B,D),alsosee(E,A).
verbgroup(A,B):- instancehypernym(B,D),haspart(C,B),hypernym(A,D).
verbgroup(A,B):- hypernym(E,B),alsosee(F,C),synsetdomaintopicof(A,D),membermeronym(F,D).
verbgroup(A,B):- membermeronym(A,D),haspart(C,B),similarto(E,A).
verbgroup(A,B):- haspart(F,A),derivationallyrelatedform(D,B),similarto(B,C),memberofdomainregion(E,A).
verbgroup(A,B):- memberofdomainregion(A,D),instancehypernym(C,A),similarto(B,C),similarto(A,C).
verbgroup(A,B):- similarto(B,D),alsosee(F,C),haspart(E,A),similarto(A,C).
verbgroup(A,B):- memberofdomainregion(B,C),instancehypernym(A,E),similarto(B,C),hypernym(D,E).
verbgroup(A,B):- memberofdomainregion(C,A),similarto(B,C),synsetdomaintopicof(D,B),instancehypernym(A,C).
verbgroup(A,B):- membermeronym(D,E),derivationallyrelatedform(C,A),derivationallyrelatedform(A,E),similarto(B,C).
verbgroup(A,B):- alsosee(F,C),alsosee(E,D),hypernym(F,B),synsetdomaintopicof(A,E).
verbgroup(A,B):- similarto(E,D),synsetdomaintopicof(C,E),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- alsosee(A,D),synsetdomaintopicof(E,B),similarto(B,C),instancehypernym(D,C).
verbgroup(A,B):- alsosee(F,C),derivationallyrelatedform(C,A),synsetdomaintopicof(E,D),memberofdomainregion(D,B).
verbgroup(A,B):- synsetdomaintopicof(A,C),similarto(B,A),hypernym(A,D).
verbgroup(A,B):- hypernym(D,B),memberofdomainusage(C,A),memberofdomainusage(D,A).
verbgroup(A,B):- alsosee(F,C),memberofdomainusage(A,D),similarto(B,C),haspart(C,E).
verbgroup(A,B):- memberofdomainusage(B,D),similarto(E,A),derivationallyrelatedform(D,C).
verbgroup(A,B):- similarto(E,A),hypernym(E,D),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- alsosee(A,D),memberofdomainregion(C,D),memberofdomainusage(D,C),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(D,A),derivationallyrelatedform(C,B),memberofdomainusage(E,A).
verbgroup(A,B):- memberofdomainregion(A,B),haspart(C,B),similarto(B,C).
verbgroup(A,B):- alsosee(F,C),instancehypernym(C,E),synsetdomaintopicof(B,D),instancehypernym(A,E).
verbgroup(A,B):- memberofdomainregion(C,B),membermeronym(E,A),membermeronym(D,A).
verbgroup(A,B):- derivationallyrelatedform(A,D),instancehypernym(C,B),memberofdomainusage(E,A).
verbgroup(A,B):- synsetdomaintopicof(B,C),hypernym(D,A),membermeronym(A,D),similarto(B,C).
verbgroup(A,B):- similarto(B,C),instancehypernym(A,E),synsetdomaintopicof(A,B),similarto(D,C).
verbgroup(A,B):- memberofdomainregion(D,B),haspart(A,B),derivationallyrelatedform(D,C).
verbgroup(A,B):- similarto(A,D),memberofdomainusage(E,D),similarto(B,C),memberofdomainusage(C,D).
verbgroup(A,B):- memberofdomainusage(A,C),membermeronym(D,B),alsosee(F,C),membermeronym(E,C).
verbgroup(A,B):- hypernym(A,E),similarto(B,D),similarto(B,C),alsosee(E,D).
verbgroup(A,B):- memberofdomainusage(F,B),alsosee(F,C),memberofdomainregion(D,A),membermeronym(E,D).
verbgroup(A,B):- derivationallyrelatedform(A,D),instancehypernym(B,E),similarto(B,C),instancehypernym(D,C).
verbgroup(A,B):- alsosee(F,C),haspart(E,F),memberofdomainregion(A,D),haspart(E,B).
verbgroup(A,B):- alsosee(D,B),derivationallyrelatedform(C,E),derivationallyrelatedform(C,A).
verbgroup(A,B):- alsosee(F,C),memberofdomainusage(D,A),similarto(B,C),haspart(E,B).
verbgroup(A,B):- memberofdomainregion(C,B),instancehypernym(C,A),derivationallyrelatedform(A,B).
verbgroup(A,B):- alsosee(F,C),similarto(F,D),memberofdomainregion(E,B),membermeronym(D,A).
verbgroup(A,B):- alsosee(A,D),derivationallyrelatedform(E,A),similarto(B,C),derivationallyrelatedform(A,C).
verbgroup(A,B):- alsosee(C,A),alsosee(D,B),synsetdomaintopicof(E,B).
verbgroup(A,B):- hypernym(B,A),synsetdomaintopicof(D,C),hypernym(B,C).
verbgroup(A,B):- haspart(D,B),hypernym(C,A),memberofdomainregion(D,A).
verbgroup(A,B):- alsosee(F,C),hypernym(D,B),alsosee(A,E),derivationallyrelatedform(C,D).
verbgroup(A,B):- membermeronym(E,F),hypernym(C,D),derivationallyrelatedform(A,E),similarto(B,C).
verbgroup(A,B):- instancehypernym(D,A),derivationallyrelatedform(A,D),hypernym(C,D),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(C,D),memberofdomainregion(B,E),haspart(A,C).
verbgroup(A,B):- alsosee(F,C),memberofdomainusage(D,A),membermeronym(D,C),similarto(E,B).
verbgroup(A,B):- alsosee(F,C),instancehypernym(E,B),derivationallyrelatedform(E,C),membermeronym(D,A).
verbgroup(A,B):- memberofdomainusage(D,B),synsetdomaintopicof(B,D),membermeronym(E,A),similarto(B,C).
verbgroup(A,B):- alsosee(D,E),similarto(E,C),similarto(B,C),instancehypernym(F,A).
verbgroup(A,B):- derivationallyrelatedform(E,A),haspart(D,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(F,E),memberofdomainregion(D,A),similarto(E,B).
verbgroup(A,B):- instancehypernym(C,A),membermeronym(C,B),memberofdomainusage(C,B).
verbgroup(A,B):- membermeronym(C,E),derivationallyrelatedform(A,D),haspart(C,B).
verbgroup(A,B):- similarto(C,B),instancehypernym(C,B),derivationallyrelatedform(A,C).
verbgroup(A,B):- synsetdomaintopicof(B,C),derivationallyrelatedform(A,D),similarto(B,C),instancehypernym(D,C).
verbgroup(A,B):- memberofdomainusage(C,D),instancehypernym(E,B),memberofdomainregion(C,A).
verbgroup(A,B):- memberofdomainusage(F,E),membermeronym(A,E),memberofdomainregion(E,D),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(C,B),derivationallyrelatedform(A,D),derivationallyrelatedform(A,B).
verbgroup(A,B):- instancehypernym(B,D),instancehypernym(B,A),similarto(B,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- similarto(E,C),instancehypernym(F,E),memberofdomainusage(A,D),similarto(B,C).
verbgroup(A,B):- haspart(E,D),alsosee(A,E),memberofdomainusage(B,F),similarto(B,C).
