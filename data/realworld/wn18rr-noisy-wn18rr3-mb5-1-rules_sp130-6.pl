verbgroup(A,B):- memberofdomainusage(A,C),hypernym(D,B),alsosee(F,C),memberofdomainusage(A,E).
verbgroup(A,B):- alsosee(A,D),memberofdomainregion(F,B),alsosee(B,E),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(D,C),similarto(B,C),haspart(A,D),memberofdomainusage(C,B).
verbgroup(A,B):- hypernym(B,C),similarto(A,E),memberofdomainregion(A,D).
verbgroup(A,B):- haspart(E,D),memberofdomainregion(F,A),alsosee(F,C),derivationallyrelatedform(E,B).
verbgroup(A,B):- membermeronym(D,E),instancehypernym(D,A),similarto(B,C),instancehypernym(A,C).
verbgroup(A,B):- similarto(A,D),alsosee(B,E),memberofdomainusage(D,B),similarto(B,C).
verbgroup(A,B):- hypernym(C,E),alsosee(F,C),memberofdomainusage(D,B),instancehypernym(F,A).
verbgroup(A,B):- similarto(B,C),alsosee(B,C),synsetdomaintopicof(C,E),haspart(D,A).
verbgroup(A,B):- memberofdomainusage(B,C),derivationallyrelatedform(C,D),alsosee(F,C),instancehypernym(A,E).
verbgroup(A,B):- membermeronym(A,D),alsosee(F,C),membermeronym(C,B),hypernym(D,E).
verbgroup(A,B):- instancehypernym(E,A),derivationallyrelatedform(A,D),similarto(B,C),synsetdomaintopicof(B,E).
verbgroup(A,B):- haspart(B,F),memberofdomainusage(A,D),haspart(E,F),similarto(B,C).
verbgroup(A,B):- similarto(B,C),haspart(D,E),synsetdomaintopicof(A,E).
verbgroup(A,B):- hypernym(C,D),haspart(D,A),similarto(B,C),memberofdomainregion(E,B).
verbgroup(A,B):- memberofdomainusage(D,C),alsosee(F,A),alsosee(F,C),synsetdomaintopicof(E,B).
verbgroup(A,B):- haspart(C,D),memberofdomainusage(A,B),alsosee(B,D).
verbgroup(A,B):- similarto(B,E),memberofdomainusage(D,C),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- alsosee(F,C),haspart(A,D),instancehypernym(E,C),haspart(F,B).
verbgroup(A,B):- instancehypernym(E,A),similarto(D,E),alsosee(F,C),synsetdomaintopicof(F,B).
verbgroup(A,B):- derivationallyrelatedform(A,F),membermeronym(D,C),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- hypernym(B,A),memberofdomainusage(C,D),derivationallyrelatedform(A,D).
verbgroup(A,B):- haspart(E,D),instancehypernym(A,E),similarto(B,C),alsosee(D,A).
verbgroup(A,B):- derivationallyrelatedform(A,D),alsosee(F,C),memberofdomainregion(F,B),haspart(E,B).
verbgroup(A,B):- memberofdomainusage(E,B),membermeronym(A,E),derivationallyrelatedform(D,B),similarto(B,C).
verbgroup(A,B):- haspart(F,C),membermeronym(A,E),instancehypernym(D,F),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(D,B),memberofdomainregion(C,A).
verbgroup(A,B):- similarto(C,A),similarto(A,B),hypernym(D,C).
verbgroup(A,B):- synsetdomaintopicof(A,C),memberofdomainusage(C,D),membermeronym(B,A).
verbgroup(A,B):- membermeronym(B,E),memberofdomainusage(A,D),derivationallyrelatedform(C,A).
verbgroup(A,B):- similarto(D,B),alsosee(B,C),similarto(B,C),haspart(B,A).
verbgroup(A,B):- instancehypernym(B,D),derivationallyrelatedform(B,A),derivationallyrelatedform(D,B),similarto(B,C).
verbgroup(A,B):- hypernym(D,A),alsosee(D,B),derivationallyrelatedform(A,D),similarto(B,C).
verbgroup(A,B):- instancehypernym(E,A),derivationallyrelatedform(C,E),alsosee(F,C),haspart(D,B).
verbgroup(A,B):- synsetdomaintopicof(C,D),hypernym(D,E),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- synsetdomaintopicof(D,C),alsosee(D,F),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- membermeronym(C,E),hypernym(C,A),memberofdomainregion(B,D).
verbgroup(A,B):- alsosee(A,D),alsosee(B,C),similarto(B,C),similarto(C,D).
verbgroup(A,B):- memberofdomainregion(D,F),alsosee(F,C),memberofdomainregion(E,A),synsetdomaintopicof(D,B).
verbgroup(A,B):- derivationallyrelatedform(E,D),haspart(C,B),membermeronym(D,A).
verbgroup(A,B):- derivationallyrelatedform(D,C),similarto(B,C),instancehypernym(E,C),memberofdomainusage(A,E).
verbgroup(A,B):- synsetdomaintopicof(D,C),instancehypernym(B,D),instancehypernym(B,A).
verbgroup(A,B):- derivationallyrelatedform(D,B),hypernym(C,A),membermeronym(D,C).
verbgroup(A,B):- memberofdomainregion(D,B),alsosee(B,E),similarto(B,C),instancehypernym(C,A).
verbgroup(A,B):- instancehypernym(D,A),memberofdomainregion(E,C),alsosee(F,C),memberofdomainusage(B,F).
verbgroup(A,B):- similarto(A,D),alsosee(C,B),similarto(B,C),memberofdomainregion(E,B).
verbgroup(A,B):- alsosee(F,C),derivationallyrelatedform(D,F),derivationallyrelatedform(A,E),haspart(F,B).
verbgroup(A,B):- similarto(A,D),instancehypernym(B,A),similarto(B,C),hypernym(C,E).
verbgroup(A,B):- memberofdomainusage(B,C),memberofdomainusage(A,D),similarto(A,B).
verbgroup(A,B):- derivationallyrelatedform(E,B),synsetdomaintopicof(C,A),memberofdomainregion(D,E).
verbgroup(A,B):- memberofdomainregion(B,E),alsosee(D,B),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- instancehypernym(A,D),synsetdomaintopicof(D,A),similarto(A,E),similarto(B,C).
verbgroup(A,B):- similarto(C,E),synsetdomaintopicof(A,D),similarto(B,C),memberofdomainusage(E,A).
verbgroup(A,B):- similarto(A,D),similarto(D,B),synsetdomaintopicof(C,B).
verbgroup(A,B):- memberofdomainregion(D,B),similarto(A,D),memberofdomainregion(B,C),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(A,C),memberofdomainregion(D,C),alsosee(F,C),membermeronym(E,B).
verbgroup(A,B):- alsosee(E,B),alsosee(F,C),memberofdomainusage(F,A),memberofdomainusage(E,D).
verbgroup(A,B):- instancehypernym(D,A),derivationallyrelatedform(D,E),similarto(C,B).
verbgroup(A,B):- membermeronym(A,E),membermeronym(C,B),similarto(B,C),membermeronym(D,A).
verbgroup(A,B):- alsosee(D,E),similarto(A,B),instancehypernym(D,B),similarto(B,C).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(D,A),similarto(B,E),instancehypernym(A,F).
verbgroup(A,B):- alsosee(F,C),memberofdomainusage(F,A),synsetdomaintopicof(D,B),memberofdomainregion(C,E).
verbgroup(A,B):- hypernym(A,E),memberofdomainregion(D,A),synsetdomaintopicof(B,A),similarto(B,C).
verbgroup(A,B):- similarto(A,D),haspart(B,C),alsosee(F,C),memberofdomainregion(E,B).
verbgroup(A,B):- derivationallyrelatedform(D,A),derivationallyrelatedform(A,D),derivationallyrelatedform(A,E),similarto(B,C).
verbgroup(A,B):- hypernym(D,A),hypernym(D,B),similarto(C,E),similarto(B,C).
verbgroup(A,B):- haspart(F,A),alsosee(F,C),hypernym(B,E),memberofdomainregion(A,D).
verbgroup(A,B):- similarto(C,A),alsosee(D,B),alsosee(F,C),memberofdomainusage(E,B).
verbgroup(A,B):- synsetdomaintopicof(A,C),instancehypernym(A,D),alsosee(F,C),haspart(E,B).
verbgroup(A,B):- derivationallyrelatedform(E,A),memberofdomainregion(F,A),similarto(B,C),haspart(A,D).
verbgroup(A,B):- haspart(D,B),similarto(B,E),derivationallyrelatedform(A,E),similarto(B,C).
verbgroup(A,B):- instancehypernym(B,D),alsosee(F,C),memberofdomainregion(F,D),instancehypernym(A,E).
verbgroup(A,B):- hypernym(B,F),synsetdomaintopicof(D,A),derivationallyrelatedform(A,E),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(A,E),memberofdomainregion(C,E),similarto(B,C),instancehypernym(D,C).
verbgroup(A,B):- hypernym(A,E),memberofdomainusage(D,C),similarto(B,C),derivationallyrelatedform(A,C).
verbgroup(A,B):- derivationallyrelatedform(E,A),instancehypernym(C,A),alsosee(F,C),memberofdomainusage(B,D).
verbgroup(A,B):- similarto(C,E),alsosee(F,C),derivationallyrelatedform(A,D),synsetdomaintopicof(C,B).
verbgroup(A,B):- membermeronym(C,E),synsetdomaintopicof(E,A),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(E,D),similarto(C,B),synsetdomaintopicof(A,E).
verbgroup(A,B):- haspart(E,D),memberofdomainusage(C,B),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- membermeronym(A,D),haspart(A,E),memberofdomainregion(B,C),alsosee(F,C).
verbgroup(A,B):- memberofdomainregion(B,F),memberofdomainregion(E,A),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- hypernym(A,E),similarto(B,C),alsosee(A,F),memberofdomainregion(A,D).
verbgroup(A,B):- instancehypernym(B,D),derivationallyrelatedform(D,B),similarto(B,C),haspart(A,D).
verbgroup(A,B):- membermeronym(C,A),instancehypernym(D,E),alsosee(F,C),membermeronym(B,E).
verbgroup(A,B):- similarto(A,D),alsosee(F,C),synsetdomaintopicof(C,E),memberofdomainregion(E,B).
verbgroup(A,B):- hypernym(D,A),instancehypernym(A,D),haspart(E,A),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(B,C),haspart(D,B),membermeronym(C,A).
verbgroup(A,B):- instancehypernym(E,D),haspart(E,C),similarto(B,C),hypernym(A,D).
verbgroup(A,B):- synsetdomaintopicof(A,C),hypernym(B,C),synsetdomaintopicof(D,A).
verbgroup(A,B):- instancehypernym(B,D),haspart(C,D),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- synsetdomaintopicof(B,F),similarto(E,A),similarto(B,C),haspart(A,D).
verbgroup(A,B):- memberofdomainregion(D,B),similarto(A,D),synsetdomaintopicof(E,A),similarto(B,C).
verbgroup(A,B):- instancehypernym(D,A),instancehypernym(B,E),instancehypernym(A,E),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(E,B),memberofdomainregion(B,F),memberofdomainusage(A,D),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(E,B),haspart(D,A),similarto(B,C),haspart(E,B).
verbgroup(A,B):- memberofdomainregion(A,C),instancehypernym(A,B),similarto(A,C).
verbgroup(A,B):- haspart(A,E),similarto(A,D),hypernym(A,C),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(D,E),haspart(D,A),similarto(B,C),membermeronym(B,D).
verbgroup(A,B):- instancehypernym(B,D),membermeronym(A,E),hypernym(D,A),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(B,D),membermeronym(E,C),hypernym(E,A).
verbgroup(A,B):- derivationallyrelatedform(C,B),synsetdomaintopicof(A,D),synsetdomaintopicof(B,A),similarto(B,C).
verbgroup(A,B):- membermeronym(A,F),membermeronym(A,E),similarto(B,C),membermeronym(D,B).
verbgroup(A,B):- similarto(D,A),alsosee(B,C),haspart(D,E).
verbgroup(A,B):- membermeronym(C,A),memberofdomainregion(A,B),memberofdomainusage(C,B).
verbgroup(A,B):- membermeronym(D,A),similarto(D,B),similarto(B,C),instancehypernym(D,C).
verbgroup(A,B):- instancehypernym(A,F),hypernym(D,E),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- alsosee(F,B),alsosee(A,E),alsosee(D,C),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(E,C),instancehypernym(A,D),instancehypernym(C,B).
verbgroup(A,B):- derivationallyrelatedform(F,A),membermeronym(D,B),alsosee(F,C),membermeronym(E,D).
verbgroup(A,B):- hypernym(F,E),hypernym(A,F),similarto(B,C),membermeronym(D,B).
verbgroup(A,B):- derivationallyrelatedform(C,A),membermeronym(C,B),synsetdomaintopicof(B,A).
verbgroup(A,B):- membermeronym(A,C),alsosee(F,C),synsetdomaintopicof(D,E),synsetdomaintopicof(E,B).
verbgroup(A,B):- synsetdomaintopicof(A,C),synsetdomaintopicof(A,D),memberofdomainregion(E,D),similarto(B,C).
verbgroup(A,B):- membermeronym(C,B),memberofdomainusage(C,A),memberofdomainusage(D,C).
verbgroup(A,B):- synsetdomaintopicof(B,C),similarto(E,A),alsosee(C,D).
verbgroup(A,B):- alsosee(A,B),membermeronym(B,C),haspart(D,A),similarto(B,C).
verbgroup(A,B):- hypernym(E,B),similarto(B,C),haspart(A,D),memberofdomainusage(D,A).
verbgroup(A,B):- instancehypernym(A,D),derivationallyrelatedform(E,B),similarto(B,C),similarto(E,B).
verbgroup(A,B):- alsosee(F,B),alsosee(E,B),alsosee(F,C),membermeronym(D,A).
verbgroup(A,B):- membermeronym(A,D),membermeronym(D,B),similarto(B,C),alsosee(C,D).
verbgroup(A,B):- haspart(E,D),similarto(B,E),haspart(C,A).
verbgroup(A,B):- memberofdomainregion(E,C),derivationallyrelatedform(A,E),similarto(B,C),alsosee(E,D).
verbgroup(A,B):- memberofdomainregion(A,E),alsosee(F,C),derivationallyrelatedform(A,C),membermeronym(B,D).
verbgroup(A,B):- derivationallyrelatedform(C,A),haspart(D,A),similarto(B,C),memberofdomainusage(E,D).
verbgroup(A,B):- derivationallyrelatedform(B,A),derivationallyrelatedform(A,B),similarto(B,C),hypernym(A,D).
verbgroup(A,B):- memberofdomainusage(D,F),alsosee(A,E),memberofdomainregion(D,B),similarto(B,C).
verbgroup(A,B):- instancehypernym(E,D),instancehypernym(E,B),similarto(B,C),instancehypernym(F,A).
verbgroup(A,B):- haspart(C,B),memberofdomainregion(C,A),alsosee(D,A).
verbgroup(A,B):- similarto(F,A),alsosee(F,C),memberofdomainregion(D,B),memberofdomainusage(A,E).
