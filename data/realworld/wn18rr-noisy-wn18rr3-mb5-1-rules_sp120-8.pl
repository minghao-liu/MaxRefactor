verbgroup(A,B):- alsosee(F,C),memberofdomainusage(A,D),membermeronym(A,E),synsetdomaintopicof(C,B).
verbgroup(A,B):- derivationallyrelatedform(A,F),derivationallyrelatedform(B,D),alsosee(F,C),synsetdomaintopicof(E,B).
verbgroup(A,B):- instancehypernym(F,C),alsosee(B,D),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- haspart(D,B),membermeronym(B,A),membermeronym(C,B).
verbgroup(A,B):- synsetdomaintopicof(A,C),similarto(A,D),similarto(E,C),similarto(B,C).
verbgroup(A,B):- similarto(A,D),hypernym(D,B),derivationallyrelatedform(A,C).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(B,F),alsosee(A,E),derivationallyrelatedform(D,F).
verbgroup(A,B):- similarto(D,B),similarto(A,B),hypernym(C,B).
verbgroup(A,B):- synsetdomaintopicof(C,F),haspart(A,E),instancehypernym(D,F),similarto(B,C).
verbgroup(A,B):- similarto(B,D),membermeronym(C,E),derivationallyrelatedform(A,C).
verbgroup(A,B):- memberofdomainregion(F,D),memberofdomainusage(B,E),memberofdomainusage(A,D),similarto(B,C).
verbgroup(A,B):- similarto(C,A),derivationallyrelatedform(C,B),memberofdomainusage(C,B).
verbgroup(A,B):- memberofdomainregion(A,E),membermeronym(D,B),alsosee(F,C),memberofdomainregion(B,C).
verbgroup(A,B):- hypernym(B,A),derivationallyrelatedform(C,B),memberofdomainusage(D,C).
verbgroup(A,B):- instancehypernym(B,A),instancehypernym(D,B),similarto(B,C),instancehypernym(E,C).
verbgroup(A,B):- synsetdomaintopicof(A,C),instancehypernym(D,C),synsetdomaintopicof(C,B).
verbgroup(A,B):- hypernym(D,A),membermeronym(B,E),derivationallyrelatedform(D,C).
verbgroup(A,B):- alsosee(F,C),hypernym(A,C),instancehypernym(A,E),haspart(B,D).
verbgroup(A,B):- similarto(C,E),synsetdomaintopicof(D,B),similarto(B,C),synsetdomaintopicof(A,B).
verbgroup(A,B):- membermeronym(A,D),similarto(F,C),instancehypernym(A,E),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(D,B),instancehypernym(D,B),derivationallyrelatedform(A,C).
verbgroup(A,B):- membermeronym(F,B),membermeronym(E,B),similarto(A,D),alsosee(F,C).
verbgroup(A,B):- memberofdomainusage(F,D),memberofdomainregion(C,E),similarto(B,C),instancehypernym(F,A).
verbgroup(A,B):- memberofdomainusage(D,C),instancehypernym(C,E),instancehypernym(A,E),similarto(B,C).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(F,E),hypernym(A,D),synsetdomaintopicof(C,B).
verbgroup(A,B):- haspart(B,E),synsetdomaintopicof(A,C),alsosee(F,C),synsetdomaintopicof(D,F).
verbgroup(A,B):- hypernym(E,C),alsosee(F,C),hypernym(A,F),alsosee(B,D).
verbgroup(A,B):- derivationallyrelatedform(D,A),alsosee(A,E),synsetdomaintopicof(B,D),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(C,D),alsosee(F,C),synsetdomaintopicof(E,B),hypernym(F,A).
verbgroup(A,B):- memberofdomainregion(B,E),instancehypernym(D,A),memberofdomainregion(C,D).
verbgroup(A,B):- alsosee(D,E),hypernym(A,C),haspart(B,E).
verbgroup(A,B):- hypernym(A,E),derivationallyrelatedform(E,C),similarto(B,C),haspart(D,E).
verbgroup(A,B):- alsosee(F,E),alsosee(F,C),haspart(A,F),alsosee(B,D).
verbgroup(A,B):- memberofdomainregion(A,E),haspart(C,F),membermeronym(D,F),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(B,E),synsetdomaintopicof(D,C),memberofdomainusage(D,A).
verbgroup(A,B):- similarto(D,A),alsosee(F,C),derivationallyrelatedform(B,E),membermeronym(D,C).
verbgroup(A,B):- haspart(D,B),alsosee(F,C),membermeronym(E,A),membermeronym(C,D).
verbgroup(A,B):- instancehypernym(E,D),memberofdomainregion(D,E),similarto(B,C),haspart(A,E).
verbgroup(A,B):- hypernym(A,E),membermeronym(D,B),membermeronym(A,C).
verbgroup(A,B):- membermeronym(D,B),similarto(D,B),instancehypernym(A,B),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(C,F),alsosee(A,D),membermeronym(E,C),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(D,B),synsetdomaintopicof(D,A),similarto(B,C),hypernym(D,E).
verbgroup(A,B):- hypernym(A,E),membermeronym(D,B),haspart(C,B).
verbgroup(A,B):- membermeronym(A,B),synsetdomaintopicof(D,A),derivationallyrelatedform(C,B).
verbgroup(A,B):- memberofdomainusage(E,B),instancehypernym(A,D),membermeronym(B,C).
verbgroup(A,B):- alsosee(A,D),similarto(A,D),similarto(B,C),memberofdomainregion(C,E).
verbgroup(A,B):- similarto(B,D),instancehypernym(D,B),synsetdomaintopicof(C,A),similarto(B,C).
verbgroup(A,B):- similarto(B,C),membermeronym(A,D),alsosee(D,C),hypernym(A,D).
verbgroup(A,B):- hypernym(B,A),instancehypernym(C,A),membermeronym(C,A).
verbgroup(A,B):- alsosee(F,C),alsosee(A,E),similarto(D,B),similarto(F,E).
verbgroup(A,B):- membermeronym(B,E),alsosee(F,C),synsetdomaintopicof(A,D),derivationallyrelatedform(D,F).
verbgroup(A,B):- memberofdomainusage(C,B),similarto(B,C),alsosee(C,D),synsetdomaintopicof(A,E).
verbgroup(A,B):- memberofdomainregion(B,C),haspart(A,D),synsetdomaintopicof(D,B).
verbgroup(A,B):- memberofdomainusage(F,E),memberofdomainusage(B,E),alsosee(F,C),hypernym(A,D).
verbgroup(A,B):- alsosee(F,E),alsosee(F,C),hypernym(B,D),memberofdomainregion(C,A).
verbgroup(A,B):- membermeronym(F,B),haspart(A,E),alsosee(F,C),membermeronym(D,A).
verbgroup(A,B):- membermeronym(A,D),instancehypernym(D,B),memberofdomainregion(C,D),similarto(B,C).
verbgroup(A,B):- membermeronym(C,A),alsosee(A,E),derivationallyrelatedform(C,D),similarto(B,C).
verbgroup(A,B):- similarto(D,A),derivationallyrelatedform(A,E),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- memberofdomainusage(D,B),similarto(C,B),memberofdomainregion(C,A).
verbgroup(A,B):- alsosee(A,D),memberofdomainregion(D,E),haspart(C,B),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(E,F),similarto(D,E),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- derivationallyrelatedform(F,A),alsosee(F,C),derivationallyrelatedform(F,E),membermeronym(B,D).
verbgroup(A,B):- haspart(E,A),similarto(C,B),membermeronym(B,D).
verbgroup(A,B):- synsetdomaintopicof(D,C),membermeronym(D,B),alsosee(F,C),haspart(A,E).
verbgroup(A,B):- instancehypernym(B,D),haspart(B,D),memberofdomainregion(C,A).
verbgroup(A,B):- instancehypernym(C,A),haspart(A,B),membermeronym(D,B).
verbgroup(A,B):- memberofdomainregion(D,B),synsetdomaintopicof(D,A),membermeronym(A,C).
verbgroup(A,B):- memberofdomainregion(F,C),hypernym(F,D),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- alsosee(D,B),haspart(C,B),memberofdomainusage(A,B).
verbgroup(A,B):- alsosee(A,D),memberofdomainregion(C,B),instancehypernym(C,A),similarto(B,C).
verbgroup(A,B):- instancehypernym(F,D),hypernym(D,B),similarto(E,A),similarto(B,C).
verbgroup(A,B):- alsosee(F,B),membermeronym(F,D),similarto(A,E),similarto(B,C).
verbgroup(A,B):- membermeronym(A,D),alsosee(C,B),derivationallyrelatedform(E,B).
verbgroup(A,B):- similarto(B,C),hypernym(A,E),haspart(B,D),synsetdomaintopicof(B,E).
verbgroup(A,B):- memberofdomainregion(D,B),synsetdomaintopicof(E,D),similarto(B,C),haspart(A,D).
verbgroup(A,B):- alsosee(F,C),membermeronym(F,D),synsetdomaintopicof(D,B),memberofdomainusage(E,A).
verbgroup(A,B):- alsosee(A,D),alsosee(F,C),synsetdomaintopicof(F,B),similarto(F,E).
verbgroup(A,B):- instancehypernym(A,F),alsosee(A,E),haspart(B,D),similarto(B,C).
verbgroup(A,B):- alsosee(F,C),haspart(A,F),memberofdomainregion(E,D),derivationallyrelatedform(B,E).
verbgroup(A,B):- instancehypernym(A,F),memberofdomainregion(A,E),memberofdomainusage(D,B),similarto(B,C).
verbgroup(A,B):- haspart(A,B),hypernym(A,C),derivationallyrelatedform(A,C).
verbgroup(A,B):- alsosee(F,C),memberofdomainregion(C,B),alsosee(A,E),derivationallyrelatedform(D,C).
verbgroup(A,B):- memberofdomainusage(C,F),similarto(B,C),hypernym(A,D),synsetdomaintopicof(A,E).
verbgroup(A,B):- derivationallyrelatedform(E,A),memberofdomainregion(D,B),similarto(B,C),alsosee(E,D).
verbgroup(A,B):- memberofdomainusage(E,F),memberofdomainregion(D,A),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- haspart(B,C),derivationallyrelatedform(D,B),membermeronym(A,B).
verbgroup(A,B):- instancehypernym(C,D),derivationallyrelatedform(F,E),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- similarto(B,C),instancehypernym(B,A),haspart(B,D),synsetdomaintopicof(D,B).
verbgroup(A,B):- derivationallyrelatedform(C,E),alsosee(F,C),similarto(C,B),haspart(A,D).
verbgroup(A,B):- haspart(D,B),alsosee(F,C),similarto(B,E),alsosee(A,F).
verbgroup(A,B):- membermeronym(D,A),memberofdomainusage(C,B),haspart(B,A).
verbgroup(A,B):- derivationallyrelatedform(C,A),instancehypernym(D,B),memberofdomainusage(A,B),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(B,F),instancehypernym(D,E),alsosee(F,C),instancehypernym(A,E).
verbgroup(A,B):- membermeronym(A,D),alsosee(C,E),hypernym(B,F),similarto(B,C).
verbgroup(A,B):- alsosee(C,E),alsosee(F,C),memberofdomainusage(A,C),memberofdomainregion(B,D).
verbgroup(A,B):- memberofdomainregion(C,F),membermeronym(A,E),similarto(D,B),similarto(B,C).
verbgroup(A,B):- alsosee(A,E),memberofdomainusage(E,C),similarto(B,C),hypernym(D,C).
verbgroup(A,B):- synsetdomaintopicof(B,C),similarto(A,B),similarto(C,D).
verbgroup(A,B):- memberofdomainusage(D,E),memberofdomainregion(B,F),alsosee(F,C),membermeronym(D,A).
verbgroup(A,B):- instancehypernym(F,E),membermeronym(A,E),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- derivationallyrelatedform(B,D),memberofdomainusage(D,B),alsosee(A,E),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(E,C),similarto(A,D),memberofdomainregion(B,C),similarto(B,C).
verbgroup(A,B):- membermeronym(E,B),instancehypernym(D,B),membermeronym(F,A),similarto(B,C).
verbgroup(A,B):- similarto(A,E),derivationallyrelatedform(C,F),alsosee(D,C),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(C,A),memberofdomainregion(A,D),memberofdomainregion(E,B).
verbgroup(A,B):- derivationallyrelatedform(A,D),alsosee(F,C),membermeronym(C,B),memberofdomainregion(E,C).
verbgroup(A,B):- membermeronym(C,A),derivationallyrelatedform(D,A),hypernym(B,C).
verbgroup(A,B):- synsetdomaintopicof(A,C),derivationallyrelatedform(E,D),similarto(E,B).
verbgroup(A,B):- haspart(E,D),similarto(B,A),instancehypernym(A,E),similarto(B,C).
verbgroup(A,B):- instancehypernym(B,D),alsosee(F,C),instancehypernym(F,E),memberofdomainusage(A,E).
verbgroup(A,B):- hypernym(D,B),instancehypernym(D,E),memberofdomainregion(F,A),similarto(B,C).
verbgroup(A,B):- membermeronym(A,D),hypernym(A,E),similarto(B,C),hypernym(A,D).
verbgroup(A,B):- hypernym(A,B),alsosee(C,D),derivationallyrelatedform(A,C).
verbgroup(A,B):- synsetdomaintopicof(E,C),instancehypernym(B,D),alsosee(F,C),memberofdomainregion(A,F).
verbgroup(A,B):- alsosee(F,C),similarto(C,A),synsetdomaintopicof(D,A),instancehypernym(B,E).
verbgroup(A,B):- derivationallyrelatedform(E,D),hypernym(F,A),similarto(B,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- haspart(F,D),alsosee(F,C),hypernym(A,F),hypernym(B,E).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(D,E),alsosee(A,C),membermeronym(B,D).
verbgroup(A,B):- alsosee(B,C),similarto(B,C),haspart(A,D),alsosee(D,A).
