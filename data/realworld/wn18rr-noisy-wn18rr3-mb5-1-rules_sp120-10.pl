verbgroup(A,B):- synsetdomaintopicof(A,C),alsosee(F,C),derivationallyrelatedform(D,B),hypernym(D,E).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(E,B),haspart(D,A),derivationallyrelatedform(A,C).
verbgroup(A,B):- similarto(D,A),derivationallyrelatedform(D,C),haspart(B,A).
verbgroup(A,B):- similarto(B,D),memberofdomainregion(E,C),memberofdomainregion(A,E),similarto(B,C).
verbgroup(A,B):- membermeronym(B,E),alsosee(F,C),memberofdomainusage(C,A),membermeronym(C,D).
verbgroup(A,B):- hypernym(A,E),hypernym(D,B),memberofdomainregion(D,E),similarto(B,C).
verbgroup(A,B):- similarto(E,F),hypernym(D,A),haspart(B,C),alsosee(F,C).
verbgroup(A,B):- similarto(B,C),alsosee(E,F),instancehypernym(D,F),hypernym(A,D).
verbgroup(A,B):- similarto(B,C),derivationallyrelatedform(A,D),hypernym(B,D),alsosee(C,D).
verbgroup(A,B):- memberofdomainregion(D,B),haspart(F,D),alsosee(A,E),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(E,C),alsosee(F,C),derivationallyrelatedform(D,B),haspart(A,C).
verbgroup(A,B):- memberofdomainregion(B,E),synsetdomaintopicof(D,E),haspart(A,C).
verbgroup(A,B):- instancehypernym(C,A),synsetdomaintopicof(D,B),memberofdomainregion(B,A).
verbgroup(A,B):- hypernym(A,D),memberofdomainusage(C,F),similarto(B,C),synsetdomaintopicof(E,F).
verbgroup(A,B):- memberofdomainusage(A,D),haspart(A,C),similarto(B,C),hypernym(D,C).
verbgroup(A,B):- similarto(A,D),synsetdomaintopicof(E,D),similarto(B,C),similarto(F,E).
verbgroup(A,B):- membermeronym(C,A),alsosee(F,C),derivationallyrelatedform(D,B),synsetdomaintopicof(E,B).
verbgroup(A,B):- hypernym(D,A),alsosee(A,E),membermeronym(F,E),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(E,A),similarto(A,D),derivationallyrelatedform(F,E),similarto(B,C).
verbgroup(A,B):- haspart(A,E),haspart(B,F),similarto(B,C),membermeronym(D,A).
verbgroup(A,B):- alsosee(A,D),alsosee(F,C),derivationallyrelatedform(F,D),similarto(E,B).
verbgroup(A,B):- alsosee(F,C),memberofdomainregion(A,F),memberofdomainusage(C,E),membermeronym(B,D).
verbgroup(A,B):- synsetdomaintopicof(E,C),membermeronym(D,B),alsosee(F,C),memberofdomainusage(C,A).
verbgroup(A,B):- memberofdomainusage(F,E),membermeronym(A,E),similarto(D,F),similarto(B,C).
verbgroup(A,B):- instancehypernym(E,A),similarto(A,C),similarto(B,C),hypernym(D,C).
verbgroup(A,B):- derivationallyrelatedform(A,D),membermeronym(C,D),similarto(B,C),alsosee(D,A).
verbgroup(A,B):- derivationallyrelatedform(E,A),membermeronym(E,F),alsosee(F,C),memberofdomainregion(D,B).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(D,C),alsosee(A,E),haspart(B,F).
verbgroup(A,B):- haspart(B,F),memberofdomainusage(C,D),alsosee(F,C),similarto(E,A).
verbgroup(A,B):- derivationallyrelatedform(A,E),similarto(B,C),synsetdomaintopicof(B,E),membermeronym(E,D).
verbgroup(A,B):- synsetdomaintopicof(A,C),alsosee(B,E),alsosee(F,C),memberofdomainusage(D,B).
verbgroup(A,B):- membermeronym(F,B),synsetdomaintopicof(F,D),membermeronym(A,E),similarto(B,C).
verbgroup(A,B):- similarto(A,D),haspart(C,B),alsosee(D,C).
verbgroup(A,B):- alsosee(B,E),alsosee(F,C),derivationallyrelatedform(A,C),synsetdomaintopicof(D,F).
verbgroup(A,B):- alsosee(C,A),alsosee(F,C),memberofdomainregion(C,D),haspart(E,B).
verbgroup(A,B):- hypernym(A,E),memberofdomainusage(D,C),haspart(D,A),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(F,D),alsosee(E,F),similarto(B,C),haspart(A,D).
verbgroup(A,B):- instancehypernym(D,A),synsetdomaintopicof(C,A),instancehypernym(C,B).
verbgroup(A,B):- alsosee(F,C),alsosee(A,E),synsetdomaintopicof(A,D),instancehypernym(C,B).
verbgroup(A,B):- synsetdomaintopicof(B,C),haspart(B,C),synsetdomaintopicof(A,B).
verbgroup(A,B):- alsosee(C,B),memberofdomainregion(B,D),similarto(A,C).
verbgroup(A,B):- instancehypernym(A,D),hypernym(F,B),similarto(B,C),haspart(D,E).
verbgroup(A,B):- instancehypernym(C,A),memberofdomainusage(B,E),memberofdomainusage(D,B),similarto(B,C).
verbgroup(A,B):- similarto(B,D),synsetdomaintopicof(B,D),similarto(B,C),haspart(A,D).
verbgroup(A,B):- membermeronym(C,B),memberofdomainusage(B,A),similarto(A,C).
verbgroup(A,B):- haspart(A,E),synsetdomaintopicof(C,D),similarto(B,C),derivationallyrelatedform(D,C).
verbgroup(A,B):- similarto(C,A),hypernym(D,B),memberofdomainusage(D,C).
verbgroup(A,B):- synsetdomaintopicof(D,C),haspart(E,A),similarto(B,C),haspart(A,E).
verbgroup(A,B):- haspart(C,D),membermeronym(B,C),memberofdomainregion(D,A).
verbgroup(A,B):- hypernym(E,B),memberofdomainusage(A,D),synsetdomaintopicof(C,A),similarto(B,C).
verbgroup(A,B):- instancehypernym(C,A),synsetdomaintopicof(A,D),haspart(B,A).
verbgroup(A,B):- alsosee(F,C),haspart(A,D),hypernym(B,E),similarto(D,C).
verbgroup(A,B):- hypernym(D,B),similarto(E,A),similarto(B,C),memberofdomainregion(E,B).
verbgroup(A,B):- instancehypernym(D,A),synsetdomaintopicof(C,E),similarto(B,C),similarto(A,C).
verbgroup(A,B):- alsosee(F,C),hypernym(A,F),hypernym(B,E),derivationallyrelatedform(D,C).
verbgroup(A,B):- derivationallyrelatedform(A,F),memberofdomainusage(F,E),instancehypernym(A,D),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(B,D),memberofdomainusage(E,C),membermeronym(A,C).
verbgroup(A,B):- synsetdomaintopicof(F,A),alsosee(F,C),haspart(F,E),synsetdomaintopicof(D,B).
verbgroup(A,B):- membermeronym(D,B),memberofdomainusage(F,C),similarto(A,E),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(C,A),hypernym(E,D),alsosee(B,D).
verbgroup(A,B):- haspart(F,A),alsosee(F,C),instancehypernym(D,B),haspart(E,F).
verbgroup(A,B):- instancehypernym(D,E),alsosee(F,C),instancehypernym(C,B),haspart(D,A).
verbgroup(A,B):- membermeronym(D,B),hypernym(C,A),derivationallyrelatedform(A,E).
verbgroup(A,B):- alsosee(F,C),alsosee(E,F),synsetdomaintopicof(B,D),synsetdomaintopicof(A,E).
verbgroup(A,B):- alsosee(F,C),memberofdomainregion(B,C),alsosee(A,E),memberofdomainregion(B,D).
verbgroup(A,B):- instancehypernym(C,D),membermeronym(A,B),synsetdomaintopicof(A,D),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(C,F),instancehypernym(A,D),memberofdomainregion(E,A),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(D,A),hypernym(B,D),similarto(B,C),instancehypernym(A,C).
verbgroup(A,B):- memberofdomainregion(A,C),hypernym(A,C),similarto(B,C),hypernym(A,D).
verbgroup(A,B):- instancehypernym(C,B),memberofdomainusage(A,B).
verbgroup(A,B):- haspart(A,B),instancehypernym(B,C),alsosee(B,D).
verbgroup(A,B):- memberofdomainusage(B,E),alsosee(F,C),derivationallyrelatedform(C,A),hypernym(C,D).
verbgroup(A,B):- hypernym(D,B),haspart(A,B),similarto(B,C),hypernym(D,E).
verbgroup(A,B):- instancehypernym(E,A),alsosee(F,C),haspart(C,B),memberofdomainusage(E,D).
verbgroup(A,B):- memberofdomainregion(F,C),memberofdomainusage(A,E),similarto(B,C),membermeronym(B,D).
verbgroup(A,B):- synsetdomaintopicof(E,B),memberofdomainregion(C,A),memberofdomainusage(E,D).
verbgroup(A,B):- alsosee(F,C),membermeronym(B,E),synsetdomaintopicof(B,D),memberofdomainusage(C,A).
verbgroup(A,B):- memberofdomainusage(B,C),memberofdomainusage(C,D),haspart(D,A),similarto(B,C).
verbgroup(A,B):- instancehypernym(D,A),derivationallyrelatedform(D,B),alsosee(D,C),similarto(B,C).
verbgroup(A,B):- haspart(C,A),synsetdomaintopicof(E,D),similarto(B,C),hypernym(A,D).
verbgroup(A,B):- membermeronym(A,D),alsosee(F,C),memberofdomainusage(C,E),derivationallyrelatedform(B,C).
verbgroup(A,B):- alsosee(F,B),derivationallyrelatedform(D,A),alsosee(F,C),alsosee(E,D).
verbgroup(A,B):- memberofdomainusage(C,D),haspart(A,B),memberofdomainusage(D,B),similarto(B,C).
verbgroup(A,B):- similarto(B,D),synsetdomaintopicof(E,A),similarto(B,C),similarto(A,C).
verbgroup(A,B):- membermeronym(A,D),instancehypernym(F,B),alsosee(F,C),memberofdomainusage(A,E).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(D,E),haspart(A,C),synsetdomaintopicof(B,E).
verbgroup(A,B):- alsosee(D,B),similarto(C,E),membermeronym(A,C).
verbgroup(A,B):- membermeronym(A,D),haspart(A,E),alsosee(D,B),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(E,B),alsosee(F,C),membermeronym(A,C),membermeronym(C,D).
verbgroup(A,B):- memberofdomainusage(B,C),instancehypernym(A,D),similarto(B,C),hypernym(D,E).
verbgroup(A,B):- membermeronym(D,B),alsosee(F,C),memberofdomainusage(E,D),instancehypernym(F,A).
verbgroup(A,B):- memberofdomainusage(E,B),derivationallyrelatedform(A,D),memberofdomainusage(D,F),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(A,E),similarto(F,D),similarto(B,C),instancehypernym(D,C).
verbgroup(A,B):- alsosee(A,D),haspart(E,D),similarto(B,C),derivationallyrelatedform(A,C).
verbgroup(A,B):- membermeronym(B,A),alsosee(A,B),memberofdomainusage(D,B),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(A,E),haspart(E,A),memberofdomainregion(B,D),similarto(B,C).
verbgroup(A,B):- instancehypernym(B,D),haspart(D,C),hypernym(D,A).
verbgroup(A,B):- memberofdomainregion(B,C),instancehypernym(B,A),memberofdomainusage(C,B).
verbgroup(A,B):- membermeronym(A,C),similarto(B,C),synsetdomaintopicof(D,B),memberofdomainregion(B,A).
verbgroup(A,B):- memberofdomainusage(B,E),alsosee(F,C),membermeronym(F,D),derivationallyrelatedform(A,C).
verbgroup(A,B):- instancehypernym(E,A),alsosee(C,E),alsosee(F,C),membermeronym(B,D).
verbgroup(A,B):- membermeronym(D,E),memberofdomainusage(A,C),membermeronym(D,B).
verbgroup(A,B):- instancehypernym(C,D),alsosee(F,C),membermeronym(E,A),haspart(F,B).
verbgroup(A,B):- membermeronym(A,D),alsosee(A,E),similarto(B,C),haspart(A,D).
verbgroup(A,B):- alsosee(D,E),hypernym(A,E),memberofdomainregion(A,F),similarto(B,C).
verbgroup(A,B):- hypernym(B,A),hypernym(B,C),memberofdomainregion(D,B),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(C,D),synsetdomaintopicof(B,A),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- derivationallyrelatedform(E,A),alsosee(F,C),instancehypernym(D,B),haspart(C,E).
verbgroup(A,B):- instancehypernym(C,D),derivationallyrelatedform(A,E),memberofdomainusage(A,B),similarto(B,C).
verbgroup(A,B):- instancehypernym(B,E),haspart(D,F),alsosee(F,C),synsetdomaintopicof(A,D).
verbgroup(A,B):- derivationallyrelatedform(A,F),synsetdomaintopicof(A,D),similarto(B,C),similarto(F,E).
verbgroup(A,B):- membermeronym(C,A),alsosee(D,B),alsosee(F,C),haspart(E,C).
verbgroup(A,B):- memberofdomainregion(A,E),alsosee(F,C),memberofdomainregion(F,B),hypernym(D,E).
verbgroup(A,B):- membermeronym(F,E),memberofdomainusage(B,E),synsetdomaintopicof(A,D),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(C,D),similarto(B,A),alsosee(B,C).
verbgroup(A,B):- derivationallyrelatedform(F,D),synsetdomaintopicof(C,D),similarto(A,E),similarto(B,C).
verbgroup(A,B):- instancehypernym(E,D),haspart(C,B),similarto(A,E),similarto(B,C).
verbgroup(A,B):- similarto(A,F),haspart(A,E),alsosee(F,C),instancehypernym(D,B).
verbgroup(A,B):- similarto(B,C),synsetdomaintopicof(D,B),memberofdomainusage(E,A).
verbgroup(A,B):- memberofdomainregion(B,E),memberofdomainusage(A,C),similarto(D,B),similarto(B,C).
