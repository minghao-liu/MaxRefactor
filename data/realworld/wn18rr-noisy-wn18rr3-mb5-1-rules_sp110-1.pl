verbgroup(A,B):- memberofdomainusage(D,F),haspart(B,F),alsosee(F,C),alsosee(E,A).
verbgroup(A,B):- alsosee(F,C),derivationallyrelatedform(F,B),alsosee(A,E),membermeronym(E,D).
verbgroup(A,B):- memberofdomainregion(E,F),derivationallyrelatedform(E,D),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- memberofdomainregion(A,B),instancehypernym(A,D),similarto(B,C),hypernym(B,E).
verbgroup(A,B):- similarto(D,B),similarto(C,B),instancehypernym(A,C).
verbgroup(A,B):- memberofdomainusage(D,E),similarto(B,C),haspart(A,D),memberofdomainregion(C,E).
verbgroup(A,B):- alsosee(A,D),instancehypernym(D,A),similarto(B,C),hypernym(C,B).
verbgroup(A,B):- similarto(B,C),memberofdomainregion(F,A),synsetdomaintopicof(E,F),synsetdomaintopicof(D,B).
verbgroup(A,B):- instancehypernym(D,A),similarto(E,B),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- derivationallyrelatedform(B,D),hypernym(A,D),similarto(A,C).
verbgroup(A,B):- alsosee(F,C),derivationallyrelatedform(F,E),membermeronym(B,F),alsosee(D,A).
verbgroup(A,B):- memberofdomainregion(F,A),alsosee(F,C),instancehypernym(E,B),hypernym(D,E).
verbgroup(A,B):- derivationallyrelatedform(C,A),instancehypernym(B,A),memberofdomainregion(D,A).
verbgroup(A,B):- derivationallyrelatedform(D,A),synsetdomaintopicof(C,D),membermeronym(B,C).
verbgroup(A,B):- similarto(D,B),hypernym(A,C),instancehypernym(C,B).
verbgroup(A,B):- derivationallyrelatedform(A,B),membermeronym(C,D),memberofdomainusage(C,B).
verbgroup(A,B):- instancehypernym(C,E),alsosee(B,C),memberofdomainusage(D,A).
verbgroup(A,B):- memberofdomainusage(A,D),alsosee(F,C),synsetdomaintopicof(D,E),instancehypernym(C,B).
verbgroup(A,B):- alsosee(A,D),similarto(E,C),similarto(B,C),alsosee(B,D).
verbgroup(A,B):- similarto(B,D),hypernym(A,C),membermeronym(E,A).
verbgroup(A,B):- similarto(B,D),alsosee(F,C),instancehypernym(B,E),memberofdomainusage(F,A).
verbgroup(A,B):- similarto(C,A),alsosee(B,E),similarto(D,E).
verbgroup(A,B):- instancehypernym(F,B),instancehypernym(A,D),alsosee(F,C),memberofdomainregion(E,C).
verbgroup(A,B):- synsetdomaintopicof(D,E),memberofdomainregion(D,A),synsetdomaintopicof(C,B).
verbgroup(A,B):- memberofdomainusage(E,B),synsetdomaintopicof(A,D),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- memberofdomainusage(B,C),alsosee(F,C),memberofdomainregion(F,D),derivationallyrelatedform(A,E).
verbgroup(A,B):- synsetdomaintopicof(A,F),derivationallyrelatedform(E,B),similarto(B,C),synsetdomaintopicof(D,F).
verbgroup(A,B):- alsosee(A,D),instancehypernym(D,E),similarto(B,C),instancehypernym(C,D).
verbgroup(A,B):- membermeronym(D,E),alsosee(B,E),alsosee(F,C),hypernym(A,C).
verbgroup(A,B):- alsosee(F,C),haspart(F,A),synsetdomaintopicof(B,D),membermeronym(E,C).
verbgroup(A,B):- membermeronym(D,A),haspart(D,A),synsetdomaintopicof(C,B).
verbgroup(A,B):- haspart(A,E),haspart(D,C),synsetdomaintopicof(C,B).
verbgroup(A,B):- synsetdomaintopicof(B,C),instancehypernym(D,E),alsosee(F,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- membermeronym(C,A),derivationallyrelatedform(D,B),derivationallyrelatedform(A,E).
verbgroup(A,B):- memberofdomainusage(F,B),alsosee(F,E),alsosee(F,C),haspart(D,A).
verbgroup(A,B):- alsosee(C,E),alsosee(A,E),similarto(B,D).
verbgroup(A,B):- derivationallyrelatedform(F,D),derivationallyrelatedform(E,D),membermeronym(A,E),similarto(B,C).
verbgroup(A,B):- hypernym(A,E),derivationallyrelatedform(E,F),hypernym(D,A),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(C,E),derivationallyrelatedform(A,C),membermeronym(B,D).
verbgroup(A,B):- memberofdomainregion(A,C),synsetdomaintopicof(D,C),derivationallyrelatedform(E,B).
verbgroup(A,B):- instancehypernym(C,D),derivationallyrelatedform(C,D),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- instancehypernym(B,D),synsetdomaintopicof(E,A),alsosee(A,C).
verbgroup(A,B):- alsosee(F,C),similarto(B,E),memberofdomainusage(D,C),memberofdomainregion(A,D).
verbgroup(A,B):- instancehypernym(C,A),memberofdomainregion(A,C),similarto(B,C),instancehypernym(A,C).
verbgroup(A,B):- haspart(D,B),instancehypernym(D,A),haspart(D,C),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(E,B),synsetdomaintopicof(D,B),similarto(A,C).
verbgroup(A,B):- alsosee(F,C),alsosee(A,E),derivationallyrelatedform(C,B),memberofdomainusage(B,D).
verbgroup(A,B):- instancehypernym(F,D),hypernym(A,E),haspart(D,B),similarto(B,C).
verbgroup(A,B):- similarto(A,C),alsosee(F,C),memberofdomainregion(F,D),haspart(E,B).
verbgroup(A,B):- alsosee(A,D),memberofdomainregion(A,B),hypernym(C,D),similarto(B,C).
verbgroup(A,B):- instancehypernym(E,A),memberofdomainusage(D,B),alsosee(F,C),memberofdomainusage(C,A).
verbgroup(A,B):- haspart(B,E),memberofdomainregion(E,C),haspart(A,D).
verbgroup(A,B):- derivationallyrelatedform(E,C),hypernym(C,D),similarto(A,E),similarto(B,C).
verbgroup(A,B):- membermeronym(C,A),hypernym(A,E),instancehypernym(D,B),similarto(B,C).
verbgroup(A,B):- haspart(D,B),membermeronym(B,E),derivationallyrelatedform(E,A),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(F,A),similarto(D,E),alsosee(F,C),derivationallyrelatedform(E,B).
verbgroup(A,B):- memberofdomainregion(A,C),hypernym(D,F),alsosee(F,C),instancehypernym(E,B).
verbgroup(A,B):- haspart(D,B),alsosee(F,C),instancehypernym(A,E),membermeronym(A,F).
verbgroup(A,B):- memberofdomainregion(D,E),memberofdomainusage(D,B),membermeronym(F,A),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(C,D),memberofdomainregion(B,C),hypernym(A,C).
verbgroup(A,B):- alsosee(F,E),memberofdomainusage(D,B),alsosee(F,C),alsosee(A,F).
verbgroup(A,B):- synsetdomaintopicof(E,C),alsosee(A,D),hypernym(C,A),similarto(B,C).
verbgroup(A,B):- similarto(D,A),alsosee(F,C),instancehypernym(D,F),haspart(E,B).
verbgroup(A,B):- alsosee(C,A),memberofdomainregion(B,D),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- derivationallyrelatedform(A,D),alsosee(F,C),instancehypernym(E,F),similarto(B,C).
verbgroup(A,B):- membermeronym(D,B),synsetdomaintopicof(E,D),similarto(B,C),membermeronym(D,A).
verbgroup(A,B):- similarto(A,F),alsosee(D,B),similarto(B,C),memberofdomainusage(E,D).
verbgroup(A,B):- haspart(A,B),memberofdomainregion(B,A),similarto(B,C),similarto(A,C).
verbgroup(A,B):- memberofdomainregion(D,B),alsosee(F,C),membermeronym(E,C),alsosee(A,F).
verbgroup(A,B):- memberofdomainusage(F,B),derivationallyrelatedform(A,D),similarto(B,C),haspart(C,E).
verbgroup(A,B):- synsetdomaintopicof(D,C),synsetdomaintopicof(C,A),alsosee(B,D).
verbgroup(A,B):- alsosee(F,C),memberofdomainregion(B,D),synsetdomaintopicof(C,E),membermeronym(A,F).
verbgroup(A,B):- hypernym(D,B),alsosee(F,C),memberofdomainregion(E,C),memberofdomainusage(E,A).
verbgroup(A,B):- derivationallyrelatedform(A,F),memberofdomainusage(D,B),alsosee(F,C),instancehypernym(B,E).
verbgroup(A,B):- haspart(E,D),instancehypernym(B,A),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- memberofdomainregion(D,B),memberofdomainusage(C,A),similarto(B,C),haspart(C,A).
verbgroup(A,B):- instancehypernym(D,C),alsosee(D,B),similarto(B,C),instancehypernym(C,A).
verbgroup(A,B):- memberofdomainusage(A,C),memberofdomainusage(D,B),memberofdomainregion(D,E),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(F,E),alsosee(F,C),instancehypernym(C,B),memberofdomainusage(D,A).
verbgroup(A,B):- alsosee(F,C),haspart(A,E),synsetdomaintopicof(D,A),derivationallyrelatedform(C,B).
verbgroup(A,B):- memberofdomainusage(D,E),memberofdomainusage(B,E),memberofdomainusage(A,D),similarto(B,C).
verbgroup(A,B):- haspart(B,C),alsosee(F,C),haspart(A,D),similarto(C,E).
verbgroup(A,B):- synsetdomaintopicof(E,A),alsosee(F,C),derivationallyrelatedform(C,B),membermeronym(C,D).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(A,D),synsetdomaintopicof(F,E),membermeronym(B,F).
verbgroup(A,B):- memberofdomainregion(C,B),synsetdomaintopicof(A,D),membermeronym(A,C),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(A,D),alsosee(F,C),membermeronym(C,B),memberofdomainregion(E,A).
verbgroup(A,B):- alsosee(D,E),synsetdomaintopicof(E,B),similarto(B,C),similarto(A,C).
verbgroup(A,B):- synsetdomaintopicof(D,C),synsetdomaintopicof(A,F),similarto(B,C),hypernym(D,E).
verbgroup(A,B):- hypernym(B,A),hypernym(D,A),alsosee(A,E),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(A,D),memberofdomainusage(E,F),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- instancehypernym(E,A),memberofdomainusage(D,A),hypernym(C,B).
verbgroup(A,B):- similarto(F,A),derivationallyrelatedform(C,E),alsosee(F,C),alsosee(B,D).
verbgroup(A,B):- similarto(A,D),memberofdomainusage(A,E),similarto(B,C),hypernym(F,C).
verbgroup(A,B):- alsosee(E,B),instancehypernym(A,D),alsosee(F,C),derivationallyrelatedform(D,C).
verbgroup(A,B):- alsosee(F,C),membermeronym(E,B),hypernym(F,D),synsetdomaintopicof(D,A).
verbgroup(A,B):- instancehypernym(A,F),similarto(D,E),instancehypernym(A,D),similarto(B,C).
verbgroup(A,B):- instancehypernym(A,D),similarto(E,C),derivationallyrelatedform(D,B),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(A,D),hypernym(C,D),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- membermeronym(A,D),memberofdomainregion(E,C),similarto(D,B),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(B,D),similarto(C,A),similarto(B,C).
verbgroup(A,B):- alsosee(C,A),haspart(A,D),synsetdomaintopicof(A,B).
verbgroup(A,B):- derivationallyrelatedform(B,D),derivationallyrelatedform(A,E),similarto(B,C),alsosee(C,D).
verbgroup(A,B):- similarto(A,F),hypernym(A,E),memberofdomainusage(B,D),similarto(B,C).
verbgroup(A,B):- alsosee(C,A),alsosee(F,C),memberofdomainusage(B,E),membermeronym(D,A).
verbgroup(A,B):- memberofdomainregion(D,C),hypernym(C,A),derivationallyrelatedform(A,E),similarto(B,C).
verbgroup(A,B):- similarto(E,F),similarto(A,D),alsosee(F,C),memberofdomainusage(C,B).
verbgroup(A,B):- instancehypernym(E,D),memberofdomainusage(D,C),similarto(B,C),instancehypernym(F,A).
verbgroup(A,B):- memberofdomainregion(A,E),membermeronym(E,C),similarto(B,C),membermeronym(E,D).
verbgroup(A,B):- hypernym(E,F),hypernym(D,B),similarto(B,C),memberofdomainusage(E,A).
verbgroup(A,B):- memberofdomainusage(F,B),similarto(A,D),alsosee(F,C),similarto(B,E).
