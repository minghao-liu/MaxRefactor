verbgroup(A,B):- synsetdomaintopicof(D,C),instancehypernym(A,E),similarto(B,C),membermeronym(B,D).
verbgroup(A,B):- alsosee(B,A),haspart(A,C),memberofdomainregion(C,A).
verbgroup(A,B):- haspart(A,E),synsetdomaintopicof(A,D),similarto(B,C),alsosee(A,F).
verbgroup(A,B):- haspart(D,B),derivationallyrelatedform(D,B),synsetdomaintopicof(B,A),similarto(B,C).
verbgroup(A,B):- haspart(B,C),memberofdomainregion(B,D),derivationallyrelatedform(A,E),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(C,A),derivationallyrelatedform(C,B),haspart(B,A).
verbgroup(A,B):- membermeronym(D,B),similarto(E,A),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- similarto(A,D),instancehypernym(B,A),memberofdomainregion(C,D),similarto(B,C).
verbgroup(A,B):- hypernym(E,F),derivationallyrelatedform(A,D),similarto(B,C),alsosee(F,D).
verbgroup(A,B):- hypernym(D,A),memberofdomainusage(A,D),similarto(B,C),alsosee(E,D).
verbgroup(A,B):- derivationallyrelatedform(A,E),haspart(B,D),similarto(B,C),similarto(F,B).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(B,D),memberofdomainusage(C,A),membermeronym(A,E).
verbgroup(A,B):- derivationallyrelatedform(A,D),memberofdomainregion(B,D),similarto(B,C),memberofdomainregion(C,E).
verbgroup(A,B):- synsetdomaintopicof(E,A),memberofdomainregion(B,D),haspart(D,A),similarto(B,C).
verbgroup(A,B):- membermeronym(D,B),alsosee(A,E),derivationallyrelatedform(D,C).
verbgroup(A,B):- memberofdomainusage(D,B),alsosee(B,C),alsosee(A,C).
verbgroup(A,B):- haspart(A,E),instancehypernym(F,B),similarto(B,C),membermeronym(E,D).
verbgroup(A,B):- haspart(A,B),similarto(A,B),synsetdomaintopicof(C,B).
verbgroup(A,B):- haspart(C,B),memberofdomainregion(D,A),hypernym(D,C).
verbgroup(A,B):- synsetdomaintopicof(D,C),alsosee(F,C),alsosee(B,C),similarto(A,E).
verbgroup(A,B):- memberofdomainregion(B,E),derivationallyrelatedform(D,A),memberofdomainregion(C,A).
verbgroup(A,B):- derivationallyrelatedform(A,C),memberofdomainusage(A,B),similarto(B,C),similarto(A,C).
verbgroup(A,B):- haspart(A,E),memberofdomainregion(E,D),similarto(B,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- memberofdomainregion(A,D),alsosee(E,C),similarto(B,C),alsosee(B,D).
verbgroup(A,B):- memberofdomainregion(A,E),derivationallyrelatedform(D,B),similarto(B,C),synsetdomaintopicof(F,C).
verbgroup(A,B):- derivationallyrelatedform(D,A),haspart(C,A),alsosee(F,C),hypernym(B,E).
verbgroup(A,B):- haspart(D,F),haspart(D,A),similarto(B,C),hypernym(C,E).
verbgroup(A,B):- similarto(B,C),hypernym(A,F),haspart(A,D),memberofdomainregion(C,E).
verbgroup(A,B):- memberofdomainusage(A,F),alsosee(F,C),synsetdomaintopicof(D,E),memberofdomainusage(B,D).
verbgroup(A,B):- similarto(C,E),haspart(D,C),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- membermeronym(C,D),similarto(B,C),hypernym(A,B),memberofdomainusage(A,E).
verbgroup(A,B):- membermeronym(E,B),memberofdomainregion(D,C),alsosee(A,C).
verbgroup(A,B):- memberofdomainregion(D,B),instancehypernym(C,B),similarto(B,C),haspart(B,A).
verbgroup(A,B):- alsosee(A,D),alsosee(D,E),alsosee(F,A),similarto(B,C).
verbgroup(A,B):- alsosee(B,A),similarto(B,C),membermeronym(D,A).
verbgroup(A,B):- similarto(B,E),haspart(D,A),similarto(B,C),memberofdomainusage(E,C).
verbgroup(A,B):- haspart(D,B),memberofdomainusage(E,B),alsosee(F,C),instancehypernym(F,A).
verbgroup(A,B):- memberofdomainregion(C,A),haspart(A,B),similarto(B,A).
verbgroup(A,B):- haspart(F,A),alsosee(F,C),instancehypernym(D,B),synsetdomaintopicof(E,B).
verbgroup(A,B):- membermeronym(B,E),derivationallyrelatedform(C,A),haspart(A,D).
verbgroup(A,B):- synsetdomaintopicof(F,A),membermeronym(D,B),haspart(E,D),similarto(B,C).
verbgroup(A,B):- alsosee(F,C),haspart(B,F),hypernym(F,D),alsosee(A,E).
verbgroup(A,B):- membermeronym(C,A),membermeronym(E,C),similarto(B,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- derivationallyrelatedform(B,D),memberofdomainusage(E,B),alsosee(F,C),alsosee(A,F).
verbgroup(A,B):- instancehypernym(D,A),derivationallyrelatedform(A,D),similarto(B,C),derivationallyrelatedform(D,C).
verbgroup(A,B):- membermeronym(D,E),instancehypernym(A,D),synsetdomaintopicof(B,D),similarto(B,C).
verbgroup(A,B):- instancehypernym(F,C),instancehypernym(A,E),similarto(B,C),derivationallyrelatedform(D,C).
verbgroup(A,B):- memberofdomainusage(C,A),synsetdomaintopicof(B,D),similarto(E,A).
verbgroup(A,B):- synsetdomaintopicof(D,C),haspart(B,C),memberofdomainusage(D,A).
verbgroup(A,B):- hypernym(A,E),haspart(A,E),similarto(B,C),alsosee(E,D).
verbgroup(A,B):- instancehypernym(C,D),membermeronym(A,E),similarto(B,C),instancehypernym(F,D).
verbgroup(A,B):- instancehypernym(A,F),memberofdomainregion(D,B),similarto(B,C),memberofdomainusage(E,D).
verbgroup(A,B):- memberofdomainusage(E,B),synsetdomaintopicof(A,D),similarto(B,C),synsetdomaintopicof(F,C).
verbgroup(A,B):- hypernym(A,E),alsosee(B,E),similarto(B,C),hypernym(D,B).
verbgroup(A,B):- similarto(E,D),membermeronym(A,E),alsosee(A,C),similarto(B,C).
verbgroup(A,B):- alsosee(A,D),memberofdomainregion(A,C),similarto(B,C),derivationallyrelatedform(A,C).
verbgroup(A,B):- alsosee(F,C),instancehypernym(B,E),similarto(E,D),derivationallyrelatedform(F,A).
verbgroup(A,B):- alsosee(A,E),similarto(E,D),similarto(B,C),instancehypernym(F,A).
verbgroup(A,B):- synsetdomaintopicof(E,A),memberofdomainusage(F,C),similarto(B,C),hypernym(A,D).
verbgroup(A,B):- derivationallyrelatedform(A,F),derivationallyrelatedform(B,D),alsosee(F,C),haspart(E,F).
verbgroup(A,B):- synsetdomaintopicof(C,D),alsosee(F,C),memberofdomainregion(A,F),instancehypernym(E,B).
verbgroup(A,B):- memberofdomainregion(D,F),alsosee(F,C),haspart(C,B),memberofdomainregion(E,A).
verbgroup(A,B):- membermeronym(C,A),alsosee(D,B),memberofdomainregion(E,A).
verbgroup(A,B):- synsetdomaintopicof(E,D),synsetdomaintopicof(A,D),derivationallyrelatedform(D,F),similarto(B,C).
verbgroup(A,B):- similarto(C,A),membermeronym(B,C),memberofdomainusage(B,A).
verbgroup(A,B):- similarto(B,C),alsosee(B,A),hypernym(E,D),synsetdomaintopicof(D,B).
verbgroup(A,B):- haspart(C,D),similarto(D,B),memberofdomainregion(D,A),similarto(B,C).
verbgroup(A,B):- alsosee(D,E),instancehypernym(A,D),similarto(B,C),membermeronym(B,D).
verbgroup(A,B):- derivationallyrelatedform(C,D),similarto(D,A),alsosee(D,B).
verbgroup(A,B):- hypernym(E,B),alsosee(F,C),memberofdomainregion(A,F),memberofdomainregion(E,D).
verbgroup(A,B):- memberofdomainregion(D,B),alsosee(F,C),hypernym(E,A),derivationallyrelatedform(D,F).
verbgroup(A,B):- membermeronym(A,D),synsetdomaintopicof(B,D),derivationallyrelatedform(A,C).
verbgroup(A,B):- hypernym(E,B),similarto(B,C),alsosee(C,D),memberofdomainusage(A,E).
verbgroup(A,B):- alsosee(C,A),derivationallyrelatedform(E,B),alsosee(B,D).
verbgroup(A,B):- derivationallyrelatedform(C,B),hypernym(A,D),memberofdomainusage(A,E).
verbgroup(A,B):- memberofdomainregion(B,E),memberofdomainregion(C,B),alsosee(F,C),haspart(A,D).
verbgroup(A,B):- memberofdomainusage(E,C),haspart(A,D),similarto(E,B).
verbgroup(A,B):- memberofdomainregion(A,B),memberofdomainregion(A,D),similarto(B,C),membermeronym(D,A).
verbgroup(A,B):- membermeronym(C,B),synsetdomaintopicof(A,D),memberofdomainregion(A,D).
verbgroup(A,B):- membermeronym(D,B),synsetdomaintopicof(A,F),similarto(B,C),alsosee(E,D).
verbgroup(A,B):- similarto(D,E),alsosee(A,E),similarto(A,E),similarto(B,C).
verbgroup(A,B):- membermeronym(A,D),memberofdomainusage(E,B),alsosee(F,C),synsetdomaintopicof(E,F).
verbgroup(A,B):- similarto(E,C),hypernym(E,B),alsosee(F,C),hypernym(A,D).
verbgroup(A,B):- alsosee(A,D),instancehypernym(D,E),similarto(B,C),haspart(B,A).
verbgroup(A,B):- memberofdomainregion(E,A),alsosee(F,C),synsetdomaintopicof(F,B),hypernym(D,E).
verbgroup(A,B):- membermeronym(A,D),memberofdomainusage(E,B),synsetdomaintopicof(A,F),similarto(B,C).
verbgroup(A,B):- haspart(B,E),membermeronym(A,D),synsetdomaintopicof(C,E).
verbgroup(A,B):- instancehypernym(D,A),hypernym(E,D),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- alsosee(E,B),membermeronym(D,B),membermeronym(F,A),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(D,B),synsetdomaintopicof(C,A),memberofdomainusage(A,B),similarto(B,C).
verbgroup(A,B):- similarto(A,C),memberofdomainusage(B,D),similarto(B,C),haspart(B,A).
verbgroup(A,B):- hypernym(A,E),hypernym(C,A),similarto(B,C),instancehypernym(D,C).
verbgroup(A,B):- derivationallyrelatedform(C,D),instancehypernym(E,B),hypernym(A,F),similarto(B,C).
verbgroup(A,B):- membermeronym(D,B),instancehypernym(E,C),similarto(A,C).
verbgroup(A,B):- membermeronym(B,A),instancehypernym(A,D),hypernym(A,C),similarto(B,C).
verbgroup(A,B):- instancehypernym(C,A),derivationallyrelatedform(B,C),alsosee(D,A).
verbgroup(A,B):- membermeronym(A,F),instancehypernym(E,B),memberofdomainregion(D,A),similarto(B,C).
verbgroup(A,B):- haspart(D,B),similarto(B,C),hypernym(A,D),memberofdomainusage(E,A).
verbgroup(A,B):- similarto(F,A),derivationallyrelatedform(D,B),similarto(B,C),memberofdomainregion(C,E).
verbgroup(A,B):- hypernym(B,A),memberofdomainregion(C,D),similarto(A,E),similarto(B,C).
