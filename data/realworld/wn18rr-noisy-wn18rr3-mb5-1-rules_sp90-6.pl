verbgroup(A,B):- similarto(B,C),instancehypernym(F,C),hypernym(A,D),hypernym(E,C).
verbgroup(A,B):- memberofdomainregion(D,B),alsosee(E,A),memberofdomainusage(C,B).
verbgroup(A,B):- instancehypernym(C,A),similarto(B,E),synsetdomaintopicof(A,D).
verbgroup(A,B):- haspart(B,F),memberofdomainusage(E,F),alsosee(F,C),derivationallyrelatedform(A,D).
verbgroup(A,B):- alsosee(F,C),instancehypernym(C,B),hypernym(A,D),membermeronym(E,D).
verbgroup(A,B):- derivationallyrelatedform(C,D),alsosee(B,D),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- similarto(A,D),memberofdomainusage(B,D),haspart(B,D),similarto(B,C).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(B,D),instancehypernym(E,A),derivationallyrelatedform(A,C).
verbgroup(A,B):- instancehypernym(E,A),membermeronym(A,C),haspart(D,A),similarto(B,C).
verbgroup(A,B):- hypernym(E,B),membermeronym(A,E),similarto(B,C),membermeronym(B,D).
verbgroup(A,B):- alsosee(F,C),memberofdomainusage(A,D),instancehypernym(C,B),hypernym(E,C).
verbgroup(A,B):- memberofdomainregion(B,A),haspart(B,D),similarto(B,C),similarto(A,C).
verbgroup(A,B):- membermeronym(C,E),memberofdomainregion(C,F),similarto(B,C),hypernym(A,D).
verbgroup(A,B):- instancehypernym(E,A),alsosee(F,C),synsetdomaintopicof(A,D),similarto(F,B).
verbgroup(A,B):- haspart(C,F),memberofdomainusage(A,D),synsetdomaintopicof(D,E),similarto(B,C).
verbgroup(A,B):- similarto(B,A),haspart(C,B),similarto(C,B).
verbgroup(A,B):- similarto(A,D),alsosee(F,C),derivationallyrelatedform(B,E),memberofdomainregion(C,E).
verbgroup(A,B):- synsetdomaintopicof(F,D),haspart(D,A),similarto(B,C),haspart(E,C).
verbgroup(A,B):- memberofdomainusage(B,C),instancehypernym(D,A),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- haspart(A,E),haspart(C,F),similarto(B,C),hypernym(D,C).
verbgroup(A,B):- membermeronym(B,A),memberofdomainregion(D,C),memberofdomainregion(C,B).
verbgroup(A,B):- instancehypernym(A,F),alsosee(F,C),instancehypernym(D,B),instancehypernym(F,E).
verbgroup(A,B):- derivationallyrelatedform(F,E),alsosee(F,C),similarto(D,B),hypernym(F,A).
verbgroup(A,B):- memberofdomainusage(C,A),membermeronym(A,E),similarto(D,B),similarto(B,C).
verbgroup(A,B):- alsosee(F,C),hypernym(A,C),hypernym(A,D),haspart(E,B).
verbgroup(A,B):- memberofdomainregion(C,A),membermeronym(E,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- derivationallyrelatedform(C,D),memberofdomainregion(B,C),similarto(A,E),similarto(B,C).
verbgroup(A,B):- hypernym(C,D),instancehypernym(B,E),alsosee(A,C).
verbgroup(A,B):- membermeronym(A,D),similarto(A,B),synsetdomaintopicof(C,B).
verbgroup(A,B):- memberofdomainregion(D,F),memberofdomainusage(D,C),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- instancehypernym(E,A),memberofdomainusage(D,E),alsosee(F,C),instancehypernym(B,F).
verbgroup(A,B):- membermeronym(B,A),derivationallyrelatedform(D,B),similarto(B,C),alsosee(E,A).
verbgroup(A,B):- hypernym(D,B),alsosee(F,C),hypernym(C,A),memberofdomainusage(B,E).
verbgroup(A,B):- derivationallyrelatedform(B,C),hypernym(A,C),similarto(B,C),hypernym(A,D).
verbgroup(A,B):- haspart(A,B),membermeronym(B,C),memberofdomainusage(C,B).
verbgroup(A,B):- synsetdomaintopicof(A,C),alsosee(B,E),membermeronym(D,B).
verbgroup(A,B):- haspart(B,F),alsosee(F,C),haspart(E,D),memberofdomainusage(A,E).
verbgroup(A,B):- similarto(D,E),hypernym(B,C),alsosee(F,C),memberofdomainusage(A,D).
verbgroup(A,B):- hypernym(C,A),synsetdomaintopicof(A,D),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- derivationallyrelatedform(B,C),synsetdomaintopicof(E,B),haspart(A,D).
verbgroup(A,B):- hypernym(A,C),membermeronym(D,C),memberofdomainusage(B,E).
verbgroup(A,B):- similarto(D,A),alsosee(F,C),memberofdomainusage(F,E),similarto(B,F).
verbgroup(A,B):- alsosee(F,C),alsosee(D,F),derivationallyrelatedform(E,A),synsetdomaintopicof(C,B).
verbgroup(A,B):- instancehypernym(C,D),membermeronym(A,E),membermeronym(A,D),similarto(B,C).
verbgroup(A,B):- hypernym(D,B),memberofdomainusage(D,A),similarto(B,C),similarto(A,C).
verbgroup(A,B):- alsosee(E,C),instancehypernym(B,A),synsetdomaintopicof(A,D),similarto(B,C).
verbgroup(A,B):- alsosee(F,C),hypernym(F,B),instancehypernym(D,F),synsetdomaintopicof(A,E).
verbgroup(A,B):- memberofdomainusage(A,C),membermeronym(D,B),similarto(B,C),similarto(E,B).
verbgroup(A,B):- derivationallyrelatedform(D,A),instancehypernym(C,A),alsosee(F,C),instancehypernym(B,E).
verbgroup(A,B):- memberofdomainregion(D,B),membermeronym(A,E),memberofdomainregion(F,D),similarto(B,C).
verbgroup(A,B):- instancehypernym(B,F),alsosee(F,C),memberofdomainregion(E,A),synsetdomaintopicof(D,F).
verbgroup(A,B):- derivationallyrelatedform(C,A),synsetdomaintopicof(E,B),memberofdomainregion(D,E).
verbgroup(A,B):- memberofdomainregion(F,B),alsosee(F,C),memberofdomainusage(C,E),haspart(A,D).
verbgroup(A,B):- alsosee(D,B),derivationallyrelatedform(B,A),similarto(B,C),synsetdomaintopicof(A,B).
verbgroup(A,B):- alsosee(A,E),alsosee(B,F),similarto(B,C),membermeronym(B,D).
verbgroup(A,B):- synsetdomaintopicof(B,F),alsosee(F,C),similarto(B,D),haspart(A,E).
verbgroup(A,B):- memberofdomainusage(C,A),alsosee(F,C),similarto(D,B),alsosee(E,D).
verbgroup(A,B):- haspart(D,B),derivationallyrelatedform(A,E),alsosee(F,C),membermeronym(B,F).
verbgroup(A,B):- memberofdomainusage(E,B),memberofdomainusage(A,D),membermeronym(A,C),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(C,D),membermeronym(D,B),instancehypernym(A,B),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(B,C),instancehypernym(A,D),alsosee(F,C),synsetdomaintopicof(B,E).
verbgroup(A,B):- membermeronym(A,D),memberofdomainregion(B,C),synsetdomaintopicof(E,B),similarto(B,C).
verbgroup(A,B):- haspart(A,D),similarto(B,C),synsetdomaintopicof(A,B),alsosee(E,D).
verbgroup(A,B):- synsetdomaintopicof(E,A),alsosee(F,C),membermeronym(B,C),derivationallyrelatedform(D,E).
verbgroup(A,B):- alsosee(B,A),similarto(A,B),similarto(B,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- alsosee(C,A),instancehypernym(A,D),synsetdomaintopicof(B,A),similarto(B,C).
verbgroup(A,B):- haspart(A,B),derivationallyrelatedform(D,B),similarto(A,C).
verbgroup(A,B):- derivationallyrelatedform(E,D),instancehypernym(A,D),memberofdomainregion(F,B),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(B,C),memberofdomainusage(C,D),memberofdomainusage(B,A).
verbgroup(A,B):- alsosee(A,D),haspart(B,F),similarto(B,C),memberofdomainusage(E,D).
verbgroup(A,B):- instancehypernym(A,D),membermeronym(E,A),hypernym(F,E),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(F,B),memberofdomainregion(D,B),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- alsosee(F,C),memberofdomainusage(D,E),synsetdomaintopicof(D,A),similarto(B,C).
verbgroup(A,B):- similarto(A,D),similarto(E,A),similarto(B,C),memberofdomainregion(C,E).
verbgroup(A,B):- alsosee(F,C),haspart(B,C),synsetdomaintopicof(D,A),similarto(A,E).
verbgroup(A,B):- instancehypernym(D,B),memberofdomainregion(B,D),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- similarto(E,C),alsosee(F,C),synsetdomaintopicof(A,D),haspart(E,B).
verbgroup(A,B):- similarto(C,D),memberofdomainusage(E,F),instancehypernym(A,E),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(D,F),memberofdomainregion(A,E),memberofdomainregion(D,C),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(B,E),membermeronym(E,F),alsosee(F,C),membermeronym(D,A).
verbgroup(A,B):- memberofdomainusage(B,D),hypernym(A,B),similarto(D,C).
verbgroup(A,B):- haspart(D,B),memberofdomainusage(E,C),membermeronym(C,A),similarto(B,C).
verbgroup(A,B):- alsosee(F,C),haspart(C,B),instancehypernym(A,E),membermeronym(D,C).
verbgroup(A,B):- memberofdomainusage(E,B),alsosee(F,C),synsetdomaintopicof(A,D),memberofdomainusage(C,B).
verbgroup(A,B):- hypernym(E,F),memberofdomainregion(A,E),hypernym(D,B),alsosee(F,C).
verbgroup(A,B):- alsosee(F,C),memberofdomainusage(A,D),haspart(E,F),memberofdomainregion(E,B).
verbgroup(A,B):- instancehypernym(A,D),alsosee(F,C),similarto(E,A),membermeronym(B,F).
verbgroup(A,B):- memberofdomainregion(B,E),instancehypernym(E,D),memberofdomainregion(C,A).
verbgroup(A,B):- membermeronym(D,A),similarto(B,C),alsosee(D,A).
verbgroup(A,B):- derivationallyrelatedform(C,D),synsetdomaintopicof(F,E),similarto(B,C),synsetdomaintopicof(A,E).
