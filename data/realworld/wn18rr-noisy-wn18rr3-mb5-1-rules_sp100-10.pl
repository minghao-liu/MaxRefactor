verbgroup(A,B):- alsosee(C,A),derivationallyrelatedform(E,D),derivationallyrelatedform(A,E),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(E,A),haspart(D,C),derivationallyrelatedform(A,E),similarto(B,C).
verbgroup(A,B):- haspart(A,E),instancehypernym(E,B),synsetdomaintopicof(A,D),similarto(B,C).
verbgroup(A,B):- hypernym(E,B),membermeronym(C,D),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- similarto(E,A),memberofdomainregion(B,D),synsetdomaintopicof(C,B).
verbgroup(A,B):- membermeronym(E,B),derivationallyrelatedform(A,D),similarto(B,C),hypernym(A,D).
verbgroup(A,B):- instancehypernym(E,B),synsetdomaintopicof(A,D),derivationallyrelatedform(D,F),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(D,B),derivationallyrelatedform(C,E),similarto(B,C),derivationallyrelatedform(A,C).
verbgroup(A,B):- instancehypernym(A,F),instancehypernym(B,D),alsosee(F,C),membermeronym(F,E).
verbgroup(A,B):- similarto(E,C),synsetdomaintopicof(D,A),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- haspart(D,B),similarto(B,C),synsetdomaintopicof(D,B),memberofdomainusage(E,A).
verbgroup(A,B):- hypernym(A,E),memberofdomainregion(D,E),similarto(B,C),hypernym(C,E).
verbgroup(A,B):- instancehypernym(F,D),similarto(C,A),alsosee(F,C),synsetdomaintopicof(E,B).
verbgroup(A,B):- haspart(E,C),instancehypernym(D,B),memberofdomainusage(A,E).
verbgroup(A,B):- hypernym(B,A),similarto(A,D),haspart(B,C),similarto(B,C).
verbgroup(A,B):- instancehypernym(D,E),alsosee(F,C),hypernym(E,A),hypernym(C,B).
verbgroup(A,B):- similarto(B,C),instancehypernym(D,E),instancehypernym(A,E),instancehypernym(B,C).
verbgroup(A,B):- instancehypernym(A,F),instancehypernym(E,F),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- alsosee(F,C),membermeronym(B,C),hypernym(E,A),alsosee(F,D).
verbgroup(A,B):- alsosee(B,E),alsosee(F,C),haspart(A,C),hypernym(C,D).
verbgroup(A,B):- synsetdomaintopicof(B,F),similarto(B,C),hypernym(A,D),memberofdomainregion(E,B).
verbgroup(A,B):- membermeronym(C,E),membermeronym(D,B),haspart(E,A).
verbgroup(A,B):- memberofdomainusage(B,E),alsosee(F,C),synsetdomaintopicof(C,A),membermeronym(C,D).
verbgroup(A,B):- haspart(B,C),memberofdomainusage(C,A),memberofdomainregion(C,A).
verbgroup(A,B):- memberofdomainusage(E,B),hypernym(C,A),memberofdomainusage(E,D).
verbgroup(A,B):- hypernym(D,F),synsetdomaintopicof(A,D),similarto(B,C),memberofdomainregion(E,B).
verbgroup(A,B):- alsosee(D,E),instancehypernym(F,B),alsosee(F,C),membermeronym(E,A).
verbgroup(A,B):- memberofdomainregion(B,D),derivationallyrelatedform(C,B),haspart(A,C).
verbgroup(A,B):- haspart(B,F),hypernym(F,D),alsosee(F,C),derivationallyrelatedform(A,E).
verbgroup(A,B):- alsosee(A,D),instancehypernym(E,B),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- haspart(E,D),instancehypernym(E,B),similarto(B,C),similarto(B,A).
verbgroup(A,B):- similarto(B,C),hypernym(E,A),hypernym(A,D),similarto(C,F).
verbgroup(A,B):- alsosee(F,C),memberofdomainregion(B,F),synsetdomaintopicof(E,D),derivationallyrelatedform(E,A).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(E,D),similarto(E,A),derivationallyrelatedform(B,F).
verbgroup(A,B):- memberofdomainregion(F,B),derivationallyrelatedform(E,C),haspart(D,A),similarto(B,C).
verbgroup(A,B):- similarto(A,D),derivationallyrelatedform(D,B),similarto(B,C),alsosee(E,A).
verbgroup(A,B):- haspart(A,E),alsosee(F,C),instancehypernym(E,F),haspart(B,D).
verbgroup(A,B):- membermeronym(C,D),memberofdomainregion(B,D),hypernym(A,B).
verbgroup(A,B):- alsosee(F,C),derivationallyrelatedform(C,E),synsetdomaintopicof(D,A),derivationallyrelatedform(C,B).
verbgroup(A,B):- synsetdomaintopicof(F,A),hypernym(A,E),alsosee(D,C),similarto(B,C).
verbgroup(A,B):- alsosee(C,E),derivationallyrelatedform(A,D),alsosee(F,C),haspart(B,F).
verbgroup(A,B):- derivationallyrelatedform(A,D),hypernym(A,C),similarto(B,C),similarto(E,B).
verbgroup(A,B):- alsosee(F,C),memberofdomainregion(A,E),synsetdomaintopicof(B,D),derivationallyrelatedform(E,F).
verbgroup(A,B):- memberofdomainregion(A,E),membermeronym(C,B),similarto(B,C),hypernym(D,C).
verbgroup(A,B):- memberofdomainregion(A,D),synsetdomaintopicof(E,A),similarto(B,C),similarto(A,C).
verbgroup(A,B):- memberofdomainusage(E,B),synsetdomaintopicof(C,A),membermeronym(C,D).
verbgroup(A,B):- hypernym(A,E),derivationallyrelatedform(E,F),similarto(B,C),memberofdomainusage(E,D).
verbgroup(A,B):- haspart(D,B),similarto(B,A),similarto(B,C),memberofdomainusage(E,D).
verbgroup(A,B):- membermeronym(D,A),membermeronym(D,B),similarto(B,C),membermeronym(B,D).
verbgroup(A,B):- instancehypernym(B,D),instancehypernym(C,A),similarto(B,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- similarto(D,E),synsetdomaintopicof(B,E),similarto(A,C).
verbgroup(A,B):- hypernym(B,F),instancehypernym(A,D),haspart(E,F),similarto(B,C).
verbgroup(A,B):- alsosee(D,E),haspart(A,E),similarto(B,C),haspart(E,B).
verbgroup(A,B):- memberofdomainregion(D,B),derivationallyrelatedform(A,C),instancehypernym(D,C).
verbgroup(A,B):- instancehypernym(A,F),synsetdomaintopicof(A,D),memberofdomainusage(C,E),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(B,C),memberofdomainusage(C,D),memberofdomainregion(B,A).
verbgroup(A,B):- instancehypernym(C,A),alsosee(F,C),instancehypernym(E,B),membermeronym(D,C).
verbgroup(A,B):- memberofdomainregion(D,A),synsetdomaintopicof(A,D),derivationallyrelatedform(C,B).
verbgroup(A,B):- synsetdomaintopicof(B,C),alsosee(F,C),derivationallyrelatedform(A,E),membermeronym(B,D).
verbgroup(A,B):- instancehypernym(C,D),instancehypernym(B,E),memberofdomainregion(A,D).
verbgroup(A,B):- membermeronym(B,E),memberofdomainusage(A,D),similarto(B,C),haspart(D,E).
verbgroup(A,B):- instancehypernym(D,C),hypernym(C,A),similarto(B,C),instancehypernym(A,C).
verbgroup(A,B):- similarto(B,C),derivationallyrelatedform(A,D),synsetdomaintopicof(B,A),instancehypernym(C,B).
verbgroup(A,B):- memberofdomainregion(C,A),alsosee(F,C),similarto(B,E),alsosee(F,D).
verbgroup(A,B):- membermeronym(A,D),membermeronym(E,A),memberofdomainusage(D,C),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(D,A),instancehypernym(A,D),instancehypernym(B,A),similarto(B,C).
verbgroup(A,B):- alsosee(C,A),alsosee(A,B),derivationallyrelatedform(B,C).
verbgroup(A,B):- derivationallyrelatedform(D,B),memberofdomainusage(C,A),similarto(B,C),memberofdomainusage(D,A).
verbgroup(A,B):- haspart(A,E),instancehypernym(D,E),alsosee(A,E),similarto(B,C).
verbgroup(A,B):- alsosee(A,B),similarto(A,B),instancehypernym(B,C).
verbgroup(A,B):- memberofdomainusage(A,C),alsosee(F,C),similarto(D,B),membermeronym(E,A).
verbgroup(A,B):- alsosee(F,C),instancehypernym(D,F),derivationallyrelatedform(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- alsosee(D,E),instancehypernym(C,A),alsosee(F,C),memberofdomainusage(B,D).
verbgroup(A,B):- memberofdomainregion(A,C),alsosee(B,E),alsosee(F,C),memberofdomainregion(B,D).
verbgroup(A,B):- alsosee(B,C),memberofdomainregion(D,A),membermeronym(D,A).
verbgroup(A,B):- derivationallyrelatedform(E,A),similarto(B,D),instancehypernym(C,A).
verbgroup(A,B):- alsosee(D,B),haspart(C,B),haspart(B,A).
verbgroup(A,B):- derivationallyrelatedform(C,A),similarto(B,C),hypernym(A,D),hypernym(C,B).
verbgroup(A,B):- derivationallyrelatedform(B,D),derivationallyrelatedform(C,A),instancehypernym(E,C).
verbgroup(A,B):- alsosee(C,E),similarto(B,A),instancehypernym(D,B),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(D,E),alsosee(B,E),alsosee(F,C),hypernym(A,C).
verbgroup(A,B):- derivationallyrelatedform(E,A),memberofdomainregion(C,B),memberofdomainusage(C,D),alsosee(F,C).
verbgroup(A,B):- haspart(D,B),memberofdomainregion(A,E),memberofdomainregion(E,C),alsosee(F,C).
verbgroup(A,B):- memberofdomainregion(A,F),instancehypernym(D,B),similarto(B,C),haspart(D,E).
verbgroup(A,B):- hypernym(B,C),synsetdomaintopicof(A,D),synsetdomaintopicof(E,B),similarto(B,C).
verbgroup(A,B):- alsosee(A,D),memberofdomainusage(E,F),memberofdomainregion(E,A),similarto(B,C).
verbgroup(A,B):- membermeronym(A,C),alsosee(F,C),haspart(E,F),alsosee(B,D).
verbgroup(A,B):- alsosee(F,C),instancehypernym(B,E),haspart(D,C),alsosee(D,A).
verbgroup(A,B):- derivationallyrelatedform(A,D),memberofdomainregion(E,D),similarto(B,C),hypernym(E,C).
verbgroup(A,B):- haspart(D,B),instancehypernym(D,E),similarto(B,C),membermeronym(D,A).
verbgroup(A,B):- derivationallyrelatedform(C,D),similarto(A,E),similarto(B,C),hypernym(C,B).
verbgroup(A,B):- alsosee(F,E),memberofdomainusage(D,B),memberofdomainregion(F,A),similarto(B,C).
verbgroup(A,B):- haspart(D,C),derivationallyrelatedform(B,E),similarto(B,C),similarto(A,C).
verbgroup(A,B):- membermeronym(C,A),memberofdomainusage(C,A),membermeronym(B,D).
verbgroup(A,B):- hypernym(D,A),memberofdomainusage(D,B),similarto(B,C),similarto(A,C).
verbgroup(A,B):- similarto(D,B),memberofdomainusage(B,A),similarto(B,C),instancehypernym(A,C).
verbgroup(A,B):- alsosee(D,B),similarto(B,C),synsetdomaintopicof(A,B),derivationallyrelatedform(D,C).
verbgroup(A,B):- hypernym(D,B),alsosee(B,E),alsosee(F,C),derivationallyrelatedform(C,A).
verbgroup(A,B):- synsetdomaintopicof(D,A),alsosee(D,C),similarto(E,B).
verbgroup(A,B):- membermeronym(A,D),instancehypernym(C,E),haspart(D,A),similarto(B,C).
