verbgroup(A,B):- similarto(D,C),synsetdomaintopicof(C,A),alsosee(B,D).
verbgroup(A,B):- alsosee(D,B),derivationallyrelatedform(F,E),membermeronym(F,A),similarto(B,C).
verbgroup(A,B):- membermeronym(A,D),membermeronym(B,A),hypernym(D,B),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(A,C),instancehypernym(A,D),memberofdomainregion(B,D).
verbgroup(A,B):- alsosee(F,C),haspart(C,B),similarto(E,A),memberofdomainregion(D,A).
verbgroup(A,B):- alsosee(E,F),alsosee(F,C),similarto(D,B),instancehypernym(F,A).
verbgroup(A,B):- alsosee(F,C),alsosee(E,C),hypernym(B,D),membermeronym(E,A).
verbgroup(A,B):- derivationallyrelatedform(E,D),instancehypernym(D,F),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- derivationallyrelatedform(E,C),synsetdomaintopicof(C,A),synsetdomaintopicof(D,B).
verbgroup(A,B):- haspart(B,C),derivationallyrelatedform(C,B),haspart(C,A).
verbgroup(A,B):- alsosee(A,B),similarto(B,C),synsetdomaintopicof(D,B),hypernym(C,B).
verbgroup(A,B):- membermeronym(B,A),haspart(D,C),similarto(A,E),similarto(B,C).
verbgroup(A,B):- alsosee(D,B),memberofdomainregion(D,C),similarto(B,C),hypernym(A,B).
verbgroup(A,B):- alsosee(D,B),derivationallyrelatedform(A,E),instancehypernym(C,B).
verbgroup(A,B):- similarto(F,A),synsetdomaintopicof(E,A),alsosee(F,C),alsosee(B,D).
verbgroup(A,B):- haspart(D,B),memberofdomainusage(F,B),membermeronym(E,A),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(C,D),similarto(B,C),synsetdomaintopicof(A,B),memberofdomainregion(A,D).
verbgroup(A,B):- similarto(B,C),instancehypernym(D,B),synsetdomaintopicof(C,E),haspart(C,A).
verbgroup(A,B):- membermeronym(A,D),alsosee(F,C),synsetdomaintopicof(D,E),similarto(B,F).
verbgroup(A,B):- memberofdomainregion(A,E),derivationallyrelatedform(A,D),derivationallyrelatedform(E,B),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(A,E),memberofdomainusage(B,D),similarto(B,C),similarto(B,F).
verbgroup(A,B):- membermeronym(A,C),derivationallyrelatedform(D,B),haspart(B,D).
verbgroup(A,B):- similarto(C,E),synsetdomaintopicof(C,A),similarto(B,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- membermeronym(A,E),memberofdomainusage(A,D),haspart(A,C),similarto(B,C).
verbgroup(A,B):- instancehypernym(E,D),haspart(E,C),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- memberofdomainregion(B,C),synsetdomaintopicof(D,B),alsosee(D,A).
verbgroup(A,B):- instancehypernym(D,A),derivationallyrelatedform(F,B),alsosee(F,C),membermeronym(E,A).
verbgroup(A,B):- derivationallyrelatedform(B,C),similarto(A,E),similarto(B,C),alsosee(E,D).
verbgroup(A,B):- hypernym(A,E),memberofdomainusage(D,F),similarto(B,C),hypernym(F,A).
verbgroup(A,B):- memberofdomainusage(C,D),alsosee(F,C),haspart(E,A),derivationallyrelatedform(B,C).
verbgroup(A,B):- memberofdomainusage(B,C),alsosee(A,E),similarto(B,C),alsosee(C,D).
verbgroup(A,B):- synsetdomaintopicof(B,C),alsosee(D,A),synsetdomaintopicof(A,E).
verbgroup(A,B):- memberofdomainregion(B,E),alsosee(F,C),alsosee(E,C),haspart(A,D).
verbgroup(A,B):- memberofdomainusage(A,E),memberofdomainusage(D,C),similarto(B,C),hypernym(F,C).
verbgroup(A,B):- haspart(B,C),derivationallyrelatedform(B,E),alsosee(D,A).
verbgroup(A,B):- hypernym(D,A),similarto(F,A),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- derivationallyrelatedform(D,B),similarto(B,C),alsosee(E,A),hypernym(E,C).
verbgroup(A,B):- memberofdomainregion(D,B),haspart(B,F),hypernym(E,A),similarto(B,C).
verbgroup(A,B):- membermeronym(D,A),memberofdomainregion(E,A),synsetdomaintopicof(C,B).
verbgroup(A,B):- membermeronym(B,D),alsosee(F,C),memberofdomainregion(D,E),instancehypernym(A,C).
verbgroup(A,B):- memberofdomainregion(E,C),alsosee(D,B),hypernym(A,F),similarto(B,C).
verbgroup(A,B):- hypernym(C,D),synsetdomaintopicof(A,D),similarto(B,A).
verbgroup(A,B):- membermeronym(A,D),memberofdomainusage(B,D),instancehypernym(A,C).
verbgroup(A,B):- similarto(A,D),alsosee(B,E),similarto(E,D),similarto(B,C).
verbgroup(A,B):- membermeronym(B,A),similarto(A,D),hypernym(D,C).
verbgroup(A,B):- derivationallyrelatedform(E,B),memberofdomainregion(A,D),similarto(D,C).
verbgroup(A,B):- haspart(D,E),membermeronym(C,B),similarto(B,C),haspart(A,D).
verbgroup(A,B):- memberofdomainregion(C,A),membermeronym(D,B),similarto(B,C),hypernym(C,E).
verbgroup(A,B):- memberofdomainusage(A,B),haspart(A,D),similarto(B,C),hypernym(A,B).
verbgroup(A,B):- membermeronym(A,D),similarto(B,C),synsetdomaintopicof(A,E).
verbgroup(A,B):- memberofdomainregion(D,B),haspart(A,C),hypernym(C,B).
verbgroup(A,B):- haspart(B,E),memberofdomainregion(D,B),derivationallyrelatedform(A,C).
verbgroup(A,B):- similarto(B,D),alsosee(F,C),membermeronym(D,F),membermeronym(E,A).
verbgroup(A,B):- alsosee(F,C),memberofdomainregion(A,E),alsosee(C,B),memberofdomainregion(D,A).
verbgroup(A,B):- similarto(B,C),derivationallyrelatedform(A,D),alsosee(A,C),alsosee(C,D).
verbgroup(A,B):- alsosee(A,D),instancehypernym(D,A),haspart(D,C),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(E,C),instancehypernym(A,D),similarto(B,C),memberofdomainregion(E,B).
verbgroup(A,B):- similarto(E,D),synsetdomaintopicof(A,D),similarto(B,C),haspart(A,D).
verbgroup(A,B):- hypernym(A,E),membermeronym(C,B),haspart(E,D).
verbgroup(A,B):- synsetdomaintopicof(F,A),instancehypernym(E,B),similarto(B,C),memberofdomainusage(E,D).
verbgroup(A,B):- memberofdomainregion(A,C),similarto(B,C).
verbgroup(A,B):- similarto(C,A),alsosee(F,C),synsetdomaintopicof(D,B),memberofdomainusage(A,E).
verbgroup(A,B):- memberofdomainusage(A,C),haspart(B,C),memberofdomainregion(B,D).
verbgroup(A,B):- alsosee(D,E),derivationallyrelatedform(A,D),similarto(B,C),hypernym(C,F).
verbgroup(A,B):- membermeronym(C,A),similarto(B,C),hypernym(A,D),memberofdomainregion(E,B).
verbgroup(A,B):- alsosee(F,C),memberofdomainusage(E,D),memberofdomainregion(A,D),similarto(B,F).
verbgroup(A,B):- memberofdomainregion(F,A),alsosee(F,C),derivationallyrelatedform(D,B),synsetdomaintopicof(F,E).
verbgroup(A,B):- memberofdomainusage(C,A),derivationallyrelatedform(C,A),memberofdomainusage(A,D),similarto(B,C).
verbgroup(A,B):- membermeronym(A,D),haspart(C,A),hypernym(A,B).
verbgroup(A,B):- memberofdomainusage(C,A),instancehypernym(D,B),alsosee(E,D).
verbgroup(A,B):- similarto(A,D),similarto(B,C),alsosee(E,A),memberofdomainregion(B,A).
verbgroup(A,B):- derivationallyrelatedform(E,A),similarto(D,E),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- memberofdomainregion(D,B),synsetdomaintopicof(A,F),derivationallyrelatedform(A,E),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(A,F),similarto(D,F),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- membermeronym(D,E),similarto(D,A),membermeronym(A,E),similarto(B,C).
verbgroup(A,B):- alsosee(A,D),derivationallyrelatedform(A,B),memberofdomainusage(C,E),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(E,B),synsetdomaintopicof(D,A),memberofdomainregion(C,A).
verbgroup(A,B):- instancehypernym(E,A),haspart(B,C),alsosee(F,C),hypernym(E,D).
verbgroup(A,B):- memberofdomainregion(B,F),similarto(A,D),alsosee(F,C),instancehypernym(A,E).
verbgroup(A,B):- memberofdomainregion(E,B),similarto(C,B),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- alsosee(A,E),similarto(B,C),haspart(D,E),derivationallyrelatedform(D,F).
verbgroup(A,B):- memberofdomainregion(A,E),membermeronym(E,C),membermeronym(D,C),similarto(B,C).
verbgroup(A,B):- haspart(A,E),derivationallyrelatedform(D,E),alsosee(F,C),instancehypernym(C,B).
verbgroup(A,B):- haspart(A,E),memberofdomainregion(F,B),haspart(E,D),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(C,B),membermeronym(A,E),haspart(B,D).
verbgroup(A,B):- membermeronym(B,A),similarto(A,B),similarto(A,C).
verbgroup(A,B):- hypernym(B,A),memberofdomainusage(D,B),membermeronym(E,A),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(D,A),membermeronym(B,C),similarto(A,C).
verbgroup(A,B):- haspart(A,E),similarto(B,D),hypernym(C,E).
verbgroup(A,B):- memberofdomainusage(B,C),hypernym(A,E),memberofdomainregion(D,E).
verbgroup(A,B):- alsosee(F,C),memberofdomainusage(A,F),synsetdomaintopicof(B,D),instancehypernym(F,E).
verbgroup(A,B):- synsetdomaintopicof(B,F),similarto(A,D),similarto(B,C),membermeronym(E,D).
verbgroup(A,B):- hypernym(D,A),alsosee(F,C),hypernym(E,D),instancehypernym(B,F).
verbgroup(A,B):- memberofdomainregion(B,F),alsosee(F,C),similarto(E,B),alsosee(D,A).
verbgroup(A,B):- instancehypernym(B,A),instancehypernym(D,B),haspart(D,A),similarto(B,C).
verbgroup(A,B):- memberofdomainregion(A,F),alsosee(F,C),similarto(D,B),derivationallyrelatedform(E,B).
verbgroup(A,B):- alsosee(C,A),alsosee(F,C),haspart(D,B),memberofdomainusage(E,A).
verbgroup(A,B):- alsosee(B,E),synsetdomaintopicof(A,D),similarto(B,C),haspart(F,E).
verbgroup(A,B):- memberofdomainusage(F,B),alsosee(D,B),alsosee(F,C),derivationallyrelatedform(E,A).
verbgroup(A,B):- memberofdomainusage(A,C),alsosee(B,C),membermeronym(B,D).
