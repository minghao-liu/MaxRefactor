verbgroup(A,B):- instancehypernym(C,D),instancehypernym(B,C),instancehypernym(A,C).
verbgroup(A,B):- alsosee(F,C),haspart(C,D),alsosee(A,E),derivationallyrelatedform(C,B).
verbgroup(A,B):- hypernym(A,C),memberofdomainregion(C,D),haspart(E,B).
verbgroup(A,B):- haspart(A,B),membermeronym(A,C),similarto(A,C).
verbgroup(A,B):- instancehypernym(D,A),synsetdomaintopicof(C,A),instancehypernym(C,B).
verbgroup(A,B):- memberofdomainregion(A,D),similarto(A,B),similarto(B,C),instancehypernym(A,C).
verbgroup(A,B):- haspart(E,D),memberofdomainregion(E,D),haspart(D,A),similarto(B,C).
verbgroup(A,B):- hypernym(D,A),derivationallyrelatedform(A,B),haspart(D,A),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(B,D),alsosee(A,E),alsosee(B,C),similarto(B,C).
verbgroup(A,B):- membermeronym(A,B),memberofdomainregion(D,C),instancehypernym(A,C).
verbgroup(A,B):- instancehypernym(B,D),membermeronym(A,E),hypernym(A,C),similarto(B,C).
verbgroup(A,B):- similarto(F,A),similarto(B,D),synsetdomaintopicof(E,A),alsosee(F,C).
verbgroup(A,B):- memberofdomainusage(E,B),alsosee(F,C),derivationallyrelatedform(B,C),alsosee(D,A).
verbgroup(A,B):- haspart(D,B),haspart(B,C),derivationallyrelatedform(A,D),similarto(B,C).
verbgroup(A,B):- haspart(D,B),hypernym(A,C),synsetdomaintopicof(C,E).
verbgroup(A,B):- haspart(D,B),alsosee(B,E),derivationallyrelatedform(B,A),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(D,A),similarto(A,D),hypernym(A,C),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(A,D),alsosee(F,C),membermeronym(B,F),memberofdomainusage(A,E).
verbgroup(A,B):- similarto(B,C),synsetdomaintopicof(A,F),instancehypernym(D,F),synsetdomaintopicof(B,E).
verbgroup(A,B):- derivationallyrelatedform(A,D),memberofdomainusage(A,D),alsosee(A,C),similarto(B,C).
verbgroup(A,B):- similarto(E,C),similarto(D,B),similarto(B,C),memberofdomainusage(D,A).
verbgroup(A,B):- haspart(B,E),memberofdomainregion(F,A),alsosee(F,C),synsetdomaintopicof(D,F).
verbgroup(A,B):- memberofdomainregion(D,F),synsetdomaintopicof(A,F),similarto(E,C),similarto(B,C).
verbgroup(A,B):- alsosee(A,D),memberofdomainregion(C,B),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- instancehypernym(D,A),alsosee(D,B),instancehypernym(B,C).
verbgroup(A,B):- alsosee(F,C),synsetdomaintopicof(B,F),synsetdomaintopicof(D,A),memberofdomainusage(C,E).
verbgroup(A,B):- membermeronym(B,D),similarto(C,E),alsosee(F,C),instancehypernym(A,C).
verbgroup(A,B):- membermeronym(E,B),haspart(D,A),similarto(B,C),similarto(C,F).
verbgroup(A,B):- hypernym(A,E),memberofdomainregion(B,C),similarto(D,B).
verbgroup(A,B):- derivationallyrelatedform(A,D),similarto(B,C),instancehypernym(B,C),synsetdomaintopicof(C,B).
verbgroup(A,B):- alsosee(D,B),hypernym(A,C),similarto(B,C),memberofdomainregion(E,A).
verbgroup(A,B):- memberofdomainusage(B,F),memberofdomainusage(D,B),alsosee(F,C),hypernym(E,A).
verbgroup(A,B):- synsetdomaintopicof(A,C),similarto(D,E),membermeronym(A,E),similarto(B,C).
verbgroup(A,B):- memberofdomainusage(D,E),haspart(B,C),alsosee(F,C),membermeronym(E,A).
verbgroup(A,B):- derivationallyrelatedform(B,A),alsosee(D,B),synsetdomaintopicof(E,D),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(C,B),similarto(B,C),hypernym(A,D),memberofdomainusage(D,A).
verbgroup(A,B):- memberofdomainusage(D,A),similarto(F,D),similarto(B,C),memberofdomainusage(A,E).
verbgroup(A,B):- haspart(B,E),memberofdomainusage(C,D),alsosee(F,C),memberofdomainusage(A,D).
verbgroup(A,B):- similarto(C,B),hypernym(D,B),similarto(B,C),hypernym(A,B).
verbgroup(A,B):- alsosee(A,D),hypernym(B,C),derivationallyrelatedform(B,A).
verbgroup(A,B):- similarto(B,D),haspart(C,B),membermeronym(A,C).
verbgroup(A,B):- similarto(A,D),alsosee(F,C),instancehypernym(B,C),memberofdomainusage(E,D).
verbgroup(A,B):- instancehypernym(A,F),haspart(B,E),similarto(B,C),synsetdomaintopicof(D,B).
verbgroup(A,B):- alsosee(C,A),similarto(B,E),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- memberofdomainusage(F,A),derivationallyrelatedform(D,B),hypernym(E,A),similarto(B,C).
verbgroup(A,B):- instancehypernym(D,E),membermeronym(C,B),memberofdomainregion(E,A).
verbgroup(A,B):- similarto(A,D),membermeronym(C,B),similarto(B,C),membermeronym(B,E).
verbgroup(A,B):- similarto(C,D),memberofdomainregion(C,D),similarto(B,C),memberofdomainregion(A,D).
verbgroup(A,B):- memberofdomainregion(C,A),synsetdomaintopicof(B,E),alsosee(D,A).
verbgroup(A,B):- instancehypernym(D,A),membermeronym(A,E),haspart(A,F),similarto(B,C).
verbgroup(A,B):- instancehypernym(F,B),alsosee(F,C),instancehypernym(C,E),hypernym(A,D).
verbgroup(A,B):- hypernym(D,B),membermeronym(A,C),synsetdomaintopicof(B,E).
verbgroup(A,B):- instancehypernym(B,D),hypernym(A,E),hypernym(D,C).
verbgroup(A,B):- instancehypernym(C,D),hypernym(A,E),derivationallyrelatedform(C,A),similarto(B,C).
verbgroup(A,B):- synsetdomaintopicof(E,C),similarto(A,D),alsosee(D,E),similarto(B,C).
verbgroup(A,B):- hypernym(A,E),synsetdomaintopicof(B,D),similarto(B,C),memberofdomainusage(B,D).
verbgroup(A,B):- haspart(B,F),membermeronym(F,D),instancehypernym(A,E),similarto(B,C).
verbgroup(A,B):- derivationallyrelatedform(E,A),instancehypernym(D,A),similarto(B,C),instancehypernym(F,A).
verbgroup(A,B):- hypernym(D,B),synsetdomaintopicof(C,D),similarto(B,A),similarto(B,C).
verbgroup(A,B):- similarto(A,D),alsosee(E,C),similarto(B,C),hypernym(A,D).
