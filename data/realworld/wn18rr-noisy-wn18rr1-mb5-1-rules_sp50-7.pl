memberofdomainregion(A,B):- instancehypernym(E,F),synsetdomaintopicof(E,D),haspart(B,C),synsetdomaintopicof(A,E).
memberofdomainregion(A,B):- similarto(D,A),instancehypernym(A,D),haspart(B,C),membermeronym(E,A).
memberofdomainregion(A,B):- haspart(F,A),membermeronym(F,C),memberofdomainusage(D,B),derivationallyrelatedform(E,A).
memberofdomainregion(A,B):- alsosee(D,F),membermeronym(F,C),derivationallyrelatedform(B,D),haspart(A,E).
memberofdomainregion(A,B):- derivationallyrelatedform(A,B),instancehypernym(E,B),haspart(B,C),hypernym(D,B).
memberofdomainregion(A,B):- synsetdomaintopicof(B,D),membermeronym(F,C),derivationallyrelatedform(E,D),similarto(C,A).
memberofdomainregion(A,B):- derivationallyrelatedform(D,B),alsosee(C,B),alsosee(B,A).
memberofdomainregion(A,B):- haspart(E,B),derivationallyrelatedform(D,E),similarto(A,C).
memberofdomainregion(A,B):- hypernym(F,E),haspart(A,D),haspart(E,A),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(E,B),derivationallyrelatedform(C,D),alsosee(A,D).
memberofdomainregion(A,B):- similarto(E,A),derivationallyrelatedform(C,E),membermeronym(D,B),haspart(B,C).
memberofdomainregion(A,B):- haspart(B,C),haspart(A,D),verbgroup(B,A),memberofdomainusage(E,A).
memberofdomainregion(A,B):- alsosee(A,C),membermeronym(D,E),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- instancehypernym(B,E),membermeronym(F,C),instancehypernym(C,D),derivationallyrelatedform(A,C).
memberofdomainregion(A,B):- hypernym(B,D),synsetdomaintopicof(A,C),hypernym(A,E),haspart(B,C).
memberofdomainregion(A,B):- alsosee(B,C),synsetdomaintopicof(D,A),memberofdomainusage(D,E).
memberofdomainregion(A,B):- instancehypernym(C,A),haspart(B,D),alsosee(E,D).
memberofdomainregion(A,B):- membermeronym(B,C),derivationallyrelatedform(B,A),membermeronym(C,A).
memberofdomainregion(A,B):- synsetdomaintopicof(A,D),membermeronym(B,A),haspart(B,C),verbgroup(C,A).
memberofdomainregion(A,B):- membermeronym(A,E),membermeronym(F,C),instancehypernym(B,F),verbgroup(A,D).
memberofdomainregion(A,B):- membermeronym(F,C),similarto(C,B),memberofdomainusage(F,E),alsosee(D,A).
memberofdomainregion(A,B):- derivationallyrelatedform(B,E),membermeronym(F,C),instancehypernym(C,A),alsosee(E,D).
memberofdomainregion(A,B):- hypernym(E,B),membermeronym(E,C),membermeronym(D,A).
memberofdomainregion(A,B):- haspart(B,C),verbgroup(E,C),membermeronym(E,D),haspart(A,E).
memberofdomainregion(A,B):- derivationallyrelatedform(A,E),instancehypernym(B,D),derivationallyrelatedform(C,B).
memberofdomainregion(A,B):- hypernym(B,D),membermeronym(F,C),synsetdomaintopicof(D,F),alsosee(E,A).
memberofdomainregion(A,B):- instancehypernym(E,B),hypernym(A,E),haspart(B,C),verbgroup(A,D).
memberofdomainregion(A,B):- hypernym(B,C),synsetdomaintopicof(E,D),instancehypernym(D,A).
memberofdomainregion(A,B):- synsetdomaintopicof(C,E),synsetdomaintopicof(C,A),instancehypernym(A,D),haspart(B,C).
memberofdomainregion(A,B):- similarto(F,D),membermeronym(F,C),derivationallyrelatedform(B,F),haspart(A,E).
memberofdomainregion(A,B):- synsetdomaintopicof(C,E),membermeronym(F,C),membermeronym(D,A),instancehypernym(B,C).
memberofdomainregion(A,B):- instancehypernym(D,F),membermeronym(E,C),derivationallyrelatedform(D,A),haspart(B,C).
memberofdomainregion(A,B):- membermeronym(F,C),haspart(D,A),instancehypernym(C,E),synsetdomaintopicof(B,F).
memberofdomainregion(A,B):- similarto(E,A),alsosee(D,B),verbgroup(A,B),haspart(B,C).
memberofdomainregion(A,B):- alsosee(A,F),hypernym(E,D),haspart(B,C),synsetdomaintopicof(D,B).
memberofdomainregion(A,B):- instancehypernym(A,D),membermeronym(F,C),membermeronym(B,E),synsetdomaintopicof(D,C).
memberofdomainregion(A,B):- haspart(B,C),memberofdomainusage(B,A),verbgroup(D,B),verbgroup(E,B).
memberofdomainregion(A,B):- similarto(E,D),derivationallyrelatedform(B,E),membermeronym(F,C),instancehypernym(A,F).
memberofdomainregion(A,B):- derivationallyrelatedform(C,B),haspart(D,A),hypernym(D,B).
memberofdomainregion(A,B):- alsosee(D,F),similarto(A,D),haspart(B,C),membermeronym(E,A).
memberofdomainregion(A,B):- membermeronym(F,C),verbgroup(B,C),membermeronym(D,A),derivationallyrelatedform(E,C).
memberofdomainregion(A,B):- alsosee(A,C),derivationallyrelatedform(B,E),membermeronym(F,C),alsosee(D,B).
memberofdomainregion(A,B):- membermeronym(F,C),verbgroup(E,C),derivationallyrelatedform(B,D),synsetdomaintopicof(A,C).
memberofdomainregion(A,B):- verbgroup(B,D),memberofdomainusage(A,E),membermeronym(F,C),derivationallyrelatedform(E,C).
memberofdomainregion(A,B):- similarto(A,E),membermeronym(D,F),alsosee(F,C),haspart(B,C).
memberofdomainregion(A,B):- hypernym(B,C),alsosee(A,D),alsosee(E,D).
memberofdomainregion(A,B):- membermeronym(F,C),synsetdomaintopicof(E,A),similarto(D,B),haspart(C,A).
memberofdomainregion(A,B):- memberofdomainusage(B,C),alsosee(A,D),haspart(B,C),derivationallyrelatedform(E,C).
memberofdomainregion(A,B):- haspart(D,B),synsetdomaintopicof(E,D),hypernym(A,F),haspart(B,C).
memberofdomainregion(A,B):- haspart(C,A),haspart(B,C),synsetdomaintopicof(D,B).
