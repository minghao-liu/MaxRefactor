interacts(A,B):- enzymeinhibitor(A,F),transporterinducer(B,E),target(D,A),enzymeinhibitor(A,C),enzyme(F,A).
interacts(A,B):- targetantagonist(B,C),targetantagonist(A,D),target(D,A),enzymesubstrate(A,E),targetagonist(B,C).
interacts(A,B):- target(D,A),enzyme(C,B),transporterinducer(B,F),enzymeinducer(B,C),enzymeinhibitor(A,E).
interacts(A,B):- targetantagonist(B,E),targetinhibitor(B,D),target(E,B),transporterinhibitor(B,F),transporterinducer(A,C).
interacts(A,B):- targetagonist(B,E),target(D,A),target(C,A),targetinhibitor(B,D),targetinhibitor(A,F).
interacts(A,B):- targetinducer(B,E),enzyme(C,B),enzymesubstrate(B,D),enzymeinhibitor(A,C),enzyme(F,A).
interacts(A,B):- targetinducer(B,E),targetagonist(B,F),targetinhibitor(A,C),targetantagonist(B,E),target(D,A).
interacts(A,B):- enzyme(C,A),target(D,A),transporterinducer(B,F),enzymesubstrate(B,E),targetinducer(A,D).
interacts(A,B):- transporter(D,B),enzyme(C,B),transporterinducer(B,E),transportersubstrate(A,E).
interacts(A,B):- enzyme(D,B),transporterinducer(B,C),transporterinhibitor(B,C),enzymesubstrate(A,D).
interacts(A,B):- targetagonist(B,D),target(D,A),enzymesubstrate(A,E),transporterinducer(B,C),enzymesubstrate(A,F).
interacts(A,B):- enzymeinducer(B,D),enzymesubstrate(B,D),transporterinducer(B,F),target(C,B),enzymeinhibitor(A,E).
interacts(A,B):- targetinducer(A,E),enzyme(D,B),enzyme(C,B),enzymeinducer(B,D),enzymesubstrate(B,D).
interacts(A,B):- targetinducer(A,E),enzymesubstrate(A,C),transporter(F,B),target(D,A),enzymeinhibitor(B,C).
interacts(A,B):- target(E,B),transportersubstrate(A,D),transporterinducer(A,F),transporterinhibitor(B,C).
interacts(A,B):- target(D,A),transporterinducer(B,C),targetantagonist(A,E),targetantagonist(A,F),targetinhibitor(A,E).
interacts(A,B):- targetinducer(B,E),targetinducer(B,F),targetinducer(A,F),transportersubstrate(B,C),target(D,A).
interacts(A,B):- targetantagonist(A,F),targetinhibitor(B,E),enzymeinducer(A,C),targetagonist(A,D).
interacts(A,B):- target(D,A),target(F,B),transporterinhibitor(A,E),target(C,B),targetinducer(A,D).
interacts(A,B):- enzymeinducer(A,D),targetagonist(B,C),target(F,A),targetagonist(A,E).
interacts(A,B):- target(D,A),enzymesubstrate(B,C),enzyme(C,B),transporterinducer(B,F),target(E,B).
interacts(A,B):- enzymeinhibitor(B,C),transporterinhibitor(A,E),enzymeinhibitor(A,F),transporter(D,A).
interacts(A,B):- targetantagonist(B,C),transporter(F,B),enzymesubstrate(B,D),transporter(F,A),transportersubstrate(A,E).
interacts(A,B):- transporterinhibitor(B,C),targetagonist(B,E),target(D,A),target(E,B),targetinhibitor(A,E).
interacts(A,B):- target(D,A),transporter(E,A),target(F,B),transporterinducer(B,C),targetinhibitor(A,F).
interacts(A,B):- targetinhibitor(A,E),enzymeinhibitor(B,D),target(C,B),enzymesubstrate(A,D).
interacts(A,B):- targetantagonist(B,C),transporter(E,B),targetinhibitor(B,C),target(D,A),target(C,B).
interacts(A,B):- enzymesubstrate(B,E),transportersubstrate(B,D),targetinducer(B,C),targetantagonist(A,C).
interacts(A,B):- enzymesubstrate(B,C),targetinducer(B,F),targetinducer(A,F),enzymesubstrate(B,D),targetantagonist(B,E).
interacts(A,B):- targetinducer(B,E),targetagonist(B,E),enzymesubstrate(B,D),transportersubstrate(B,C),enzyme(F,A).
interacts(A,B):- targetinhibitor(A,D),transporter(C,B),enzymesubstrate(B,F),targetantagonist(A,E).
interacts(A,B):- enzymeinducer(A,D),enzyme(C,B),enzymeinducer(B,D),enzymesubstrate(B,D),transporterinhibitor(B,E).
interacts(A,B):- targetagonist(B,D),transporterinhibitor(A,C),enzyme(F,B),targetantagonist(B,E),enzyme(F,A).
interacts(A,B):- targetinducer(A,E),targetinhibitor(B,C),transporter(F,B),targetantagonist(B,E),target(D,A).
interacts(A,B):- targetinducer(B,E),transporter(F,B),targetantagonist(B,E),target(C,B),enzymeinhibitor(A,D).
interacts(A,B):- enzyme(E,B),targetinhibitor(A,C),target(D,A),targetinhibitor(A,D),targetantagonist(A,F).
interacts(A,B):- targetagonist(A,D),targetagonist(A,E),transporter(C,A),targetantagonist(B,E),transportersubstrate(B,F).
interacts(A,B):- enzymeinducer(A,E),enzymeinducer(B,E),transporterinhibitor(B,C),target(D,A),transporterinducer(B,C).
interacts(A,B):- targetantagonist(B,C),enzyme(E,B),transporterinducer(A,D),transporterinhibitor(B,D).
interacts(A,B):- enzymeinhibitor(B,C),enzymesubstrate(A,E),enzymeinhibitor(A,F),enzymeinhibitor(B,D).
interacts(A,B):- transporterinhibitor(B,F),targetantagonist(A,C),enzyme(E,A),transporterinhibitor(A,D).
interacts(A,B):- targetantagonist(B,C),enzyme(F,B),targetantagonist(B,E),target(D,A),enzymeinducer(A,F).
interacts(A,B):- enzymesubstrate(B,C),enzymeinducer(A,D),transporter(F,B),target(E,A),targetantagonist(B,E).
interacts(A,B):- targetinducer(A,E),enzymesubstrate(B,C),targetagonist(B,E),enzymesubstrate(B,D),enzymeinhibitor(B,D).
interacts(A,B):- enzyme(C,B),enzymeinducer(A,C),transporter(D,A),targetantagonist(B,E),targetinhibitor(A,E).
interacts(A,B):- target(D,A),transporterinducer(B,F),transporterinducer(B,C),targetinhibitor(B,D),enzyme(E,A).
interacts(A,B):- targetinducer(A,E),enzymeinducer(A,C),targetantagonist(B,E),targetinhibitor(B,E),enzymeinhibitor(B,D).
interacts(A,B):- enzymesubstrate(B,D),transporterinducer(A,E),transportersubstrate(B,E),targetantagonist(A,C),enzyme(D,A).
interacts(A,B):- targetantagonist(B,E),targetinhibitor(B,D),targetinhibitor(A,D),enzymeinhibitor(A,C),transporterinhibitor(A,F).
interacts(A,B):- targetagonist(B,E),targetinhibitor(A,C),enzymeinducer(B,D),enzymesubstrate(B,D),enzymeinhibitor(B,D).
