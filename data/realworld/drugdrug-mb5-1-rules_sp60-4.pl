interacts(A,B):- targetagonist(B,E),transportersubstrate(A,D),enzymesubstrate(A,C),targetinducer(A,F).
interacts(A,B):- transporterinhibitor(B,E),targetantagonist(A,C),transporter(F,B),enzyme(D,A).
interacts(A,B):- targetagonist(B,D),transporterinhibitor(A,C),targetantagonist(A,D),target(D,A),enzyme(E,A).
interacts(A,B):- targetantagonist(B,C),targetinducer(A,F),transporterinhibitor(A,D),enzymeinhibitor(A,E).
interacts(A,B):- transporterinhibitor(B,C),targetagonist(A,D),targetagonist(B,E),targetantagonist(B,E),targetinhibitor(B,D).
interacts(A,B):- enzyme(C,A),enzymesubstrate(B,D),target(F,B),enzymeinhibitor(A,C),targetinhibitor(A,E).
interacts(A,B):- targetinducer(B,E),target(D,A),targetagonist(A,F),targetantagonist(A,C),targetinhibitor(A,F).
interacts(A,B):- transporterinhibitor(A,C),enzymeinducer(B,D),enzymesubstrate(B,D),targetantagonist(A,F),targetinhibitor(B,E).
interacts(A,B):- target(F,A),enzymesubstrate(B,D),transporterinducer(B,C),targetinhibitor(A,E),enzymeinhibitor(A,D).
interacts(A,B):- targetantagonist(B,E),targetinhibitor(B,D),targetinhibitor(A,D),enzymesubstrate(A,F),enzymeinducer(B,C).
interacts(A,B):- targetinducer(A,C),enzymesubstrate(B,F),enzyme(E,A),enzyme(D,A).
interacts(A,B):- transportersubstrate(A,F),targetinhibitor(A,C),transporter(F,B),target(D,A),enzyme(E,A).
interacts(A,B):- targetagonist(B,E),targetinducer(B,C),targetantagonist(A,E),target(D,A).
interacts(A,B):- enzymeinducer(A,E),transporterinducer(A,C),enzymeinducer(B,F),targetinhibitor(B,D).
interacts(A,B):- transporter(C,B),enzymesubstrate(B,D),enzymesubstrate(A,E),enzyme(E,A),enzyme(D,A).
interacts(A,B):- enzymeinducer(A,D),transportersubstrate(B,E),enzyme(F,A),targetagonist(B,C).
interacts(A,B):- enzymeinducer(B,E),targetinducer(B,F),enzymesubstrate(B,D),targetinducer(B,C),targetagonist(A,C).
interacts(A,B):- enzymeinhibitor(B,C),target(D,B),target(F,A),transporterinducer(A,E).
interacts(A,B):- transportersubstrate(B,D),enzyme(C,B),transporterinhibitor(A,F),enzymeinhibitor(B,E).
interacts(A,B):- enzymesubstrate(B,C),targetagonist(B,E),transporter(D,A).
interacts(A,B):- targetantagonist(B,E),target(C,A),target(C,B),targetinhibitor(A,F),enzyme(D,A).
interacts(A,B):- transporterinducer(A,C),transporterinhibitor(B,C),targetantagonist(B,D),targetantagonist(A,E).
interacts(A,B):- targetinhibitor(A,D),target(C,B),enzymeinducer(A,F),targetantagonist(A,E).
interacts(A,B):- targetantagonist(B,E),transporterinducer(B,F),target(C,A),enzymeinhibitor(B,D),enzymeinhibitor(A,D).
interacts(A,B):- enzymeinducer(B,E),enzyme(D,B),targetantagonist(A,F),transportersubstrate(A,C).
interacts(A,B):- transporter(C,B),enzymesubstrate(B,D),transporter(E,A),enzymeinhibitor(B,D),targetinhibitor(A,F).
interacts(A,B):- transporterinhibitor(B,C),targetinducer(A,F),transporter(C,A),enzymesubstrate(B,D),target(E,B).
interacts(A,B):- enzyme(C,A),targetinducer(B,E),enzyme(F,B),target(D,A),enzyme(F,A).
interacts(A,B):- target(F,A),transporter(D,A),targetantagonist(B,E),targetinducer(B,C),targetagonist(A,C).
interacts(A,B):- targetinducer(B,E),transporterinhibitor(B,C),enzyme(D,B),enzymesubstrate(A,F).
interacts(A,B):- targetinducer(B,E),targetagonist(B,D),enzymeinducer(A,C),transportersubstrate(B,F).
interacts(A,B):- targetantagonist(A,F),targetantagonist(B,E),targetinducer(B,C),targetinducer(A,C),targetinducer(A,D).
interacts(A,B):- enzyme(E,B),transporterinhibitor(A,C),targetantagonist(B,D),target(D,A),target(D,B).
interacts(A,B):- targetinhibitor(B,E),transporterinducer(A,F),enzymeinhibitor(A,D),targetantagonist(A,C).
interacts(A,B):- targetagonist(B,F),target(D,A),transporterinducer(B,C),enzyme(E,A),enzymeinhibitor(A,E).
interacts(A,B):- targetinducer(A,F),targetinhibitor(B,C),targetantagonist(B,E),targetinhibitor(A,E),transporterinducer(A,D).
interacts(A,B):- transporter(C,B),target(D,A),enzyme(F,A),targetinducer(B,D),enzymeinhibitor(A,E).
interacts(A,B):- enzyme(C,B),transporter(F,B),enzymesubstrate(B,D),enzymeinhibitor(B,C),transportersubstrate(A,E).
interacts(A,B):- targetinducer(B,E),targetinhibitor(B,C),targetantagonist(B,E),targetinhibitor(A,D),targetantagonist(B,F).
interacts(A,B):- enzyme(D,B),target(F,A),targetantagonist(B,E),targetinhibitor(B,E),targetagonist(A,C).
interacts(A,B):- targetagonist(A,D),targetantagonist(A,D),targetinhibitor(B,C),targetantagonist(B,E),enzymeinducer(B,F).
interacts(A,B):- targetinhibitor(B,C),targetinhibitor(A,C),enzymesubstrate(B,D),targetinducer(B,C),enzymeinhibitor(A,E).
interacts(A,B):- target(E,B),transporter(D,B),targetinhibitor(A,C),transportersubstrate(B,F).
interacts(A,B):- enzymesubstrate(B,C),target(D,A),enzymeinhibitor(A,C),enzymesubstrate(A,F),enzymeinhibitor(A,E).
interacts(A,B):- targetagonist(B,D),target(D,A),target(C,A),enzymesubstrate(A,E),targetinhibitor(A,F).
interacts(A,B):- enzyme(E,B),transporterinhibitor(B,C),transporter(C,A),enzymesubstrate(B,D),transportersubstrate(A,C).
interacts(A,B):- targetinducer(A,F),transporterinducer(A,E),target(D,A),targetinducer(B,D),targetagonist(A,C).
interacts(A,B):- targetinducer(B,F),targetantagonist(B,E),targetinhibitor(B,D),targetinducer(A,C),targetinhibitor(A,E).
interacts(A,B):- enzymeinducer(B,E),enzymesubstrate(B,D),enzymeinducer(A,C),enzymesubstrate(B,E),enzymeinhibitor(A,D).
interacts(A,B):- targetagonist(B,E),transporter(D,A),targetantagonist(B,E),transporterinhibitor(A,F),targetagonist(B,C).
interacts(A,B):- targetagonist(B,E),targetinhibitor(B,C),targetantagonist(B,E),target(E,B),enzyme(D,A).
interacts(A,B):- targetinducer(B,E),transporter(D,A),targetantagonist(B,E),transporterinhibitor(B,F),targetagonist(A,C).
interacts(A,B):- enzymeinhibitor(A,F),targetantagonist(B,E),transporterinducer(A,C),targetinducer(A,D),enzymeinducer(B,F).
interacts(A,B):- targetantagonist(B,E),transporterinducer(B,F),targetinducer(B,C),transporterinducer(A,D),targetagonist(A,C).
interacts(A,B):- enzyme(D,B),enzymesubstrate(B,D),transporterinducer(A,C),targetinhibitor(B,E),enzymeinducer(B,F).
interacts(A,B):- transporter(D,B),enzymeinducer(A,C),targetantagonist(B,E),target(E,B),transporterinducer(A,F).
interacts(A,B):- transportersubstrate(B,D),transporterinducer(B,C),transporter(E,B),target(F,A).
interacts(A,B):- targetinducer(B,E),enzymeinhibitor(B,F),enzymeinhibitor(A,D),transporterinducer(A,C).
interacts(A,B):- targetantagonist(B,C),target(D,B),target(E,A),targetinhibitor(B,D).
interacts(A,B):- targetantagonist(B,C),enzymeinducer(A,D),enzymesubstrate(B,D),target(E,B),enzymeinducer(B,F).
