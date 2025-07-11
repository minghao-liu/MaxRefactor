interacts(A,B):- enzymesubstrate(B,D),targetantagonist(B,E),target(C,A),targetantagonist(A,C),enzymeinducer(B,F).
interacts(A,B):- enzyme(F,B),target(D,A),targetinducer(B,C),transportersubstrate(A,E),targetagonist(B,C).
interacts(A,B):- target(C,A),targetantagonist(B,F),transportersubstrate(A,D),transporterinhibitor(A,E).
interacts(A,B):- target(D,A),transporter(E,B),transporter(E,A),enzymeinhibitor(B,C),enzymeinducer(B,F).
interacts(A,B):- targetantagonist(B,C),enzymesubstrate(A,D),targetantagonist(B,E),targetantagonist(A,F),targetinducer(A,C).
interacts(A,B):- targetinhibitor(A,D),enzyme(F,B),target(E,A),enzymeinducer(B,C).
interacts(A,B):- target(E,A),targetantagonist(B,E),transportersubstrate(A,D),targetinhibitor(B,F),targetagonist(A,C).
interacts(A,B):- targetinducer(A,F),targetagonist(A,E),transporterinhibitor(B,D),targetinhibitor(B,C),targetantagonist(B,E).
interacts(A,B):- targetinducer(B,E),targetagonist(B,F),enzymesubstrate(B,D),targetantagonist(A,E),targetagonist(A,C).
interacts(A,B):- targetinducer(B,E),transporter(C,A),transportersubstrate(B,C),target(D,A),targetinhibitor(A,D).
interacts(A,B):- transportersubstrate(A,F),targetagonist(B,E),target(D,A),targetantagonist(A,C),targetagonist(A,C).
interacts(A,B):- targetinducer(A,E),targetagonist(A,D),transporterinhibitor(B,F),transportersubstrate(B,C).
interacts(A,B):- transporter(F,A),enzyme(C,B),enzymeinducer(B,D),enzymeinhibitor(A,E).
interacts(A,B):- transporter(F,A),enzymesubstrate(A,E),transportersubstrate(A,D),targetagonist(B,C).
interacts(A,B):- targetinducer(A,E),enzymeinducer(B,D),enzymeinducer(A,C),targetantagonist(B,E),targetantagonist(A,F).
interacts(A,B):- targetantagonist(B,C),targetagonist(B,D),targetinducer(B,E),target(D,A),enzymeinducer(A,F).
interacts(A,B):- targetagonist(B,D),target(F,A),target(D,A),enzymesubstrate(B,E),transporterinducer(A,C).
interacts(A,B):- enzymeinhibitor(B,C),transporterinducer(A,D),targetagonist(B,E),target(E,A).
interacts(A,B):- targetinducer(A,E),targetagonist(A,D),transporterinducer(B,C),target(E,A).
interacts(A,B):- enzyme(C,A),enzymeinhibitor(B,E),enzymesubstrate(B,E),targetinhibitor(B,D).
interacts(A,B):- enzyme(C,B),transporter(F,A),transporter(D,A),transporterinducer(B,F),targetantagonist(B,E).
interacts(A,B):- targetantagonist(B,C),targetinhibitor(B,C),target(D,A),targetinhibitor(B,E),targetinhibitor(B,D).
interacts(A,B):- enzymesubstrate(B,D),target(F,B),targetantagonist(B,F),targetinhibitor(A,E),targetagonist(A,C).
interacts(A,B):- enzymeinhibitor(B,C),transportersubstrate(B,F),targetantagonist(B,E),enzyme(D,A).
interacts(A,B):- enzymeinducer(B,F),enzymeinhibitor(B,E),transporter(C,A),transporter(D,A).
interacts(A,B):- transporterinhibitor(B,E),targetinducer(B,C),target(F,A),targetinhibitor(B,D).
interacts(A,B):- targetinducer(A,E),targetagonist(A,D),enzymesubstrate(A,C),targetinducer(B,F),targetantagonist(B,E).
interacts(A,B):- enzymesubstrate(B,D),enzymeinducer(A,C),transporter(E,A),transporter(F,A),transporterinhibitor(A,E).
interacts(A,B):- enzyme(D,B),transportersubstrate(B,C),enzymeinducer(B,F),targetantagonist(A,E).
interacts(A,B):- targetagonist(B,F),transporterinhibitor(A,C),target(D,A),targetinhibitor(A,F),enzymeinhibitor(A,E).
interacts(A,B):- enzymeinhibitor(B,C),enzymesubstrate(A,E),transportersubstrate(A,D),enzymeinducer(A,F).
interacts(A,B):- targetantagonist(B,E),transporterinducer(B,F),transporterinducer(A,D),transporterinhibitor(A,F),targetagonist(B,C).
interacts(A,B):- targetinhibitor(B,E),enzymeinducer(B,D),targetagonist(B,C),targetagonist(A,C).
interacts(A,B):- targetagonist(B,D),targetinducer(A,F),targetantagonist(B,E),targetagonist(B,F),targetantagonist(A,C).
interacts(A,B):- targetagonist(B,D),transporterinhibitor(B,C),transportersubstrate(B,E),target(F,A).
interacts(A,B):- targetinducer(B,E),transporter(D,B),targetantagonist(B,E),targetinducer(B,C),transporterinducer(A,F).
interacts(A,B):- enzymesubstrate(B,D),transporterinducer(B,F),enzymesubstrate(B,E),target(C,B),enzyme(D,A).
interacts(A,B):- targetinhibitor(B,C),target(D,A),target(E,B),target(D,B),targetinhibitor(A,F).
interacts(A,B):- targetinducer(B,E),targetantagonist(A,D),targetantagonist(B,E),transporter(F,A),enzymeinhibitor(A,C).
interacts(A,B):- targetinducer(B,E),targetinducer(A,E),targetantagonist(A,C),enzyme(D,A).
