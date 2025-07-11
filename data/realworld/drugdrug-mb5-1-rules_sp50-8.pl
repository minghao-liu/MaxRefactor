interacts(A,B):- enzymesubstrate(B,E),enzymeinducer(A,C),transportersubstrate(A,D),enzyme(E,A).
interacts(A,B):- enzymesubstrate(A,C),enzymesubstrate(B,D),targetagonist(B,F),enzymesubstrate(B,E),enzymeinhibitor(B,E).
interacts(A,B):- enzymesubstrate(A,C),enzyme(C,B),target(D,A),target(D,B),enzymeinhibitor(B,E).
interacts(A,B):- enzyme(D,B),enzymesubstrate(A,C),enzyme(C,B),transporter(F,B),targetantagonist(B,E).
interacts(A,B):- enzymeinducer(A,C),enzymesubstrate(A,D),target(E,A),transportersubstrate(B,F).
interacts(A,B):- enzymeinhibitor(B,C),targetagonist(B,D),transporterinducer(B,E),targetinhibitor(A,F).
interacts(A,B):- targetagonist(B,E),targetinhibitor(A,C),target(D,A),targetinhibitor(A,E),targetinducer(B,D).
interacts(A,B):- target(C,A),transporter(E,B),transporterinhibitor(A,D).
interacts(A,B):- transporterinducer(B,D),targetantagonist(B,E),transportersubstrate(B,D),targetantagonist(A,C),enzymeinducer(B,F).
interacts(A,B):- targetinhibitor(B,E),targetantagonist(B,D),targetinhibitor(A,C),transporterinducer(A,F).
interacts(A,B):- transporter(C,B),targetagonist(B,E),targetantagonist(B,E),transporterinducer(A,D),enzymeinducer(B,F).
interacts(A,B):- enzyme(C,A),enzymesubstrate(B,D),transporterinducer(B,F),enzymeinhibitor(B,D),enzyme(E,A).
interacts(A,B):- enzymesubstrate(A,E),targetagonist(B,D),enzymeinducer(A,C),enzymeinducer(B,E).
interacts(A,B):- transporterinducer(B,E),targetantagonist(A,D),targetinhibitor(B,F),targetagonist(B,C).
interacts(A,B):- target(D,A),targetantagonist(A,E),enzymeinhibitor(A,C),targetinhibitor(B,E),targetinhibitor(B,D).
interacts(A,B):- targetinhibitor(B,C),enzymeinducer(B,D),targetantagonist(B,E),targetantagonist(A,F),targetinhibitor(A,F).
interacts(A,B):- enzyme(D,B),targetinhibitor(A,E),transporter(C,B),enzyme(D,A).
interacts(A,B):- enzymeinhibitor(A,C),transporter(D,B),targetagonist(B,E),transporterinducer(B,F).
interacts(A,B):- targetinducer(A,E),targetinducer(A,C),enzymeinhibitor(A,D),targetinhibitor(B,C).
interacts(A,B):- enzymeinducer(B,E),targetagonist(B,D),targetinhibitor(A,C),target(F,A).
interacts(A,B):- targetinducer(B,E),enzymesubstrate(A,C),transporter(D,A),targetantagonist(B,E),transportersubstrate(A,D).
interacts(A,B):- transporter(C,B),targetagonist(B,E),transporter(C,A),enzymesubstrate(B,D),targetantagonist(B,F).
interacts(A,B):- targetantagonist(B,D),enzymeinducer(B,E),enzymesubstrate(A,C),transportersubstrate(A,F).
interacts(A,B):- targetantagonist(B,D),transporter(C,A),target(F,A),target(D,A),enzymeinhibitor(A,E).
interacts(A,B):- enzyme(C,B),transporter(D,A),targetantagonist(B,E),transporterinducer(A,F),transportersubstrate(B,F).
interacts(A,B):- enzymesubstrate(B,C),targetantagonist(A,D),targetinducer(B,D),enzymeinducer(A,C).
interacts(A,B):- enzymeinducer(A,E),enzymeinducer(B,E),enzymesubstrate(B,D),enzymeinhibitor(A,C),targetinhibitor(B,F).
interacts(A,B):- enzymesubstrate(B,C),enzyme(D,B),enzymeinducer(B,D),enzymeinducer(A,C).
interacts(A,B):- enzyme(C,A),enzymesubstrate(A,C),enzymesubstrate(B,D),targetantagonist(B,F),enzymeinhibitor(A,E).
interacts(A,B):- targetinducer(A,E),transporterinhibitor(B,C),transporter(F,B),target(D,A),target(D,B).
interacts(A,B):- targetinhibitor(A,C),targetagonist(B,E),enzymeinducer(A,F),enzyme(D,A).
interacts(A,B):- transporterinhibitor(A,E),transporterinhibitor(B,F),enzymeinhibitor(A,D),targetagonist(B,C).
interacts(A,B):- enzymesubstrate(B,D),transporter(E,A),transporterinhibitor(B,E),transporterinhibitor(A,E),targetinducer(B,C).
interacts(A,B):- enzymeinducer(A,E),target(D,A),transporterinhibitor(A,C),transportersubstrate(A,C),transporterinhibitor(B,F).
interacts(A,B):- target(F,B),targetagonist(A,C),targetinducer(B,E),enzyme(D,A).
interacts(A,B):- enzyme(C,A),enzymesubstrate(B,D),enzymesubstrate(A,E),targetantagonist(A,F),enzymeinhibitor(B,D).
interacts(A,B):- enzymeinhibitor(B,C),transportersubstrate(B,E),enzymeinducer(A,F),targetinducer(B,D).
interacts(A,B):- enzyme(E,B),enzymesubstrate(A,C),transportersubstrate(B,D),targetinhibitor(A,F).
interacts(A,B):- enzymesubstrate(B,D),targetantagonist(B,E),targetagonist(A,C),targetinhibitor(B,F),enzyme(D,A).
interacts(A,B):- targetantagonist(B,C),enzymesubstrate(B,D),targetantagonist(B,E),transporterinhibitor(A,F),targetagonist(A,C).
interacts(A,B):- targetinducer(A,E),transportersubstrate(A,D),transporterinducer(B,D),transporter(C,A).
interacts(A,B):- targetantagonist(B,C),targetagonist(B,D),transporterinhibitor(A,F),transportersubstrate(A,E).
interacts(A,B):- transporterinhibitor(B,E),transportersubstrate(A,D),targetinducer(A,C),targetinhibitor(B,F).
interacts(A,B):- transporterinhibitor(A,E),transporterinducer(A,C),transportersubstrate(B,C),transporterinhibitor(A,D).
interacts(A,B):- enzyme(C,A),transporterinducer(A,D),transporter(E,B),transporterinducer(B,F).
interacts(A,B):- enzyme(C,A),enzymeinducer(A,C),targetantagonist(B,E),targetagonist(A,F),enzyme(D,A).
interacts(A,B):- targetagonist(A,F),targetinducer(A,C),transportersubstrate(B,E),targetinducer(A,D).
interacts(A,B):- enzymesubstrate(B,C),transporterinducer(A,F),transporterinducer(B,E),enzymesubstrate(B,D).
interacts(A,B):- targetantagonist(B,F),transporter(C,B),targetinducer(A,E),transporterinhibitor(A,D).
interacts(A,B):- targetantagonist(A,C),transporter(E,B),target(D,A),target(D,B),targetinducer(B,D).
