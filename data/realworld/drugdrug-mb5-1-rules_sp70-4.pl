interacts(A,B):- targetantagonist(B,E),transportersubstrate(B,F),target(C,B),targetagonist(B,C),enzyme(D,A).
interacts(A,B):- transporter(C,B),targetagonist(B,E),target(D,A),target(E,B),targetantagonist(B,F).
interacts(A,B):- targetantagonist(A,C),targetantagonist(A,D),targetantagonist(B,E),target(C,B),enzymeinducer(A,F).
interacts(A,B):- transporterinducer(A,F),transporterinducer(B,E),targetinducer(B,D),targetagonist(B,C).
interacts(A,B):- targetantagonist(B,E),targetagonist(A,C),targetinhibitor(A,E),enzymeinhibitor(A,D),enzyme(D,A).
interacts(A,B):- targetantagonist(B,C),target(D,A),enzymeinhibitor(A,F),transporter(E,A),target(D,B).
interacts(A,B):- targetagonist(B,D),transporter(E,B),target(D,A),targetinducer(B,D),targetagonist(A,C).
interacts(A,B):- targetinhibitor(A,D),target(E,B),targetinducer(A,C),targetinducer(B,F).
interacts(A,B):- transporter(D,B),targetantagonist(B,E),transporter(D,A),enzymeinhibitor(B,C),target(F,B).
interacts(A,B):- enzymesubstrate(B,C),enzymeinducer(A,D),transporterinducer(A,E),targetinhibitor(A,F).
interacts(A,B):- enzyme(C,A),enzymeinducer(B,E),enzymesubstrate(A,F),transporter(D,A).
interacts(A,B):- targetinducer(B,E),enzymeinducer(A,C),enzymesubstrate(A,D),target(E,A),targetantagonist(B,E).
interacts(A,B):- transportersubstrate(B,D),transporterinducer(A,D),targetinhibitor(A,C),targetagonist(A,C).
interacts(A,B):- targetagonist(A,D),enzymesubstrate(A,C),target(D,A),enzymesubstrate(A,E),target(D,B).
interacts(A,B):- targetinducer(A,F),targetinhibitor(A,C),enzymesubstrate(A,D),enzymesubstrate(B,D),targetantagonist(B,E).
interacts(A,B):- enzyme(E,B),enzymeinducer(A,C),target(D,A),enzymeinhibitor(B,C),transporterinducer(A,F).
interacts(A,B):- targetinducer(B,C),enzymeinhibitor(B,D),transporterinducer(B,E),transportersubstrate(A,E).
interacts(A,B):- targetinducer(A,E),target(D,A),enzymeinhibitor(B,C),enzymeinducer(B,C),transportersubstrate(B,F).
interacts(A,B):- targetagonist(A,D),transporter(F,A),transporter(C,A),target(D,A),transporterinhibitor(B,E).
interacts(A,B):- targetinducer(A,E),targetagonist(B,D),transporterinhibitor(B,F),transporter(C,A).
interacts(A,B):- targetantagonist(B,F),targetinhibitor(B,C),target(D,A),enzymesubstrate(A,E),enzyme(E,A).
interacts(A,B):- enzymesubstrate(B,D),targetagonist(A,C),transportersubstrate(B,F),transportersubstrate(A,E),enzyme(D,A).
interacts(A,B):- enzyme(C,B),targetantagonist(B,E),target(E,B),enzymeinhibitor(B,D),transporterinhibitor(A,F).
interacts(A,B):- targetantagonist(B,C),targetagonist(A,D),transporterinhibitor(A,F),transportersubstrate(A,E).
interacts(A,B):- enzyme(C,A),target(D,A),enzymeinhibitor(A,C),targetantagonist(A,F),transportersubstrate(B,E).
interacts(A,B):- enzyme(E,B),enzyme(F,B),enzymesubstrate(B,D),enzymesubstrate(A,E),targetinducer(B,C).
interacts(A,B):- enzymeinducer(A,E),targetagonist(A,D),target(D,A),targetantagonist(B,F),targetagonist(B,C).
interacts(A,B):- transporterinhibitor(A,E),target(C,B),transporter(E,B),enzymeinducer(B,D).
interacts(A,B):- targetagonist(B,D),transporterinhibitor(B,C),transporter(C,A),targetantagonist(B,E),targetantagonist(B,F).
interacts(A,B):- transporter(E,B),targetantagonist(A,D),target(D,A),transporterinducer(A,C),targetinhibitor(B,D).
interacts(A,B):- transporterinhibitor(B,C),target(F,A),enzymesubstrate(B,D),transporterinhibitor(B,E),transporterinhibitor(A,E).
interacts(A,B):- enzymeinhibitor(B,C),targetinhibitor(A,D),target(E,A),targetantagonist(A,E).
interacts(A,B):- enzyme(C,B),enzyme(F,B),targetantagonist(A,D),target(E,A),targetantagonist(B,E).
interacts(A,B):- transportersubstrate(A,D),target(C,B),targetantagonist(A,C),transporter(E,A).
interacts(A,B):- transportersubstrate(B,D),transporterinhibitor(A,F),transporterinducer(A,C),transporterinhibitor(A,E).
interacts(A,B):- enzyme(E,B),enzymesubstrate(B,C),target(D,A),enzymeinducer(B,C),enzyme(E,A).
interacts(A,B):- target(E,B),targetinducer(A,C),transporterinhibitor(A,F),enzymesubstrate(A,D).
interacts(A,B):- transporterinhibitor(B,D),transportersubstrate(B,E),targetinhibitor(A,C),targetinhibitor(A,F).
interacts(A,B):- targetagonist(B,D),transporterinhibitor(B,C),targetagonist(A,E),targetantagonist(B,E),transportersubstrate(B,F).
interacts(A,B):- enzyme(C,A),targetinducer(A,E),enzymeinducer(B,D),enzymesubstrate(B,D),enzymeinhibitor(B,D).
interacts(A,B):- transporterinhibitor(A,C),target(E,A),transporterinducer(B,F),transporter(D,A),targetantagonist(B,E).
interacts(A,B):- target(D,A),enzymeinducer(A,C),transporterinducer(B,F),transporterinhibitor(A,F),enzymeinhibitor(A,E).
interacts(A,B):- targetinducer(B,E),enzymesubstrate(A,D),targetantagonist(B,E),targetinhibitor(B,E),target(C,B).
interacts(A,B):- transporterinhibitor(B,C),enzymesubstrate(B,D),transporter(F,A),target(E,B),transporterinhibitor(B,F).
interacts(A,B):- enzyme(C,A),targetagonist(B,D),enzymeinducer(B,C),target(D,A),targetinducer(B,D).
interacts(A,B):- enzyme(E,B),transportersubstrate(A,D),transporterinhibitor(A,C),transporterinhibitor(A,D).
interacts(A,B):- targetagonist(A,D),enzymesubstrate(A,F),targetagonist(A,E),targetagonist(B,C).
interacts(A,B):- enzymeinducer(B,E),enzyme(C,B),enzymesubstrate(A,C),enzyme(D,A).
interacts(A,B):- targetantagonist(B,D),targetagonist(A,E),enzymeinducer(A,C),targetantagonist(B,E),transporterinhibitor(A,F).
interacts(A,B):- enzymeinhibitor(B,C),transporterinhibitor(A,E),transporter(E,B),targetinducer(A,D).
interacts(A,B):- targetinhibitor(A,D),enzyme(E,B),transporterinducer(B,C),enzyme(F,B).
interacts(A,B):- targetinducer(B,F),targetagonist(A,E),target(D,A),targetagonist(B,C),targetagonist(A,C).
interacts(A,B):- targetantagonist(B,C),targetinducer(A,E),transportersubstrate(A,F),transporter(D,A),targetantagonist(B,E).
interacts(A,B):- targetantagonist(B,F),transportersubstrate(A,C),targetinhibitor(B,D),enzymeinhibitor(A,E).
interacts(A,B):- targetinducer(A,E),targetagonist(A,E),enzymesubstrate(B,D),enzymeinhibitor(A,C),targetantagonist(B,F).
interacts(A,B):- targetantagonist(B,C),targetinducer(A,F),enzymesubstrate(B,D),targetinhibitor(B,E),enzymeinhibitor(B,D).
interacts(A,B):- target(C,A),targetinducer(A,E),transporterinhibitor(B,F),transportersubstrate(B,D).
interacts(A,B):- enzyme(C,A),transporterinhibitor(B,F),enzymeinducer(A,D),transporter(E,A).
interacts(A,B):- targetantagonist(B,C),targetinhibitor(A,C),target(E,A),enzymesubstrate(B,D),target(C,A).
interacts(A,B):- transporterinhibitor(A,E),targetagonist(A,D),target(C,B),targetinhibitor(A,C).
interacts(A,B):- targetagonist(B,D),targetinhibitor(A,C),transporter(F,B),target(D,A),transportersubstrate(A,E).
interacts(A,B):- transportersubstrate(B,C),targetantagonist(B,E),targetinhibitor(A,D),target(F,B),transporterinducer(B,C).
interacts(A,B):- targetinducer(A,E),targetagonist(A,E),target(D,A),transporterinhibitor(A,F),enzymeinducer(B,C).
interacts(A,B):- target(C,A),target(C,B),transporterinducer(A,D),targetagonist(A,E).
interacts(A,B):- transportersubstrate(A,E),enzymeinducer(A,F),enzymeinhibitor(B,D),transporter(C,A).
interacts(A,B):- target(D,A),enzyme(C,B),enzymeinducer(A,C),target(E,A),enzymeinducer(A,F).
interacts(A,B):- transporterinducer(B,C),transporterinducer(A,E),targetinducer(A,D).
interacts(A,B):- targetantagonist(B,E),target(D,A),targetinducer(A,C),transporterinducer(A,F),targetagonist(B,C).
interacts(A,B):- transporter(E,B),enzymesubstrate(B,D),transporterinducer(A,E),transportersubstrate(A,C),transporterinhibitor(B,E).
interacts(A,B):- transporterinducer(A,D),transporter(D,B),targetinhibitor(B,C),transportersubstrate(A,E).
