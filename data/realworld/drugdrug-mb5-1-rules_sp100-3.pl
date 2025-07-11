interacts(A,B):- targetinducer(B,E),enzymeinducer(A,C),target(D,A),transporterinhibitor(A,F),transportersubstrate(B,F).
interacts(A,B):- transporterinhibitor(B,E),enzymesubstrate(B,C),targetinducer(B,F),targetantagonist(A,D).
interacts(A,B):- targetinhibitor(A,D),enzymeinhibitor(A,C),targetinhibitor(A,E),transporter(F,B).
interacts(A,B):- enzymeinhibitor(A,F),transporter(D,B),targetinhibitor(B,E),transporter(C,A).
interacts(A,B):- targetinducer(A,F),targetinhibitor(A,C),target(D,A),target(C,B),enzymeinhibitor(B,E).
interacts(A,B):- targetagonist(A,D),enzymesubstrate(B,C),targetantagonist(B,D),target(D,A),target(D,B).
interacts(A,B):- targetagonist(B,D),targetinhibitor(A,E),targetinhibitor(A,C),enzymeinducer(B,F).
interacts(A,B):- transporterinducer(B,E),transporter(C,A),enzymesubstrate(B,D),enzyme(F,A),transportersubstrate(A,E).
interacts(A,B):- targetantagonist(B,C),enzymesubstrate(B,F),transporterinducer(A,D),enzymeinhibitor(A,E).
interacts(A,B):- transporterinhibitor(A,C),targetagonist(A,E),targetantagonist(B,E),transporterinhibitor(A,D).
interacts(A,B):- targetinhibitor(A,E),targetinducer(B,C),targetinducer(B,F),targetinducer(B,D).
interacts(A,B):- transporterinhibitor(A,E),targetantagonist(B,D),transporter(C,A),transportersubstrate(A,C).
interacts(A,B):- targetinducer(B,E),transporter(D,B),enzyme(C,B),enzymeinducer(A,C),targetantagonist(B,E).
interacts(A,B):- targetagonist(B,D),enzymeinhibitor(A,F),transporterinhibitor(A,C),enzyme(F,B),targetantagonist(B,E).
interacts(A,B):- targetinhibitor(B,C),targetantagonist(B,E),transporterinducer(B,F),transportersubstrate(A,D),targetinducer(A,C).
interacts(A,B):- transporterinhibitor(B,E),targetagonist(A,D),targetagonist(B,C),targetinhibitor(A,F).
interacts(A,B):- enzymeinducer(A,D),enzymeinducer(B,D),transporter(C,A),enzymesubstrate(B,D),enzyme(E,A).
interacts(A,B):- targetinducer(B,C),enzymesubstrate(A,F),enzymeinhibitor(B,E),transporterinhibitor(A,D).
interacts(A,B):- targetantagonist(B,C),targetagonist(B,E),target(E,A),targetantagonist(B,E),target(D,B).
interacts(A,B):- transporterinhibitor(B,E),targetagonist(B,D),enzymesubstrate(B,C),targetantagonist(A,F).
interacts(A,B):- transporterinhibitor(B,E),enzymeinducer(A,C),enzymeinducer(A,D),enzymesubstrate(A,D).
interacts(A,B):- enzymeinducer(B,D),targetantagonist(B,E),targetagonist(A,F),target(E,B),targetantagonist(A,C).
interacts(A,B):- transporterinhibitor(B,E),transporterinducer(B,C),enzymeinducer(A,D),targetinducer(B,F).
interacts(A,B):- transporter(D,B),enzymeinducer(A,C),targetantagonist(B,E),transportersubstrate(B,D),targetantagonist(A,F).
interacts(A,B):- target(D,A),transporterinducer(B,C),transportersubstrate(A,E),targetinducer(A,D),target(D,B).
interacts(A,B):- target(F,B),transporterinhibitor(A,E),enzymesubstrate(B,C),enzymeinhibitor(A,D).
interacts(A,B):- transportersubstrate(A,F),targetantagonist(B,E),targetinducer(B,C),enzymeinhibitor(B,D),targetantagonist(A,C).
interacts(A,B):- targetagonist(A,C),enzymeinhibitor(B,F),transporter(D,A),targetantagonist(B,E).
interacts(A,B):- target(E,B),targetantagonist(A,C),enzyme(F,A),targetinducer(A,D).
interacts(A,B):- transportersubstrate(A,F),transporterinhibitor(B,C),targetagonist(A,D),targetagonist(B,E).
interacts(A,B):- transporter(F,A),target(D,B),enzymeinhibitor(B,C),targetantagonist(A,E).
interacts(A,B):- enzymeinducer(B,E),enzymesubstrate(B,D),enzymeinhibitor(B,C),enzyme(F,A),enzymeinhibitor(B,E).
interacts(A,B):- transportersubstrate(A,F),enzyme(C,B),target(D,A),transporterinhibitor(B,E),transporterinhibitor(A,F).
interacts(A,B):- target(D,A),targetagonist(A,D),transportersubstrate(B,C),transportersubstrate(A,C),targetinhibitor(A,D).
interacts(A,B):- target(C,A),enzyme(F,B),enzymesubstrate(B,D),enzymesubstrate(B,E).
interacts(A,B):- enzymeinhibitor(B,D),enzymesubstrate(B,F),enzyme(E,A),targetinducer(A,C).
interacts(A,B):- target(F,A),targetantagonist(B,E),targetinducer(A,C),transporterinducer(A,D),targetagonist(B,C).
interacts(A,B):- enzymesubstrate(A,C),target(D,A),enzymesubstrate(B,E),enzymeinhibitor(A,C),enzymeinhibitor(B,E).
interacts(A,B):- targetinducer(A,E),target(D,A),enzymeinhibitor(B,C),target(D,B),targetinhibitor(B,F).
interacts(A,B):- enzymeinhibitor(A,C),targetantagonist(B,D),transporterinhibitor(A,F),enzymeinducer(B,E).
interacts(A,B):- enzymesubstrate(A,E),transporter(C,B),enzyme(F,A),transporterinhibitor(A,D).
interacts(A,B):- targetinducer(A,F),transportersubstrate(A,E),targetagonist(B,C),enzyme(D,A).
interacts(A,B):- target(E,B),targetagonist(A,D),targetinducer(B,F),targetantagonist(A,C).
interacts(A,B):- targetinducer(A,E),enzymesubstrate(B,D),transporterinducer(A,C),enzyme(F,A),enzymeinducer(B,F).
interacts(A,B):- enzymeinducer(B,E),targetinducer(A,C),enzymeinducer(A,F),enzyme(D,A).
interacts(A,B):- targetagonist(B,D),targetantagonist(A,F),transporter(E,B),transporterinhibitor(B,C).
interacts(A,B):- transporter(F,A),enzymeinducer(B,D),transportersubstrate(B,C),transporter(E,A).
interacts(A,B):- targetagonist(B,D),targetinducer(B,F),targetantagonist(B,E),target(D,A),transporterinducer(B,C).
interacts(A,B):- targetagonist(A,D),targetagonist(A,E),target(E,A),targetantagonist(B,E),enzymeinducer(B,C).
interacts(A,B):- targetantagonist(B,C),transporterinducer(B,E),transporter(E,B),target(D,A),targetinhibitor(B,F).
interacts(A,B):- transporterinhibitor(A,C),enzymeinducer(B,D),enzymesubstrate(B,D),enzymesubstrate(A,E),transporterinhibitor(B,F).
interacts(A,B):- transporter(C,B),enzymesubstrate(B,D),enzymesubstrate(A,D),transportersubstrate(A,C),transporterinhibitor(A,E).
interacts(A,B):- targetagonist(B,D),transporterinducer(B,E),targetinhibitor(B,C),target(D,A),targetinhibitor(B,D).
interacts(A,B):- enzymeinhibitor(A,F),targetantagonist(A,D),target(D,A),enzymeinducer(B,C),enzyme(E,A).
interacts(A,B):- enzyme(C,A),enzymeinducer(A,D),enzymesubstrate(A,C),enzymesubstrate(B,D).
interacts(A,B):- enzyme(F,B),targetantagonist(B,E),transportersubstrate(B,D),transportersubstrate(A,D),targetagonist(B,C).
interacts(A,B):- enzymeinhibitor(A,F),enzymeinducer(A,D),enzyme(C,B),targetantagonist(B,E),enzymesubstrate(A,F).
interacts(A,B):- transportersubstrate(B,D),targetinducer(B,F),targetantagonist(A,C),transporterinhibitor(A,E).
interacts(A,B):- enzymeinducer(B,E),targetantagonist(A,F),target(C,B),enzyme(D,A).
interacts(A,B):- enzymeinducer(A,E),transportersubstrate(A,F),transporter(F,B),target(D,A),targetinducer(B,C).
interacts(A,B):- enzymeinducer(B,D),enzymesubstrate(B,D),targetinhibitor(B,C),target(C,A),transporterinhibitor(A,E).
interacts(A,B):- target(F,A),targetantagonist(B,E),targetagonist(B,F),transporterinducer(B,C),transporterinducer(A,D).
interacts(A,B):- transportersubstrate(A,E),enzymeinducer(A,D),enzymesubstrate(B,F),targetinhibitor(A,C).
interacts(A,B):- enzyme(C,A),targetinducer(A,E),targetinducer(A,F),enzymesubstrate(B,D),target(F,B).
interacts(A,B):- enzymesubstrate(B,C),targetinducer(B,F),target(D,A),targetantagonist(B,F),transportersubstrate(A,E).
interacts(A,B):- transportersubstrate(B,D),enzymesubstrate(A,C),transportersubstrate(B,E),transportersubstrate(A,E).
interacts(A,B):- targetinducer(B,E),targetagonist(B,D),transporter(C,B),target(D,A),transporterinducer(B,C).
interacts(A,B):- enzymeinducer(B,F),transporterinducer(A,C),enzymeinhibitor(A,D),enzyme(E,A).
interacts(A,B):- target(C,A),enzymeinhibitor(B,F),targetinhibitor(A,E),transporterinducer(A,D).
interacts(A,B):- transporterinhibitor(B,C),target(D,A),targetinhibitor(A,D),targetinducer(B,D),targetinducer(A,D).
interacts(A,B):- targetagonist(A,E),transporterinhibitor(B,D),transporter(F,B),targetantagonist(B,E),targetagonist(B,C).
interacts(A,B):- targetagonist(A,D),enzymesubstrate(B,F),transporterinhibitor(B,C),transporterinducer(B,E).
interacts(A,B):- transporterinducer(B,E),targetinhibitor(B,C),target(D,A),targetantagonist(A,F),targetinhibitor(A,F).
interacts(A,B):- targetinhibitor(A,C),target(E,A),target(F,A),enzymesubstrate(B,D),enzymeinhibitor(B,D).
interacts(A,B):- targetinducer(B,E),enzyme(D,B),targetantagonist(A,F),targetinhibitor(B,C).
interacts(A,B):- transporter(D,A),transportersubstrate(B,F),enzyme(E,A),transportersubstrate(A,C).
interacts(A,B):- enzyme(C,B),targetinhibitor(B,D),target(D,A),transporterinhibitor(A,F),transportersubstrate(A,E).
interacts(A,B):- target(D,A),transporter(E,A),targetinducer(A,C),target(C,B),enzyme(F,A).
interacts(A,B):- enzymeinhibitor(B,D),target(C,B),enzymeinducer(B,D),targetinhibitor(A,C).
interacts(A,B):- targetagonist(B,D),targetantagonist(B,E),transportersubstrate(A,C),target(E,B),targetinhibitor(B,E).
interacts(A,B):- target(D,A),transporter(C,B),transporter(E,A),targetinhibitor(B,F),targetinhibitor(A,F).
interacts(A,B):- target(D,A),transporter(F,B),enzymeinducer(A,C),targetantagonist(B,E),targetinhibitor(B,E).
interacts(A,B):- enzymeinducer(A,E),transporter(C,B),transporterinhibitor(A,C),transporter(C,A),enzymesubstrate(B,D).
interacts(A,B):- targetinducer(A,E),transporter(C,A),enzymesubstrate(B,D),transporterinducer(B,C),enzymeinhibitor(A,D).
interacts(A,B):- enzyme(C,B),target(F,B),target(D,A),transporterinhibitor(B,E),enzymeinducer(B,C).
interacts(A,B):- target(C,A),enzymeinducer(B,E),enzymeinhibitor(A,D),transporterinducer(B,F).
interacts(A,B):- transportersubstrate(A,F),transporter(C,A),transporter(F,B),targetantagonist(B,E),transporterinducer(A,D).
interacts(A,B):- enzymesubstrate(B,C),targetagonist(A,E),targetantagonist(B,E),targetinhibitor(B,F),enzyme(D,A).
interacts(A,B):- enzymeinducer(A,E),enzymeinhibitor(A,F),target(D,A),enzymeinducer(B,C),targetinducer(A,D).
interacts(A,B):- targetinducer(B,D),transportersubstrate(B,C),target(D,A),transporterinhibitor(A,E),transportersubstrate(A,E).
interacts(A,B):- transportersubstrate(A,F),enzymeinhibitor(A,C),transportersubstrate(B,E),transportersubstrate(B,D).
interacts(A,B):- targetinducer(A,F),targetinhibitor(B,C),enzymesubstrate(B,D),enzymesubstrate(A,E),targetinhibitor(B,F).
interacts(A,B):- targetagonist(A,C),transporterinhibitor(B,E),transporterinhibitor(A,D),transporter(E,A).
interacts(A,B):- enzymesubstrate(B,E),transporterinhibitor(A,C),enzymeinducer(B,D),transportersubstrate(B,C).
interacts(A,B):- targetantagonist(B,C),targetinducer(A,E),transporter(F,B),target(D,A),targetinhibitor(B,E).
interacts(A,B):- enzymeinducer(B,E),target(D,A),enzymeinhibitor(B,C),enzymeinducer(B,F),enzymeinhibitor(A,E).
interacts(A,B):- enzymesubstrate(B,D),enzymesubstrate(B,E),enzymeinhibitor(A,C),targetantagonist(A,F),enzyme(E,A).
interacts(A,B):- targetinhibitor(A,D),enzyme(E,B),enzyme(C,B),enzyme(F,A).
interacts(A,B):- targetinducer(A,E),enzyme(F,B),targetinhibitor(B,C),targetantagonist(B,E),transporterinhibitor(A,D).
interacts(A,B):- targetinducer(B,E),target(D,A),transporterinducer(B,F),transporterinducer(B,C),transporterinducer(A,F).
