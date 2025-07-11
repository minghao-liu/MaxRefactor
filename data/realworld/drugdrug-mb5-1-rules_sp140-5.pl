interacts(A,B):- targetinhibitor(A,D),target(E,B),targetinducer(A,E),targetantagonist(A,C).
interacts(A,B):- targetagonist(B,D),enzymesubstrate(A,C),targetantagonist(A,D),transporterinducer(B,E),target(D,A).
interacts(A,B):- enzymeinhibitor(A,F),transporterinhibitor(B,D),targetantagonist(B,E),enzymeinhibitor(B,C),enzymesubstrate(A,F).
interacts(A,B):- targetinhibitor(A,C),enzymesubstrate(B,D),targetantagonist(A,E),targetantagonist(B,E),targetagonist(B,C).
interacts(A,B):- transportersubstrate(A,C),targetantagonist(B,D),target(E,A),targetagonist(B,F).
interacts(A,B):- target(D,B),transporterinducer(B,F),targetantagonist(A,C),enzymeinhibitor(A,E).
interacts(A,B):- targetantagonist(B,C),targetinducer(A,E),targetagonist(B,D),targetantagonist(A,E).
interacts(A,B):- targetantagonist(B,C),enzymesubstrate(B,D),enzymesubstrate(B,E),enzymesubstrate(A,E),targetagonist(A,C).
interacts(A,B):- target(D,A),targetagonist(A,E),transporterinducer(B,F),targetinhibitor(B,E),targetagonist(A,C).
interacts(A,B):- targetinducer(B,E),transporter(C,B),targetantagonist(B,E),target(F,B),targetinducer(A,D).
interacts(A,B):- enzyme(C,A),targetantagonist(A,D),targetantagonist(B,E),targetagonist(A,F),targetinhibitor(A,E).
interacts(A,B):- enzymesubstrate(A,C),transportersubstrate(B,E),targetinhibitor(B,F),target(D,A).
interacts(A,B):- enzyme(F,B),transporter(C,A),enzymesubstrate(B,D),transporterinducer(B,C),enzymeinhibitor(B,E).
interacts(A,B):- target(D,A),transporterinducer(B,F),targetinducer(B,C),targetinducer(A,C),transportersubstrate(B,E).
interacts(A,B):- enzymesubstrate(B,D),transporterinhibitor(B,F),enzymeinhibitor(A,D),targetantagonist(A,C),enzymeinhibitor(B,E).
interacts(A,B):- targetantagonist(A,F),targetantagonist(B,D),targetantagonist(A,C),targetantagonist(B,E).
interacts(A,B):- enzymesubstrate(A,C),transportersubstrate(B,E),transporterinhibitor(A,F),enzyme(D,A).
interacts(A,B):- targetinducer(A,E),transporterinducer(B,D),enzyme(C,B),targetantagonist(B,E),targetantagonist(A,E).
interacts(A,B):- targetinducer(A,D),transporterinducer(B,C),transporter(C,A),enzyme(E,A).
interacts(A,B):- enzymeinducer(B,D),enzymesubstrate(B,D),enzymesubstrate(A,D),enzymeinhibitor(B,D),targetagonist(A,C).
interacts(A,B):- enzymeinducer(B,D),targetantagonist(B,E),transporterinducer(B,F),targetinducer(B,C),transporterinhibitor(A,F).
interacts(A,B):- enzymeinducer(A,D),targetagonist(B,E),enzymesubstrate(B,D),enzymeinhibitor(A,C),targetinhibitor(A,E).
interacts(A,B):- enzyme(C,B),enzymesubstrate(A,C),targetantagonist(B,E),target(D,A).
interacts(A,B):- transporter(C,B),targetinducer(B,F),targetinducer(A,D),enzymeinhibitor(A,E).
interacts(A,B):- targetinducer(A,E),transporter(C,B),enzymeinducer(A,D),enzyme(F,B).
interacts(A,B):- enzyme(C,B),transporterinhibitor(A,D),targetagonist(B,F),targetantagonist(B,E),transporterinducer(A,D).
interacts(A,B):- transporterinducer(A,C),enzyme(D,B),enzymesubstrate(B,F),targetantagonist(A,E).
interacts(A,B):- targetagonist(A,D),targetagonist(A,E),transportersubstrate(B,C),transporterinducer(B,F).
interacts(A,B):- enzymeinducer(A,E),transporterinhibitor(A,C),transporterinhibitor(B,D),enzyme(E,A).
interacts(A,B):- targetagonist(B,D),targetantagonist(B,E),transporterinducer(B,C),enzyme(F,A),targetinducer(A,D).
interacts(A,B):- targetinducer(A,E),targetagonist(B,E),target(D,A),transporterinducer(B,C),targetinhibitor(B,D).
interacts(A,B):- enzyme(C,A),transporterinhibitor(A,E),enzyme(F,B),transporterinducer(B,D).
interacts(A,B):- targetagonist(A,D),targetantagonist(B,E),targetinhibitor(B,E),targetinducer(A,C),enzyme(F,A).
interacts(A,B):- targetantagonist(B,D),transporterinducer(B,E),target(D,A),transporterinhibitor(B,E),targetantagonist(A,C).
interacts(A,B):- enzymeinhibitor(A,F),transporter(D,B),targetinhibitor(B,C),transporterinducer(B,E).
interacts(A,B):- transportersubstrate(A,E),enzymeinhibitor(B,D),targetinducer(B,F),targetinhibitor(A,C).
interacts(A,B):- targetantagonist(B,E),enzymeinhibitor(B,C),target(E,B),target(D,B),targetinhibitor(A,E).
interacts(A,B):- targetinhibitor(A,E),targetinducer(B,C),enzymeinducer(A,D),enzymesubstrate(A,D).
interacts(A,B):- enzyme(C,A),targetinducer(B,F),targetantagonist(A,D),enzymeinhibitor(A,E).
interacts(A,B):- targetagonist(A,E),transporterinhibitor(B,D),targetantagonist(A,E),targetantagonist(B,E),targetantagonist(A,C).
interacts(A,B):- enzymesubstrate(A,E),enzymeinhibitor(B,D),targetinducer(A,F),targetagonist(A,C).
interacts(A,B):- enzyme(C,B),target(D,A),target(F,B),targetantagonist(B,F),transportersubstrate(B,E).
interacts(A,B):- enzymeinhibitor(A,F),enzymesubstrate(A,D),transportersubstrate(B,C),targetantagonist(B,E),transporterinducer(B,C).
interacts(A,B):- transporterinducer(B,D),targetantagonist(B,E),enzymeinhibitor(A,C),targetinhibitor(B,E),targetantagonist(B,F).
interacts(A,B):- transporterinhibitor(B,C),targetagonist(A,E),target(D,A).
interacts(A,B):- enzyme(E,B),enzymeinducer(A,C),target(D,A),target(F,B),target(D,B).
interacts(A,B):- targetinducer(B,E),enzyme(C,B),transporter(D,A),targetantagonist(B,E),transporter(F,A).
interacts(A,B):- enzymeinhibitor(B,C),enzymeinducer(A,D),targetagonist(A,E),targetantagonist(B,E).
interacts(A,B):- enzyme(C,A),enzymesubstrate(A,E),transporter(D,B),enzymeinducer(B,C).
interacts(A,B):- transportersubstrate(A,C),enzymesubstrate(B,D),enzymesubstrate(A,D),transporterinducer(B,F),transporterinhibitor(A,E).
interacts(A,B):- targetinducer(A,F),targetinducer(B,D),target(D,A),enzymeinhibitor(B,C),transportersubstrate(A,E).
interacts(A,B):- targetagonist(A,F),enzymeinducer(A,C),transportersubstrate(B,D),enzymeinhibitor(B,E).
interacts(A,B):- transporterinhibitor(B,C),transporterinducer(B,E),target(F,A),target(D,A),targetantagonist(A,F).
interacts(A,B):- targetantagonist(A,C),enzyme(D,B),targetantagonist(B,E),enzymeinhibitor(B,D),enzymeinducer(A,F).
interacts(A,B):- enzymeinducer(B,C),target(D,A),enzymeinhibitor(A,C),enzymesubstrate(A,E),targetinducer(B,D).
interacts(A,B):- targetagonist(B,D),target(E,A),target(D,A),enzymeinhibitor(A,C),target(D,B).
interacts(A,B):- targetagonist(B,D),targetantagonist(B,E),targetinhibitor(B,D),enzymeinhibitor(B,C),enzymeinducer(A,F).
interacts(A,B):- transporterinducer(B,C),targetantagonist(B,E),target(E,B),transportersubstrate(A,D),enzymeinducer(B,F).
interacts(A,B):- target(D,A),targetantagonist(A,E),target(E,B),target(C,B),targetagonist(B,C).
interacts(A,B):- targetinducer(A,F),target(D,A),target(E,B),transporterinducer(B,C),targetinhibitor(B,F).
interacts(A,B):- enzymeinhibitor(B,E),enzymesubstrate(B,D),targetinducer(B,C),targetantagonist(A,C),enzyme(E,A).
interacts(A,B):- transporter(F,B),transporterinducer(A,E),enzymesubstrate(B,D),transporterinhibitor(A,E),targetagonist(B,C).
interacts(A,B):- enzymeinducer(A,E),enzymeinhibitor(A,D),transportersubstrate(B,C),transportersubstrate(B,F).
interacts(A,B):- targetinducer(A,F),targetinhibitor(B,C),target(D,A),targetinhibitor(B,E),targetagonist(B,C).
interacts(A,B):- enzyme(C,A),enzymesubstrate(B,C),transportersubstrate(A,E),transporter(D,A).
interacts(A,B):- targetinducer(A,E),targetinducer(A,F),target(D,A),enzymeinhibitor(B,C),targetantagonist(A,F).
interacts(A,B):- transporterinducer(B,E),target(D,A),transporterinducer(B,C),targetinducer(A,D),target(D,B).
interacts(A,B):- target(D,A),transporter(F,A),enzymesubstrate(A,E),enzymeinducer(B,C),transportersubstrate(B,F).
interacts(A,B):- targetantagonist(B,C),targetantagonist(A,D),target(D,A),targetinhibitor(A,E),targetinhibitor(B,F).
interacts(A,B):- target(D,B),targetinducer(B,C),target(E,A),transportersubstrate(B,F).
interacts(A,B):- targetinducer(B,E),targetinhibitor(B,C),target(D,A),targetinducer(A,D),targetinhibitor(A,F).
interacts(A,B):- enzyme(C,B),enzymesubstrate(B,D),enzymeinducer(A,C),targetinhibitor(A,E),enzyme(F,A).
interacts(A,B):- transporterinhibitor(A,E),transportersubstrate(A,C),transporterinducer(A,C),targetinhibitor(B,D).
interacts(A,B):- enzyme(C,A),targetagonist(B,D),targetagonist(A,D),target(D,A),enzymeinhibitor(B,C).
interacts(A,B):- enzymeinducer(A,D),targetantagonist(A,C),enzymeinhibitor(B,E),enzymeinhibitor(A,E).
interacts(A,B):- enzymesubstrate(B,C),targetagonist(B,E),targetantagonist(B,E),targetinhibitor(A,F),enzyme(D,A).
interacts(A,B):- transporter(E,B),target(D,A),targetinducer(B,C),transporterinhibitor(A,F),targetagonist(A,C).
interacts(A,B):- enzymeinducer(A,E),enzyme(E,B),target(D,A),target(D,B),targetantagonist(A,C).
interacts(A,B):- transporterinducer(A,E),transporterinhibitor(B,D),transportersubstrate(B,C),transportersubstrate(B,F).
interacts(A,B):- enzymeinducer(B,E),targetinducer(B,F),target(D,A),enzymeinhibitor(B,E),targetagonist(A,C).
interacts(A,B):- transporterinducer(A,D),enzymesubstrate(A,F),transporterinducer(B,E),transportersubstrate(A,C).
interacts(A,B):- enzymesubstrate(A,E),transportersubstrate(A,C),transporterinducer(B,C),target(D,A).
interacts(A,B):- transporterinhibitor(B,E),targetinhibitor(B,D),targetagonist(B,C),transporter(E,A).
interacts(A,B):- targetinducer(A,E),targetantagonist(B,D),targetantagonist(B,E),targetantagonist(A,E),targetagonist(A,C).
interacts(A,B):- transporterinhibitor(B,C),transporterinhibitor(A,C),enzymesubstrate(B,D),targetantagonist(B,E),target(E,B).
interacts(A,B):- enzymesubstrate(B,E),enzymeinducer(A,D),target(C,B),transportersubstrate(B,F).
interacts(A,B):- transporter(E,B),targetinducer(A,F),target(D,A),target(C,A),targetinducer(B,D).
interacts(A,B):- enzymesubstrate(A,C),transporter(F,B),enzymesubstrate(B,D),transporterinhibitor(B,F),enzymeinhibitor(B,E).
interacts(A,B):- targetagonist(A,F),transportersubstrate(A,D),targetinhibitor(B,E),transporterinhibitor(A,C).
interacts(A,B):- target(D,A),transportersubstrate(A,C),enzymesubstrate(A,E),transporterinducer(B,C),transportersubstrate(B,F).
interacts(A,B):- enzymeinducer(A,E),targetinducer(B,F),enzymesubstrate(B,D),enzymesubstrate(B,E),targetinducer(B,C).
interacts(A,B):- enzymeinhibitor(B,F),transportersubstrate(B,E),targetagonist(B,C),transporterinhibitor(A,D).
interacts(A,B):- target(D,A),enzymesubstrate(B,E),targetinducer(B,C),targetinducer(A,C),enzymeinhibitor(B,E).
interacts(A,B):- target(D,A),transporterinhibitor(A,C),targetantagonist(A,D),transporterinducer(A,E),transporterinducer(B,F).
interacts(A,B):- enzymesubstrate(B,C),enzymesubstrate(A,D),targetantagonist(B,E),targetinhibitor(B,E),transporterinducer(A,F).
interacts(A,B):- targetinducer(A,E),enzymeinducer(A,D),enzymesubstrate(B,D),target(C,A),enzymeinhibitor(B,D).
interacts(A,B):- transportersubstrate(A,D),transporterinducer(B,C),transportersubstrate(B,E),transportersubstrate(B,F).
interacts(A,B):- target(D,A),targetagonist(B,F),enzymeinducer(B,C),targetinhibitor(B,F),enzyme(E,A).
interacts(A,B):- enzyme(C,B),transporterinducer(B,E),enzymesubstrate(B,D),enzymesubstrate(A,D),transportersubstrate(A,E).
interacts(A,B):- targetantagonist(B,C),enzymeinducer(B,E),targetantagonist(A,C),enzymesubstrate(B,D).
interacts(A,B):- targetantagonist(B,C),transportersubstrate(B,D),targetinducer(A,C).
interacts(A,B):- target(D,A),transporter(E,A),transporterinducer(A,C),transportersubstrate(B,E),targetantagonist(B,F).
interacts(A,B):- target(C,B),target(D,A),targetinducer(B,C),targetinhibitor(A,E),target(D,B).
interacts(A,B):- enzymeinhibitor(B,F),enzymeinducer(A,D),target(C,B),targetantagonist(A,E).
interacts(A,B):- enzyme(C,A),targetagonist(A,F),enzymesubstrate(B,D),enzymeinhibitor(B,E).
interacts(A,B):- targetantagonist(A,D),targetagonist(A,E),transportersubstrate(B,C),target(D,A),targetantagonist(B,F).
interacts(A,B):- enzymesubstrate(A,E),targetinducer(A,C),enzymeinducer(A,D),enzyme(F,B).
interacts(A,B):- enzymeinducer(A,E),targetantagonist(B,C),enzymesubstrate(B,D),targetinhibitor(B,F),enzymeinhibitor(A,E).
interacts(A,B):- enzymesubstrate(B,E),transporterinducer(A,D),targetinhibitor(A,C),transportersubstrate(B,F).
interacts(A,B):- targetagonist(B,F),targetinhibitor(B,C),targetagonist(A,E),enzymesubstrate(B,D),targetantagonist(A,E).
interacts(A,B):- enzyme(C,A),transporterinhibitor(B,F),enzymeinhibitor(B,D),targetinducer(B,E).
interacts(A,B):- enzymesubstrate(B,C),targetinducer(B,F),target(D,A),enzymesubstrate(A,E),targetantagonist(B,F).
interacts(A,B):- targetagonist(B,E),enzymesubstrate(B,D),target(E,B),targetantagonist(A,F),transporterinducer(A,C).
interacts(A,B):- targetagonist(B,E),enzymeinducer(B,D),targetantagonist(B,E),enzymeinhibitor(B,C),enzyme(D,A).
interacts(A,B):- targetinducer(B,E),transporterinducer(B,D),targetagonist(A,E),enzymeinducer(A,C).
interacts(A,B):- targetantagonist(B,C),targetinducer(A,E),target(D,A),target(C,A),targetinducer(B,C).
interacts(A,B):- targetantagonist(B,E),target(D,B),targetinducer(A,C),enzymesubstrate(A,F),enzymeinducer(B,F).
interacts(A,B):- targetinhibitor(B,C),targetantagonist(B,E),transporterinhibitor(A,D),transporter(F,A),targetinhibitor(B,E).
interacts(A,B):- targetinducer(B,E),targetantagonist(A,D),targetinhibitor(A,C),target(D,A),targetinducer(B,D).
interacts(A,B):- enzymeinhibitor(A,C),enzymeinhibitor(B,D),enzymesubstrate(A,F),targetagonist(A,E).
interacts(A,B):- targetinducer(A,D),transporterinducer(B,C),transporterinhibitor(A,F),target(E,A).
interacts(A,B):- targetinducer(B,E),enzymesubstrate(B,C),targetinducer(A,F),enzymeinducer(A,C),target(D,A).
interacts(A,B):- enzyme(D,B),enzymesubstrate(A,C),target(E,A),targetantagonist(B,E),enzymeinducer(A,F).
interacts(A,B):- enzymeinhibitor(B,C),transporter(E,B),target(D,A),targetinhibitor(A,D),targetinducer(B,D).
interacts(A,B):- targetantagonist(A,F),targetagonist(B,C),enzymesubstrate(B,D),target(E,A).
interacts(A,B):- transporter(C,B),enzymeinducer(A,D),targetantagonist(B,E),targetagonist(B,F),targetinhibitor(A,F).
interacts(A,B):- targetinducer(A,D),targetagonist(B,D),targetagonist(B,C),targetantagonist(B,E).
interacts(A,B):- enzymesubstrate(B,E),transporterinducer(A,D),targetinhibitor(B,C),targetantagonist(A,C).
interacts(A,B):- target(F,B),target(E,B),enzymeinducer(A,D),targetinhibitor(A,C).
interacts(A,B):- transporterinhibitor(A,C),targetagonist(B,E),targetantagonist(B,E),transportersubstrate(A,C),transporterinducer(A,D).
interacts(A,B):- target(F,B),targetinducer(A,E),enzymeinducer(A,C),transporterinhibitor(A,D).
interacts(A,B):- targetagonist(B,D),transporter(C,B),targetantagonist(B,E),targetinhibitor(A,D),targetinducer(B,D).
interacts(A,B):- targetinhibitor(A,E),targetantagonist(B,E),enzymeinhibitor(A,C),transporterinhibitor(B,F),enzymeinhibitor(A,D).
interacts(A,B):- targetagonist(B,F),transporterinducer(B,D),targetagonist(B,E),targetantagonist(B,E),transportersubstrate(A,C).
interacts(A,B):- transporterinhibitor(B,C),targetantagonist(B,E),transporterinducer(A,C),enzymeinducer(B,F),enzyme(D,A).
interacts(A,B):- enzymeinhibitor(A,C),transporterinducer(B,D),transportersubstrate(B,E),transporterinhibitor(A,F).
interacts(A,B):- enzymeinducer(A,C),targetantagonist(B,E),transporterinducer(A,D),transporterinhibitor(A,F),transportersubstrate(B,F).
interacts(A,B):- targetinhibitor(A,C),targetantagonist(B,E),target(C,B),enzymeinhibitor(A,D),enzymeinducer(A,F).
interacts(A,B):- targetinducer(B,E),targetagonist(A,E),enzymesubstrate(B,D),targetantagonist(A,E),targetantagonist(A,C).
interacts(A,B):- target(E,B),enzymeinhibitor(A,F),enzymeinhibitor(B,D),transporterinhibitor(B,C).
