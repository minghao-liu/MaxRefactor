interacts(A,B):- enzymesubstrate(B,C),enzymeinducer(A,D),enzymesubstrate(B,D),enzymesubstrate(A,D),enzymeinhibitor(A,E).
interacts(A,B):- targetinducer(B,F),transporter(E,B),enzymesubstrate(B,D),target(C,A),enzyme(D,A).
interacts(A,B):- targetagonist(A,D),transporterinhibitor(A,C),targetantagonist(B,E),target(E,B),target(D,B).
interacts(A,B):- transporterinhibitor(B,C),transporterinducer(B,E),target(F,A),enzymesubstrate(B,D),target(F,B).
interacts(A,B):- transportersubstrate(A,F),transporter(C,B),targetantagonist(B,D),target(D,A),enzymeinhibitor(A,E).
interacts(A,B):- transporter(C,B),targetantagonist(A,D),target(E,A),target(D,A),transporter(F,A).
interacts(A,B):- targetantagonist(B,C),transporterinhibitor(A,E),transporterinducer(A,E),target(D,A).
interacts(A,B):- target(D,B),enzyme(C,B),transporterinducer(A,E),targetinducer(A,D).
interacts(A,B):- target(D,A),targetagonist(B,F),transporterinhibitor(B,C),transporter(E,A),targetinhibitor(B,D).
interacts(A,B):- enzymeinducer(A,E),enzymesubstrate(B,D),transportersubstrate(B,C),enzymesubstrate(A,E),enzymeinhibitor(B,E).
interacts(A,B):- target(D,A),transportersubstrate(A,C),transporterinhibitor(A,F),targetinhibitor(B,D),transporter(E,A).
interacts(A,B):- targetinducer(A,E),enzyme(D,B),enzymeinducer(A,D),targetantagonist(B,E),transportersubstrate(A,C).
interacts(A,B):- enzymeinhibitor(B,E),enzymesubstrate(B,D),transporterinducer(A,C),enzymeinducer(B,F),enzymeinhibitor(A,E).
interacts(A,B):- transporterinhibitor(A,C),enzymesubstrate(A,E),enzymeinhibitor(B,D),targetantagonist(B,F).
interacts(A,B):- transporterinducer(B,E),transporterinducer(A,E),target(D,A),transporterinducer(B,C),transporterinhibitor(B,F).
interacts(A,B):- transporterinhibitor(B,C),enzymeinducer(B,D),enzymesubstrate(B,D),target(F,B),enzymeinhibitor(A,E).
interacts(A,B):- enzymesubstrate(B,D),enzymesubstrate(A,D),target(E,A),transporter(F,A),target(C,B).
interacts(A,B):- targetinducer(A,E),targetagonist(A,D),targetinhibitor(A,E),enzymeinducer(B,C).
interacts(A,B):- targetinhibitor(A,D),targetinhibitor(B,C),targetinhibitor(B,F),target(E,A).
interacts(A,B):- targetinhibitor(A,E),targetantagonist(A,D),transportersubstrate(B,C),targetinhibitor(B,D).
interacts(A,B):- transporterinhibitor(B,C),targetantagonist(B,D),targetantagonist(A,D),target(E,A),targetantagonist(B,E).
interacts(A,B):- transporterinhibitor(A,C),enzymesubstrate(B,D),targetantagonist(A,E),targetinhibitor(B,E),transporterinhibitor(B,F).
interacts(A,B):- transporterinducer(A,D),enzymesubstrate(A,C),transportersubstrate(B,E),transporterinducer(B,E).
interacts(A,B):- enzymesubstrate(B,E),enzymeinhibitor(B,D),targetagonist(A,F),transportersubstrate(B,C).
interacts(A,B):- enzymeinducer(A,E),transporterinhibitor(B,C),transporterinhibitor(B,D).
interacts(A,B):- targetantagonist(B,D),targetagonist(A,E),target(D,A),target(C,A),target(D,B).
interacts(A,B):- targetinducer(A,C),targetinducer(B,F),transporterinducer(A,E),targetinhibitor(B,D).
interacts(A,B):- target(C,A),transporterinducer(B,D),enzymesubstrate(B,E),targetagonist(A,C).
interacts(A,B):- targetinducer(A,F),transporter(E,B),enzymesubstrate(B,D),transporterinducer(A,E),targetantagonist(A,C).
interacts(A,B):- transporterinhibitor(A,D),transporterinducer(A,D),targetagonist(B,C),enzymeinhibitor(A,E).
interacts(A,B):- targetagonist(B,E),enzymeinhibitor(B,D),targetinducer(A,F),enzymeinducer(A,C).
interacts(A,B):- enzyme(C,A),targetantagonist(B,F),targetinhibitor(A,E),enzymesubstrate(B,D).
interacts(A,B):- targetinducer(B,E),transporterinducer(A,D),targetinhibitor(A,F),targetagonist(A,C).
interacts(A,B):- targetinducer(A,F),enzymesubstrate(B,D),transportersubstrate(A,C),enzyme(E,A),enzyme(D,A).
interacts(A,B):- enzymeinducer(A,E),enzymesubstrate(B,D),transporterinducer(B,F),targetantagonist(A,C),enzyme(E,A).
interacts(A,B):- targetinducer(B,C),enzyme(F,B),targetantagonist(A,D),enzymeinhibitor(A,E).
interacts(A,B):- transporterinhibitor(B,E),enzymeinhibitor(B,F),enzymesubstrate(A,C),transporter(D,A).
interacts(A,B):- transporter(F,A),enzyme(D,B),targetinhibitor(A,C),transporter(E,A).
interacts(A,B):- target(D,A),transporter(E,A),enzymeinhibitor(B,C),transportersubstrate(B,E),targetinducer(B,D).
interacts(A,B):- enzyme(C,A),targetinducer(B,E),targetagonist(B,F),target(D,A),target(E,B).
interacts(A,B):- targetinducer(A,E),targetagonist(A,E),enzymesubstrate(A,D),targetantagonist(B,E),enzymeinhibitor(A,C).
interacts(A,B):- targetantagonist(B,C),enzymesubstrate(B,D),targetantagonist(A,E),transporter(F,A),enzymeinhibitor(B,D).
interacts(A,B):- transporterinhibitor(B,C),transporterinducer(B,E),enzyme(F,A),enzymesubstrate(B,D).
interacts(A,B):- targetinhibitor(B,C),target(D,A),transporter(F,A),transportersubstrate(B,E),transportersubstrate(A,E).
interacts(A,B):- enzyme(E,B),targetagonist(A,D),target(D,A),targetinducer(A,C),targetinducer(B,D).
interacts(A,B):- enzymeinducer(A,D),transporter(E,B),enzymesubstrate(B,D),transportersubstrate(B,C),transporterinducer(A,C).
interacts(A,B):- targetinducer(A,E),targetinducer(A,C),targetinhibitor(B,C),transporterinhibitor(A,D).
interacts(A,B):- enzymeinducer(A,D),enzymesubstrate(A,D),targetantagonist(B,E),transporterinhibitor(B,F),targetagonist(A,C).
interacts(A,B):- enzymeinhibitor(B,C),transporter(F,B),targetantagonist(B,E),targetinhibitor(A,D),targetinducer(A,D).
interacts(A,B):- target(C,A),enzymesubstrate(A,E),targetinducer(B,C),transporterinducer(B,D).
interacts(A,B):- transporter(F,A),enzyme(C,B),targetagonist(B,E),targetantagonist(B,D).
interacts(A,B):- enzymeinducer(A,D),enzymesubstrate(B,D),targetinducer(B,C),enzymeinhibitor(B,D),enzyme(D,A).
interacts(A,B):- transportersubstrate(A,E),transporterinhibitor(B,C),transporter(E,B),targetantagonist(A,D).
interacts(A,B):- enzymesubstrate(A,C),targetinducer(B,F),enzymesubstrate(B,D),enzymesubstrate(A,E),targetinhibitor(B,F).
interacts(A,B):- transporterinducer(B,D),transporterinhibitor(B,F),targetinhibitor(B,C),transporterinducer(A,E).
interacts(A,B):- enzymeinhibitor(A,C),target(D,B),target(F,A),target(E,A).
interacts(A,B):- targetantagonist(B,C),transporter(E,B),enzymesubstrate(B,D),transporterinhibitor(B,F),enzyme(D,A).
interacts(A,B):- enzyme(E,B),enzymeinhibitor(A,F),enzymesubstrate(A,C),target(D,A),targetinhibitor(B,D).
interacts(A,B):- enzyme(C,A),enzymeinducer(A,D),targetinducer(A,F),targetantagonist(B,E),target(E,B).
interacts(A,B):- enzymeinducer(B,E),target(D,A),enzymeinhibitor(A,C),transporterinhibitor(B,F),enzyme(E,A).
interacts(A,B):- enzymesubstrate(B,C),transporterinhibitor(B,D),enzymeinducer(B,F),enzymeinhibitor(A,E).
interacts(A,B):- enzyme(C,A),enzyme(C,B),transporterinhibitor(B,D),targetantagonist(B,E),enzymeinducer(B,F).
interacts(A,B):- transporterinhibitor(B,C),enzymeinhibitor(A,F),target(D,A),targetinhibitor(B,E),target(D,B).
interacts(A,B):- transporter(E,B),enzymesubstrate(B,D),transporterinducer(A,E),target(C,B),enzymeinhibitor(A,D).
interacts(A,B):- target(D,A),enzymesubstrate(A,C),targetantagonist(B,D),targetantagonist(A,E),targetinhibitor(A,D).
interacts(A,B):- targetagonist(B,E),enzymesubstrate(B,D),enzymeinhibitor(A,C),transporterinhibitor(B,F),transportersubstrate(B,F).
interacts(A,B):- enzyme(C,A),enzymesubstrate(A,C),enzyme(F,B),targetantagonist(B,E),transporterinducer(A,D).
interacts(A,B):- targetinducer(B,F),targetinducer(B,C),targetantagonist(B,E),targetagonist(A,F),transportersubstrate(A,D).
interacts(A,B):- targetinhibitor(A,D),enzymesubstrate(A,C),enzymeinducer(A,F),enzymeinhibitor(B,E).
interacts(A,B):- enzymeinducer(A,E),targetinducer(A,F),enzymesubstrate(B,D),enzymesubstrate(A,D),targetagonist(B,C).
interacts(A,B):- transporterinhibitor(A,C),transporterinhibitor(B,E),enzymeinducer(A,D).
interacts(A,B):- transportersubstrate(B,D),enzymeinducer(A,F),enzymeinducer(A,C),transporter(E,A).
interacts(A,B):- targetinducer(A,F),transportersubstrate(B,C),target(D,A),targetantagonist(B,E),transporterinducer(A,C).
interacts(A,B):- transporterinducer(B,D),target(E,A),transporterinducer(B,F),targetantagonist(B,E),targetantagonist(A,C).
interacts(A,B):- targetantagonist(B,F),transportersubstrate(B,C),enzymesubstrate(A,D),enzymeinhibitor(A,E).
interacts(A,B):- enzymesubstrate(A,C),transporterinducer(B,E),target(F,A),enzymesubstrate(B,D),enzymeinhibitor(B,C).
interacts(A,B):- target(D,A),targetinducer(B,C),transporterinhibitor(B,F),enzyme(E,A),targetagonist(A,C).
interacts(A,B):- targetantagonist(B,E),targetinhibitor(A,D),targetinhibitor(B,F),targetantagonist(A,C),targetinhibitor(A,F).
interacts(A,B):- enzymeinhibitor(B,C),transporterinhibitor(A,E),targetantagonist(A,D),transportersubstrate(A,F).
interacts(A,B):- target(E,B),enzyme(D,B),transporterinhibitor(A,C),transporterinhibitor(B,F).
interacts(A,B):- transporter(C,B),enzymeinhibitor(B,D),enzymesubstrate(A,F),targetantagonist(A,E).
interacts(A,B):- transporter(F,B),targetantagonist(B,E),transporterinhibitor(A,D),targetinducer(A,C),targetinhibitor(A,E).
interacts(A,B):- enzymeinducer(A,D),transporter(E,B),target(C,B),enzymesubstrate(B,D),transporterinhibitor(B,F).
interacts(A,B):- targetagonist(A,C),enzyme(E,B),transporterinhibitor(B,D),enzymeinducer(B,E).
interacts(A,B):- transporterinhibitor(B,E),target(D,A),target(C,A),transportersubstrate(A,E),targetagonist(A,C).
interacts(A,B):- transporter(E,B),target(D,A),targetinducer(B,C),target(C,B),target(D,B).
interacts(A,B):- target(D,A),target(C,A),target(C,B),transportersubstrate(B,E),targetinducer(A,D).
interacts(A,B):- enzymesubstrate(B,C),transporterinducer(B,E),target(D,A),transporterinhibitor(A,E),enzyme(F,A).
interacts(A,B):- transporterinhibitor(A,E),targetagonist(A,D),transportersubstrate(A,E),enzymeinducer(B,C).
interacts(A,B):- transportersubstrate(A,E),transporterinducer(B,D),transportersubstrate(A,D),targetantagonist(A,C).
interacts(A,B):- targetagonist(B,F),enzymeinducer(B,D),enzymeinducer(A,C),targetantagonist(B,E),enzymeinducer(B,C).
interacts(A,B):- enzyme(C,A),enzymeinducer(A,C),targetantagonist(B,E),transportersubstrate(B,D),targetantagonist(A,F).
interacts(A,B):- enzyme(C,A),targetinducer(A,E),transporter(D,B),targetagonist(B,F).
interacts(A,B):- transporterinhibitor(A,E),transportersubstrate(A,D),enzyme(C,B),transporterinducer(B,F).
interacts(A,B):- enzymesubstrate(B,D),transportersubstrate(A,C),transporterinhibitor(B,E),enzymeinhibitor(A,D),transporter(E,A).
interacts(A,B):- target(F,B),targetagonist(A,D),transportersubstrate(B,C),transporterinhibitor(B,E).
interacts(A,B):- targetagonist(A,F),transporterinhibitor(B,E),transporterinhibitor(B,D),targetinhibitor(A,C).
interacts(A,B):- targetantagonist(A,D),targetinhibitor(B,C),targetantagonist(B,E),targetinhibitor(A,D),targetinhibitor(B,F).
interacts(A,B):- targetagonist(B,E),transporterinhibitor(A,D),targetantagonist(A,E),targetantagonist(B,E),enzymeinducer(B,C).
interacts(A,B):- target(D,A),transporterinducer(A,E),transportersubstrate(A,C),targetantagonist(B,F),transportersubstrate(A,E).
interacts(A,B):- enzymesubstrate(B,E),targetantagonist(A,C),transportersubstrate(B,D),target(F,A).
interacts(A,B):- transporterinhibitor(B,C),transporter(F,A),targetantagonist(B,E),targetinhibitor(A,D),transportersubstrate(B,F).
interacts(A,B):- targetantagonist(B,C),targetagonist(B,D),target(D,A),transporterinhibitor(B,E),targetinhibitor(B,F).
interacts(A,B):- enzymesubstrate(A,C),enzymesubstrate(B,D),transporterinducer(B,F),transporterinhibitor(A,E),enzymeinhibitor(B,D).
interacts(A,B):- enzymesubstrate(B,C),enzymeinhibitor(B,D),enzyme(F,B),targetantagonist(B,E),targetinhibitor(A,E).
interacts(A,B):- enzymesubstrate(A,C),enzyme(C,B),enzymesubstrate(B,D),enzymeinducer(B,F),enzymeinhibitor(A,E).
interacts(A,B):- enzymeinducer(B,E),transporter(C,B),targetantagonist(A,D),transporterinducer(A,C).
interacts(A,B):- enzymeinducer(A,D),targetinducer(A,F),targetinhibitor(B,C),enzymesubstrate(B,D),transporterinducer(A,E).
interacts(A,B):- enzymeinducer(B,C),transporterinducer(B,E),enzyme(F,B),target(D,A),transportersubstrate(A,E).
interacts(A,B):- enzymesubstrate(B,C),target(D,A),targetinhibitor(B,E),enzymeinducer(A,F),targetinducer(B,D).
interacts(A,B):- transporter(C,A),enzymesubstrate(B,D),transportersubstrate(B,C),targetantagonist(B,E),transporterinhibitor(A,F).
interacts(A,B):- targetagonist(B,D),targetantagonist(B,E),target(D,A),transporterinducer(B,C),target(D,B).
interacts(A,B):- targetinducer(A,E),targetinducer(B,C),transporterinhibitor(B,D),transporter(F,B).
interacts(A,B):- enzymesubstrate(A,E),enzyme(F,B),enzymeinducer(A,C),enzyme(D,A).
interacts(A,B):- enzymeinducer(A,E),transporterinhibitor(B,F),target(C,B),enzyme(D,A).
interacts(A,B):- targetagonist(B,D),targetantagonist(A,D),targetinhibitor(A,C),targetantagonist(B,E),enzyme(F,A).
interacts(A,B):- transporterinhibitor(B,C),targetantagonist(B,D),targetagonist(A,E),transportersubstrate(B,F).
interacts(A,B):- targetantagonist(B,C),enzymesubstrate(B,D),transporterinducer(A,E),transporterinhibitor(B,E),enzymeinducer(B,F).
interacts(A,B):- enzyme(C,A),targetagonist(A,D),targetinducer(A,F),targetantagonist(B,E),targetagonist(B,F).
interacts(A,B):- targetinhibitor(A,F),target(D,A),enzymesubstrate(B,E),targetinhibitor(B,D),targetagonist(B,C).
