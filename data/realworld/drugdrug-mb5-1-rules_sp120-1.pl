interacts(A,B):- targetagonist(B,D),target(D,A),target(E,B),transporterinducer(B,C),enzyme(F,A).
interacts(A,B):- targetinducer(B,E),targetinducer(A,D),targetantagonist(A,F),enzymeinducer(A,C).
interacts(A,B):- enzyme(C,B),target(E,A),targetantagonist(B,E),enzymeinducer(A,F),targetinhibitor(B,D).
interacts(A,B):- target(E,B),targetinhibitor(B,E),enzymesubstrate(A,C),targetinducer(B,D).
interacts(A,B):- enzymeinducer(A,E),transportersubstrate(A,C),enzymesubstrate(B,D),transporterinducer(B,F),enzyme(E,A).
interacts(A,B):- enzymesubstrate(B,C),targetantagonist(A,D),target(D,A),targetinhibitor(B,F),enzyme(E,A).
interacts(A,B):- enzymeinducer(B,E),transporterinhibitor(A,C),enzymeinducer(B,D),transporterinducer(A,F).
interacts(A,B):- enzymeinhibitor(B,C),transportersubstrate(A,E),targetantagonist(B,D),target(F,A).
interacts(A,B):- targetagonist(A,D),transporter(C,B),targetagonist(A,E),target(E,A),target(D,A).
interacts(A,B):- transporterinhibitor(B,D),transporter(D,A),targetantagonist(B,E),target(C,A),transporterinducer(A,F).
interacts(A,B):- targetagonist(A,D),transportersubstrate(B,C),transporterinducer(B,F),targetantagonist(B,E),targetinhibitor(B,D).
interacts(A,B):- targetinducer(B,E),targetinducer(B,C),targetinducer(A,F),target(D,A).
interacts(A,B):- enzymeinducer(B,E),enzymesubstrate(A,C),enzymesubstrate(B,D),enzymesubstrate(B,E),enzyme(E,A).
interacts(A,B):- targetagonist(A,E),target(D,A),targetantagonist(A,F),target(C,B),target(D,B).
interacts(A,B):- targetinhibitor(B,C),targetagonist(B,E),target(D,A),targetinducer(B,C),targetinhibitor(B,E).
interacts(A,B):- transporterinhibitor(A,C),targetinducer(B,F),enzymesubstrate(B,D),target(F,A),transporter(E,A).
interacts(A,B):- target(E,A),target(D,A),transporterinducer(B,C),enzyme(F,A),target(D,B).
interacts(A,B):- enzyme(E,A),targetinhibitor(B,C),target(D,A),targetinducer(A,C),targetinhibitor(A,F).
interacts(A,B):- enzymesubstrate(B,E),enzymeinhibitor(A,C),enzymeinhibitor(A,F),targetagonist(A,D).
interacts(A,B):- target(D,A),targetantagonist(B,F),targetinducer(B,C),targetinhibitor(B,F),enzymeinhibitor(B,E).
interacts(A,B):- enzymeinhibitor(A,C),enzyme(E,B),targetagonist(A,F),targetinducer(A,D).
interacts(A,B):- transporterinducer(B,C),transporter(C,A),targetantagonist(B,E),targetantagonist(A,F),transporterinducer(A,D).
interacts(A,B):- targetinducer(A,C),transporterinhibitor(B,D),transporterinhibitor(A,D),targetantagonist(A,E).
interacts(A,B):- transporterinhibitor(A,E),targetantagonist(A,D),targetinducer(B,D),transporterinducer(A,C).
interacts(A,B):- enzyme(E,B),enzymesubstrate(B,D),enzymesubstrate(A,D),enzymesubstrate(B,E),targetagonist(A,C).
interacts(A,B):- targetantagonist(B,C),targetinhibitor(A,D),targetantagonist(B,E),target(C,A),targetinhibitor(A,E).
interacts(A,B):- targetinducer(B,E),targetagonist(B,D),target(D,A),targetinhibitor(B,F),targetantagonist(A,C).
interacts(A,B):- enzymeinducer(A,E),targetantagonist(B,F),targetinducer(B,C),enzymeinducer(B,D).
interacts(A,B):- targetagonist(A,E),targetantagonist(B,E),transporterinhibitor(A,D),target(C,A),targetinducer(B,C).
interacts(A,B):- targetagonist(B,E),enzymesubstrate(B,D),target(E,A),targetantagonist(A,E),targetinducer(A,C).
interacts(A,B):- targetagonist(B,F),enzyme(C,B),transporterinhibitor(B,D),enzymeinducer(A,C),targetantagonist(B,E).
interacts(A,B):- targetantagonist(B,C),target(D,A),transporter(F,A),transporterinhibitor(B,F),enzyme(E,A).
interacts(A,B):- transporter(D,B),transporterinhibitor(B,D),targetantagonist(B,E),targetinducer(B,C),enzyme(F,A).
interacts(A,B):- transportersubstrate(A,E),enzymesubstrate(B,C),targetinhibitor(B,F),targetinhibitor(B,D).
interacts(A,B):- transportersubstrate(A,F),enzymesubstrate(B,D),target(E,A),targetagonist(A,C).
interacts(A,B):- targetinducer(B,E),enzyme(C,B),enzymesubstrate(B,D),targetantagonist(A,E),enzymeinducer(B,C).
interacts(A,B):- targetinducer(B,F),targetantagonist(B,E),targetinhibitor(A,D),enzymeinhibitor(A,C),targetinhibitor(A,E).
interacts(A,B):- target(D,A),transporterinhibitor(A,C),transporterinducer(B,E),transportersubstrate(A,C),enzymeinducer(B,F).
interacts(A,B):- targetinhibitor(A,D),transportersubstrate(B,E),targetinhibitor(B,C),enzymeinducer(A,F).
interacts(A,B):- targetantagonist(B,E),target(D,A),target(C,A),enzymesubstrate(A,F),targetinducer(A,D).
interacts(A,B):- enzymeinducer(B,E),enzymesubstrate(B,D),enzymesubstrate(A,D),transportersubstrate(B,C),targetantagonist(B,F).
interacts(A,B):- targetinducer(B,E),targetagonist(A,D),transporter(C,A),targetantagonist(B,E),transporterinducer(A,C).
interacts(A,B):- enzymeinducer(A,D),enzymesubstrate(B,D),transportersubstrate(B,C),transportersubstrate(A,C),enzymeinhibitor(B,E).
interacts(A,B):- targetinducer(A,F),target(D,A),enzymeinhibitor(A,C),target(D,B),enzyme(E,A).
interacts(A,B):- targetantagonist(B,C),targetagonist(B,E),target(D,A),targetinhibitor(A,D),targetinducer(A,D).
interacts(A,B):- enzymeinhibitor(B,D),transporterinhibitor(A,C),enzymesubstrate(B,D),transporter(E,A),transporterinducer(A,F).
interacts(A,B):- targetinducer(B,E),enzymeinhibitor(A,C),targetinducer(B,F),transporterinducer(A,D).
interacts(A,B):- transporterinducer(B,D),transporter(C,A),targetantagonist(B,E),target(F,B),targetagonist(A,F).
interacts(A,B):- transporterinducer(B,D),enzymesubstrate(A,C),enzymeinducer(A,C),targetantagonist(B,E),transporterinhibitor(A,F).
interacts(A,B):- target(D,A),enzymeinhibitor(B,E),transporterinhibitor(A,C),transportersubstrate(A,C),enzyme(E,A).
interacts(A,B):- targetantagonist(B,E),targetagonist(B,F),transporterinducer(A,C),targetantagonist(A,F),enzymeinhibitor(A,D).
interacts(A,B):- enzyme(C,A),targetagonist(B,E),target(D,A),targetinhibitor(A,E),enzymeinducer(A,F).
interacts(A,B):- enzyme(C,A),targetagonist(B,D),enzymesubstrate(A,F),transporterinducer(B,E).
interacts(A,B):- targetagonist(B,E),targetantagonist(B,E),transporterinducer(A,C),transportersubstrate(A,D),enzymeinducer(B,F).
interacts(A,B):- targetantagonist(B,C),targetantagonist(B,D),target(D,A),enzyme(E,A),targetagonist(A,C).
interacts(A,B):- targetantagonist(B,E),transporterinducer(A,C),targetinhibitor(B,E),enzyme(F,A),target(D,B).
interacts(A,B):- enzyme(C,B),target(D,A),targetinhibitor(A,D),transportersubstrate(B,F),enzymeinhibitor(A,E).
interacts(A,B):- enzymeinhibitor(B,C),targetagonist(B,E),enzymesubstrate(A,F),transporterinhibitor(B,D).
interacts(A,B):- targetantagonist(B,D),targetinducer(A,F),targetantagonist(B,E),targetagonist(A,F),targetantagonist(A,C).
interacts(A,B):- targetinhibitor(A,D),target(C,B),targetinducer(A,F),enzymeinhibitor(B,E).
interacts(A,B):- enzyme(C,B),enzymesubstrate(B,D),enzymesubstrate(A,D),transporter(F,A),transporterinhibitor(A,E).
interacts(A,B):- enzyme(D,B),enzymeinducer(A,C),targetantagonist(B,E),targetantagonist(B,F),enzymeinducer(B,C).
interacts(A,B):- targetinducer(B,F),enzymesubstrate(B,D),targetinducer(A,C),targetinhibitor(B,F),enzymeinhibitor(B,E).
interacts(A,B):- enzymeinducer(A,C),targetantagonist(B,F),enzymeinhibitor(A,D),enzymeinhibitor(B,E).
interacts(A,B):- targetantagonist(B,C),enzymeinducer(B,E),enzymeinducer(B,D),transporterinhibitor(A,F).
interacts(A,B):- targetantagonist(B,E),transportersubstrate(A,C),target(E,A),target(D,A).
interacts(A,B):- targetinducer(B,F),targetinhibitor(A,C),enzymesubstrate(B,D),targetantagonist(B,E),targetagonist(A,F).
interacts(A,B):- enzymeinducer(B,D),enzymeinducer(A,C),targetantagonist(B,E),transporterinhibitor(B,F),enzymeinhibitor(A,D).
interacts(A,B):- transporter(C,B),enzymeinducer(B,D),transporter(C,A),targetantagonist(B,E),enzyme(F,A).
interacts(A,B):- enzymesubstrate(B,D),target(C,A),targetantagonist(A,C),enzymeinhibitor(B,E),enzyme(D,A).
interacts(A,B):- transporter(E,B),target(D,A),transporterinducer(A,C),target(D,B),targetinhibitor(B,F).
interacts(A,B):- transporter(C,B),targetantagonist(B,E),target(D,A),targetinducer(A,D),transportersubstrate(B,F).
interacts(A,B):- transporter(F,B),target(E,A),transporterinducer(B,F),enzymesubstrate(B,D),enzymeinhibitor(A,C).
interacts(A,B):- target(C,A),target(E,B),targetinhibitor(A,F),targetinducer(A,D).
interacts(A,B):- transporter(E,B),transporter(F,B),target(D,A),target(C,A),transportersubstrate(A,E).
interacts(A,B):- target(C,B),transporter(E,B),transporterinhibitor(A,F),enzyme(D,A).
interacts(A,B):- transportersubstrate(A,F),transportersubstrate(A,D),enzyme(C,B),transportersubstrate(A,E).
interacts(A,B):- targetinducer(B,E),targetantagonist(A,D),targetinhibitor(A,C),targetantagonist(B,E),targetinhibitor(A,E).
interacts(A,B):- targetinhibitor(B,C),targetagonist(A,E),target(D,A),target(C,A),targetinducer(A,D).
interacts(A,B):- transporter(F,A),enzymesubstrate(B,D),targetantagonist(A,E),target(C,A),transporterinhibitor(B,F).
interacts(A,B):- targetagonist(B,D),transporter(C,A),target(D,A),targetinhibitor(A,D),enzymesubstrate(A,E).
interacts(A,B):- targetagonist(A,D),target(E,A),targetantagonist(B,E),target(E,B),enzymeinducer(B,C).
interacts(A,B):- targetinducer(B,E),enzyme(C,B),transporterinhibitor(A,D).
interacts(A,B):- enzymeinducer(A,C),targetagonist(A,D),enzymeinducer(A,F),enzymeinhibitor(B,E).
interacts(A,B):- target(D,A),target(C,A),targetinhibitor(B,E),enzymeinducer(A,F),targetinhibitor(B,D).
interacts(A,B):- targetantagonist(A,E),enzymeinducer(B,D),targetinhibitor(A,F),enzymeinducer(B,C).
interacts(A,B):- transporterinducer(B,E),targetinhibitor(B,C),targetinducer(B,C),enzymesubstrate(B,D),targetantagonist(A,F).
interacts(A,B):- target(D,A),enzymesubstrate(B,C),enzymesubstrate(A,C),target(E,A),targetantagonist(B,E).
interacts(A,B):- enzymeinducer(A,D),transporterinducer(B,E),enzymesubstrate(B,D),enzymeinducer(A,C).
interacts(A,B):- targetantagonist(B,E),enzymeinhibitor(B,C),enzymeinhibitor(A,C),transportersubstrate(B,D),enzymeinducer(B,F).
interacts(A,B):- enzymeinhibitor(B,C),enzymeinhibitor(B,F),targetinhibitor(B,E),transporter(D,A).
interacts(A,B):- transporterinhibitor(B,E),enzyme(D,B),transporterinhibitor(B,C),transporter(E,A).
interacts(A,B):- enzyme(E,B),enzymeinducer(A,D),transporterinducer(A,C),transporter(C,A).
interacts(A,B):- target(C,A),transporterinhibitor(A,E),transporterinducer(A,D),transporter(E,B).
interacts(A,B):- targetinducer(B,C),transporter(D,A),target(C,A),targetantagonist(B,E),targetantagonist(A,F).
interacts(A,B):- enzymesubstrate(A,C),transporter(F,B),enzymesubstrate(A,D),targetantagonist(B,E),transporterinhibitor(B,F).
interacts(A,B):- targetinducer(A,E),targetinhibitor(B,C),target(F,A),transporter(D,A),targetantagonist(B,E).
interacts(A,B):- targetantagonist(A,D),target(E,A),targetantagonist(B,E),target(C,A),targetantagonist(A,C).
interacts(A,B):- transportersubstrate(A,D),enzymesubstrate(B,C),transporter(D,A),enzymeinhibitor(A,E).
interacts(A,B):- targetinducer(A,E),targetinducer(B,F),enzymesubstrate(B,D),transportersubstrate(A,C),target(F,B).
interacts(A,B):- enzyme(C,A),target(D,A),target(F,B),transportersubstrate(B,E),targetinhibitor(A,F).
interacts(A,B):- targetinducer(B,E),targetantagonist(A,C),targetantagonist(B,D),target(D,A),targetinhibitor(B,D).
interacts(A,B):- enzymeinducer(A,D),targetantagonist(B,E),enzymeinducer(B,C),enzymeinhibitor(B,C),enzymeinhibitor(A,D).
interacts(A,B):- targetinhibitor(A,C),enzymesubstrate(B,D),targetantagonist(B,E),targetantagonist(A,F),targetantagonist(A,C).
interacts(A,B):- targetantagonist(B,C),targetinducer(A,E),enzymesubstrate(A,F),transporter(D,A).
interacts(A,B):- enzyme(E,B),transporter(C,A),target(F,A),target(D,A),target(F,B).
interacts(A,B):- targetantagonist(B,D),targetagonist(B,E),target(D,A),transporter(F,A),targetinducer(A,C).
interacts(A,B):- transporterinhibitor(B,E),transportersubstrate(A,D),enzymeinhibitor(A,F),transporterinhibitor(A,C).
interacts(A,B):- transporterinducer(B,D),targetinhibitor(B,E),targetinducer(A,F),enzymeinducer(A,C).
interacts(A,B):- enzymeinhibitor(A,F),transporterinducer(A,D),targetagonist(B,E),targetagonist(A,C).
interacts(A,B):- transportersubstrate(A,D),targetinhibitor(B,E),targetinhibitor(B,C),targetinhibitor(B,F).
interacts(A,B):- target(F,A),enzymesubstrate(A,D),targetantagonist(B,E),enzymeinhibitor(B,C),targetinhibitor(A,F).
interacts(A,B):- targetinducer(A,E),target(D,A),targetagonist(A,F),target(D,B),enzymeinducer(B,C).
interacts(A,B):- target(E,B),targetinhibitor(A,C),enzymeinhibitor(A,D),transporter(F,B).
interacts(A,B):- enzyme(F,B),targetinhibitor(A,C),enzymesubstrate(B,D),targetinducer(B,C),targetinhibitor(B,E).
interacts(A,B):- enzymeinducer(A,C),targetantagonist(B,E),enzymeinhibitor(B,C),transportersubstrate(A,D),enzymeinducer(B,F).
interacts(A,B):- targetantagonist(B,C),enzymesubstrate(B,D),transporter(F,A),target(E,B),targetagonist(B,C).
interacts(A,B):- transporter(D,B),enzymesubstrate(A,F),targetinhibitor(A,C),targetantagonist(A,E).
interacts(A,B):- transporterinhibitor(A,C),targetinducer(A,F),enzyme(E,A),targetinhibitor(B,D).
interacts(A,B):- enzyme(E,B),targetagonist(A,D),targetinhibitor(B,D),enzymeinducer(B,C).
