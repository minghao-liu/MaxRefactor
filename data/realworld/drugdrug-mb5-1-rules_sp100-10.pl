interacts(A,B):- targetantagonist(B,C),enzyme(D,B),targetantagonist(B,E),targetantagonist(B,F),targetinhibitor(A,F).
interacts(A,B):- targetagonist(B,E),targetagonist(A,E),targetinducer(A,D),transportersubstrate(A,C).
interacts(A,B):- enzymeinducer(B,D),targetagonist(A,E),targetantagonist(B,E),enzymeinducer(B,C).
interacts(A,B):- transporterinhibitor(B,C),transporterinhibitor(A,C),targetagonist(A,E),target(E,A),target(D,A).
interacts(A,B):- transporter(C,B),enzymeinhibitor(A,D),transporterinducer(A,E),enzymesubstrate(A,D).
interacts(A,B):- targetagonist(B,D),targetinhibitor(A,C),targetantagonist(B,E),target(E,B),targetinhibitor(A,E).
interacts(A,B):- targetantagonist(B,E),transporterinducer(B,F),enzymeinducer(B,C),targetinducer(A,D),transportersubstrate(B,F).
interacts(A,B):- enzymesubstrate(B,C),target(D,A),transporterinhibitor(A,E),transporterinducer(A,F),enzymeinducer(B,C).
interacts(A,B):- enzymesubstrate(B,C),targetinducer(A,F),target(F,A),target(D,A),targetinhibitor(A,E).
interacts(A,B):- targetinducer(A,E),transporter(C,B),transporterinhibitor(A,C),target(D,A),targetagonist(A,F).
interacts(A,B):- transporter(F,B),target(E,A),transportersubstrate(B,C),targetantagonist(B,E),enzymeinhibitor(A,D).
interacts(A,B):- targetinducer(A,E),targetagonist(A,F),targetantagonist(B,E),enzymeinducer(B,C),targetinhibitor(A,D).
interacts(A,B):- targetagonist(B,F),enzymeinducer(B,E),target(D,A),targetinducer(B,D),targetagonist(B,C).
interacts(A,B):- transporter(F,B),enzymesubstrate(B,D),enzymeinducer(B,C),enzymeinhibitor(A,C),enzymeinhibitor(A,E).
interacts(A,B):- targetinhibitor(B,C),target(D,A),enzymesubstrate(B,E),targetinducer(B,C),transporterinhibitor(A,F).
interacts(A,B):- transporterinducer(B,E),enzymesubstrate(B,D),transportersubstrate(A,C),target(F,B),targetantagonist(A,F).
interacts(A,B):- enzymesubstrate(B,C),enzyme(D,B),transporterinhibitor(B,F),enzyme(E,A).
interacts(A,B):- targetinhibitor(A,D),targetagonist(A,D),targetagonist(B,E),targetinhibitor(A,C).
interacts(A,B):- transporterinducer(A,C),enzymesubstrate(B,F),transporterinducer(B,E),targetinhibitor(B,D).
interacts(A,B):- target(D,A),transporter(E,A),targetinducer(B,C),enzymesubstrate(A,F),enzymeinducer(B,F).
interacts(A,B):- targetantagonist(B,D),transporter(E,B),enzymeinducer(A,C),target(D,A),targetantagonist(A,F).
interacts(A,B):- target(C,A),transportersubstrate(A,E),transportersubstrate(B,E),targetinducer(B,D).
interacts(A,B):- targetagonist(A,C),target(E,B),targetinhibitor(B,E),target(D,A).
interacts(A,B):- enzymeinducer(B,E),targetinducer(B,C),targetantagonist(B,D),targetinducer(A,F).
interacts(A,B):- targetantagonist(B,C),enzymeinducer(B,E),targetantagonist(A,D),target(D,A),target(C,B).
interacts(A,B):- targetagonist(B,E),target(D,A),enzymeinhibitor(B,C),targetinhibitor(B,E),targetinducer(A,D).
interacts(A,B):- enzymeinducer(B,F),enzymeinducer(B,E),enzymesubstrate(A,C),transporter(D,A).
interacts(A,B):- targetagonist(B,F),transporterinducer(B,E),targetinhibitor(A,C),target(F,A),target(D,A).
interacts(A,B):- targetinducer(A,F),targetagonist(B,E),target(D,A),targetantagonist(B,F),enzymeinducer(B,C).
interacts(A,B):- transporter(F,B),target(D,A),enzymesubstrate(B,E),transporterinducer(A,C),transporterinducer(A,F).
interacts(A,B):- enzyme(C,A),transporterinducer(B,D),enzymeinhibitor(B,C),transporter(D,A).
interacts(A,B):- target(D,A),targetinhibitor(A,D),enzymeinhibitor(A,C),target(E,B),enzyme(F,A).
interacts(A,B):- target(D,A),transporter(F,B),transportersubstrate(A,C),target(D,B),transportersubstrate(A,E).
interacts(A,B):- enzymeinhibitor(A,C),targetinhibitor(A,E),enzymeinducer(B,D),enzymesubstrate(A,D).
interacts(A,B):- targetagonist(A,D),transporter(C,A),targetantagonist(B,E),target(F,B),targetantagonist(B,F).
interacts(A,B):- transporterinducer(B,D),transporter(C,B),targetantagonist(A,F),targetagonist(B,E).
interacts(A,B):- targetagonist(A,D),transporterinhibitor(B,F),targetinhibitor(A,C),transporterinducer(A,E).
interacts(A,B):- targetinducer(B,E),targetantagonist(A,C),target(D,A),targetinhibitor(B,D),targetinhibitor(A,F).
interacts(A,B):- targetantagonist(B,E),target(D,B),enzymeinducer(A,C),enzymeinducer(B,C).
interacts(A,B):- enzymesubstrate(B,C),targetagonist(A,E),targetantagonist(B,E),target(D,A),target(E,B).
interacts(A,B):- enzymeinhibitor(A,F),target(D,A),targetinhibitor(B,D),enzyme(E,A),targetagonist(A,C).
interacts(A,B):- enzymeinducer(A,D),transporter(F,B),transporterinducer(A,E),enzymesubstrate(B,D),transporterinducer(B,C).
interacts(A,B):- targetantagonist(B,D),enzymeinducer(A,C),target(D,A),transporterinhibitor(B,E),targetinhibitor(A,F).
interacts(A,B):- enzymeinducer(A,E),targetagonist(B,D),transporterinhibitor(A,C),transporter(F,B).
interacts(A,B):- enzymesubstrate(B,E),targetantagonist(B,F),enzymeinhibitor(B,C),enzyme(D,A).
interacts(A,B):- transporterinducer(A,E),targetantagonist(A,C),targetinducer(B,D),targetagonist(B,F).
interacts(A,B):- enzyme(C,A),enzymesubstrate(B,C),enzymeinducer(A,D),targetantagonist(B,E),targetantagonist(A,E).
interacts(A,B):- transporter(F,B),targetantagonist(B,E),targetinhibitor(B,D),targetinducer(A,C),targetinducer(A,D).
interacts(A,B):- enzymesubstrate(A,E),transporterinhibitor(A,C),transporterinhibitor(B,D),targetagonist(B,F).
interacts(A,B):- enzyme(C,A),targetinhibitor(B,E),target(E,A),transporterinhibitor(A,D).
interacts(A,B):- enzyme(C,A),targetantagonist(B,D),target(D,A),target(E,B),transporterinducer(A,F).
interacts(A,B):- targetinhibitor(A,D),transporterinducer(B,C),enzymesubstrate(B,F),targetantagonist(A,E).
interacts(A,B):- transportersubstrate(B,D),targetinhibitor(B,E),targetagonist(B,E),targetinhibitor(A,C).
interacts(A,B):- transporterinhibitor(B,E),enzyme(D,B),targetinducer(B,C),targetagonist(A,C).
interacts(A,B):- enzyme(F,B),targetagonist(A,E),targetantagonist(B,E),enzymeinhibitor(A,D),targetagonist(B,C).
interacts(A,B):- transportersubstrate(A,F),targetinhibitor(A,C),transporterinducer(B,E),enzymesubstrate(B,D).
interacts(A,B):- targetagonist(A,D),transporter(C,B),targetantagonist(B,E),targetinhibitor(B,D),transporterinhibitor(A,F).
interacts(A,B):- targetagonist(A,F),transporter(C,B),enzymeinducer(B,D),enzyme(E,A).
interacts(A,B):- transporter(C,A),target(D,A),enzymesubstrate(B,E),enzymesubstrate(A,E),enzymeinhibitor(A,E).
interacts(A,B):- enzyme(C,A),targetinducer(B,E),transporter(D,B),enzyme(F,B).
interacts(A,B):- enzymesubstrate(B,D),transporterinducer(B,F),enzymeinhibitor(A,C),enzymeinhibitor(B,D),enzymeinhibitor(B,E).
interacts(A,B):- targetantagonist(B,C),targetantagonist(B,E),transporterinhibitor(A,D),targetantagonist(B,F),targetagonist(B,C).
interacts(A,B):- enzymeinhibitor(A,C),enzymeinhibitor(B,F),enzymesubstrate(B,D),enzymeinducer(B,E).
interacts(A,B):- transportersubstrate(A,D),targetinducer(B,C),targetinhibitor(B,E),targetagonist(B,C).
interacts(A,B):- target(D,A),targetagonist(A,D),transporterinducer(B,F),targetinducer(A,C),transportersubstrate(A,E).
interacts(A,B):- targetagonist(A,D),enzymesubstrate(B,C),target(D,A),target(F,B),transporterinhibitor(A,E).
interacts(A,B):- targetinducer(A,E),enzymesubstrate(B,C),enzymesubstrate(A,C),transporterinhibitor(B,D).
interacts(A,B):- target(C,A),enzyme(D,B),targetinducer(A,C),transporterinducer(B,E).
interacts(A,B):- enzymesubstrate(A,E),targetantagonist(A,F),targetinhibitor(A,C),targetagonist(B,D).
interacts(A,B):- transportersubstrate(B,C),targetantagonist(B,E),targetinhibitor(A,E),enzymeinhibitor(A,D),targetinhibitor(B,F).
interacts(A,B):- enzymeinducer(A,E),enzymesubstrate(B,D),target(C,A),targetinhibitor(B,F),targetagonist(A,C).
interacts(A,B):- transportersubstrate(A,F),transporterinhibitor(B,C),enzymeinhibitor(A,D),transportersubstrate(A,E).
interacts(A,B):- targetinhibitor(B,C),targetantagonist(B,E),transporter(F,A),targetinducer(A,C),targetinducer(A,D).
interacts(A,B):- target(C,B),targetinhibitor(A,C),targetantagonist(B,E),targetinhibitor(B,D),targetinhibitor(A,E).
interacts(A,B):- transporter(C,A),target(D,A),enzymesubstrate(B,E),transporterinducer(A,F),enzymeinhibitor(A,E).
interacts(A,B):- transporterinhibitor(A,C),targetinducer(A,F),target(D,A),target(E,B),targetinhibitor(A,F).
interacts(A,B):- enzymeinhibitor(A,C),targetagonist(B,D),enzymeinducer(B,C),transporter(E,A).
interacts(A,B):- target(D,A),transporterinhibitor(B,F),targetantagonist(A,E),transporterinducer(A,F),enzymeinducer(B,C).
interacts(A,B):- enzymeinhibitor(B,C),targetantagonist(B,E),targetinhibitor(A,D),targetinhibitor(A,E),enzymesubstrate(A,F).
interacts(A,B):- targetantagonist(B,C),target(E,B),enzymeinducer(A,F),enzymesubstrate(B,D).
interacts(A,B):- transportersubstrate(A,F),transporter(C,A),target(D,A),transporterinhibitor(A,E),transportersubstrate(B,E).
interacts(A,B):- enzymesubstrate(B,E),enzymeinhibitor(B,F),enzymeinducer(A,D),enzymeinducer(B,C).
interacts(A,B):- targetagonist(A,C),targetantagonist(B,D),targetagonist(B,F),enzymeinhibitor(A,E).
interacts(A,B):- targetinhibitor(A,C),enzymesubstrate(B,D),transporterinhibitor(A,E),enzymeinducer(B,F),targetagonist(A,C).
interacts(A,B):- enzymesubstrate(B,C),targetantagonist(B,E),enzymeinhibitor(B,C),targetinhibitor(B,E),enzymeinhibitor(A,D).
interacts(A,B):- targetinducer(B,E),target(C,B),transporter(D,A),transportersubstrate(B,F).
interacts(A,B):- targetantagonist(B,C),enzymeinhibitor(A,F),targetinducer(A,D),transporter(E,A).
interacts(A,B):- targetantagonist(B,C),enzymeinducer(A,D),enzymesubstrate(B,D),enzymesubstrate(B,E),enzyme(D,A).
interacts(A,B):- targetinducer(B,C),targetantagonist(B,E),transportersubstrate(B,D),transportersubstrate(A,D),transporterinducer(A,D).
interacts(A,B):- targetagonist(B,D),enzymesubstrate(A,C),target(D,A),transporterinhibitor(A,F),enzymeinhibitor(A,E).
interacts(A,B):- enzymeinducer(B,F),enzymeinhibitor(B,E),enzymesubstrate(A,D),targetagonist(A,C).
interacts(A,B):- transporter(F,B),target(D,A),transporterinhibitor(A,E),transportersubstrate(B,E),targetagonist(B,C).
interacts(A,B):- enzyme(C,A),transportersubstrate(B,D),targetantagonist(A,F),transporterinducer(B,E).
interacts(A,B):- targetantagonist(B,C),target(F,A),target(D,A),target(E,B),target(C,B).
interacts(A,B):- enzymeinhibitor(B,C),targetinducer(A,E),transporter(D,A),transportersubstrate(A,F).
interacts(A,B):- transporterinhibitor(A,C),targetantagonist(B,D),targetantagonist(B,E),targetantagonist(A,E),targetinhibitor(B,D).
interacts(A,B):- transporter(F,A),enzymeinhibitor(B,C),target(E,A),transporterinhibitor(A,D).
interacts(A,B):- targetinducer(B,E),transporter(D,B),targetinhibitor(A,C),targetantagonist(B,E),targetagonist(B,F).
interacts(A,B):- enzyme(C,A),transporterinducer(B,D),targetinducer(B,E),targetantagonist(B,E),transporterinducer(B,F).
interacts(A,B):- targetagonist(A,F),enzymesubstrate(A,E),transporterinhibitor(B,D),enzymeinducer(B,C).
