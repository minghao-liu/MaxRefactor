interacts(A,B):- enzymesubstrate(B,C),target(D,A),enzymeinhibitor(B,C),enzymesubstrate(A,E),enzyme(E,A).
interacts(A,B):- enzymesubstrate(B,C),transporter(E,B),target(D,A),targetagonist(A,F),transporterinhibitor(A,E).
interacts(A,B):- targetinhibitor(A,C),enzymesubstrate(B,D),transporter(E,A),targetinducer(A,C),enzyme(D,A).
interacts(A,B):- targetantagonist(B,C),enzymeinducer(A,D),enzymeinducer(B,D),enzyme(E,A).
interacts(A,B):- target(D,A),transporter(C,B),enzymeinhibitor(A,F),targetagonist(B,E),transportersubstrate(A,C).
interacts(A,B):- transporterinhibitor(A,C),enzymesubstrate(B,D),enzymesubstrate(A,E),enzyme(F,A),enzymeinhibitor(B,E).
interacts(A,B):- transportersubstrate(A,F),target(D,A),transporterinducer(A,C),transporterinducer(B,C),targetinhibitor(B,E).
interacts(A,B):- transporterinducer(A,E),target(D,A),transporterinducer(A,C),transporterinhibitor(B,F),transportersubstrate(B,E).
interacts(A,B):- transporter(E,B),enzymesubstrate(B,D),transporterinducer(B,F),targetinducer(A,C),enzyme(D,A).
interacts(A,B):- transporter(C,B),enzymeinducer(A,D),enzyme(F,B),targetantagonist(B,E),transporterinducer(A,C).
interacts(A,B):- targetagonist(B,C),enzymeinhibitor(A,D),enzymesubstrate(B,D),targetantagonist(B,E).
interacts(A,B):- targetantagonist(B,C),enzymeinducer(A,D),targetantagonist(B,E),target(C,A),transportersubstrate(B,F).
interacts(A,B):- targetantagonist(B,C),targetagonist(B,E),targetantagonist(B,E),transportersubstrate(A,D),targetinhibitor(A,F).
interacts(A,B):- target(E,B),enzyme(D,B),targetinhibitor(A,C),transportersubstrate(B,F).
interacts(A,B):- targetinducer(B,E),transportersubstrate(A,F),transporter(C,B),transporter(C,A),target(D,A).
interacts(A,B):- enzymeinducer(A,E),enzymeinhibitor(A,C),enzymeinhibitor(B,D),enzymesubstrate(A,D).
interacts(A,B):- targetantagonist(B,C),targetinducer(B,E),targetantagonist(B,E),targetinhibitor(A,E),transporterinducer(A,D).
interacts(A,B):- transporter(C,B),enzymesubstrate(B,D),transporterinhibitor(B,E),targetantagonist(A,F),enzymeinhibitor(B,D).
interacts(A,B):- targetagonist(A,F),targetagonist(B,E),enzymeinducer(A,C),transporterinhibitor(A,D).
interacts(A,B):- transporterinhibitor(B,C),targetagonist(B,E),targetantagonist(B,E),transporter(F,A),enzyme(D,A).
interacts(A,B):- enzymeinhibitor(A,F),enzyme(C,B),targetagonist(A,E),targetagonist(A,D).
interacts(A,B):- targetantagonist(B,C),targetagonist(B,F),targetinducer(B,F),target(D,A),enzymesubstrate(B,E).
interacts(A,B):- target(C,B),targetinhibitor(A,C),targetantagonist(A,C),enzyme(D,A).
interacts(A,B):- targetantagonist(B,F),transportersubstrate(A,D),targetinhibitor(A,E),enzymeinducer(B,C).
interacts(A,B):- enzymesubstrate(B,E),enzymeinducer(B,D),targetinhibitor(A,C),enzymeinhibitor(B,E).
interacts(A,B):- targetinhibitor(A,E),targetinhibitor(B,C),target(D,A),target(E,B),transporterinhibitor(B,F).
interacts(A,B):- enzymeinhibitor(B,D),enzymesubstrate(B,D),targetantagonist(B,E),transporterinducer(A,F),targetagonist(A,C).
interacts(A,B):- targetantagonist(B,C),transporterinhibitor(A,E),targetinhibitor(B,C),enzyme(D,A).
interacts(A,B):- transportersubstrate(A,F),target(D,A),transporter(F,B),transportersubstrate(B,C),transporter(E,A).
interacts(A,B):- transportersubstrate(A,F),transporterinducer(B,D),transporter(D,B),targetantagonist(B,E),transportersubstrate(A,C).
interacts(A,B):- enzyme(C,A),enzymeinducer(A,D),enzymeinducer(A,C),targetantagonist(B,E),target(E,B).
interacts(A,B):- targetagonist(A,E),target(D,A),enzymeinhibitor(B,C),targetantagonist(B,F),targetinhibitor(A,F).
interacts(A,B):- transporterinhibitor(B,C),transporter(C,A),target(D,A),transporterinhibitor(B,E),transportersubstrate(B,F).
interacts(A,B):- targetinhibitor(A,E),target(D,B),enzymesubstrate(B,F),transporterinducer(B,C).
interacts(A,B):- enzymeinhibitor(A,C),enzymeinhibitor(B,E),transporter(D,A),enzymeinducer(A,C).
interacts(A,B):- transporterinducer(B,D),targetantagonist(B,E),targetantagonist(A,E),target(E,B),targetagonist(A,C).
interacts(A,B):- enzymeinducer(B,D),target(E,A),targetantagonist(B,E),enzymesubstrate(A,F),targetagonist(B,C).
interacts(A,B):- targetinhibitor(B,C),targetagonist(A,E),targetantagonist(B,E),transporterinducer(A,D),enzymeinducer(B,F).
interacts(A,B):- targetinhibitor(A,D),transportersubstrate(B,E),transporterinducer(B,E),targetagonist(B,C).
interacts(A,B):- enzymeinducer(A,E),targetinhibitor(B,C),enzymesubstrate(B,D),targetinducer(A,C),targetagonist(A,C).
interacts(A,B):- transporter(F,A),target(E,B),enzymesubstrate(B,C),enzyme(D,A).
interacts(A,B):- enzymeinducer(A,D),transporterinducer(B,E),targetinhibitor(B,C),enzymesubstrate(B,D),enzymeinducer(B,F).
interacts(A,B):- transporter(F,A),targetagonist(B,C),transporter(E,B),enzymesubstrate(A,D).
interacts(A,B):- targetantagonist(B,E),transporter(F,A),transportersubstrate(A,D),targetantagonist(A,C),targetagonist(A,C).
interacts(A,B):- enzymeinducer(A,E),targetagonist(B,D),targetinducer(B,C),transporter(F,B).
interacts(A,B):- targetagonist(B,D),targetinhibitor(A,C),targetantagonist(B,E),targetinhibitor(B,D),enzymesubstrate(A,F).
interacts(A,B):- enzymesubstrate(B,D),transportersubstrate(B,C),transporterinducer(B,F),transporterinducer(A,C),targetinhibitor(A,E).
interacts(A,B):- transportersubstrate(A,F),target(D,A),transporterinhibitor(B,E),targetinducer(A,C),targetagonist(B,C).
interacts(A,B):- enzymesubstrate(B,D),target(E,A),target(C,B),targetantagonist(A,C),targetagonist(B,C).
interacts(A,B):- transportersubstrate(B,C),targetinhibitor(B,F),enzymeinhibitor(A,E),enzyme(D,A).
interacts(A,B):- targetantagonist(B,C),targetantagonist(A,D),transporterinducer(A,E),target(D,A),targetantagonist(B,F).
interacts(A,B):- target(D,A),targetagonist(A,D),targetinhibitor(A,C),transporterinducer(B,F),targetinhibitor(B,E).
interacts(A,B):- targetantagonist(B,D),enzymesubstrate(A,F),transporterinducer(A,E),targetagonist(B,C).
interacts(A,B):- targetantagonist(B,D),targetantagonist(A,D),targetantagonist(B,E),transporterinducer(B,C),targetinducer(B,D).
interacts(A,B):- targetantagonist(B,C),enzyme(F,B),transporterinducer(B,E),enzymesubstrate(B,D),targetantagonist(A,C).
interacts(A,B):- target(C,B),transporter(D,A),targetantagonist(B,E),target(F,B),targetinhibitor(A,E).
interacts(A,B):- targetinducer(B,E),targetagonist(A,E),enzymesubstrate(B,D),transportersubstrate(A,C),targetantagonist(A,F).
interacts(A,B):- transporter(C,B),transporter(C,A),enzymesubstrate(A,D),targetantagonist(B,E),targetinhibitor(B,F).
interacts(A,B):- targetantagonist(B,C),targetinducer(B,E),transporterinhibitor(A,D),targetantagonist(A,E),targetantagonist(B,E).
interacts(A,B):- enzyme(D,B),transporter(C,B),enzymesubstrate(B,D),transporterinducer(A,C),enzymeinhibitor(B,D).
interacts(A,B):- targetinhibitor(A,C),target(D,A),enzymeinducer(A,F),enzymeinhibitor(B,E),targetagonist(A,C).
interacts(A,B):- targetinducer(A,F),targetinducer(B,D),target(D,A),enzymeinhibitor(A,C),transportersubstrate(A,E).
interacts(A,B):- targetantagonist(B,C),enzymeinducer(A,D),enzyme(F,B),enzymesubstrate(B,D),enzyme(E,A).
interacts(A,B):- transporter(F,B),targetantagonist(B,E),enzymesubstrate(B,D),enzymeinhibitor(B,C),enzymeinhibitor(A,C).
interacts(A,B):- enzyme(C,A),enzyme(F,B),targetantagonist(B,E),enzymeinhibitor(A,C),transportersubstrate(B,D).
interacts(A,B):- transporter(C,B),transportersubstrate(B,C),target(D,A),target(E,B),transportersubstrate(B,F).
interacts(A,B):- transporterinducer(B,D),transporter(C,B),targetantagonist(B,E),transportersubstrate(A,C),target(E,B).
interacts(A,B):- targetantagonist(B,C),enzyme(E,B),targetagonist(A,D),targetagonist(A,F).
interacts(A,B):- transporterinhibitor(B,C),target(D,A),transporterinhibitor(B,E),transporterinducer(B,C),targetinducer(B,D).
interacts(A,B):- target(C,A),enzymesubstrate(A,E),enzyme(D,B),enzymeinhibitor(B,D).
