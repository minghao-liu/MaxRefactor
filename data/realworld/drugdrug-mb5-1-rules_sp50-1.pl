interacts(A,B):- transportersubstrate(A,D),targetinducer(B,C),enzymeinducer(A,F),targetantagonist(A,E).
interacts(A,B):- enzymesubstrate(B,C),enzymeinducer(B,D),targetantagonist(B,E),targetinhibitor(B,F),targetinhibitor(A,F).
interacts(A,B):- target(C,A),target(E,B),enzyme(D,B),targetantagonist(B,C).
interacts(A,B):- targetantagonist(B,C),targetantagonist(A,C),target(D,A),enzymeinducer(A,F),enzymeinhibitor(A,E).
interacts(A,B):- enzyme(C,A),enzyme(E,B),enzymeinducer(B,E),target(D,A),enzymeinhibitor(A,C).
interacts(A,B):- transportersubstrate(A,D),transporterinhibitor(B,C),targetantagonist(B,E),target(E,B),targetantagonist(A,F).
interacts(A,B):- targetinducer(B,E),transporterinhibitor(B,C),transporterinhibitor(A,D),targetantagonist(B,E),enzymeinducer(B,F).
interacts(A,B):- enzyme(C,A),targetinducer(B,E),transporter(D,B),targetantagonist(B,E),transporterinhibitor(A,D).
interacts(A,B):- targetinducer(A,E),transporterinhibitor(A,C),target(F,A),target(D,A),transporterinducer(B,C).
interacts(A,B):- targetinhibitor(A,D),transporterinducer(B,E),targetinducer(A,D),targetagonist(A,C).
interacts(A,B):- enzymesubstrate(B,C),enzyme(F,B),enzymesubstrate(B,D),enzymeinducer(B,C),enzymeinhibitor(A,E).
interacts(A,B):- transporterinhibitor(B,D),enzymeinducer(A,F),targetantagonist(B,E),targetagonist(A,C).
interacts(A,B):- transporterinhibitor(A,C),targetantagonist(B,E),targetinhibitor(B,D),targetagonist(A,F),targetinhibitor(B,F).
interacts(A,B):- targetinhibitor(B,C),enzymesubstrate(A,D),targetantagonist(B,E),targetinducer(B,C),transporterinhibitor(A,F).
interacts(A,B):- transporterinhibitor(A,C),transporter(E,B),enzymesubstrate(B,D),transportersubstrate(A,C),transportersubstrate(B,F).
interacts(A,B):- enzymeinhibitor(B,C),transporterinhibitor(B,D),enzyme(F,A),enzyme(E,A).
interacts(A,B):- enzyme(D,B),enzymesubstrate(B,D),transporter(E,A),targetagonist(B,C),enzyme(D,A).
interacts(A,B):- transporter(E,B),transportersubstrate(B,C),target(D,A),transporterinducer(B,C),targetinhibitor(B,D).
interacts(A,B):- targetinducer(A,E),targetinducer(A,C),enzymesubstrate(B,F),targetinducer(B,D).
interacts(A,B):- targetagonist(B,D),transporter(C,B),transportersubstrate(B,C),target(D,A),transportersubstrate(A,E).
interacts(A,B):- target(C,A),enzymeinhibitor(B,D),transporterinducer(A,E),transporterinducer(B,F).
interacts(A,B):- targetinducer(A,F),transporter(C,A),targetantagonist(B,E),targetantagonist(A,E),targetinhibitor(B,D).
interacts(A,B):- targetantagonist(B,E),transportersubstrate(B,D),targetantagonist(A,F),targetantagonist(A,C),targetinhibitor(A,F).
interacts(A,B):- targetinducer(B,E),transporterinhibitor(A,C),target(F,A),targetantagonist(B,E),target(D,A).
interacts(A,B):- transporterinducer(B,D),transportersubstrate(B,C),targetantagonist(B,E),targetagonist(A,F),transporterinducer(A,D).
interacts(A,B):- targetantagonist(A,D),transporterinducer(B,E),target(D,A),target(F,B),targetinducer(A,C).
interacts(A,B):- transporter(E,B),enzyme(F,B),enzymesubstrate(B,D),targetinducer(A,C),enzymeinhibitor(B,D).
interacts(A,B):- enzyme(F,B),target(D,A),targetinhibitor(A,D),transporterinducer(B,C),targetinhibitor(A,E).
interacts(A,B):- targetantagonist(B,D),targetinhibitor(A,C),target(D,A),target(E,B),targetinhibitor(A,E).
interacts(A,B):- targetagonist(B,E),targetagonist(A,E),targetantagonist(B,E),targetinducer(B,D),targetagonist(A,C).
interacts(A,B):- target(D,A),transporterinhibitor(A,C),transporter(E,B),transporterinducer(B,F),targetinhibitor(B,D).
interacts(A,B):- transporterinducer(A,D),targetagonist(B,E),targetagonist(A,E),enzymeinducer(A,C).
interacts(A,B):- enzymeinhibitor(B,C),transportersubstrate(B,D),enzymesubstrate(A,C),targetinducer(B,E).
interacts(A,B):- enzymesubstrate(B,D),target(E,A),enzymeinhibitor(A,C),target(E,B),targetantagonist(B,F).
interacts(A,B):- enzymeinducer(B,F),enzyme(E,B),targetinhibitor(A,C),transporter(D,A).
interacts(A,B):- targetantagonist(B,C),enzymesubstrate(A,E),targetinhibitor(B,C),targetinducer(B,D).
interacts(A,B):- targetinducer(A,E),targetinhibitor(B,F),targetantagonist(A,C),targetinhibitor(B,D).
interacts(A,B):- targetinducer(B,E),targetagonist(A,E),target(D,A),transporterinhibitor(A,F),targetantagonist(A,C).
interacts(A,B):- enzymeinducer(A,E),targetinducer(B,C),targetinducer(A,C),targetinhibitor(A,D).
interacts(A,B):- targetantagonist(B,C),targetagonist(A,E),enzymesubstrate(B,D),targetantagonist(A,E),targetinhibitor(B,E).
interacts(A,B):- enzymesubstrate(B,C),enzymesubstrate(B,D),target(E,B),transporterinhibitor(B,F),enzyme(D,A).
interacts(A,B):- targetagonist(A,D),target(E,A),targetantagonist(B,E),enzymeinhibitor(A,C),targetantagonist(B,F).
interacts(A,B):- targetantagonist(B,D),targetantagonist(B,E),target(E,B),transporterinducer(A,F),targetagonist(A,C).
interacts(A,B):- enzymeinducer(B,D),transporter(C,A),enzymesubstrate(B,D),transportersubstrate(B,C),enzymeinhibitor(B,D).
interacts(A,B):- targetinducer(B,E),transporterinhibitor(A,C),targetantagonist(B,E),targetinhibitor(A,D),transporterinhibitor(A,F).
interacts(A,B):- transporterinhibitor(B,E),targetantagonist(B,F),transporterinducer(A,C),transporterinhibitor(A,D).
interacts(A,B):- transporterinhibitor(B,C),transporter(C,A),targetantagonist(B,E),transportersubstrate(A,D),enzymeinducer(B,F).
interacts(A,B):- transporter(E,B),targetantagonist(A,D),target(D,A),targetinhibitor(A,D),enzymeinducer(B,C).
interacts(A,B):- transporterinhibitor(A,C),transporter(C,A),enzymesubstrate(B,D),target(F,B),transporterinhibitor(A,E).
interacts(A,B):- transporter(C,B),transporter(C,A),targetantagonist(B,E),transportersubstrate(A,D),enzyme(F,A).
