## An encoder for encoding of LTLp specifications into PDDL

Follow the encoding rules in the paper, we implement the encoding process.

We use LTL2BA to translate LTLp formulas into automata. As mentioned in the paper, this is feasible since the similarity between LTL and LTLp. We need an alphabet to map propositions in LTL to state formulas in LTLp. For example, [](GOAL(f(x1,x2)) -> PRE(a(x,y), x=y))) is a valid LTLp formula. "p" and "q" are used to represent "GOAL(f(x1,x2))" and "PRE(a(x,y), x=y))" respectively. Therefore, the LTL formula [](p -> q) is fed to LTL2BA to obtain the corresponding automaton. Then we utilize the alphabet to write the encoding reversely.


