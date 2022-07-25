# Vertex-Cover based Polynomial SAT Solver

C++ implementation of the paper "Polynomial Exact-3-SAT-Solving Algorithm" from Matthias Michael Mueller, 2020-Sep-19, Version E-1.1. In graph theory, a vertex cover (sometimes node cover) of a graph is a set of vertices that includes at least one endpoint of every edge of the graph. In computer science, the problem of finding a minimum vertex cover is a classical optimization problem. It is NP-hard, so it cannot be solved by a polynomial-time algorithm if P ≠ NP. Moreover, it is hard to approximate – it cannot be approximated up to a factor smaller than 2 if the unique games conjecture is true. On the other hand, it has several simple 2-factor approximations. It is a typical example of an NP-hard optimization problem that has an approximation algorithm. Its decision version, the vertex cover problem, was one of Karp's 21 NP-complete problems and is therefore a classical NP-complete problem in computational complexity theory. Furthermore, the vertex cover problem is fixed-parameter tractable and a central problem in parameterized complexity theory. This is an implementation of a polynomial time and space bound algorithm to identify if a given SAT formula is satisfiable or not.

The paper describes an algorithm which is supposed by the author to be capable of solving any instance of a 3-SAT CNF in maximal O(n15), whereby n is the variable index range within the 3-SAT CNF to solve. The presented algorithm imitates the proceeding of an exponential, fail-safe solver. This exponential solver stores internal data in m-SAT clauses, with 3 ≤ m ≤ n. The polynomial solver works similarly, but uses 3-SAT clauses only to save the same data. The paper explains how, and proves why this can be achieved. 

Problems denoted as ‘NP-complete’ are those algorithms which need an amount of computing time or space which grows exponentially with the problem size n. If it should be accomplished to solve in general at least one of those problems in polynomial time and space, all NP-complete problems out of the complexity class NP could from then on be solvable much more efficiently. Finding the answer to the open question if such a faster computation is possible at all is called the P versus NP problem. The paper describes an algorithm which is supposed by its author to solve the NP-complete problem ‘exact-3-SAT’ in polynomial time and space. This persuasion comes from the fact that the implementation of the algorithm correctly solved absolutely every 3-SAT CNF which was given as input. Those 3-SAT CNFs had a size n of up to 26, in the course of around 6 months at least one million of them have been processed with always correct output. Of course one must be skeptical, many attempts to build a polynomial 3-SAT solver failed in the early stages or the related algorithm did later turn out to be incorrect. The author of this paper does nevertheless believe the presented algorithm is relevant to the scientific community, because it did never fail and because it is extremely simple and can therefore easily be further examined by any interested reader. 

## Requirements

We have tested the implementation on Ubuntu Linux and MacOS Monterey and expect to work on any modern Linux or Mac based platform. 

## Compilation

The entire DMM based SAT solver is implemnted in one file, no Makefile required. We typically compile the file with:

```g++ poly.cc -o poly -std=c++11 -O3``` 

After compilation, the file "poly" is being produced in the directory.

## Running the SAT Solve

The repository contains a few test instances. You can run the solverwith default parameters:

```./poly FILE.cnf <threads>```

This will load the CNF file and run <threads> instances to solve it. When a solution is found (the system evolved to an energy level of zero unsat clauses), the variable assignments are being printed.

## Restrictions

This implementation is restricted to 3-SAT formulations where each clause has to have exactly three literals.

