# An exact solution to TSP using SAT solving and TSP heuristics

A path-enumeration based approach with the help of z3 Theorem Prover in order to find an exact solution to the Travelling Salesman Problem (TSP), using as an upper bound an optimal solution as obtained from Christofides algorithm.

## Prerequisites

1. **Python 3.7 or higher.**
2. **Colorama.** Can be installed using the terminal command

    ```shell
       pip3 install colorama
    ```
3. **Numpy and Matplotlib.** Can be installed using the terminal command

    ```shell
       pip3 install numpy matplotlib
    ```
4. **TSPLIB95 and Networkx.** Can be installed using the terminal command

    ```shell
       pip3 install networkx tsplib95
       pip3 install --upgrade networkx
    ```
5. **z3 Theorem Prover.** Can be installed using the terminal command

    ```shell
       pip3 install z3-solver
       pip3 install --upgrade z3-solver
    ```
    Their [github repository](https://github.com/Z3Prover/z3) can be checked for further details.

## Source Code

A source code for the algorithm can be found in the ./src/ directory. To run the algorithm, one can install the prerequisites and then run the following command in terminal.

```shell
git clone https://github.com/dassarthak18/tsp_sat.git
cd tsp_sat/src
python3 main.py
```
