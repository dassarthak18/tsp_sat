import networkx as nx
from z3 import *

def toSMT2Benchmark(f, status="unknown", name="benchmark", logic=""):
	v = (Ast * 0)()
	if isinstance(f, Solver):
		a = f.assertions()
		if len(a) == 0:
			f = BoolVal(True)
		else:
			f = And(*a)
	return Z3_benchmark_to_smtlib_string(f.ctx_ref(), name, logic, status, "", 0, v, f.as_ast())

def edge_cost(G,u,v):
	if G.has_edge(u,v):
		return G[u][v]['weight']
	else:
		return 0

G = nx.read_edgelist("graph.edgelist")

u = 1
k = G.number_of_nodes()
s = Solver()
err = 0

# Upper bound obtained from an existing TSP heuristic
try:
	path = nx.algorithms.approximation.traveling_salesman.christofides(G)
	ub = 0.0
	i = 0
	while i < len(path)-1:
		ub += edge_cost(G,path[i],path[i+1])
		i = i+1
	with open("path.txt", "w") as file:
		if len(path) == k+1:
			file.write(str(path)+"\n")
			file.write(str(ub))
		else:
			err = 1
except:
	err = 1

if err == 1:
	with open("path.txt", "w") as file:
		file.write("Error")
	exit(0)

# SAT Encoding

exp1 = And(Bool(f"v{u}_0"),Bool(f"v{u}_{k}")) # The path forms a cycle starting and ending in u

exp2 = Bool("exp2")
exp2 = True
for i in range(k+1):
	for j in nx.nodes(G):
		exp2a = Bool("exp2a")
		exp2a = True
		for l in nx.nodes(G):
			if l != j:
				exp2a = And(exp2a, Not(Bool(f"v{l}_{i}")))
		exp2 = And(exp2, Implies(Bool(f"v{j}_{i}"), exp2a)) # The cycle is a valid path

exp3 = Bool("exp3")
exp3 = True
for i in range(k):
	for j in nx.nodes(G):
		exp3a = Bool("exp3a")
		exp3a = False
		for l in nx.neighbors(G, j):
			exp3a = Or(exp3a, Bool(f"v{l}_{i+1}"))            
		exp3 = And(exp3, Implies(Bool(f"v{j}_{i}"), exp3a)) # The cycle exists in the given graph

exp4 = Bool("exp4")
exp4 = True
for i in nx.nodes(G):
	for j in range(1,k):
		exp4a = Bool("exp4a")
		exp4a = True
		for l in range(1,k):
			if l != j:
				exp4a = And(exp4a, Not(Bool(f"v{i}_{l}")))
			exp4 = And(exp4, Implies(Bool(f"v{i}_{j}"),exp4a))
exp4b = Bool("exp4b")
exp4b = True
for i in range(1,k):
	exp4b = And(exp4b, Not(Bool(f"v{u}_{i}")))
exp4 = And(exp4, exp4b) # The cycle is a Hamiltonian cycle

# Encoding path cost into SAT solver for setting a bound
exp5 = Bool("exp5")
exp5 = True
for i in range(k):
	c_i = Real(f"c{i}")
	for j in nx.nodes(G):
		for l in nx.nodes(G):
			exp5 = And(exp5, Implies(And(Bool(f"v{j}_{i}"),Bool(f"v{l}_{i+1}")), c_i == edge_cost(G,j,l)))
c = Real("c")
c = 0.0
for i in range(k):
	c = c + Real(f"c{i}")

# Writing our encoding to an smt file

s.add(exp1, exp2, exp3, exp4, exp5)
f = open("graph_raw.smt2", "w")
f.write(toSMT2Benchmark(s))
f.close()

print("Graph encoded and SMT file written.")
