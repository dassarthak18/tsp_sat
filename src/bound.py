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

G = nx.read_edgelist("graph.edgelist")
k = G.number_of_nodes()
s = Solver()

# SAT Bound Encoding

c = Real("c")
c = 0.0
for i in range(k):
	c = c + Real(f"c{i}")

# Writing our bound encoding to an smt file

bound = float(sys.argv[1])
s.add(c < bound) # Re-adjusting the upper bound
f = open("graph_bound.smt2", "w")
f.write(toSMT2Benchmark(s))
f.close()

with open("graph_bound.smt2", "r") as file:
	string = file.readlines()
	i = 0
	while True:
		line = string[i].strip()
		i = i + 1
		if "assert" in line:
			break
i = i -1

with open("graph_bound.smt2", "w") as file:
	for j in range(len(string)):
		if j >= i:
			file.write(string[j])
