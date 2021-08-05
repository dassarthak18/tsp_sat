import datetime
import networkx as nx
import z3
from load import *
from colorama import Fore, Style

def edge_cost(G,u,v):
	if G.has_edge(u,v):
		return G[u][v]['weight']
	else:
		return 0

def calc_cost_subs(G,path,flag=0):
	cost = 0.0
	i = 0
	while i < len(path)-1:
		cost += edge_cost(G,path[i],path[i+1])
		i = i+1
	if flag == 0:
		print(Fore.GREEN +"Found path " + str(path) + " with cost " + str(cost) + ".")
	return cost

def heuristic(G):
	path = nx.algorithms.approximation.traveling_salesman.christofides(G)
	ub = calc_cost_subs(G,path,1)
	return ub

def z3_path_subs(G,u=1):
	k = G.number_of_nodes()
	s = z3.Solver()

	# Upper bound obtained from an existing TSP heuristic
	t5 = datetime.datetime.now()
	ub = heuristic(G)
	t6 = datetime.datetime.now()
	print(Style.RESET_ALL + "Time taken to obtain a TSP upper bound (hr:min:sec): ", t6-t5)

	# SAT Encoding

	t1 = datetime.datetime.now()
	print(Style.RESET_ALL + "Encoding graph into SAT.")

	exp1 = z3.And(z3.Bool(f"v{u}_0"),z3.Bool(f"v{u}_{k}")) # The path forms a cycle starting and ending in u

	exp2 = z3.Bool("exp2")
	exp2 = True
	for i in range(k+1):
		for j in nx.nodes(G):
			exp2a = z3.Bool("exp2a")
			exp2a = True
			for l in nx.nodes(G):
				if l != j:
					exp2a = z3.And(exp2a, z3.Not(z3.Bool(f"v{l}_{i}")))
			exp2 = z3.And(exp2, z3.Implies(z3.Bool(f"v{j}_{i}"), exp2a)) # The cycle is a valid path

	exp3 = z3.Bool("exp3")
	exp3 = True
	for i in range(k):
		for j in nx.nodes(G):
			exp3a = z3.Bool("exp3a")
			exp3a = False
			for l in nx.neighbors(G, j):
				exp3a = z3.Or(exp3a, z3.Bool(f"v{l}_{i+1}"))            
			exp3 = z3.And(exp3, z3.Implies(z3.Bool(f"v{j}_{i}"), exp3a)) # The cycle exists in the given graph

	exp4 = z3.Bool("exp4")
	exp4 = True
	for i in nx.nodes(G):
		for j in range(1,k):
			exp4a = z3.Bool("exp4a")
			exp4a = True
			for l in range(1,k):
				if l != j:
					exp4a = z3.And(exp4a, z3.Not(z3.Bool(f"v{i}_{l}")))
				exp4 = z3.And(exp4, z3.Implies(z3.Bool(f"v{i}_{j}"),exp4a))
	exp4b = z3.Bool("exp4b")
	exp4b = True
	for i in range(1,k):
		exp4b = z3.And(exp4b, z3.Not(z3.Bool(f"v{u}_{i}")))
	exp4 = z3.And(exp4, exp4b) # The cycle is a Hamiltonian cycle

	# Encoding path cost into SAT solver for setting a bound
	exp5 = z3.Bool("exp5")
	exp5 = True
	for i in range(k):
		c_i = z3.Real(f"c{i}")
		for j in nx.nodes(G):
			for l in nx.nodes(G):
				exp5 = z3.And(exp5, z3.Implies(z3.And(z3.Bool(f"v{j}_{i}"),z3.Bool(f"v{l}_{i+1}")), c_i == edge_cost(G,j,l)))
	c = z3.Real("c")
	c = 0.0
	for i in range(k):
		c = c + z3.Real(f"c{i}")

	s.add(c <= ub) # Setting an upper bound to TSP cost

	# Inputting the graph encoding to the SAT Solver
	s.add(exp1, exp2, exp3, exp4, exp5)
	print(Style.RESET_ALL + "Done encoding.")
	t2 = datetime.datetime.now()
	print(Style.RESET_ALL + "Time taken to encode into SAT (hr:min:sec): ", t2-t1)

	# Searching for TSP solution
	t3 = datetime.datetime.now()
	count = 1
	tsp_cost = 0.0
	tsp_path = []
	flag = 1

	while True:
		if s.check() == z3.unsat:
			if count == 1:
				print(Fore.RED + "No solution to TSP exists for the given graph.")
				flag = 0
			break
		path = [] # map the truth assignment back into a valid path in G
		for j in range(k+1):
			for i in nx.nodes(G):
				x = z3.Bool(f"v{i}_{j}")
				if str(s.model()[x]) == "True":
					path.append(i)
					break
		tsp_path = path
		tsp_cost = calc_cost_subs(G,path) # calculate the cost of the path

		# Once a cycle is obtained another cycle of cost greater than equal to the previous is rejected
		s.reset()
		s.add(exp1, exp2, exp3, exp4, exp5)
		s.add(c < tsp_cost)
		count += 1

	if flag == 1:
		print(Style.RESET_ALL + "Search ended.")
		print(Style.RESET_ALL + "The solution to TSP for the given graph is " + str(tsp_path) + " with cost " + str(tsp_cost) +".")

	t4 = datetime.datetime.now()
	print(Style.RESET_ALL + "Time taken by z3 to solve TSP (hr:min:sec): ", t4-t3)
