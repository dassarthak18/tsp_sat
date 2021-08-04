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

def calc_cost_subs(G,path,min_cost=0.0,flag=0):
	new_cost = 0.0
	i = 0
	while i < len(path)-1:
		new_cost += edge_cost(G,path[i],path[i+1])
		if new_cost >= min_cost and min_cost != 0.0:
			i = -1
			break
		i = i+1
	if i == -1:
		if flag == 1:
			print(Fore.RED +"Searching.")
		return min_cost
	if flag == 1:
		print(Fore.GREEN +"Found path " + str(path) + " with cost " + str(new_cost) + ".")
	return new_cost

def heuristic(G):
	path = nx.algorithms.approximation.traveling_salesman.christofides(G)
	ub = calc_cost_subs(G,path)
	return ub

def z3_path_subs(G,u=1):
	k = G.number_of_nodes()
	s = z3.Solver()

	# Upper bound obtained from an existing TSP heuristic
	t5 = datetime.datetime.now()
	ub = heuristic(G)
	t6 = datetime.datetime.now()
	print(Style.RESET_ALL + "Time taken to obtain a TSP upper bound (hr:min:sec): ", t6-t5)

	t3 = datetime.datetime.now()
	print(Style.RESET_ALL + "Encoding graph into SAT.")

	# INIT Step - Ensures that the initial node is the source node
	exp1 = z3.Bool("exp1")
	exp1 = True
	for i in nx.nodes(G):
		if i == u:
			exp1 = z3.And(exp1, z3.Bool(f"v{i}_0"))
		else:
			exp1 = z3.And(exp1, z3.Not(z3.Bool(f"v{i}_0")))

	# NEXT Step - Ensures that the path follows correct transitions
	exp2 = z3.Bool("exp2")
	exp2 = True
	for i in range(k):
		for j in nx.nodes(G):
			exp2a = z3.Bool("exp2a")
			exp2a = False
			for l in nx.neighbors(G, j):
			    exp2a = z3.Or(exp2a, z3.Bool(f"v{l}_{i+1}"))            
			exp2 = z3.And(exp2, z3.Implies(z3.Bool(f"v{j}_{i}"), exp2a))

	# UNIQUE_NODE Step - Ensures that path has a unique node in every step
	exp3 = z3.Bool("exp3")
	exp3 = True
	for i in range(k):
		for j in nx.nodes(G):
			exp3a = z3.Bool("exp3a")
			exp3a = True
			for l in nx.nodes(G):
				if l != j:
					exp3a = z3.And(exp3a, z3.Not(z3.Bool(f"v{l}_{i+1}")))
			exp3 = z3.And(exp3, z3.Implies(z3.Bool(f"v{j}_{i+1}"), exp3a))

	# TARGET Step - Ensures that the final node is the target node
	exp4 = z3.Bool(f"v{u}_{k}")

	# EXCLUDE_REPEATED_NODE Step - Ensures that with the exception of source node, all other nodes in the path are unique
	exp5 = z3.Bool("exp5")
	exp5 = True
	for i in nx.nodes(G):
		if i == u:
			for j in range(k):
				exp5a = z3.Bool("exp5a")
				exp5a = True
				for l in range(k):
					if l != j:
						exp5a = z3.And(exp5a, z3.Not(z3.Bool(f"v{i}_{l}")))
				exp5 = z3.And(exp5, z3.Implies(z3.Bool(f"v{i}_{j}"),exp5a))
		else:
			for j in range(k+1):
				exp5a = z3.Bool("exp5a")
				exp5a = True
				for l in range(k+1):
					if l != j:
						exp5a = z3.And(exp5a, z3.Not(z3.Bool(f"v{i}_{l}")))
				exp5 = z3.And(exp5, z3.Implies(z3.Bool(f"v{i}_{j}"),exp5a))

	# BOUND Step - Ensures that the path cost has an upper bound
	exp6 = z3.Bool("exp6")
	exp6 = True
	for i in range(k):
		c_i = z3.Real(f"c{i}")
		for j in nx.nodes(G):
			for l in nx.nodes(G):
				exp_a = z3.And(z3.Bool(f"v{j}_{i}"),z3.Bool(f"v{l}_{i+1}"))
				exp = z3.Implies(exp_a, c_i == edge_cost(G,j,l))
				exp6 = z3.And(exp6,exp)
	c = z3.Real("c")
	c = 0.0
	for i in range(k):
		c = c + z3.Real(f"c{i}")
	s.add(exp6,c <= ub)

	# Inputting the graph encoding to the SAT Solver
	s.add(exp1, exp2, exp3, exp4, exp5)
	print(Style.RESET_ALL + "Done encoding.")
	t4 = datetime.datetime.now()
	print(Style.RESET_ALL + "Time taken to encode into SAT (hr:min:sec): ", t4-t3)

	# Printing potential TSP solutions
	t1 = datetime.datetime.now()
	count = 1
	min_cost = 0.0
	min_path = []
	flag = 1
	while True:
		if s.check() == z3.unsat:
			if count == 1:
				print(Fore.RED + "No solution to TSP exists for the given graph.")
				flag = 0
			break
		path = []
		for j in range(k+1):
			for i in nx.nodes(G):
				x = z3.Bool(f"v{i}_{j}")
				if str(s.model()[x]) == "True":
					path.append(i)
					break
		val = calc_cost_subs(G,path,min_cost,1)
		if val < min_cost or count == 1:
			min_path = path
		min_cost = val

		# NEGATION Step - Ensures that a previous path or its permutation does not repeat in future iterations
		exp1 = z3.Bool("exp1")
		exp2 = z3.Bool("exp2")
		exp1 = False
		exp2 = False
		for i in range(k+1):
			exp1 = z3.Or(exp1, z3.Not(z3.Bool(f"v{path[i]}_{i}")))
			exp2 = z3.Or(exp2, z3.Not(z3.Bool(f"v{path[i]}_{k-i}")))

		s.add(z3.And(exp1,exp2))
		count += 1

	if flag == 1:
		print(Style.RESET_ALL + "Search ended.")
		print(Style.RESET_ALL + "The solution to TSP for the given graph is " + str(min_path) + " with cost " + str(min_cost) +".")
	t2 = datetime.datetime.now()
	print(Style.RESET_ALL + "Time taken by z3 to solve TSP (hr:min:sec): ", t2-t1)
