import tsplib95 as tsp
import networkx as nx
from os import sys

def edge_cost(G,u,v):
	if G.has_edge(u,v):
		return G[u][v]['weight']
	else:
		return 0

choice = int(sys.argv[1])

if choice == 1:
	filename = str(sys.argv[2])
	file = 'benchmarks/'+str(filename)+'.tsp'
	problem = tsp.load(file)
	H = problem.get_graph()
	G = H.to_undirected()
else:
	n = int(input("Enter the number of nodes. "))
	H = nx.Graph()
	for i in range(n):
		H.add_node(i+1)
	for i in range(n):
		for j in range(n):
			if i < j:
				w = float(input(f"Enter the weight of edge {i+1} to {j+1}. (0 if no edge exists.) "))
				if w != 0:
					H.add_edge(i+1,j+1,weight = w)
	G = H.to_undirected()

nx.write_gpickle(G, "tsp.gpickle")

print("Graph loaded.")
