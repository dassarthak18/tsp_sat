import datetime
import tsplib95 as tsp
import networkx as nx
import matplotlib.pyplot as plt

def plot_graph(G,n=2):
	if n == 1:
		pos=nx.spring_layout(G)
		nx.draw_networkx(G,pos)
		labels = nx.get_edge_attributes(G,'weight')
		nx.draw_networkx_edge_labels(G,pos,edge_labels=labels)
	elif n == 2:	
		nx.draw(G, with_labels=True, font_weight='bold', node_color='blue')		
	plt.show()

def load():
	filename = input("Enter the .tsp file to process. ")
	file = 'benchmarks/'+str(filename)+'.tsp'
	t1 = datetime.datetime.now()
	problem = tsp.load(file)
	G = problem.get_graph()
	t2 = datetime.datetime.now()
	print("Time taken to load model (hr:min:sec): ", t2-t1)
	#n = int(input("Show edge weights? \n1. Yes\n2. No\n"))
	#plot_graph(G,n)
	plot_graph(G)
	return G.to_undirected()

def graph():
	n = int(input("Enter the number of nodes. "))
	m = int(input("Enter the number of edges. "))
	G = nx.Graph()
	for i in range(n):
		G.add_node(i+1)
	print("Nodes labelled from 1 to ", n, "have been added.")
	for i in range(m):
		u = int(input(f"Enter the first node of edge {i+1}. "))
		v = int(input(f"Enter the second node of edge {i+1}. "))
		w = float(input(f"Enter the weight of edge {i+1}. "))
		G.add_edge(u,v,weight = w)
	#x = int(input("Show edge weights? \n1. Yes\n2. No\n"))
	#plot_graph(G,x)
	plot_graph(G)
	return G.to_undirected()
