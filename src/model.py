import networkx as nx

def calc_cost_subs(G,path):
	cost = 0.0
	i = 0
	while i < len(path)-1:
		cost += G[path[i]][path[i+1]]['weight']
		i = i+1
	return cost

G = nx.read_edgelist("graph.edgelist")
k = G.number_of_nodes()

with open("model.txt", "r") as file:
	string = file.readlines()

check = string[0].strip()
path = []
for i in range(k+1):
	path.append('0')
for i in range(2,len(string)-1):
	if "Bool" in string[i].strip():
		if "true" in string[i+1].strip():
			x = string[i].strip()
			y = x[x.find("v")+1:x.find("_")]
			z = x[x.find("_")+1:x.find(" () ")]
			path[int(z)] = str(y)

cost = calc_cost_subs(G,path)

with open("path.txt", "w") as file:
	file.write(str(path)+"\n")
	file.write(str(cost))
