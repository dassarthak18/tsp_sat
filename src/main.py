from algo import *

choice = 0
while choice < 1 or choice > 2:
	choice = int(input("1. Input TSP file\n2.Load a graph manually\nEnter your choice. "))
	if choice < 1 or choice > 2:
		print("Sorry, choice not recognized! Enter again.")
if choice == 1:
	G = load()
else:
	G = graph()

z3_path_subs(G,1)
