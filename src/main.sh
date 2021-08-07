# Load graph
if [ "$1" = "v1" ]; then
	echo "Loading tsp file $2.tsp."
	python3 graph.py "1" "$2"
elif [ "$1" = "v2" ]; then
	echo "Loading graph manually."
	python3 graph.py "2" "None"
else
	echo "Invalid arguments provided."
	exit 1
fi

# Encode graph into SMTLIB2
python3 encode.py
tsp_path=$(awk 'NR==1' path.txt)
tsp_cost=$(awk 'NR==2' path.txt)
if [ "$tsp_path" = "Error" ]; then
	echo "No TSP solution exists to the given graph."
	rm graph.edgelist
	rm path.txt
	exit 0
fi
head -n -1 graph_raw.smt2 > temp.smt2 ; mv temp.smt2 graph_raw.smt2
echo "Christofides returned path $tsp_path with cost $tsp_cost."

# Algorithm

count=$(( 1 ))
flag=$(( 1 ))
check="sat"

while true
do
	python3 bound.py "$tsp_cost"
	echo "(get-model)" >> graph_bound.smt2
	>test_sat.smt2
	cat graph_raw.smt2 >> test_sat.smt2
	cat graph_bound.smt2 >> test_sat.smt2
	>model.txt
	z3 test_sat.smt2 >> model.txt
	check=$(awk 'NR==1' model.txt)
	if [ "$check" = "sat" ]; then
		python3 model.py
	fi
	
	if [ "$check" = "unsat" ]; then
		break
	else
		tsp_path=$(awk 'NR==1' path.txt)
		tsp_cost=$(awk 'NR==2' path.txt)
		echo "Found path $tsp_path with cost $tsp_cost."
	fi
	count=$(( count + 1 ))
done

echo "Search ended."
echo "The solution to TSP for the given graph is $tsp_path with cost $tsp_cost."

# Cleaning the directory after job is done
rm graph.edgelist
rm graph_raw.smt2
rm graph_bound.smt2
rm test_sat.smt2
rm model.txt
rm path.txt
