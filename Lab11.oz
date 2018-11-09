/*
1a)
0 -> [2]
1 -> [4 7]
2 -> [5 6]
3 -> [2]
4 -> nil
5 -> [6]
6 -> [5]
7 -> nil
8 -> [1]
*/


%1b)
declare
fun{M2L	Cond L H}	
   for I in L..H collect:C do
      {C I#for J in L..H collect:D do	
	      if {Cond I J} then {D J} end
	   end}	
   end
end
Graph = {M2L fun {$ X Y} {Or (X+3==Y) (X+5==Y)} end 0 15}
{Browse Graph}

%1c)
declare
fun{M2L	Cond L H}	
   for I in L..H collect:C do
      {C I#for J in L..H collect:D do	
	      if {Cond I J} then {D J} end
	   end}	
   end
end
fun{Rand P L H}
   {M2L fun{$ X Y} ({OS.rand} mod 100)>(100-P)end L H}
end
Graph2 = {Rand 100 0 15}
{Browse Graph2}


/*
2a)
FoldL applies the function over each node. After it is applied to a node, you get an updated graph, so by the end you will get the fully updated graph with the function being applied to each node. The function that is being applied to each node will grab the successors of a node A and see what other node contains contain the node A in the succesor and add the successors of node A to to the successor of that node.

*/
fun{DeclTrans G}
   Xs={Map G fun {$ X#_} X end}
in
   {Fold L Xs
    fun	{$ InG X}
       SX = {Succ X InG} in
       {Map InG
	fun{$ Y#SY}
	   Y#if	{Member	X SY} then
		{Union SY SX} else SY end
	end}
    end	G}
end

%increases at Y|{Union A2 B}
%3a loop through and compare every element