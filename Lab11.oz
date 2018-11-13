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
%{Browse Graph}

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
%{Browse Graph2}


/*
2a)
FoldL applies the function over each node. After it is applied to a node, you get an updated graph, so by the end you will get the fully updated graph with the function being applied to each node. The function that is being applied to each node will grab the successors of a node A and see what other node contains contain the node A in the succesor and add the successors of node A to to the successor of that node.

*/
%2b
declare
Edges = {NewCell 0}
Y = {NewCell 0}
Z = {NewCell 0}
fun {Union A B}
   case A#B
   of nil#B then B
   [] A#nil then A
   [] (X|A2)#(Y|B2) then
      if X==Y then X|{Union A2 B2}
      elseif X<Y then X|{Union A2 B}
      elseif X>Y then Edges:=@Edges+1 Y|{Union A B2}
      end
   end
end

fun {Succ X G}
   case G of Y#SY|G2 then
      if X==Y then SY else {Succ X G2} end
   end
end

fun{DeclTrans G}
   Xs={Map G fun {$ X#_} X end}
in
   {FoldL Xs
    fun	{$ InG X}
       SX = {Succ X InG} in
       {Map InG
	fun{$ Y#SY}
	   Y#if	{Member	X SY} then
		{Union SY SX} else SY end
	end}
    end	G}
end
Graph1 = {DeclTrans {M2L fun {$ X Y} {Or (X+3==Y) (X+5==Y)} end 0 15}}
%increases at Y|{Union A2 B}
%3a loop through and compare every element