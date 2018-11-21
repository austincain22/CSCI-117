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
%{Browse Graph2}


/*
2a)
FoldL applies the function over each node. After it is applied to a node, you get an updated graph, so by the end you will get the fully updated graph with the function being applied to each node. The function that is being applied to each node will grab the successors of a node A and see what other node contains contain the node A in the succesor and add the successors of node A to to the successor of that node.
*/

%2b
declare
Edges = {NewCell 0}
Un = {NewCell 0}
Sy = {NewCell 0}
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
		Un:=@Un+1
		{Union SY SX}
	     else
		Sy:=@Sy+1
		SY
	     end
	end}
    end	G}
end
Graph1 = {DeclTrans {M2L fun {$ X Y} {Or (X+3==Y) (X+5==Y)} end 0 15}}
{Browse 'Edges added'#@Edges}
{Browse 'Union called'#@Un}
{Browse 'SY Returned'#@Sy}


%2c
declare
Edg = {NewCell 0}
Gmc = {NewCell 0}
proc {StateTrans GM}
   L={Array.low GM}
   H={Array.high GM}
in
   for K in L..H do
      for I in L..H do
	 Gmc:=@Gmc+1
	 if GM.I.K then
	    for J in L..H do
	       Gmc:=@Gmc+1
	       if GM.K.J then
		  if @GM.I.J == false then
		     Edg:=@Edg+1
		  end
		  Gmc:=@Gmc+1
		  GM.I.J:=true
	       end
	    end
	 end
      end
   end
end
fun {M2L GM}
   L={Array.low GM}
   H={Array.high GM}
in
   for I in L..H collect:C do
      {C I#for J in L..H collect:D do
	      if GM.I.J then {D J} end
	   end}
   end
end
fun {L2M GL}
   M={Map GL fun {$ I#_} I end}
   L={FoldL M Min M.1}
   H={FoldL M Max M.1}
   GM={NewArray L H unit}
in
   for I#Ns in GL do
      GM.I:={NewArray L H false}
      for J in Ns do GM.I.J:=true end
   end
   GM
end
declare GM in
{StateTrans GM={L2M [1#[2 3] 2#[1] 3#nil]}}
{Browse {M2L GM}}
%Graph1 = {StateTrans {M2L fun {$ X Y} {Or (X+3==Y) (X+5==Y)} end 0 15}}
{Browse 'Edges added'#@Edg}
{Browse 'GM accessed'#@Gmc}

%3a loop through and compare every element
declare
fun{Compare Xs Ys}
   case Xs#Ys of nil#nil then true
   [] ((X#Xl)|Xr)#((Y#Yl)|Yr) andthen X==Y then
      fun{Help Xl Yl}
	 case Xl#Yl of nil#nil then true
	 [] (Xl|Xf)#(Yl|Yf) andthen Xl == Yl then
	    {Help Xf Yf}
	 else false
	 end
      end
   in
      if {Help Xl Yl} then 
	 {Compare Xr Yr}
      else false
      end
   [] (X|Xr)#(Y|Yr) then false
   else false
   end
end
fun{M2L	Cond L H}	
   for I in L..H collect:C do
      {C I#for J in L..H collect:D do	
	      if {Cond I J} then {D J} end
	   end}	
   end
end
Graph = {M2L fun {$ X Y} {Or (X+3==Y) (X+5==Y)} end 0 15}
Graph2 = {M2L fun {$ X Y} {Or (X+3==Y) (X+5==Y)} end 0 15}
{Browse {Compare Graph Graph2}}

%3b
declare
proc{Both G}
   {Browse 'start'}
   G1 = {DeclTrans G}
   {Browse 'middle'}
   G2 = G
   {StateTrans G2}
   {Browse 'finish'}
in
   {Browse 'G1'#G1#'G2'#G2}
   {Browse 'Compare'#{Compare G1 G2}}
end


%3c
{Both {M2L fun {$ X Y} {Or (X+3==Y) (X+5==Y)} end 0 500}}
{Both {M2L fun {$ X Y} {Or (X+3==Y) (X+5==Y)} end 0 100}}
/*
The declaritive algorithm has better performance than the stateful algorithm
*/

%4a
/*
Stateful programs tend to be more monolithic than declarative programs,
because explicit state can be modified in any order.
*/

%4b
/*
Yes, because the algorithm will still go to them but no edges will be formed from it.
*/

%4c
/*
In the stateful algorithm it sets an edge to true every time even though it may have already been true.
										*/







% Question 6 from lab 10: 

declare A Temp Left Right

proc {Merge A Temp Left Right Mid}
   local I1 = {NewCell Left}
   I2 = {NewCell Mid+1} in
   for Curr in Left..Right do
		%*****1******
      if @I1 == Mid+1 then             % Left Sublist exhausted
         A.Curr := Temp.@I2
         I2:=@I2+1
      elseif @I2 > Right then          % Right sublist exhausted
         A.Curr := Temp.@I1
         I1:=@I1+1
      elseif Temp.@I1 =< Temp.@I2 then % Get smaller value
         A.Curr := Temp.@I1
         I1:=@I1+1
      else
         A.Curr := Temp.@I2
         I2:=@I2+1
      end
   end
   end
end

proc {MergeSort A Temp Left Right}
   if (Left == Right) then skip        % List has one record
   else
   local Mid = (Left + Right) div 2 in % Select midpoint
      {MergeSort A Temp Left Mid}      % MergeSort First Half
      {MergeSort A Temp Mid+1 Right}   % MergeSort Second Half
      for I in Left..Right do 	    % Copy subarray
	   Temp.I := A.I end 
      {Merge A Temp Left Right Mid}    % Merge back to A
   end
   end
end

Left = 0
Right = 9
A = {NewArray Left Right 0}
for I in Left..Right do A.I := (I mod 3) end
Temp = {NewArray Left Right 0}
{MergeSort A Temp Left Right}
for I in Left..Right do {Browse A.I} end

/*
Here is the general invariant for MergeSort: 

1.	If left <= right, then mergesort(A, temp, left, right) terminates and A[left..right] is sorted.

Here are the invariants that are true each time we get to position *1* in the Merege function
1.	Both temp[left..mid] and temp[mid+1..right] are sorted
2.	A[left..curr-1] is sorted and contains the elements of temp[left..i1-1] and temp[mid+1..i2-1]
3.	temp[i1] >= temp[mid+1..i2-1]
4.	temp[i2] >= temp[left..i1-1].

This proof is done by strong induction on n = right - left
Complete the proof be verifying the following steps:
1.	The recursive calls are on lists smaller than size n
-when it makes the recursive call it splits the array in half constantly until it gets down to one element so it's constistently getting smaller.

2.	The invariants are true in the base case when Merge is first called
-The array from low to high is sorted.
					       
3.	The invariants are maintained in the recursive case, showing that if the invariants are true, they will be true for the next iteration of the for loop
-The list is progressively getting smaller and sorted along the way so it will sort it accordingly.


4.	The invariants imply the MergeSort invariant upon termination, when the loop exits 
-absally when the loop exits then the array from low to high will be sorted.
*/