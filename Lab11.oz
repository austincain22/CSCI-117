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
/*fun {M2L GM}
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
end*/
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
declare GM in
{StateTrans GM={L2M [1#[2 3] 2#[1] 3#nil]}}
{Browse {M2L GM}}
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
fun{Both G}
   {Browse 'start'}
   G1 = {DeclTrans G}
   {Browse 'middle'}
   G2 = G
   {StateTrans G2}
   {Browse 'finish'}
in
   {Browse 'G1'#G1#'G2'#G2}
   {Compare G1 G2}
end
