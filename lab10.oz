% CSci 117 
% Lab 10
% 11/1/18

% Question 1: Abstractions and memory management. Consider the following ADT which allows to collect information together into a list. The ADT has three operations. The call C={NewCollector} creates a new collector C. The call {Collect C X} adds X to C’s collection. The call L={EndCollect C} returns the final list containing all collected items in the order they were collected. Here are two ways to implement collectors that we will compare:

% •	C is a cell that contains a pair H#T, where H is the head of the collected list and T is its unbound tail. Collect is implemented as: 
declare
proc {Collect C X} H T in
  {Exchange C H#(X|T) H#T}
end

% (a) Implement the NewCollector and EndCollect operations with this representation.
fun{NewCollector}
   local H in
      {NewCell H#H}
   end
end

fun{EndCollect A}
   case @A of (X|Xs)#T then T = nil end
   (@A).1
end

A = {NewCollector}
{Collect A 3}
{Collect A 5}
L = {EndCollect A}
{Inspect L}
     


% •	C is a pair H#T, where H is the head of the collected list and T is a cell that contains its unbound tail. Collect is implemented as:
declare
   proc {Collect2 C X} T in
	  {Exchange C.2 X|T T}  %old C.2 = 3|T new C.2 = T  
   end

% (b) Implement the NewCollector and EndCollect operations with this representation.
   fun {NewCollector2}
      local H T in
	 H#{NewCell H}
      end
   end
   fun {EndCollector2 A}
      case A of H#X then @X = nil end
      A.1
   end

   A = {NewCollector2}
   {Collect2 A 3}
   {Collect2 A 5}
   L = {EndCollector2 A}
   {Inspect L}
   


% (c) Bonus: Describe the process in which values are being collected, in relation to the store, and give some insight into the differences between the two implementations. 





% Question 2: Call by name. Section 6.4.4 shows how to code call by name in the stateful computation model. For this exercise, consider the following example taken from [56]:
/*
procedure swap(callbyname x,y:integer); 
var t:integer;
begin
t:=x; x:=y; y:=t
end;

var a:array [1..10] of integer;
var i:integer;

i:=1; a[1]:=2; a[2]=1; 
swap(i, a[i]); 
writeln(a[1], a[2]);
*/

% This example shows a curious behavior of call by name. Running the example does not swap i and a[i], as one might expect. This shows an undesirable interaction between destructive assignment and the delayed evaluation of an argument.
% (a) Explain the behavior of this example using your understanding of call by name.



% (b) Code the example in the stateful computation model. Use the following encoding of array[1..10]:
declare I = {NewCell 1}  
A={MakeTuple array 10}
for J in 1..10 do A.J={NewCell 0} end
(A.1) := 2
(A.2) := 1

proc {Swap X Y}
   local T in
      T = @{X}
      {X} := @{Y}
      {Y} := T
   end
end
{Swap fun{$} I end
      fun{$}A.@I end}
{Browse @(A.2)}
{Browse @(A.1)}
% That is, code the array as a tuple of cells.



% (c) Explain the behavior again in terms of your coding.






% Question 3: Call by need. With call by name, the argument is evaluated again each time it is needed. For this exercise, 
% (a) redo the swap example of the previous exercise with call by need instead of call by name. 
declare Z V I = {NewCell 1}  
A={MakeTuple array 10}

for J in 1..10 do A.J={NewCell 0} end
(A.1) := 2
(A.2) := 1

proc {Swap X Y}
   Z = {Y}
   V = {X}
in
   local T in
      T = @V
      V := @Z
      Z := T
   end
end
{Swap fun{$} I end
      fun{$}A.@I end}
{Browse @(A.2)}
{Browse @(A.1)}

% (b)Does the counterintuitive behavior still occur? If not, can similar problems still occur with call by need by changing the definition of swap?





% Question 4: Extensible arrays. (P 443) The extensible array of Section 6.5 only extends the array upwards. For this exercise, modify the extensible array so it extends the array in both directions.
declare
fun {NewExtensibleArray L H Init}
   A={NewCell {NewArray L H Init}}#Init
   proc {CheckOverflow I}
      Arr=@(A.1)
      Low={Array.low Arr}
      High={Array.high Arr}
   in
      if I>High then
	 High2={Max I High+(High-Low)}
	 Arr2={NewArray Low High2 A.2}
      in
	 for K in Low..High do Arr2.K:=Arr.K end
	 (A.1):=Arr2
      elseif I<Low then
	 if I>0 then
	    Low2 = Low-{Min I Low-(High-Low)}
	    Arr2 = {NewArray Low2 High A.2}
	 in
	    for K in Low..High do Arr2.K:=Arr.K end
	    (A.1):=Arr2
	 end
      end
   end
   proc {Put I X}
      {CheckOverflow I}
      @(A.1).I:=X
   end
   fun {Get I}
      {CheckOverflow I}
      @(A.1).I
   end
in
   extArray(get:Get put:Put)
end




% Question 5: Re-implement the dictionary from the book (P 199) that uses Key#Value pairs and linear search. Keys do not have to be integers, so the input will simply put new values at the end of the dictionary, and the get, will go through the dictionary with a linear seach. Use state to store the dictionary values, and bundle the operations. (Similar to the Stack bundle example from the book).record should contain push, get, domain
declare
fun {NewDictionary}
   Ds = {NewCell nil}
   fun {Put Key Value}
      local PutHelp in
	 Ds := fun {PutHelp Ds Key Value}
		  case @Ds
		  of nil then [Key#Value]
		  [](K#V)|Dr andthen Key==K then
		     (Key#Value)|Dr
		  [] (K#V)|Dr then
		     (K#V)|{PutHelp Dr Key Value}
		  end
	       end
      end
   end
   fun {CondGet Key Default}
      local GetHelper in
	 fun{GetHelper Ds Key Default}
	    case @Ds of nil then Default
	    [] (K#V)|Dr andthen Key == K then V
	    [] (K#V)|Dr then {GetHelper Dr Key Default}
	    end
	 end
      end
   end
   fun {Domain Ds}
      {Map @Ds fun {$ K#_} K end}
   end
in
   ops(put:Put condget:CondGet domain:Domain)
end
Dict = {NewDictionary}
{Dict.put 1 2}
{Dict.get 1 5}

% Question 6: 

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

2.	The invariants are true in the base case when Merge is first called

3.	The invariants are maintained in the recursive case, showing that if the invariants are true, they will be true for the next iteration of the for loop

4.	The invariants imply the MergeSort invariant upon termination, when the loop exits 

*/
