#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, Order, Random, RandomProcess, Stabilizer,
#  Sym, get_standard_gens_s82

#  Defines: S82Identify, get_standard_gens_s82

DeclareGlobalFunction("S82Identify@");

get_standard_gens_s82@:=function(G)
#  /out:
#  Find standard generators of S(8,2).
#  Assumes G is S(8,2).
#  Algorithm and code by Bill Unger 4/12/2003.
#  Standard gens as defined in Birmingham Atlas at that date.

local P,a,ab,b,count,found_5B,ord,x;
  P:=RandomProcess(G);
  repeat
    x:=Random(P);
    
  until Order(x)=24;
  #   1 in 24
  a:=x^12;
  #   a is in 2B
  repeat
    repeat
      x:=Random(P);
      ord:=Order(x);
      
    until ord in Set([5,10,15]);
    #   49 in 300
    x:=x^(QuoInt(ord,5));
    #   x is in 5B with prob 36/49
    count:=0;
    repeat
      count:=count+1;
      b:=x^Random(P);
      found_5B:=Order(a*b) in Set([14,17,18,20,21,24,30]);
      #   x in 5B gives prob 152/357 we get found_5B true here
      
    until found_5B or count=10;
    
  until found_5B;
  #   now we know that x is in 5B
  repeat
    b:=x^Random(P);
    ab:=a*b;
    
  until Order(ab)=17 and Order(ab*b)=21;
  return rec(val1:=a,
    val2:=b);
end;
;
InstallGlobalFunction(S82Identify@,
function(group)
local F,M,Print,S,a,ag,b,bg,group,homom,max,maximals,phi,s82;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  S:=SymmetricGroup(120);
  a:=(1,2)(3,4)(5,7)(6,9)(8,12)(10,14)(11,16)(15,21)(17,23)(18,25)(19,27)(20,29)
   (22,32)(24,34)(26,36)(28,38)(31,42)(35,46)(37,49)(39,52)(40,53)(41,54)(43,56)
   (44,58)(45,60)(47,63)(48,65)(51,69)(59,74)(61,76)(64,80)(67,72)(70,78)(71,85)
   (75,89)(77,83)(81,95)(82,97)(84,98)(88,102)(90,105)(94,108)(96,109)(99,111)
   (100,101)(103,113)(104,112)(114,119) #CAST S
    ;
  b:=(1,3,5,8,2)(4,6,10,15,22)(7,11,17,24,16)(9,13,19,28,39)(12,18,26,29,40)
   (14,20,30,41,55)(21,31,43,57,72)(23,33,44,59,52)(25,35,47,64,32)
   (27,37,50,68,83)(34,45,61,77,92)(36,48,66,82,42)(38,51,46,62,78)
   (49,67,65,81,96)(53,60,75,90,106)(54,70,84,99,112)(56,71,86,101,69)
   (58,73,87,95,105)(63,79,93,107,116)(74,88,103,114,120)(76,91,85,100,102)
   (80,94,89,104,115)(97,108,113,118,119)(98,110,117,111,109) #CAST S
    ;
  s82:=SubStructure(S,a,#TODO CLOSURE
    b);
  s82.Order:=47377612800;
  #   presentation from B'ham Atlas 
  F:=SubGroup(x,y,[x^2,y^5,(x*y)^17,Tuple([x,y])^3,Tuple([x,y^2])
   ^4,Tuple([x,y*x*y])^3,Tuple([x,y^2*x*y*x*y^2])^2,Tuple([x,y^2*x*y^2])
   ^3,Tuple([x,(x*y^2)^4])^2,Tuple([x,y*x*y*x*y])
   ^3,(x*y*x*y*x*y^2*x*y^-1*x*y^-2)^4]);
  phi:=GroupHomomorphismByImages(F,s82,
    a,b);
  if Print > 1 then
    Print("Setting up isomorphism");
  fi;
  #  Find standard generators of socle
  # =v= MULTIASSIGN =v=
  bg:=get_standard_gens_s82@(group);
  ag:=bg.val1;
  bg:=bg.val2;
  # =^= MULTIASSIGN =^=
  group:=SubStructure(group,ag,#TODO CLOSURE
    bg);
  group.Order:=47377612800;
  homom:=GroupHomomorphismByImages(group,s82,
    GeneratorsOfGroup(group),[a,b]);
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=s82,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  if Print > 1 then
    Print("getting maximals");
  fi;
  #   O-(8,2).2
  M:=SubStructure(s82,a^(b^2),#TODO CLOSURE
    b*a*b^2*a*b*a*b*a*b^-2*a);
  M.Order:=394813440;
  #   Index 120 
  Add(maximals,M);
  #   O+(8,2).2
  M:=SubStructure(s82,a,#TODO CLOSURE
    a^(b^2),b*a*b*a*b*a*b^-1*a*b^-2*a*b^-1*a*b);
  M.Order:=348364800;
  #   Index 136 
  Add(maximals,M);
  #   2^7.S(6,2) 2-local
  M:=SubStructure(s82,a^b,#TODO CLOSURE
    a^(b^2),a^(b^-2*a),a^(b^-1*a*b^-1),a^(b^-2*a*b*a));
  M.Order:=185794560;
  #   Index 255 
  Add(maximals,M);
  #   2^(6+4).A8 2-local [ = 2^(6+4).L(4,2) ]
  M:=SubStructure(s82,a*b*a*b^-1*a,#TODO CLOSURE
    b^-2*a*b^2,b*a*b^2*a*b*a*b^-2*a*b^-1);
  M.Order:=20643840;
  #   Index 2295 
  Add(maximals,M);
  #   2^(1+2+8).3.2.A6.2 (chief factors) 2-local
  #   2^(3+8):(L(2,2)xS(4,2)) ???
  #   M := Centralizer(s82,a);
  M:=SubStructure(s82,b*a*b^-1*a*b,#TODO CLOSURE
    b*a*b*a*b^-1*a*b^-1*a*b*a*b);
  M.Order:=8847360;
  #   Index 5355 
  Add(maximals,M);
  #   S3.S(6,2)
  M:=SubStructure(s82,b*a*b^2*a*b^-1*a*b^-2*a*b^2*a*b^-2*a*b^-1,#TODO CLOSURE
    a*b*a*b^-1*a*b^-2*a*b^-1*a*b*a*b*a*b*a*b*a*b);
  M.Order:=8709120;
  #   Index 5440 
  Add(maximals,M);
  #   2^(3+6).3.2^(3+1).L(3,2) 2-local [2^(3+6+3).(S3 x L(3,2)) ?]
  M:=SubStructure(s82,b^2*a*b^-1*a*b^-1*a*b*a*b*a*b^-2,#TODO CLOSURE
    a*b*a*b*a*b^2*a*b^-1*a*b^-1*a*b^2*a,
   a*b^2*a*b^-1*a*b^-1*a*b^-1*a*b^-1*a*b^2*a*b^-2*a*b);
  M:=Stabilizer(s82,Set([2,5,9,25,35,56,75,113]));
  M.Order:=4128768;
  #   Index 11475 
  Add(maximals,M);
  #   S10
  M:=SubStructure(s82,a*b^-1*a*b^-2*a*b^2*a*b*a*b^2*a*b^-2,#TODO CLOSURE
    b^-1*a*b^2*a*b*a*b^2*a*b^-2*a*b^-1*a*b^-1,
   a*b*a*b^-1*a*b^-1*a*b^-1*a*b^-2*a*b*a*b^2*a*b^-1);
  M.Order:=3628800;
  #   Index 13056 
  Add(maximals,M);
  #   S(4,4):2
  M:=SubStructure(s82,b^-1*a*b^-1*a*b^2*a*b^-1*a*b^2*a*b*a*b^-1*a,#TODO CLOSURE
    b^-1*a*b*a*b^2*a*b^-1*a*b^-2*a*b^2*a*b^-2*a);
  M.Order:=1958400;
  #   Index 24192 
  Add(maximals,M);
  #   A6^2.D8 [S(4,2) wr 2 ???]
  M:=SubStructure(s82,b^-1*a*b^-1*a*b^2*a*b^-2*a*b*a*b,#TODO CLOSURE
    b*a*b^2*a*b*a*b*a*b*a*b*a*b*a*b^-2,
   a*b^2*a*b^-1*a*b^-1*a*b^-1*a*b^-1*a*b*a*b*a*b*a*b^-1);
  M.Order:=1036800;
  #   Index 45696 
  Add(maximals,M);
  #   L(2,17) - unchecked for maximality
  #           - checked not in any conjugate of any above
  M:=SubStructure(s82,
   a*b*a*b^2*a*b*a*b^2*a*b*a*b^-1*a*b^-2*a*b*a*b^-2*a*b^2*a*b^-2,#TODO CLOSURE
    a*b^2*a*b^-2*a*b^-1*a*b^-1*a*b^-1*a*b^-2*a*b*a*b^-2*a*b*a*b^2*a*b^-2);
  M.Order:=2448;
  #   index 19353600 
  Add(maximals,M);
  return rec(val1:=homom,
    val2:=s82,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);


