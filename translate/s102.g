#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, CorrectForm, FPGroupStrong, GL, Order, PSp,
#  Random, RandomProcess, SOMinus, SOPlus, Sp, SymplecticForm, 
 get_standard_gens

#  Defines: S102Identify, get_standard_gens

DeclareGlobalFunction("S102Identify@");

get_standard_gens@:=function(G)
#  /out:
#  Find standard generators of S(8,2).
#  Assumes G is S(8,2).
#  Algorithm and code by Derek Holt 13/05/2005
#  Standard gens as defined in Birmingham Atlas at that date.

local P,a,b,ord,x;
  P:=RandomProcess(G);
  repeat
    x:=Random(P);
    
  until Order(x)=34;
  #   1 in 17
  a:=x^17;
  #   a is in 2A
  repeat
    x:=Random(P);
    ord:=Order(x);
    
  until ord in Set([11,33]);
  #   1 in 11
  x:=x^(QuoInt(ord,11));
  repeat
    b:=x^Random(P);
    
  until Order(a*b)=15;
  #  1 1n 31
  return rec(val1:=a,
    val2:=b);
end;
;
InstallGlobalFunction(S102Identify@,
function(group)
local 
   F,Print,a,a1,b,b1,factor,form,group,homom,isit,max,maximals,phi,psp,sp,
   trans;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  if Print > 1 then
    Info(InfoWarning,1,"making standard group");
  fi;
  sp:=SP(10,2);
  psp:=PSp(10,2);
  factor:=GroupHomomorphismByImages(sp,psp,
    psp.1,psp.2);
  psp:=sp@factor;
  if Print > 1 then
    Info(InfoWarning,1,"making homomorphism");
  fi;
  # =v= MULTIASSIGN =v=
  b:=get_standard_gens@(group);
  a:=b.val1;
  b:=b.val2;
  # =^= MULTIASSIGN =^=
  # =v= MULTIASSIGN =v=
  b1:=get_standard_gens@(psp);
  a1:=b1.val1;
  b1:=b1.val2;
  # =^= MULTIASSIGN =^=
  group:=SubStructure(group,a,#TODO CLOSURE
    b);
  homom:=GroupHomomorphismByImages(group,psp,
    a1,b1);
  psp:=SubStructure(psp,a1,#TODO CLOSURE
    b1);
  if Print > 1 then
    Info(InfoWarning,1,"Calling FPGroupStrong");
  fi;
  # =v= MULTIASSIGN =v=
  phi:=FPGroupStrong(psp);
  F:=phi.val1;
  phi:=phi.val2;
  # =^= MULTIASSIGN =^=
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=psp,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  if Print > 1 then
    Print("getting reducibles");
  fi;
  maximals:=Concatenation(maximals,List(ReduciblesSp@(10,2),m->m@factor));
  #  two imprimitives are non-maximal - preserve orthogonals
  if Print > 1 then
    Print("getting semilinears");
  fi;
  Add(maximals,GammaSp@(10,2,5)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting orthogonals");
  fi;
  Add(maximals,SOPlus(10,2)@factor);
  # =v= MULTIASSIGN =v=
  form:=SymplecticForm@(SOMinus(10,2));
  isit:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,isit);
  trans:=CorrectForm(form,10,2,"symplectic") #CAST GL(10,2)
    ;
  Add(maximals,(SOMinus(10,2)^trans)@factor);
  return rec(val1:=homom,
    val2:=psp,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);


