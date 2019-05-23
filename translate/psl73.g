#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, FPGroupStrong, Generators, Ngens, SL, SO

#  Defines: L73Identify

DeclareGlobalFunction("L73Identify@");

#  
#  * This file contains the functions to construct the maximal
#  * subgroups of an almost simple group $G$ with $PSL(7, 3) < G <
#  * PSL2(7, 3) - note Aut(PSL)/PSL = 2

#  ***************************************************************
InstallGlobalFunction(L73Identify@,
function(group)
local 
   F,Print,apsl,factor,g,group,homom,is_novelty,max,maximals,newgens,phi,psl,sl,
   soc,subapsl;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  if Print > 1 then
    Print("Making standard group");
  fi;
  sl:=SL(7,3);
  apsl:=PSL2@(7,3);
  factor:=GroupHomomorphismByImages(sl,apsl,
    apsl.1,apsl.2);
  psl:=sl@factor;
  if Print > 1 then
    Print("Setting up isomorphism");
  fi;
  # =v= MULTIASSIGN =v=
  group:=MakeHomomGeneral@(group,7,3,1,psl,apsl,factor:Print:=0);
  homom:=group.val1;
  soc:=group.val2;
  group:=group.val3;
  # =^= MULTIASSIGN =^=
  #   Set up the subgroup of the outer automorphism group induced by group
  if max then
    is_novelty:=Size(group)=Size(apsl);
  fi;
  if Print > 1 then
    Print("Calling FPGroupStrong");
  fi;
  # =v= MULTIASSIGN =v=
  phi:=FPGroupStrong(SubStructure(psl,List([1..Ngens(soc)],i->soc.i@homom)));
  F:=phi.val1;
  phi:=phi.val2;
  # =^= MULTIASSIGN =^=
  #  get apsl right
  newgens:=List([1..Ngens(group)],i->group.i@homom);
  subapsl:=SubStructure(apsl,newgens);
  for g in Generators(apsl) do
    if not g in subapsl then
      Add(newgens,g);
      subapsl:=SubStructure(apsl,newgens);
    fi;
  od;
  apsl:=subapsl;
  if not max then
    return rec(val1:=homom,
      val2:=apsl,
      val3:=[],
      val4:=F,
      val5:=phi);
  fi;
  maximals:=[];
  if Print > 1 then
    Info(InfoWarning,1,"getting reducibles");
  fi;
  maximals:=Concatenation(maximals,List(ReduciblesSL@(7,3:Novelties:=is_novelty)
   ,m->m@factor));
  if Print > 1 then
    Info(InfoWarning,1,"getting semilinear");
  fi;
  Add(maximals,GammaLMeetSL@(7,3,7)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting orthogonal");
  fi;
  Add(maximals,SO(7,3)@factor);
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);


