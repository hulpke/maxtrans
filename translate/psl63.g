#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, FPGroupStrong, GF, GL, Generators, Ngens,
#  Order, SL, Sp, proj

#  Defines: L63Identify

DeclareGlobalFunction("L63Identify@");

#  
#  * This file will contain the functions to construct the maximal
#  * subgroups of an almost simple group $G$ with $PSL(6, 3) < G <
#  * PGL2(6, 3) - note Aut(PSL)/PSL = 2x2

#  ***************************************************************
InstallGlobalFunction(L63Identify@,
function(group)
local 
   F,Print,apsl,c9,delta,factor,g,gl,group,groupquot,homom,invol,iota,
   is_novelty,l33,m12,max,maximals,newgens,phi,proj,psl,quot,sl,soc,subapsl;
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
  gl:=GL(6,3);
  sl:=SL(6,3);
  apsl:=PGL2@(6,3);
  factor:=GroupHomomorphismByImages(gl,apsl,
    apsl.1,apsl.2);
  psl:=sl@factor;
  if Print > 1 then
    Print("Setting up isomorphism");
  fi;
  # =v= MULTIASSIGN =v=
  group:=MakeHomomGeneral@(group,6,3,1,psl,apsl,factor:Print:=0);
  homom:=group.val1;
  soc:=group.val2;
  group:=group.val3;
  # =^= MULTIASSIGN =^=
  #   Set up the subgroup of the outer automorphism group induced by group
  if max then
    # =v= MULTIASSIGN =v=
    proj:=Subquo(apsl,[psl]);
    quot:=proj.val1;
    proj:=proj.val2;
    # =^= MULTIASSIGN =^=
    delta:=proj(apsl.1);
    #  diagonal aut.
    iota:=proj(apsl.3);
    Assert(1,Order(iota)=2);
    #  graph aut
    newgens:=List([1..Ngens(group)],i->group.i@homom);
    groupquot:=SubStructure(quot,List(newgens,g->proj(g)));
    is_novelty:=not IsSubset(SubStructure(quot,delta),groupquot);
    if Print > 1 then
      Print("is_novelty = ",is_novelty);
    fi;
    c9:=IsSubset(SubStructure(quot,delta*iota),groupquot);
    if Print > 1 then
      Print("c9 = ",c9);
    fi;
    invol:=apsl.3;
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
  maximals:=Concatenation(maximals,List(ReduciblesSL@(6,3:Novelties:=is_novelty)
   ,m->m@factor));
  if is_novelty then
    maximals:=Concatenation(maximals,[SLStabOfHalfDim@(6,3)@factor]);
    #  not a novelty!
  fi;
  if Print > 1 then
    Info(InfoWarning,1,"getting imprimitives");
  fi;
  Add(maximals,ImprimsMeetSL@(6,3,2)@factor);
  Add(maximals,ImprimsMeetSL@(6,3,3)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting semilinears");
  fi;
  Add(maximals,GammaLMeetSL@(6,3,2)@factor);
  Add(maximals,GammaLMeetSL@(6,3,3)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting tensor product");
  fi;
  Add(maximals,SLTensor@(2,3,3)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting symplectics");
  fi;
  Add(maximals,SP(6,3)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting orthogonals");
  fi;
  Add(maximals,NormOfO@(6,3,1)@factor);
  Add(maximals,NormOfO@(6,3,-1)@factor);
  if c9 then
    if Print > 1 then
      Info(InfoWarning,1,"getting psl33s");
    fi;
    l33:=SubMatrixGroup(6,GF(3),[[[1,0,0,0,0,0],[1,1,0,0,0,0],[1,0,2,1,0,0]
     ,[2,0,2,0,0,0]
     ,[2,0,0,0,1,0],[0,0,2,0,0,1]]
,[[2,1,0,0,0,0],[1,1,1,0,0,0],[0,1,0,0,0,0],[2,2,0,0,1,0],[1,2,0,0,0,1]
     ,[1,0,0,1,0,0]]
])@factor;
    maximals:=Concatenation(maximals,[l33,l33^invol]);
    if Print > 1 then
      Info(InfoWarning,1,"getting m12s");
    fi;
    m12:=SubMatrixGroup(6,GF(3),[[[0,1,0,0,0,2],[1,0,0,0,0,1],[0,0,0,1,0,1]
     ,[0,0,1,0,0,2]
     ,[0,0,0,0,1,0],[0,0,0,0,0,1]]
,[[0,1,1,0,0,0],[0,2,1,0,0,0],[1,1,1,0,0,0],[0,0,1,0,1,0],[0,1,2,0,0,1]
     ,[0,1,0,2,0,0]]
])@factor;
    maximals:=Concatenation(maximals,[m12,m12^invol]);
  fi;
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);


