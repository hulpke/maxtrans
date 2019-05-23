#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: A6, Append, DiagonalMatrix, Eltseq, FPGroupStrong,
#  Factorisation, GF, GL, Generators, Image, IsSquare, Ngens, PrimitiveElement,
#  Random, SL, SO, SU, SetToSequence, SquareRoot, SubfieldSL

#  Defines: A6, L3p2Identify, SubfieldSL

DeclareGlobalFunction("L3p2Identify@");

#  
#  functions in this file are:
#  SubfieldSL(p)
#  A6(q)
#  L3p2Maximals(group, p)

#  ****************************************************************
SubfieldSL@:=function(p)
local gens,i,newgens;
  gens:=SetToSequence(Generators(SL(3,p)));
  newgens:=[];
  for i in [1..Size(gens)] do
    Add(newgens,Eltseq(gens[i]) #CAST SL(3,p^2)
      );
  od;
  return SubStructure(SL(3,p^2),newgens);
end;
;
#  ***********************************************************
A6@:=function(q)
local b5,group,h_2,half,hbar_2,omega,r5,z;
  Assert(1,Size(CollectedFactors(q))=1);
  Assert(1,IsSquare(5 #CAST GF(q)
    ));
  r5:=SquareRoot(5 #CAST GF(q)
    );
  b5:=((-1+r5)/2) #CAST GF(q)
    ;
  z:=PrimitiveElement(GF(q));
  omega:=z^(QuoInt((q-1),3));
  h_2:=(omega-b5) #CAST GF(q)
    *(2^-1);
  hbar_2:=(omega^2-b5) #CAST GF(q)
    *(2^-1);
  half:=(2^-1) #CAST GF(q)
    ;
  group:=SubStructure(GL(3,q),DiagonalMat([1,-1,-1]),#TODO CLOSURE
    [0,1,0,0,0,1,1,0,0],[-1,0,0,0,0,-1,0,-1,0]
   ,[half,-half,-h_2,-half,half,-h_2,hbar_2,hbar_2,0]);
  return group;
end;
;
InstallGlobalFunction(L3p2Identify@,
function(group,q)
local 
   F,Print,a6,apsl,diag,fac,factor,gl,group,groups,homom,image,invol,max,
   maximals,newgens,p,pgammal,pgl,phi,psl,sl,so3,soc,su,subf,type;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  fac:=CollectedFactors(q);
  p:=fac[1][1];
  Assert(1,p > 2);
  Assert(1,fac[1][2]=2);
  if Print > 1 then
    Print("Making standard group");
  fi;
  gl:=GL(3,p^2);
  sl:=SL(3,p^2);
  apsl:=PGammaL2@(3,p^2);
  factor:=GroupHomomorphismByImages(gl,apsl,
    apsl.1,apsl.2);
  psl:=sl@factor;
  pgl:=gl@factor;
  pgammal:=SubStructure(apsl,apsl.1,#TODO CLOSURE
    apsl.2,apsl.3);
  if Print > 1 then
    Print("Setting up isomorphism");
  fi;
  # =v= MULTIASSIGN =v=
  group:=MakeHomomGeneral@(group,3,p,2,psl,apsl,factor:Print:=0);
  homom:=group.val1;
  soc:=group.val2;
  group:=group.val3;
  # =^= MULTIASSIGN =^=
  if Print > 1 then
    Print("Calling FPGroupStrong");
  fi;
  # =v= MULTIASSIGN =v=
  phi:=FPGroupStrong(SubStructure(psl,List([1..Ngens(soc)],i->soc.i@homom)));
  F:=phi.val1;
  phi:=phi.val2;
  # =^= MULTIASSIGN =^=
  if Print > 1 then
    Print("Identifying group");
  fi;
  #   Also get the generators of apsl correct
  newgens:=List([1..Ngens(group)],i->group.i@homom);
  image:=Image(homom);
  if image=psl then
    type:="psl";
    apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.1,apsl.3,apsl.4]));
  elif image=apsl then
    type:="aut_psl";
    apsl:=SubStructure(apsl,newgens);
  elif image=SubStructure(apsl,apsl.1,#TODO CLOSURE
    apsl.2) then
    type:="pgl";
    apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.3,apsl.4]));
  elif image=pgammal then
    type:="pgammal";
    apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.4]));
  elif Size(image)=6*Size(psl) then
    type:="psl.3+";
    apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.4]));
  elif Size(image)=4*Size(psl) then
    type:="psl.2^2";
    apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.1]));
    #  want invol in coset of apsl.4
    invol:=Random(Image(homom));
    while not invol*apsl.4 in pgl do
      invol:=Random(Image(homom));
    od;
  else
    Assert(1,Size(image)=2*Size(psl));
    if SubStructure(apsl,Concatenation(newgens,[apsl.1]))
     =SubStructure(apsl,apsl.1,#TODO CLOSURE
      apsl.2,apsl.3) then
      type:="psl.2_G";
      apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.1,apsl.4]));
      invol:=group.(Ngens(group))@homom;
    elif SubStructure(apsl,Concatenation(newgens,[apsl.1]))
     =SubStructure(apsl,apsl.1,#TODO CLOSURE
      apsl.2,apsl.4) then
      type:="psl.2_A";
      apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.1,apsl.3]));
      invol:=group.(Ngens(group))@homom;
    else
      Assert(1,SubStructure(apsl,Concatenation(newgens,[apsl.1]))
       =SubStructure(apsl,apsl.1,#TODO CLOSURE
        apsl.2,apsl.3*apsl.4));
      type:="psl.2_AG";
      apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.1,apsl.4]));
      invol:=group.(Ngens(group))@homom;
    fi;
  fi;
  if Print > 1 then
    Print("type =",type);
  fi;
  diag:=GL(3,p^2).1@factor;
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=apsl,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  #  
  #  * Reducible - if we have psl then we get 2 classes, conjugate under
  #  * inverse transpose. Otherwise, we get two novelties, intersections
  #  * are point with line containing it and point with line not
  #  * containing it. In both cases the two groups are returned as matrix
  #  * groups, so we factor by the centre before applying homom.
  
  if Print > 1 then
    Info(InfoWarning,1,"getting reducibles");
  fi;
  if type in Set(["psl","pgl","psl.2_G","pgammal"]) then
    Add(maximals,SLPointStab@(3,p^2)@factor);
    Add(maximals,SLStabOfNSpace@(3,p^2,1)@factor);
  else
    Add(maximals,SLPointMeetHyperplane@(3,p^2)@factor);
    Add(maximals,SLPointUnmeetHyperplane@(3,p^2)@factor);
  fi;
  if Print > 1 then
    Info(InfoWarning,1,"getting imprimitives");
  fi;
  Add(maximals,ImprimsMeetSL@(3,p^2,3)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting semilinears");
  fi;
  Add(maximals,GammaLMeetSL@(3,p^2,3)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting subfields");
  fi;
  subf:=SubfieldSL@(p)@factor;
  if p mod 3=2 then
    if type in Set(["psl","psl.2_AG"]) then
      groups:=ImageCopies@(subf,3,diag);
      maximals:=Concatenation(maximals,groups);
    elif type in Set(["psl.2_A","psl.2_G","psl.2^2"]) then
      subf:=SelectGroupGeneral@(psl,subf,diag,invol);
      Add(maximals,subf);
    fi;
  else
    Add(maximals,subf);
  fi;
  if Print > 1 then
    Info(InfoWarning,1,"getting classicals");
  fi;
  so3:=SO(3,p^2)@factor;
  if type="psl" or (p mod 3=1 and type="psl.2_G") or (p mod 3=2 and 
     type="psl.2_AG") then
    groups:=ImageCopies@(so3,3,diag);
    maximals:=Concatenation(maximals,groups);
  elif type in Set(["psl.2_A","psl.2_G","psl.2_AG","psl.2^2"]) then
    so3:=SelectGroupGeneral@(psl,so3,diag,invol);
    Add(maximals,so3);
  fi;
  if p mod 3=2 then
    Add(maximals,SU(3,p)@factor);
  elif type in Set(["psl","psl.2_G"]) then
    groups:=ImageCopies@(SU(3,p)@factor,3,diag);
    maximals:=Concatenation(maximals,groups);
  elif type in Set(["psl.2_A","psl.2_AG","psl.2^2"]) then
    su:=SelectGroupGeneral@(psl,SU(3,p)@factor,diag,invol);
    Add(maximals,su);
  fi;
  if Print > 1 then
    Info(InfoWarning,1,"getting C_9s");
  fi;
  if p mod 15 in Set([7,13]) then
    a6:=A6@(p^2)@factor;
    if type in Set(["psl","psl.2_G"]) then
      groups:=ImageCopies@(a6,3,diag);
      maximals:=Concatenation(maximals,groups);
    elif type in Set(["psl.2_A","psl.2_AG","psl.2^2"]) then
      a6:=SelectGroupGeneral@(psl,a6,diag,invol);
      Add(maximals,a6);
    fi;
  elif p mod 15 in Set([2,8]) then
    a6:=A6@(p^2)@factor;
    if type in Set(["psl","psl.2_AG"]) then
      groups:=ImageCopies@(a6,3,diag);
      maximals:=Concatenation(maximals,groups);
    elif type in Set(["psl.2_A","psl.2_G","psl.2^2"]) then
      a6:=SelectGroupGeneral@(psl,a6,diag,invol);
      Add(maximals,a6);
    fi;
  fi;
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);


