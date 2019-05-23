#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, AssertAttribute, ClassicalForms,
#  Deq1Maximals, Deq1WhichGroup, Deq7Maximals, Deq7WhichGroup, Determinant,
#  FPGroupStrong, Factorisation, GL, Gcd, Generators, GetInvol, GetLibraryRoot,
#  Getu33d7b, IsAbsolutelyIrreducible, IsEven, IsPrime, IsPrimitive,
#  IsSemiLinear, IsTensor, Ngens, Order, Random, RandomSchreier, Read, SL, proj

#  Defines: Deq1Maximals, Deq1WhichGroup, Deq7Maximals, Deq7WhichGroup,
#  GetInvol, Getu33d7b, L7pIdentify

DeclareGlobalFunction("L7pIdentify@");

#  
#  This file contains functions called:
#  GetInvol(group,kernel)
#  Deq1WhichGroup(quot,groupquot,delta,iota,p)
#  Deq7WhichGroup(quot,groupquot,delta,iota,p,proj)
#  Deq1Maximals(p, factor,  is_novelty, has_sl211, has_sl3q, Print)
#  Deq7Maximals(p, factor, psl, d6, Print)
#  L7pIdentify(group, p)

#  files from DFH - slightly modified to return functions not
#  objects.
#  
#  load "~colva/maximals/code/construct.m";
#  load "~colva/maximals/code/psl7p/u33d7b";

Getu33d7b@:=function(p)
local L,_LR,_LRS,c9,c9lib;
  c9lib:=Concatenation(GetLibraryRoot(),"/c9lattices/");
  _LRS:=Read(Concatenation(c9lib,"u33d7b"));
  _LR:=#EVAL
      _LRS;
  L:=ReduceOverFiniteField@(_LR,p);
  c9:=L[1];
  #  can remove this later.
  Assert(1,IsAbsolutelyIrreducible(c9) and (not IsSemiLinear(c9)) and 
   IsPrimitive(c9) and (not IsTensor(c9)) and ClassicalForms(c9)
   .formType="linear");
  return c9;
end;
;
#  **************************************************************
#  used for finding outer involution - very small group so no point
#  being clever
GetInvol@:=function(group,kernel)
local invol;
  invol:=Random(group);
  while (invol in kernel) or (not (Order(invol)=2)) do
    invol:=Random(group);
  od;
  return invol;
end;
;
#  **************************************************************
#   d eq 1 WhichGroup we have Out(PSL7(p)) = 2.
#  possible groups: PSL itself and Aut(PSL).

Deq1WhichGroup@:=function(group,p)
local has_u33,is_novelty;
  Assert(1,IsPrimeInt(p) and Gcd(p-1,7)=1);
  #  first check whether PSL, else novelty C1s
  is_novelty:=Size(group)=(2*Size(SL(7,p)));
  #  single class of u33 if p equiv 1 mod 4
  has_u33:=(p mod 4)=1;
  return rec(val1:=is_novelty,
    val2:=has_u33);
end;
;
#   d eq 7 WhichGroup we have Out(PSL7(p)) = D_{2 x 7}

Deq7WhichGroup@:=function(group,soc,apsl,psl,p,homom)
local DT@,d7,groupquot,newgens,proj,quot,quot_order;
  DT@:="unneeded record format";
  d7:=rec();
  quot_order:=QuoInt(Size(group),Size(psl));
  if quot_order=2 then
    # =v= MULTIASSIGN =v=
    proj:=Subquo(apsl,[psl]);
    quot:=proj.val1;
    proj:=proj.val2;
    # =^= MULTIASSIGN =^=
    newgens:=List([1..Ngens(group)],i->group.i@homom);
    groupquot:=SubStructure(quot,List(newgens,g->proj(g)));
  fi;
  #  first check whether subgroup of PGL.
  d7.is_novelty:=IsEvenInt(quot_order);
  #  action on all groups with more than one class has trivial kernel.
  d7.in_ker:=quot_order=1;
  #  stabiliser of all groups with more than one class is involution
  d7.in_stab:=quot_order < 3;
  if d7.in_stab and not d7.in_ker then
    d7.invol:=GetInvol@(groupquot,SubStructure(groupquot,#NOP
    ))@@proj;
  fi;
  d7.has_u33:=((p mod 4)=1) and d7.in_stab;
  return d7;
end;
;
#  **************************************************************
#  This makes maximal subgroups when Gcd(p-1, 7) = 1.
Deq1Maximals@:=function(p,factor,is_novelty,has_u33,Print)
#  /out:PSL(7, 2) and PSL(7, 3) have already been done as special cases.
local c9,diag,i,maximals,so;
  Assert(1,p > 3 and IsPrimeInt(p));
  diag:=GL(7,p).1@factor;
  maximals:=[];
  if Print > 1 then
    Info(InfoWarning,1,"getting reducibles");
  fi;
  if not is_novelty then
    Add(maximals,(SLPointStab@(7,p)@factor));
    for i in [2..6] do
      Add(maximals,(SLStabOfNSpace@(7,p,i)@factor));
    od;
  else
    for i in [1..3] do
      Add(maximals,(SLStabOfNSpaceMeetDual@(7,p,i)@factor));
      Add(maximals,(SLStabOfNSpaceMissDual@(7,p,i)@factor));
    od;
  fi;
  if Print > 1 then
    Info(InfoWarning,1,"getting imprimitives");
  fi;
  Add(maximals,(ImprimsMeetSL@(7,p,7)@factor));
  if Print > 1 then
    Info(InfoWarning,1,"getting superfields");
  fi;
  Add(maximals,(GammaLMeetSL@(7,p,7)@factor));
  if Print > 1 then
    Info(InfoWarning,1,"getting orthogonal");
  fi;
  so:=NormOfO@(7,p,0);
  Add(maximals,so@factor);
  #  finally the C9s.
  if has_u33 then
    if Print > 1 then
      Info(InfoWarning,1,"getting U_3(3)");
    fi;
    c9:=Getu33d7b@(p);
    Add(maximals,c9@factor);
  fi;
  return maximals;
end;
;
#  ******************************************************************
#  makes maximals when (p-1, 7) = 7.
#  d7 is all the data about where in the group we are, and hence what
#  subgroups and conjugacy classes must be made.
Deq7Maximals@:=function(p,factor,psl,d7,Print)
local c9,diag,ext,ext1,groups,grp,i,maximals,so;
  Assert(1,IsPrimeInt(p));
  Assert(1,p mod 7=1);
  diag:=GL(7,p).1@factor;
  maximals:=[];
  if Print > 1 then
    Info(InfoWarning,1,"getting reducibles");
  fi;
  if not d7.is_novelty then
    Add(maximals,(SLPointStab@(7,p)@factor));
    for i in [2..6] do
      Add(maximals,(SLStabOfNSpace@(7,p,i)@factor));
    od;
  else
    for i in [1..3] do
      Add(maximals,(SLStabOfNSpaceMeetDual@(7,p,i)@factor));
      Add(maximals,(SLStabOfNSpaceMissDual@(7,p,i)@factor));
    od;
  fi;
  if Print > 1 then
    Info(InfoWarning,1,"getting imprimitives");
  fi;
  Add(maximals,(ImprimsMeetSL@(7,p,7)@factor));
  if Print > 1 then
    Info(InfoWarning,1,"getting semilinears");
  fi;
  Add(maximals,(GammaLMeetSL@(7,p,7)@factor));
  if d7.in_stab then
    if Print > 1 then
      Info(InfoWarning,1,"getting extraspecial groups");
    fi;
    ext:=NormaliserOfExtraSpecialGroup@(7,p);
    ext1:=SubStructure(ext,List(Filtered([1..Ngens(ext)]
     ,i->DeterminantMat(ext.i)=1),i->ext.i));
    if d7.in_ker then
      groups:=ImageCopies@(ext1@factor,7,diag);
      maximals:=Concatenation(maximals,groups);
    else
      Add(maximals,SelectGroupFromSubset@(psl,ext1@factor,diag,d7.invol,7));
    fi;
    if Print > 1 then
      Info(InfoWarning,1,"getting orthogonal groups");
    fi;
    so:=NormOfO@(7,p,0);
    if d7.in_ker then
      groups:=ImageCopies@(so@factor,7,diag);
      maximals:=Concatenation(maximals,groups);
    else
      Add(maximals,SelectGroupFromSubset@(psl,so@factor,diag,d7.invol,7));
    fi;
    #  and now the C9
    if d7.has_u33 then
      if Print > 1 then
        Info(InfoWarning,1,"getting U3(3)");
      fi;
      c9:=Getu33d7b@(p);
      if d7.in_ker then
        groups:=ImageCopies@(c9@factor,7,diag);
        maximals:=Concatenation(maximals,groups);
      else
        grp:=SelectGroupFromSubset@(psl,c9@factor,diag,d7.invol,7);
        Add(maximals,grp);
      fi;
    fi;
  fi;
  return maximals;
end;
;
#  ***************************************************************
#   The main function.
#  * Input: - a group isomorphic to an almost simple group with
#  *          socle PSL(7, p) for p prime,
#  *        - the prime p;
#  *        - a flag "max" (default true) to say whether we want
#  *          the maximals or just to do constructive recognition.
#  *        - a Print level (default 0) if > 1 we print stuff.
#  *
#  * Output: - 5 things.
#  *           first is homom from standard PSL to the copy of Aut(PSL)
#  *             where the maximals live.
#  *           third is the maximal subgroups,
#  *           others are other maps.

InstallGlobalFunction(L7pIdentify@,
function(group,p)
local 
   F,Print,apsl,d,d7,fac,factor,g,gl,group,has_u33,homom,is_novelty,max,
   maximals,newgens,ord_apsl,phi,psl,sl,soc,subapsl;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  fac:=CollectedFactors(p);
  Assert(1,Size(fac)=1);
  Assert(1,p > 3);
  d:=Gcd(p-1,7);
  if Print > 1 then
    Print("Making standard group");
  fi;
  gl:=GL(7,p);
  sl:=SL(7,p);
  apsl:=PGL2@(7,p);
  AssertAttribute(apsl,"Order",(QuoInt(2*Size(GL(7,p)),(p-1))));
  if Print > 2 then
    Info(InfoWarning,1,"Making factor map");
  fi;
  factor:=GroupHomomorphismByImages(gl,apsl,
    apsl.1,apsl.2);
  if Print > 2 then
    Info(InfoWarning,1,"Finding image of SL in perm rep");
  fi;
  psl:=sl@factor;
  AssertAttribute(psl,"Order",(QuoInt(Size(SL(7,p)),Gcd(p-1,7))));
  if Print > 1 then
    Print("Setting up isomorphism");
  fi;
  # =v= MULTIASSIGN =v=
  group:=MakeHomomGeneral@(group,7,p,1,psl,apsl,factor:Print:=0);
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
  if Print > 2 then
    Print("minimising generators");
  fi;
  #  get apsl right
  ord_apsl:=Order(apsl);
  newgens:=List([1..Ngens(group)],i->group.i@homom);
  subapsl:=SubStructure(apsl,newgens);
  RandomSchreier(subapsl);
  for g in Generators(apsl) do
    if not g in subapsl then
      Add(newgens,g);
      subapsl:=SubStructure(apsl,newgens);
      RandomSchreier(subapsl);
    fi;
  od;
  apsl:=SubStructure(apsl,subapsl);
  apsl.Order:=ord_apsl;
  if not max then
    return rec(val1:=homom,
      val2:=apsl,
      val3:=[],
      val4:=F,
      val5:=phi);
  fi;
  if Print > 1 then
    Info(InfoWarning,1,"Creating maximals");
  fi;
  if d=1 then
    # =v= MULTIASSIGN =v=
    has_u33:=Deq1WhichGroup@(group,p);
    is_novelty:=has_u33.val1;
    has_u33:=has_u33.val2;
    # =^= MULTIASSIGN =^=
    if Print > 1 then
      Print("is novelty =",is_novelty,"has U_3(3) =",has_u33);
    fi;
    maximals:=Deq1Maximals@(p,factor,is_novelty,has_u33,Print);
  elif d=7 then
    d7:=Deq7WhichGroup@(group,soc,apsl,psl,p,homom);
    if Print > 1 then
      Print("is novelty =",d7.is_novelty,"in kernel =",d7.in_kernel);
      Print("in stab =",d7.in_stab,"has U_3(3) =",d7.has_u33);
    fi;
    maximals:=Deq7Maximals@(p,factor,psl,d7,Print);
  fi;
  #  return statement should also return F, phi when testing complete.
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);


