#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, AssertAttribute, ChiefFactors, Deq1Maximals,
#  Deq1WhichGroup, Deq7Maximals, Deq7WhichGroup, Determinant, FPGroupStrong,
#  Factorisation, GL, Gcd, Generators, GetInvol, IsEven, IsOdd, Lcm, Ngens,
#  Order, Random, RandomSchreier, SL, proj

#  Defines: DT, Deq1Maximals, Deq1WhichGroup, Deq7Maximals, Deq7WhichGroup,
#  GetInvol, L7qIdentify

DeclareGlobalFunction("L7qIdentify@");

#  
#  This file contains functions called:
#  GetInvol(group,kernel)
#  Deq1WhichGroup(quot, groupquot, delta, phi)
#  Deq7WhichGroup(quot, groupquot, delta, phi, iota,p,e)
#  Deq1Maximals(p,e,factor,d7, Print)
#  Deq7Maximals(p,e,factor, psl, d7, Print)
#  L7qIdentify(group, q)

DT@:="unneeded record format";
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
#   d eq 1 WhichGroup we have Out(PSL7(p^e)) = 2 x e.

Deq1WhichGroup@:=function(quot,groupquot,delta,phi)
local d7;
  d7:=rec();
  #  check whether PSL, else novelty C1s
  d7.is_novelty:=not IsSubset(SubStructure(quot,delta,#TODO CLOSURE
    phi),groupquot);
  return d7;
end;
;
#   d eq 7 WhichGroup we have Out(PSL7(p^e)) = 7:e:2

Deq7WhichGroup@:=function(quot,groupquot,delta,phi,iota,proj,p,e)
local d7,ker;
  d7:=rec();
  #  first check for novelty reducibles
  d7.is_novelty:=not (IsSubset(SubStructure(quot,delta,#TODO CLOSURE
    phi),groupquot));
  #  for all irred geometric groups we get the same stabiliser and kernel
  #  when there's 7 of them.
  d7.in_stab:=ForAny([0..6],i->IsSubset(SubStructure(quot,delta^7,#TODO CLOSURE
    phi,iota)^(delta^i),groupquot));
  if d7.in_stab then
    if (p mod 7)=1 then
      ker:=SubStructure(quot,delta^7,#TODO CLOSURE
        phi);
    elif (p mod 7) in [2,4] then
      ker:=SubStructure(quot,delta^7,#TODO CLOSURE
        phi^3);
    elif (p mod 7) in [3,5] then
      ker:=SubStructure(quot,delta^7,#TODO CLOSURE
        phi^6,iota*phi^3);
    else
      Assert(1,(p mod 7)=6);
      ker:=SubStructure(quot,delta^7,#TODO CLOSURE
        phi^2,iota^phi);
    fi;
    d7.in_ker:=IsSubset(ker,groupquot);
    if not d7.in_ker then
      d7.invol:=GetInvol@(groupquot,ker)@@proj;
    fi;
  fi;
  #  e must be odd and minimal subject to 7|(p^e-1),so e = 3.
  if (e=3) and ((p mod 7) in [2,4]) then
    d7.has_c6:=true;
  fi;
  return d7;
end;
;
#  **************************************************************
#  This makes maximal subgroups when Gcd(q-1, 7) = 1.
Deq1Maximals@:=function(p,e,factor,d7,Print)
local d,diag,f,fac_e,half,maximals,q,so,su;
  q:=p^e;
  diag:=GL(7,q).1@factor;
  maximals:=[];
  #  1 conjugacy class of subfield for each prime divisor of e.
  if Print > 1 then
    Info(InfoWarning,1,"getting subfields");
  fi;
  fac_e:=CollectedFactors(e);
  for d in fac_e do
    f:=QuoInt(e,d[1]);
    Add(maximals,SubfieldSL@(7,p,e,f)@factor);
  od;
  if IsOddInt(q) then
    if Print > 1 then
      Info(InfoWarning,1,"getting orthogonal");
    fi;
    so:=NormOfO@(7,q,0);
    Add(maximals,so@factor);
  fi;
  if IsEvenInt(e) then
    if Print > 1 then
      Info(InfoWarning,1,"getting unitary");
    fi;
    half:=QuoInt(e,2);
    su:=NormOfSU@(7,p^half);
    Add(maximals,su@factor);
  fi;
  return maximals;
end;
;
#  ******************************************************************
#  makes maximals when (q-1, 7) = 7.
Deq7Maximals@:=function(p,e,factor,psl,d7,Print)
local 
   copies,d,diag,ext,ext1,f,fac_e,groups,grps,half,maximals,q,so,su,su_copies,
   subf;
  q:=p^e;
  diag:=GL(7,q).1@factor;
  maximals:=[];
  #  first the subfield groups
  if Print > 1 then
    Info(InfoWarning,1,"getting subfields");
  fi;
  fac_e:=CollectedFactors(e);
  for d in fac_e do
    f:=QuoInt(e,d[1]);
    copies:=(QuoInt((q-1),Lcm(p^f-1,QuoInt((q-1),7))));
    Assert(1,copies in [1,7]);
    if copies=1 or d7.in_stab then
      subf:=SubfieldSL@(7,p,e,f)@factor;
      if copies=1 then
        Add(maximals,subf);
      elif d7.in_ker then
        grps:=ImageCopies@(subf,7,diag);
      else
        Add(maximals,SelectGroupFromSubset@(psl,subf,diag,d7.invol,7));
      fi;
    fi;
  od;
  #  now the extraspecial normalisers.
  if d7.has_c6 and d7.in_stab then
    if Print > 1 then
      Info(InfoWarning,1,"getting extraspecial groups");
    fi;
    ext:=NormaliserOfExtraSpecialGroup@(7,q);
    ext1:=SubStructure(ext,List(Filtered([1..Ngens(ext)]
     ,i->DeterminantMat(ext.i)=1),i->ext.i))@factor;
    if d7.in_ker then
      groups:=ImageCopies@(ext1,7,diag);
      maximals:=Concatenation(maximals,groups);
    else
      Add(maximals,SelectGroupFromSubset@(psl,ext1,diag,d7.invol,7));
    fi;
  fi;
  if d7.in_stab and IsOddInt(q) then
    if Print > 1 then
      Info(InfoWarning,1,"getting orthogonal groups");
    fi;
    so:=NormOfO@(7,q,0)@factor;
    if d7.in_ker then
      groups:=ImageCopies@(so,7,diag);
      maximals:=Concatenation(maximals,groups);
    else
      Add(maximals,SelectGroupFromSubset@(psl,so,diag,d7.invol,7));
    fi;
  fi;
  if IsEvenInt(e) then
    half:=QuoInt(e,2);
    su_copies:=QuoInt((q-1),Lcm((p^half)+1,QuoInt((q-1),7)));
    Assert(1,su_copies in [1,7]);
    if su_copies=1 or d7.in_stab then
      if Print > 1 then
        Info(InfoWarning,1,"getting unitary group");
      fi;
      su:=NormOfSU@(7,p^half)@factor;
      if su_copies=1 then
        Add(maximals,su);
      elif d7.in_ker then
        groups:=ImageCopies@(su,7,diag);
      else
        Add(maximals,SelectGroupFromSubset@(psl,su,diag,d7.invol,7));
      fi;
    fi;
  fi;
  return maximals;
end;
;
#  ***************************************************************
#   The main function.
#  * Input: - a group isomorphic to an almost simple group with
#  *          socle PSL(7, q) for q prime power,
#  *        - the prime power q;
#  *        - a flag "max" (default true) to say whether we want
#  *          the maximals or just to do constructive recognition.
#  *        - a Print level (default 0) if > 1 we print stuff.
#  *
#  * Output: - 5 things.
#  *           first is homom from standard PSL to the copy of Aut(PSL)
#  *             where the maximals live.
#  *           third is the maximal subgroups,
#  *           others are other maps.

InstallGlobalFunction(L7qIdentify@,
function(group,q)
local 
   F,Print,apsl,d,d7,delta,e,fac,factor,g,gl,group,groupquot,homom,i,iota,max,
   maximals,newgens,ord_apsl,p,phi,phia,proj,psl,quot,sl,soc,subapsl;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  fac:=CollectedFactors(q);
  Assert(1,Size(fac)=1);
  e:=fac[1][2];
  Assert(1,e > 1);
  p:=fac[1][1];
  Assert(1,q > 3);
  d:=Gcd(q-1,7);
  if Print > 1 then
    Print("Making standard group");
  fi;
  gl:=GL(7,q);
  sl:=SL(7,q);
  apsl:=PGammaL2@(7,q);
  AssertAttribute(apsl,"Order",(QuoInt(2*e*Size(GL(7,q)),(q-1))));
  if Print > 2 then
    Info(InfoWarning,1,"Making factor map");
  fi;
  factor:=GroupHomomorphismByImages(gl,apsl,
    apsl.1,apsl.2);
  if Print > 2 then
    Info(InfoWarning,1,"Finding image of SL in perm rep");
  fi;
  psl:=sl@factor;
  AssertAttribute(psl,"Order",(QuoInt(Size(SL(7,q)),Gcd(q-1,7))));
  if Print > 1 then
    Print("Setting up isomorphism");
  fi;
  # =v= MULTIASSIGN =v=
  group:=MakeHomomGeneral@(group,7,p,e,psl,apsl,factor:Print:=0);
  homom:=group.val1;
  soc:=group.val2;
  group:=group.val3;
  # =^= MULTIASSIGN =^=
  #   Set up the subgroup of the outer automorphism group induced by group
  if max then
    if Print > 1 then
      Print("d = ",d);
    fi;
    # =v= MULTIASSIGN =v=
    proj:=Subquo(apsl,[psl]);
    quot:=proj.val1;
    proj:=proj.val2;
    # =^= MULTIASSIGN =^=
    delta:=proj(apsl.1);
    Assert(1,Order(delta)=d);
    #  diagonal aut.
    phia:=proj(apsl.3);
    Assert(1,Order(phia)=e);
    #  field aut
    iota:=proj(apsl.4);
    Assert(1,Order(iota)=2);
    #  graph aut
    newgens:=List([1..Ngens(group)],i->group.i@homom);
    groupquot:=SubStructure(quot,List(newgens,g->proj(g)));
    if Print > 1 then
      Print("Out aut group is",ChiefFactors(groupquot));
    fi;
  fi;
  if Print > 1 then
    Print("Calling FPGroupStrong");
  fi;
  # =v= MULTIASSIGN =v=
  phi:=FPGroupStrong(SubStructure(psl,List([1..Ngens(soc)],i->soc.i@homom)));
  F:=phi.val1;
  phi:=phi.val2;
  # =^= MULTIASSIGN =^=
  #  this restriction also in for testing purposes
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
    d7:=Deq1WhichGroup@(quot,groupquot,delta,phia);
  elif d=7 then
    d7:=Deq7WhichGroup@(quot,groupquot,delta,phia,iota,proj,p,e);
  fi;
  maximals:=[];
  if Print > 1 then
    Info(InfoWarning,1,"getting reducibles");
  fi;
  if not d7.is_novelty then
    Add(maximals,(SLPointStab@(7,q)@factor));
    for i in [2..6] do
      Add(maximals,(SLStabOfNSpace@(7,q,i)@factor));
    od;
  else
    for i in [1..3] do
      Add(maximals,(SLStabOfNSpaceMeetDual@(7,q,i)@factor));
      Add(maximals,(SLStabOfNSpaceMissDual@(7,q,i)@factor));
    od;
  fi;
  if q > 4 then
    if Print > 1 then
      Info(InfoWarning,1,"getting imprimitives");
    fi;
    Add(maximals,(ImprimsMeetSL@(7,q,7)@factor));
  fi;
  if Print > 1 then
    Info(InfoWarning,1,"getting semilinears");
  fi;
  Add(maximals,(GammaLMeetSL@(7,q,7)@factor));
  #  now we make the maximals that depend on congruences of q.
  if d=1 then
    maximals:=Concatenation(maximals,Deq1Maximals@(p,e,factor,d7,Print));
  elif d=7 then
    maximals:=Concatenation(maximals,Deq7Maximals@(p,e,factor,psl,d7,Print));
  fi;
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);


