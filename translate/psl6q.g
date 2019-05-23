#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, AssertAttribute, ChiefFactors,
#  ClassicalForms, Deq1Maximals, Deq1WhichGroup, Deq2Maximals, Deq2WhichGroup,
#  Deq3Maximals, Deq3WhichGroup, Deq6Maximals, Deq6WhichGroup, FPGroupStrong,
#  Factorisation, GF, GL, GModule, Gcd, Generators, Get6a6d6, Get6a7d6,
#  GetEltOrder6, GetInvol, GetLibraryRoot, IsAbsolutelyIrreducible, IsEven,
#  IsNormal, IsOdd, IsPrimitive, IsSemiLinear, IsSquare, IsTensor, MatrixGroup,
#  Ngens, Order, Random, RandomSchreier, Read, SL, SymmetricSquare, Transpose,
#  proj

#  Defines: DT, Deq1Maximals, Deq1WhichGroup, Deq2Maximals, Deq2WhichGroup,
#  Deq3Maximals, Deq3WhichGroup, Deq6Maximals, Deq6WhichGroup, Get6a6d6,
#  Get6a7d6, GetEltOrder6, GetInvol, L6qIdentify

DeclareGlobalFunction("L6qIdentify@");

#  
#  This file contains functions called:
#  GetInvol(group,kernel)
#  GetEltOrder6(group,kernel)
#  Deq1WhichGroup(quot, groupquot, delta, phi, iota, e)
#  Deq2WhichGroup(quot, groupquot, delta,phi, iota, p,e)
#  Deq3WhichGroup(quot, groupquot,delta,phi,iota,e,proj)
#  Deq6WhichGroup(quot,groupquot,delta,phi,iota,p,e,proj)
#  Deq1Maximals(q, factor, d6, Print)
#  Deq2Maximals(q, factor, d6, Print)
#  Deq3Maximals(q, factor, psl, d6, Print)
#  Deq6Maximals(q, factor, psl, d6, Print)
#  L6qIdentify(group, q)

#  files from DFH - slightly modified to return functions not
#  objects.
#  
#  load "~colva/maximals/code/construct.m";
#  load "~colva/maximals/code/psl6p/6a7d6";
#  load "~colva/maximals/code/psl6p/6a6d6";

Get6a6d6@:=function(p)
local L,_LR,_LRS,c9,c9lib;
  c9lib:=Concatenation(GetLibraryRoot(),"/c9lattices/");
  _LRS:=Read(Concatenation(c9lib,"6a6d6"));
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
Get6a7d6@:=function(p)
local L,_LR,_LRS,c9,c9lib;
  c9lib:=Concatenation(GetLibraryRoot(),"/c9lattices/");
  _LRS:=Read(Concatenation(c9lib,"6a7d6"));
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
#  this one will be used with quot not groupquot, as need something to
#  get us between the two sets of 6A7s, each of size 6, so we can find
#  the 4 to normalise.
GetEltOrder6@:=function(group,kernel)
local elt;
  elt:=Random(group);
  while (elt in kernel) or (not (Order(elt)=6)) do
    elt:=Random(group);
  od;
  return elt;
end;
;
#  **************************************************************
#  
#  * When (q-1, 6) = 1 we have Out(PSL(6, p^e)) = e x 2.
#  * We have p = 2 and e is odd.

Deq1WhichGroup@:=function(quot,groupquot,delta,phi,iota,e)
#  /out:only get into this case with odd powers of 2.
local d6;
  Assert(1,IsOddInt(e) and e > 1);
  d6:=rec();
  #  only need to check whether subgroup of PGammaL
  d6.is_novelty:=not IsSubset(SubStructure(quot,delta,#TODO CLOSURE
    phi),groupquot);
  return d6;
end;
;
#   When (p^e-1, 6) = 2 we have Out(PSL6(p^e)) = (2^2 x e), where e is odd
#  * OR p = 3.

Deq2WhichGroup@:=function(quot,groupquot,delta,phi,iota,p,e)
local d6,q;
  q:=p^e;
  d6:=rec();
  #  first check whether subgroup of PGammaL
  d6.is_novelty:=not IsSubset(SubStructure(quot,delta,#TODO CLOSURE
    phi),groupquot);
  #  then check whether in stabiliser of any subfield groups
  d6.in_subfield_stab:=IsSubset(SubStructure(quot,phi,#TODO CLOSURE
    iota),groupquot);
  d6.in_l3q_ker:=(IsSquare(2 #CAST GF(q)
    ) and IsSubset(SubStructure(quot,iota,#TODO CLOSURE
    phi),groupquot)) or ((not IsSquare(2 #CAST GF(q)
    )) and IsSubset(SubStructure(quot,delta*iota,#TODO CLOSURE
    phi),groupquot));
  return d6;
end;
;
#   When (p^e-1, 6) = 3 we have p = 2 and e even, so
#  * Out(PSL(6, 2^e)) = 3:(e x 2)

Deq3WhichGroup@:=function(quot,groupquot,delta,phi,iota,e,proj)
#  /out:only get into this case with even powers of 2
local d6,kernel;
  Assert(1,IsEvenInt(e));
  d6:=rec();
  #  first check whether subgroup of PGammaL
  d6.is_novelty:=not IsSubset(SubStructure(quot,delta,#TODO CLOSURE
    phi),groupquot);
  #  now sort out conjugacy of subfield and classical groups
  d6.in_sp_stab:=ForAny([0..2],i->IsSubset(SubStructure(quot,phi,#TODO CLOSURE
    iota)^(delta^i),groupquot));
  kernel:=SubStructure(quot,phi^2,#TODO CLOSURE
    iota*phi);
  Assert(1,IsNormal(quot,kernel));
  #  kernel is a normal subgroup!
  d6.in_sp_ker:=IsSubset(kernel,groupquot);
  if d6.in_sp_stab and not d6.in_sp_ker then
    d6.sp_invol:=GetInvol@(groupquot,kernel)@@proj;
  fi;
  return d6;
end;
;
#   When (p^e-1, 6) = 6 we have Out(PSL6(p)) = 6:e:2

Deq6WhichGroup@:=function(quot,groupquot,delta,phi,iota,p,e,proj)
local d6,kernel,q;
  q:=p^e;
  d6:=rec();
  #  first check whether subgroup of PGammaL.
  d6.is_novelty:=not IsSubset(SubStructure(quot,delta,#TODO CLOSURE
    phi),groupquot);
  #  now need to do subfield and unitary groups. we need different stabilisers
  #  depending on how many classes.
  #  stabiliser is S3 from CUP text, but that depends on number of
  #  classes. kernel is K1 (p = -1 (mod #classes)) or K2 (otherwise).
  #  number of classes could be 1 (in which case nothing to do),
  #  or 2 or 3 or 6 (not sure if this last case can happen, but do it
  #  anyway). if number of classes is 3 or 6 we need an outer
  #  involution.
  d6.in_ceq2_ker:=IsSubset(SubStructure(quot,delta^2,#TODO CLOSURE
    phi,iota),groupquot);
  d6.in_ceq3_stab:=ForAny([0..5],i->IsSubset(SubStructure(quot,delta^3,#TODO 
   CLOSURE
    phi,iota)^(delta^i),groupquot));
  if d6.in_ceq3_stab then
    if (p mod 3)=1 then
      kernel:=SubStructure(quot,delta^3,#TODO CLOSURE
        phi);
    else
      Assert(1,(p mod 3)=2);
      kernel:=SubStructure(quot,delta^3,#TODO CLOSURE
        phi^2,iota*phi);
    fi;
    d6.in_ceq3_ker:=IsSubset(kernel,groupquot);
    if not d6.in_ceq3_ker then
      d6.ceq3_invol:=GetInvol@(groupquot,kernel);
    fi;
  fi;
  d6.in_ceq6_stab:=ForAny([0..5],i->IsSubset(SubStructure(quot,delta^6,#TODO 
   CLOSURE
    phi,iota)^(delta^i),groupquot));
  if d6.in_ceq6_stab then
    if (p mod 6)=1 then
      kernel:=SubStructure(quot,delta^6,#TODO CLOSURE
        phi);
    else
      Assert(1,(p mod 6)=5);
      kernel:=SubStructure(quot,delta^6,#TODO CLOSURE
        phi^2,iota*phi);
    fi;
    d6.in_ceq6_ker:=IsSubset(kernel,groupquot);
    if not d6.in_ceq6_ker then
      d6.ceq6_invol:=GetInvol@(groupquot,kernel);
    fi;
  fi;
  #  stabiliser for Sp, O+, O- (q = 3(4)) is S3 from CUP text
  d6.in_sp_stab:=ForAny([0..5],i->IsSubset(SubStructure(quot,delta^3,#TODO 
   CLOSURE
    phi,iota)^(delta^i),groupquot));
  #  kernel for Sp, O+, O- (q = 3(4)) is K2 from CUP text when p = 1(3)
  if d6.in_sp_stab and (p mod 3)=1 then
    kernel:=SubStructure(quot,delta^3,#TODO CLOSURE
      phi);
    #  kernel for Sp, O+, O-(q = 3(4)) is K3 from CUP text when p = 2(3)
  elif d6.in_sp_stab and (p mod 3)=2 then
    kernel:=SubStructure(quot,delta^3,#TODO CLOSURE
      phi^2,iota*phi);
  fi;
  d6.in_sp_ker:=IsSubset(kernel,groupquot);
  if d6.in_sp_stab and not d6.in_sp_ker then
    d6.sp_invol:=GetInvol@(groupquot,kernel)@@proj;
  fi;
  if q mod 4=3 then
    d6.in_ominus_stab:=d6.in_sp_stab;
    d6.in_ominus_ker:=d6.in_sp_ker;
    if d6.in_ominus_stab and not d6.in_ominus_ker then
      d6.ominus_invol:=d6.sp_invol;
    fi;
  else
    #  kernel S4 from CUP text
    d6.in_ominus_stab:=ForAny([0..5]
     ,i->IsSubset(SubStructure(quot,delta^3,#TODO CLOSURE
      phi*delta^(QuoInt((p-1),2)),iota*delta^-1)^(delta^i),groupquot));
    if p mod 3=1 then
      kernel:=SubStructure(quot,delta^3,#TODO CLOSURE
        phi*delta^(QuoInt((p-1),2)));
    else
      kernel:=SubStructure(quot,delta^3,#TODO CLOSURE
        phi^2,iota*phi);
    fi;
    d6.in_ominus_ker:=IsSubset(kernel,groupquot);
    if d6.in_ominus_stab and not d6.in_ominus_ker then
      d6.ominus_invol:=GetInvol@(groupquot,kernel)@@proj;
    fi;
  fi;
  #  6A_7.
  if ((p mod 24) in [5,11,13,19]) and (e=2) then
    if (p mod 6)=1 then
      d6.in_a7_stab:=ForAny([0..5],i->IsSubset(SubStructure(quot,phi*iota)
       ^delta^i,groupquot));
    elif (p mod 6)=5 then
      d6.in_a7_stab:=ForAny([0..5],i->IsSubset(SubStructure(quot,phi)
       ^delta^i,groupquot));
    fi;
    d6.in_a7_ker:=groupquot=SubStructure(quot,#NOP
    );
    if d6.in_a7_stab and not d6.in_a7_ker then
      d6.a7_invol:=GetInvol@(groupquot,SubStructure(quot,#NOP
      ))@@proj;
      d6.a7_elt:=GetEltOrder6@(groupquot,SubStructure(groupquot,delta))@@proj;
    fi;
  fi;
  #  6A_6. usually contained in 6A_7 but two copies novelty under
  #  duality. only bother defining a "stab" here as there's a unique
  #  conjugacy class of subgroups where anything happens.
  if ((p mod 24) in [5,11,13,19]) and (e=2) then
    if (p mod 6)=1 then
      d6.in_a6_stab:=ForAny([0..5],i->groupquot=SubStructure(quot,phi)^(delta^i)
       );
    elif (p mod 6)=5 then
      d6.in_a6_stab:=ForAny([0..5],i->groupquot=SubStructure(quot,phi*iota)
       ^(delta^i));
    fi;
    if d6.in_a6_stab then
      d6.a6_invol:=GetInvol@(groupquot,SubStructure(quot,#NOP
      ))@@proj;
    fi;
  fi;
  #  And finally, L3(q).
  d6.in_l3q_ker:=(IsSquare(2 #CAST GF(q)
    ) and IsSubset(SubStructure(quot,delta^2,#TODO CLOSURE
    phi,iota),groupquot)) or ((not IsSquare(2 #CAST GF(p)
    )) and IsSubset(SubStructure(quot,delta^2,#TODO CLOSURE
    phi,delta*iota),groupquot));
  return d6;
end;
;
#  end of the functions to determine which conjugacy classes must
#  be constructed.
#  ****************************************************************
#  beginning of the functions that make the maximals whose
#  existence/conjugacy depends on congruence of q mod 6.
#  makes remaining maximal subgroups when (q-1, 6)=1;
Deq1Maximals@:=function(q,factor,d6,Print)
local d,diag,e,f,fac,fac_e,maximals,p;
  Assert(1,IsEvenInt(q));
  Assert(1,q > 4);
  fac:=CollectedFactors(q);
  Assert(1,Size(fac)=1);
  p:=fac[1][1];
  Assert(1,p=2);
  e:=fac[1][2];
  Assert(1,IsOddInt(e));
  diag:=GL(6,q).1@factor;
  maximals:=[];
  #  single conjugacy class of subfields for each prime divisor of
  #  e.
  if Print > 1 then
    Info(InfoWarning,1,"getting subfields");
  fi;
  fac_e:=CollectedFactors(e);
  for d in fac_e do
    f:=QuoInt(e,d[1]);
    Add(maximals,SubfieldSL@(6,2,e,f)@factor);
  od;
  #  single conjugacy class of symplectics
  if Print > 1 then
    Info(InfoWarning,1,"getting symplectic");
  fi;
  Add(maximals,NormOfSp@(6,q)@factor);
  #  no unitary groups as e odd.
  #  no C9s
  return maximals;
end;
;
#  **************************************************************
#  This makes maximal subgroups when Gcd(p-1, 6) = 2.
Deq2Maximals@:=function(q,factor,d6,Print)
local 
   copies,d,diag,e,f,fac,fac_e,groups,half,maximals,p,sl,sominus,soplus,su,
   subfield;
  fac:=CollectedFactors(q);
  Assert(1,Size(fac)=1);
  p:=fac[1][1];
  Assert(1,IsOddInt(p));
  e:=fac[1][2];
  Assert(1,(IsOddInt(e) or p=3));
  diag:=GL(6,q).1@factor;
  maximals:=[];
  if Print > 1 then
    Info(InfoWarning,1,"getting subfields");
  fi;
  fac_e:=CollectedFactors(e);
  for d in fac_e do
    f:=QuoInt(e,d[1]);
    copies:=Gcd(6,QuoInt((q-1),(p^f-1)));
    subfield:=SubfieldSL@(6,p,e,f);
    if copies=1 then
      Add(maximals,subfield@factor);
    else
      Assert(1,copies=2);
      if d6.in_subfield_stab then
        groups:=ImageCopies@(subfield@factor,2,diag);
        maximals:=Concatenation(maximals,groups);
      fi;
    fi;
  od;
  if Print > 1 then
    Info(InfoWarning,1,"getting orthogonals");
  fi;
  #  single conjugacy class
  soplus:=NormOfO@(6,q,1);
  Add(maximals,soplus@factor);
  sominus:=NormOfO@(6,q,-1);
  Add(maximals,sominus@factor);
  #  single conjugacy class
  if Print > 1 then
    Info(InfoWarning,1,"getting symplectic");
  fi;
  Add(maximals,NormOfSp@(6,q)@factor);
  #  get one unitary group when p = 3 (so e might be even)
  if IsEvenInt(e) and d6.in_subfield_stab then
    if Print > 1 then
      Info(InfoWarning,1,"getting SU_3(q)");
    fi;
    half:=QuoInt(e,2);
    su:=NormOfSU@(6,p^half)@factor;
    groups:=ImageCopies@(su,2,diag);
    maximals:=Concatenation(maximals,groups);
  fi;
  if d6.in_l3q_ker then
    if Print > 1 then
      Info(InfoWarning,1,"getting SL_3(q)");
    fi;
    sl:=MatrixGroup(SymmetricSquare(GModule(SL(3,q))));
    Assert(1,IsAbsolutelyIrreducible(sl) and (not IsSemiLinear(sl)) and 
     IsPrimitive(sl) and (not IsTensor(sl)) and ClassicalForms(sl)
     .formType="linear");
    Add(maximals,sl@factor);
    Add(maximals,(sl@factor)^diag);
  fi;
  return maximals;
end;
;
#  **************************************************************
#  This makes maximal subgroups when Gcd(q-1, 6) = 3.
Deq3Maximals@:=function(q,factor,psl,d6,Print)
local copies,d,diag,e,f,fac,fac_e,groups,grp,half,maximals,p,su,subfield;
  fac:=CollectedFactors(q);
  Assert(1,Size(fac)=1);
  p:=fac[1][1];
  Assert(1,p=2);
  e:=fac[1][2];
  Assert(1,IsEvenInt(e));
  diag:=GL(6,q).1@factor;
  maximals:=[];
  #  first the subfields. number of classes depends on divisor of
  #  e.
  if Print > 1 then
    Info(InfoWarning,1,"getting subfields");
  fi;
  fac_e:=CollectedFactors(e);
  for d in fac_e do
    f:=QuoInt(e,d[1]);
    copies:=Gcd(6,QuoInt((2^e-1),(2^f-1)));
    subfield:=SubfieldSL@(6,2,e,f);
    if copies=1 then
      Add(maximals,subfield@factor);
    else
      Assert(1,copies=3);
      if d6.in_sp_ker then
        groups:=ImageCopies@(subfield@factor,3,diag);
        maximals:=Concatenation(maximals,groups);
      elif d6.in_sp_stab then
        Add(maximals,SelectGroupFromSubset@(psl,subfield@factor,diag,
         d6.sp_invol,3));
      fi;
    fi;
  od;
  if d6.in_sp_stab then
    if Print > 1 then
      Info(InfoWarning,1,"getting symplectic");
    fi;
    grp:=NormOfSp@(6,q)@factor;
    if d6.in_sp_ker then
      groups:=ImageCopies@(grp,3,diag);
      maximals:=Concatenation(maximals,groups);
    else
      Add(maximals,SelectGroupFromSubset@(psl,grp,diag,d6.sp_invol,3));
    fi;
  fi;
  half:=QuoInt(e,2);
  #  if half is odd then single copy of unitary, else 3.
  if IsOddInt(half) then
    if Print > 1 then
      Info(InfoWarning,1,"getting unitary");
    fi;
    Add(maximals,NormOfSU@(6,2^half)@factor);
  elif d6.in_sp_stab then
    if Print > 1 then
      Info(InfoWarning,1,"getting unitary");
    fi;
    su:=NormOfSU@(6,2^half)@factor;
    if d6.in_sp_ker then
      groups:=ImageCopies@(su,3,diag);
      maximals:=Concatenation(maximals,groups);
    else
      Add(maximals,SelectGroupFromSubset@(psl,su,diag,d6.sp_invol,3));
    fi;
  fi;
  return maximals;
end;
;
#  ******************************************************************
#  makes maximals when (q-1, 6) = 6.
#  d6 is all the data about where in the group we are, and hence what
#  subgroups and conjugacy classes must be made.
Deq6Maximals@:=function(q,factor,psl,d6,Print)
local 
   c9,c92,classes,copies,d,diag,e,f,fac,fac_e,groups,groups1,groups2,grp,grp1,
   grp2,grp3,half,maximals,ominus,oplus,p,q_0,sp,su,subfield;
  Assert(1,q > 11);
  fac:=CollectedFactors(q);
  Assert(1,Size(fac)=1);
  p:=fac[1][1];
  e:=fac[1][2];
  Assert(1,q mod 6=1);
  diag:=GL(6,q).1@factor;
  maximals:=[];
  #  first the subfield groups
  if Print > 1 then
    Info(InfoWarning,1,"getting subfields");
  fi;
  fac_e:=CollectedFactors(e);
  for d in fac_e do
    f:=QuoInt(e,d[1]);
    copies:=Gcd(6,QuoInt((p^e-1),(p^f-1)));
    if (copies=1) or (copies=2 and d6.in_c2_ker) or (copies=3 and d6.in_c3_stab)
        or (copies=6 and d6.in_c6_stab) then
      subfield:=SubfieldSL@(6,p,e,f)@factor;
      if copies=1 then
        Add(maximals,subfield);
      elif copies=2 then
        groups:=ImageCopies@(subfield,2,diag);
        maximals:=Concatenation(maximals,groups);
      elif copies=3 and d6.in_c3_ker then
        groups:=ImageCopies@(subfield,3,diag);
        maximals:=Concatenation(maximals,groups);
      elif copies=3 then
        Add(groups,SelectGroupFromSubset@(psl,subfield,diag,d6.c3_invol,3));
      elif copies=6 and d6.in_c6_ker then
        groups:=ImageCopies@(subfield,6,diag);
      else
        Assert(1,copies=6);
        grp:=SelectGroupFromSubset@(psl,subfield,diag,d6.c3_invol,6);
        Add(maximals,grp);
        Add(maximals,grp^(diag^3));
      fi;
    fi;
  od;
  if d6.in_sp_stab then
    if Print > 1 then
      Info(InfoWarning,1,"getting symplectic");
    fi;
    sp:=NormOfSp@(6,q)@factor;
    if d6.in_sp_ker then
      groups:=ImageCopies@(sp,3,diag);
      maximals:=Concatenation(maximals,groups);
    else
      Add(maximals,SelectGroupFromSubset@(psl,sp,diag,d6.sp_invol,3));
    fi;
    if Print > 1 then
      Info(InfoWarning,1,"getting SOPlus");
    fi;
    oplus:=NormOfO@(6,q,1)@factor;
    if d6.in_sp_ker then
      groups:=ImageCopies@(oplus,3,diag);
      maximals:=Concatenation(maximals,groups);
    else
      Add(maximals,SelectGroupFromSubset@(psl,oplus,diag,d6.sp_invol,3));
    fi;
  fi;
  if d6.in_ominus_stab then
    if Print > 1 then
      Info(InfoWarning,1,"getting SOMinus");
    fi;
    ominus:=NormOfO@(6,q,-1)@factor;
    if d6.in_ominus_ker then
      groups:=ImageCopies@(ominus@factor,3,diag);
      maximals:=Concatenation(maximals,groups);
    else
      Add(maximals,SelectGroupFromSubset@(psl,ominus,diag,d6.omin_invol,3));
    fi;
  fi;
  if IsEvenInt(e) then
    half:=QuoInt(e,2);
    q_0:=p^half;
    classes:=Gcd(q_0-1,6);
    if (classes=2 and d6.in_c2_stab) or (classes=6 and d6.in_c6_stab) then
      if Print > 1 then
        Info(InfoWarning,1,"getting SU");
      fi;
      su:=NormOfSU@(6,q_0)@factor;
      if (classes=2) or (classes=6 and d6.in_c6_ker) then
        groups:=ImageCopies@(su,classes,diag);
        maximals:=Concatenation(maximals,groups);
      else
        grp:=SelectGroupFromSubset@(psl,su,diag,d6.c6_invol,6);
        Add(maximals,grp);
        Add(maximals,grp^(diag^3));
      fi;
    fi;
  fi;
  #  and now the C9s
  #  now 6A7. 12 classes in PSL(6,p^2) when (p mod 24) in [5,11,13,19]
  if d6.in_a7_stab then
    if Print > 1 then
      Info(InfoWarning,1,"getting 6A_7");
    fi;
    c9:=Get6a7d6@(q);
    if d6.in_a6_ker then
      c92:=SubStructure(GL(6,q),List([1..Ngens(c9)],i->TransposedMat(c9.-i)));
      groups1:=ImageCopies@(c9@factor,6,diag);
      groups2:=ImageCopies@(c92@factor,6,diag);
      maximals:=Concatenation(maximals,groups1,groups2);
    else
      c9:=c9@factor;
      grp:=SelectGroupFromSubset@(psl,c9,diag,d6.a7_invol,6);
      Add(maximals,grp);
      Add(maximals,grp^(diag^3));
      grp2:=c9^(d6.a7_elt);
      grp3:=SelectGroupFromSubset@(psl,grp2,diag,d6.a7_invol,6);
      Add(maximals,grp3);
      Add(maximals,grp3^(diag^3));
    fi;
  fi;
  #  now 6A6, which is a novelty maximal when out is a conjugate of
  #  <frob> ( p  = 1(6)) or <frob*iota> (p = 5(6)), and p mod 24
  #  in [ 5,11,13,19]. otherwise contained in 6A7.
  if d6.in_a6_stab then
    if Print > 1 then
      Info(InfoWarning,1,"getting 6A_6");
    fi;
    c9:=Get6a6d6@(q);
    grp1:=SelectGroupFromSubset@(psl,c9@factor,diag,d6.a6_invol,6);
    Add(maximals,grp1);
    Add(maximals,grp1^(diag^3));
  fi;
  if d6.in_l3q_ker then
    if Print > 1 then
      Info(InfoWarning,1,"getting SL_3(q)");
    fi;
    c9:=MatrixGroup(SymmetricSquare(GModule(SL(3,q))));
    #  just testing this for now, delete later.
    Assert(1,IsAbsolutelyIrreducible(c9) and (not IsSemiLinear(c9)) and 
     IsPrimitive(c9) and (not IsTensor(c9)) and ClassicalForms(c9)
     .formType="linear");
    groups:=ImageCopies@(c9@factor,2,diag);
    maximals:=Concatenation(maximals,groups);
  fi;
  return maximals;
end;
;
#  ***************************************************************
#   The main function.
#  * Input: - a group isomorphic to an almost simple group with
#  *          socle PSL(6, q) for q prime power,
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

InstallGlobalFunction(L6qIdentify@,
function(group,q)
local 
   F,Print,apsl,d,d6,delta,e,fac,factor,g,gl,group,groupquot,homom,iota,max,
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
  if Print > 1 then
    Print("Making standard group");
  fi;
  gl:=GL(6,q);
  sl:=SL(6,q);
  apsl:=PGammaL2@(6,q);
  AssertAttribute(apsl,"Order",(QuoInt(2*e*Size(GL(6,q)),(q-1))));
  factor:=GroupHomomorphismByImages(gl,apsl,
    apsl.1,apsl.2);
  psl:=sl@factor;
  AssertAttribute(psl,"Order",(QuoInt(Size(SL(6,q)),Gcd(6,q-1))));
  if Print > 1 then
    Print("Setting up isomorphism");
  fi;
  # =v= MULTIASSIGN =v=
  group:=MakeHomomGeneral@(group,6,p,e,psl,apsl,factor:Print:=0);
  homom:=group.val1;
  soc:=group.val2;
  group:=group.val3;
  # =^= MULTIASSIGN =^=
  #   Set up the subgroup of the outer automorphism group induced by group
  if max then
    d:=Gcd(q-1,6);
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
    Assert(1,p=2);
    d6:=Deq1WhichGroup@(quot,groupquot,delta,phia,iota,e);
  elif d=2 then
    d6:=Deq2WhichGroup@(quot,groupquot,delta,phia,iota,p,e);
  elif d=3 then
    Assert(1,p=2);
    d6:=Deq3WhichGroup@(quot,groupquot,delta,phia,iota,e,proj);
  elif d=6 then
    d6:=Deq6WhichGroup@(quot,groupquot,delta,phia,iota,p,e,proj);
  fi;
  maximals:=[];
  if Print > 1 then
    Info(InfoWarning,1,"getting reducibles");
  fi;
  if not d6.is_novelty then
    Add(maximals,(SLPointStab@(6,q)@factor));
    Add(maximals,(SLStabOfNSpace@(6,q,2)@factor));
    Add(maximals,(SLStabOfNSpace@(6,q,4)@factor));
    Add(maximals,(SLStabOfNSpace@(6,q,5)@factor));
  else
    Add(maximals,(SLStabOfNSpaceMeetDual@(6,q,1)@factor));
    Add(maximals,(SLStabOfNSpaceMissDual@(6,q,1)@factor));
    Add(maximals,(SLStabOfNSpaceMeetDual@(6,q,2)@factor));
    Add(maximals,(SLStabOfNSpaceMissDual@(6,q,2)@factor));
  fi;
  Add(maximals,SLStabOfHalfDim@(6,q)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting imprimitives");
  fi;
  if q > 4 then
    Add(maximals,(ImprimsMeetSL@(6,q,6)@factor));
  fi;
  Add(maximals,(ImprimsMeetSL@(6,q,3)@factor));
  Add(maximals,(ImprimsMeetSL@(6,q,2)@factor));
  if Print > 1 then
    Info(InfoWarning,1,"getting semilinears");
  fi;
  Add(maximals,(GammaLMeetSL@(6,q,2)@factor));
  Add(maximals,(GammaLMeetSL@(6,q,3)@factor));
  if Print > 1 then
    Info(InfoWarning,1,"getting tensors");
  fi;
  Add(maximals,(SLTensor@(2,3,q))@factor);
  if d=1 then
    maximals:=Concatenation(maximals,Deq1Maximals@(q,factor,d6,Print));
  elif d=2 then
    maximals:=Concatenation(maximals,Deq2Maximals@(q,factor,d6,Print));
  elif d=3 then
    maximals:=Concatenation(maximals,Deq3Maximals@(q,factor,psl,d6,Print));
  elif d=6 then
    maximals:=Concatenation(maximals,Deq6Maximals@(q,factor,psl,d6,Print));
  fi;
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);


