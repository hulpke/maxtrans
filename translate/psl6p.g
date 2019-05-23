#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, AssertAttribute, ChiefFactors,
#  ClassicalForms, Deq2Maximals, Deq2WhichGroup, Deq6Maximals, Deq6WhichGroup,
#  FPGroupStrong, Factorisation, GF, GL, GModule, Gcd, Generators, Get6a6d6,
#  Get6a7d6, Get6l34d6, Get6u43d6, GetInvol, GetLibraryRoot, Getsl211d6,
#  IsAbsolutelyIrreducible, IsPrime, IsPrimitive, IsSemiLinear, IsSquare,
#  IsTensor, MatrixGroup, Ngens, Order, Random, RandomSchreier, Read, SL,
#  SymmetricSquare, Transpose, proj

#  Defines: Deq2Maximals, Deq2WhichGroup, Deq6Maximals, Deq6WhichGroup,
#  Get6a6d6, Get6a7d6, Get6l34d6, Get6u43d6, GetInvol, Getsl211d6, L6pIdentify

DeclareGlobalFunction("L6pIdentify@");

#  
#  This file contains functions called:
#  GetInvol(group,kernel)
#  Deq2WhichGroup(quot,groupquot,delta,iota,p)
#  Deq6WhichGroup(quot,groupquot,delta,iota,p,proj)
#  Deq2Maximals(p, factor,  is_novelty, has_sl211, has_sl3q, Print)
#  Deq6Maximals(p, factor, psl, d6, Print)
#  L6pIdentify(group, p)

#  files from DFH - slightly modified to return functions not
#  objects.
Getsl211d6@:=function(p)
local L,_LR,_LRS,c9,c9lib;
  c9lib:=Concatenation(GetLibraryRoot(),"/c9lattices/");
  _LRS:=Read(Concatenation(c9lib,"sl211d6"));
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
Get6u43d6@:=function(p)
local L,_LR,_LRS,c9,c9lib;
  c9lib:=Concatenation(GetLibraryRoot(),"/c9lattices/");
  _LRS:=Read(Concatenation(c9lib,"6au43d6"));
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
Get6l34d6@:=function(p)
local L,_LR,_LRS,c9,c9lib;
  c9lib:=Concatenation(GetLibraryRoot(),"/c9lattices/");
  _LRS:=Read(Concatenation(c9lib,"6l34d6"));
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
#   d eq 2 WhichGroup we have Out(PSL6(p)) = 2^2.
#  5 possible groups: PSL itself, PGL, PSigmaL, PSL.2_3 and Aut(PSL).

Deq2WhichGroup@:=function(quot,groupquot,delta,iota,p)
#  /out:first check whether subgroup of PGL
local has_l211,has_sl3q,is_novelty;
  is_novelty:=not IsSubset(SubStructure(quot,delta),groupquot);
  if (not (p=11)) and IsSquare((-11) #CAST GF(p)
    ) then
    has_l211:=IsSubset(SubStructure(quot,delta*iota),groupquot);
  else
    has_l211:=false;
  fi;
  if IsSquare(2 #CAST GF(p)
    ) then
    has_sl3q:=IsSubset(SubStructure(quot,iota),groupquot);
  else
    has_sl3q:=IsSubset(SubStructure(quot,delta*iota),groupquot);
  fi;
  return rec(val1:=is_novelty,
    val2:=has_l211,
    val3:=has_sl3q);
end;
;
#   d eq 6 WhichGroup we have Out(PSL6(p)) = D_{2 x 6}

Deq6WhichGroup@:=function(quot,groupquot,delta,iota,p,proj)
local DT@,d6,kernel;
  DT@:="unneeded record format";
  d6:=rec();
  #  first check whether subgroup of PGL.
  d6.is_novelty:=not IsSubset(SubStructure(quot,delta),groupquot);
  #  action on all classical groups has same kernel.
  kernel:=SubStructure(quot,delta^3);
  d6.in_kernel:=IsSubset(kernel,groupquot);
  #  stabiliser for Sp, O+, O- (p = 3(4)) is S3 from CUP text
  d6.in_sp_stab:=ForAny([0..5],i->IsSubset(SubStructure(quot,delta^3,#TODO 
   CLOSURE
    iota)^(delta^i),groupquot));
  #  kernel for Sp, O+, O- (p = 3(4)) is K2 from CUP text.
  if d6.in_sp_stab and not d6.in_kernel then
    d6.sp_invol:=GetInvol@(groupquot,kernel)@@proj;
  fi;
  d6.in_ominus_stab:=d6.in_sp_stab;
  if (p mod 4)=1 then
    d6.in_ominus_stab:=ForAny([0..5]
     ,i->IsSubset(SubStructure(quot,delta^3,#TODO CLOSURE
      iota*delta)^(delta^i),groupquot));
    if d6.in_ominus_stab and not d6.in_kernel then
      d6.omin_invol:=GetInvol@(groupquot,kernel)@@proj;
    fi;
  fi;
  d6.in_u43_stab:=false;
  if (p mod 12)=1 then
    d6.in_u43_ker:=IsSubset(SubStructure(quot,#NOP
    ),groupquot);
    d6.in_u43_stab:=ForAny([0..5],i->IsSubset(SubStructure(quot,iota)^(delta^i)
     ,groupquot));
    if d6.in_u43_stab and not d6.in_u43_ker then
      d6.u43_invol:=GetInvol@(groupquot,SubStructure(quot,#NOP
      ))@@proj;
    fi;
  elif (p mod 12)=7 then
    d6.in_u43_ker:=IsSubset(SubStructure(quot,delta^3),groupquot);
    d6.in_u43_stab:=not ((delta in groupquot) or (delta^2 in groupquot));
    if d6.in_u43_stab and not d6.in_u43_ker then
      d6.u43_invol:=GetInvol@(groupquot,SubStructure(quot,delta^3))@@proj;
    fi;
  fi;
  d6.in_l211_stab:=false;
  if IsSquare((-11) #CAST GF(p)
    ) then
    d6.in_l211_ker:=IsSubset(SubStructure(quot,#NOP
    ),groupquot);
    d6.in_l211_stab:=ForAny([0..5],i->IsSubset(SubStructure(quot,iota*delta)
     ^(delta^i),groupquot));
    if d6.in_l211_stab and not d6.in_l211_ker then
      d6.l211_invol:=GetInvol@(groupquot,SubStructure(quot,#NOP
      ))@@proj;
    fi;
  fi;
  d6.in_l34_stab:=false;
  if (p mod 24) in [1,19] then
    d6.in_l34_ker:=IsSubset(SubStructure(quot,#NOP
    ),groupquot);
    d6.in_l34_stab:=ForAny([0..5],i->IsSubset(SubStructure(quot,iota)^(delta^i)
     ,groupquot));
    if d6.in_l34_stab and not d6.in_l34_ker then
      d6.l34_invol:=GetInvol@(groupquot,SubStructure(quot,#NOP
      ))@@proj;
    fi;
  elif (p mod 24) in [7,13] then
    #  get novelties in this case. "kernel" means find three copies
    #  later and "stab" means find one copy.
    d6.in_l34_ker:=groupquot=SubStructure(quot,delta^3);
    #  get 1 copy if have a nontrivial group
    d6.in_l34_stab:=d6.in_l34_ker or ForAny([0..5]
     ,i->groupquot=SubStructure(quot,delta*iota)^(delta^i)) or Size(groupquot)
     =4;
    if d6.in_l34_stab and not d6.in_l34_ker then
      #  both delta*iota and delta^2*iota fix same group, so any involution
      #   other then delta^3
      d6.l34_invol:=GetInvol@(groupquot,SubStructure(quot,delta^3))@@proj;
    fi;
  fi;
  #  6A_7. 12 classes so regular representation.
  d6.in_a7_ker:=(((p mod 24) in [1,7]) and (groupquot=SubStructure(quot,#NOP
  )));
  #  6A_6. usually contained in 6A_7 but two copies novelty under
  #  duality*diag. only bother defining a "stab" here as there's a unique
  #  conjugacy class of subgroups where anything happens.
  d6.in_a6_stab:=((p mod 24) in [1,7]) and ForAny([0..5]
   ,i->groupquot=SubStructure(quot,delta*iota)^(delta^i));
  if d6.in_a6_stab then
    d6.a6_invol:=GetInvol@(groupquot,SubStructure(quot,#NOP
    ))@@proj;
  fi;
  #  And finally, L3(p).
  d6.in_l3p_ker:=(IsSquare(2 #CAST GF(p)
    ) and IsSubset(SubStructure(quot,delta^2,#TODO CLOSURE
    iota),groupquot)) or ((not IsSquare(2 #CAST GF(p)
    )) and IsSubset(SubStructure(quot,delta^2,#TODO CLOSURE
    delta*iota),groupquot));
  return d6;
end;
;
#  **************************************************************
#  This makes maximal subgroups when Gcd(p-1, 6) = 2.
Deq2Maximals@:=function(p,factor,is_novelty,has_sl211,has_sl3q,Print)
#  /out:there's some weird behaviour for small fields that we can ignore.
local diag,i,k,maximals,sl,sominus,soplus;
  Assert(1,p > 4 and IsPrimeInt(p));
  diag:=GL(6,p).1@factor;
  maximals:=[];
  if Print > 1 then
    Info(InfoWarning,1,"getting reducibles");
  fi;
  if not is_novelty then
    Add(maximals,(SLPointStab@(6,p)@factor));
    for i in [2,4,5] do
      Add(maximals,(SLStabOfNSpace@(6,p,i)@factor));
    od;
  else
    Add(maximals,(SLStabOfNSpaceMeetDual@(6,p,1)@factor));
    Add(maximals,(SLStabOfNSpaceMissDual@(6,p,1)@factor));
    Add(maximals,(SLStabOfNSpaceMeetDual@(6,p,2)@factor));
    Add(maximals,(SLStabOfNSpaceMissDual@(6,p,2)@factor));
  fi;
  Add(maximals,SLStabOfHalfDim@(6,p)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting imprimitives");
  fi;
  for k in [2,3,6] do
    Add(maximals,(ImprimsMeetSL@(6,p,k)@factor));
  od;
  if Print > 1 then
    Info(InfoWarning,1,"getting superfields");
  fi;
  Add(maximals,(GammaLMeetSL@(6,p,2)@factor));
  Add(maximals,(GammaLMeetSL@(6,p,3)@factor));
  if Print > 1 then
    Info(InfoWarning,1,"getting tensor");
  fi;
  #  single conjugacy class
  Add(maximals,(SLTensor@(2,3,p)@factor));
  if Print > 1 then
    Info(InfoWarning,1,"getting orthogonals");
  fi;
  #  single conjugacy class
  soplus:=NormOfO@(6,p,1);
  sominus:=NormOfO@(6,p,-1);
  Add(maximals,soplus@factor);
  Add(maximals,sominus@factor);
  #  single conjugacy class
  if Print > 1 then
    Info(InfoWarning,1,"getting symplectic");
  fi;
  Add(maximals,(NormOfSp@(6,p))@factor);
  #  finally the C9s.
  if has_sl211 then
    if Print > 1 then
      Info(InfoWarning,1,"getting SL_2(11)");
    fi;
    sl:=Getsl211d6@(p);
    Add(maximals,sl@factor);
    Add(maximals,(sl@factor)^diag);
  fi;
  if has_sl3q then
    if Print > 1 then
      Info(InfoWarning,1,"getting SL_3(p)");
    fi;
    sl:=MatrixGroup(SymmetricSquare(GModule(SL(3,p))));
    Assert(1,IsAbsolutelyIrreducible(sl) and (not IsSemiLinear(sl)) and 
     IsPrimitive(sl) and (not IsTensor(sl)) and ClassicalForms(sl)
     .formType="linear");
    Add(maximals,sl@factor);
    Add(maximals,(sl@factor)^diag);
  fi;
  return maximals;
end;
;
#  ******************************************************************
#  makes maximals when (p-1, 6) = 6.
#  d6 is all the data about where in the group we are, and hence what
#  subgroups and conjugacy classes must be made.
Deq6Maximals@:=function(p,factor,psl,d6,Print)
local 
   c,c9,c92,diag,groups,groups1,groups2,grp,grp1,grps,maximals,sominus,soplus,
   sp;
  Assert(1,IsPrimeInt(p));
  Assert(1,p mod 6=1);
  diag:=GL(6,p).1@factor;
  maximals:=[];
  if Print > 1 then
    Info(InfoWarning,1,"getting reducibles");
  fi;
  if not d6.is_novelty then
    Add(maximals,(SLPointStab@(6,p)@factor));
    Add(maximals,(SLStabOfNSpace@(6,p,2)@factor));
    Add(maximals,(SLStabOfNSpace@(6,p,4)@factor));
    Add(maximals,(SLStabOfNSpace@(6,p,5)@factor));
  else
    Add(maximals,(SLStabOfNSpaceMeetDual@(6,p,1)@factor));
    Add(maximals,(SLStabOfNSpaceMissDual@(6,p,1)@factor));
    Add(maximals,(SLStabOfNSpaceMeetDual@(6,p,2)@factor));
    Add(maximals,(SLStabOfNSpaceMissDual@(6,p,2)@factor));
  fi;
  Add(maximals,SLStabOfHalfDim@(6,p)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting imprimitives");
  fi;
  Add(maximals,(ImprimsMeetSL@(6,p,6)@factor));
  Add(maximals,(ImprimsMeetSL@(6,p,3)@factor));
  Add(maximals,(ImprimsMeetSL@(6,p,2)@factor));
  if Print > 1 then
    Info(InfoWarning,1,"getting semilinears");
  fi;
  Add(maximals,(GammaLMeetSL@(6,p,2)@factor));
  Add(maximals,(GammaLMeetSL@(6,p,3)@factor));
  if Print > 1 then
    Info(InfoWarning,1,"getting tensors");
  fi;
  Add(maximals,(SLTensor@(2,3,p))@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting classical groups");
  fi;
  soplus:=NormOfO@(6,p,1);
  sominus:=NormOfO@(6,p,-1);
  sp:=NormOfSp@(6,p);
  if d6.in_kernel then
    for grp in [soplus,sominus,sp] do
      groups:=ImageCopies@(grp@factor,3,diag);
      maximals:=Concatenation(maximals,groups);
    od;
  elif d6.in_sp_stab then
    grps:=[soplus,sp];
    if (p mod 4)=3 then
      Add(grps,sominus);
    fi;
    for grp in grps do
      if grp=soplus then
        Info(InfoWarning,1,"getting soplus");
      elif grp=sominus then
        Info(InfoWarning,1,"getting sominus");
      elif grp=sp then
        Info(InfoWarning,1,"getting sp");
      fi;
      Add(maximals,SelectGroupFromSubset@(psl,grp@factor,diag,d6.sp_invol,3));
    od;
  fi;
  if ((p mod 4)=1) and d6.in_ominus_stab and not d6.in_kernel then
    Add(maximals,SelectGroupFromSubset@(psl,sominus@factor,diag,d6.omin_invol,3)
     );
  fi;
  #  and now the C9s. many many of them
  #  first deal with U4(3). always there, tho' number of copies and
  #  stabiliser depend on congruences mod 12.
  if d6.in_u43_stab then
    if Print > 1 then
      Info(InfoWarning,1,"getting U4(3)");
    fi;
    c9:=Get6u43d6@(p);
    if d6.in_u43_ker and (p mod 12)=1 then
      groups:=ImageCopies@(c9@factor,6,diag);
      maximals:=Concatenation(maximals,groups);
    elif d6.in_u43_ker and (p mod 12)=7 then
      groups:=ImageCopies@(c9@factor,3,diag);
      maximals:=Concatenation(maximals,groups);
    elif (p mod 12)=1 then
      grp1:=SelectGroupFromSubset@(psl,c9@factor,diag,d6.u43_invol,6);
      Add(maximals,grp1);
      Add(maximals,grp1^(diag^3));
    elif (p mod 12)=7 then
      Add(maximals,SelectGroupFromSubset@(psl,c9@factor,diag,d6.u43_invol,3));
    fi;
  fi;
  #  next SL(2, 11). There when (-11) is a square in GF(p), either
  #  2 or 6 copies depending on whether in kernel or stabiliser.
  if d6.in_l211_stab then
    if Print > 1 then
      Info(InfoWarning,1,"getting L2(11)");
    fi;
    c9:=Getsl211d6@(p);
    if d6.in_l211_ker then
      groups:=ImageCopies@(c9@factor,6,diag);
      maximals:=Concatenation(maximals,groups);
    else
      grp1:=SelectGroupFromSubset@(psl,c9@factor,diag,d6.l2_11invol,6);
      Add(maximals,grp1);
      Add(maximals,grp1^(diag^3));
    fi;
  fi;
  #  novelty subgroup of SL^{\pm}, SL.<delta*iota> (and its conjugates)
  #  SL.<delta^3,iota> (and its conjugates) when p = 7,13(24)
  #  otherwise fairly well behaved.
  if d6.in_l34_stab then
    if Print > 1 then
      Info(InfoWarning,1,"getting 6L_3(4)");
    fi;
    c9:=Get6l34d6@(p);
    #  just testing this for now, delete later.
    Assert(1,IsAbsolutelyIrreducible(c9) and (not IsSemiLinear(c9)) and 
     IsPrimitive(c9) and (not IsTensor(c9)) and ClassicalForms(c9)
     .formType="linear");
    if (p mod 24) in [1,19] then
      c:=6;
    else
      c:=3;
    fi;
    if d6.in_l34_ker then
      groups:=ImageCopies@(c9@factor,c,diag);
      maximals:=Concatenation(maximals,groups);
    else
      grp1:=SelectGroupFromSubset@(psl,c9@factor,diag,d6.l34_invol,c);
      Add(maximals,grp1);
      if (p mod 24) in [1,19] then
        Add(maximals,grp1^(diag^3));
      fi;
    fi;
  fi;
  #  now 6A7. 12 classes in PSL when p = 1,7(24), otherwise none.
  if d6.in_a7_ker then
    if Print > 1 then
      Info(InfoWarning,1,"getting 6A_7");
    fi;
    c9:=Get6a7d6@(p);
    c92:=SubStructure(GL(6,p),List([1..Ngens(c9)],i->TransposedMat(c9.-i)));
    groups1:=ImageCopies@(c9@factor,6,diag);
    groups2:=ImageCopies@((c92@factor),6,diag);
    maximals:=Concatenation(maximals,groups1,groups2);
  fi;
  #  now 6A6, which is a novelty maximal when out is a conjugate of
  #  <iota>, and p = 1,7(24). otherwise contianed in 6A7.
  if d6.in_a6_stab then
    if Print > 1 then
      Info(InfoWarning,1,"getting 6A_6");
    fi;
    c9:=Get6a6d6@(p);
    grp1:=SelectGroupFromSubset@(psl,c9@factor,diag,d6.a6_invol,6);
    Add(maximals,grp1);
    Add(maximals,grp1^(diag^3));
  fi;
  if d6.in_l3p_ker then
    if Print > 1 then
      Info(InfoWarning,1,"getting SL_3(p)");
    fi;
    c9:=MatrixGroup(SymmetricSquare(GModule(SL(3,p))));
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
#  *          socle PSL(6, p) for p prime,
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

InstallGlobalFunction(L6pIdentify@,
function(group,p)
local 
   F,Print,apsl,d,d6,delta,fac,factor,g,gl,group,groupquot,has_sl211,has_sl3q,
   homom,iota,is_novelty,max,maximals,newgens,ord_apsl,phi,proj,psl,quot,sl,soc,
   subapsl;
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
  if Print > 1 then
    Print("Making standard group");
  fi;
  gl:=GL(6,p);
  sl:=SL(6,p);
  apsl:=PGammaL2@(6,p);
  Assert(1,Ngens(apsl)=3);
  AssertAttribute(apsl,"Order",(QuoInt(2*Size(GL(6,p)),(p-1))));
  factor:=GroupHomomorphismByImages(gl,apsl,
    apsl.1,apsl.2);
  psl:=sl@factor;
  AssertAttribute(psl,"Order",(QuoInt(Size(SL(6,p)),Gcd(p-1,6))));
  if Print > 1 then
    Print("Setting up isomorphism");
  fi;
  # =v= MULTIASSIGN =v=
  group:=MakeHomomGeneral@(group,6,p,1,psl,apsl,factor:Print:=0);
  homom:=group.val1;
  soc:=group.val2;
  group:=group.val3;
  # =^= MULTIASSIGN =^=
  #   Set up the subgroup of the outer automorphism group induced by group
  if max then
    d:=Gcd(p-1,6);
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
    iota:=proj(apsl.3);
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
  if d=2 then
    # =v= MULTIASSIGN =v=
    has_sl3q:=Deq2WhichGroup@(quot,groupquot,delta,iota,p);
    is_novelty:=has_sl3q.val1;
    has_sl211:=has_sl3q.val2;
    has_sl3q:=has_sl3q.val3;
    # =^= MULTIASSIGN =^=
    if Print > 1 then
      Print("is novelty =",is_novelty,"has_sl211 
       =",has_sl211,"has_sl3q=",has_sl3q);
    fi;
    maximals:=Deq2Maximals@(p,factor,is_novelty,has_sl211,has_sl3q,Print);
  elif d=6 then
    d6:=Deq6WhichGroup@(quot,groupquot,delta,iota,p,proj);
    if Print > 1 then
      Print("is novelty =",d6.is_novelty,"in kernel =",d6.in_kernel);
      Print("in sp stab =",d6.in_sp_stab,"in ominus stab =",d6.in_ominus_stab);
      Print("in U_4(3) stab =",d6.in_u43_stab,"in SL_2(11) stab 
       =",d6.in_l211_stab);
      Print("in L_3(4) stab =",d6.in_l34_stab,"in A_7 ker =",d6.in_a7_ker);
      Print("in A_6 stab =",d6.in_a6_stab,"in SL(3,p) ker =",d6.in_l3p_ker);
    fi;
    maximals:=Deq6Maximals@(p,factor,psl,d6,Print);
  fi;
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);


