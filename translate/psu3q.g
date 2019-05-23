#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, Classes, Coefficients, CopiesInGU3,
#  CorrectForm, DefiningPolynomial, DiagonalMatrix, Eltseq, FPGroupStrong,
#  Factorisation, GF, GL, GU, Gcd, Imprims, IsCyclic, IsEven, IsOdd, IsPrime,
#  Matrix, Ngens, NormalSubgroups, Order, OuterInvol, PGammaU, PSigmaU, Parent,
#  PrimitiveElement, Quotrem, Random, Root, SL, SO, SU, ScalarMatrix, Semilin,
#  Socle, SubfieldSO, SubfieldSU, SylowSubgroup, UnitaryForm, WhichGroup, homom

#  Defines: CopiesInGU3, Imprims, OuterInvol, Semilin, SubfieldSO, SubfieldSU,
#  U3qIdentify, WhichGroup

DeclareGlobalFunction("OuterInvol@");

DeclareGlobalFunction("U3qIdentify@");

#  
#  function names in this file:
#  WhichGroup(group, q)
#  OuterInvol(group, q)
#  CopiesInGU3(group, q, factor, homom)
#  Imprims(q)
#  Semilin(q)
#  SubfieldSO(q)
#  SubfieldSU(p, e)
#  U3qMaximals(group, q)

#  ***************************************************************
#  This function takes as input a group with socle PSU(3, q) for
#  some nonprime q and returns the socle, and an integer.
#  this integer is -1 if (3, q+1) = 1 and so there is at most
#  one conjugacy class of each type of subfield group in PSU (the
#  same is therefore true of each extension of PSU. The integer is
#  0 if (3, q+1) = 3 and the group contains PGU, so that in many
#  instances no subfield groups are maximal. The integer is 1 if (3,
#  q+1) = 3 and the group does not contain PGU. This means that of the
#  three conjugate copies of subfield groups under PGU, one will
#  extend to a maximal subgroup of the input group, and the other two
#  fuse.
WhichGroup@:=function(group,q)
local 
   cls_group,cls_sigma,e,f,fac,info_group,info_sigma,m,n,out_group,p,s3,
   s3_sigma,soc,target;
  soc:=Socle(group);
  # =v= MULTIASSIGN =v=
  f:=Subquo(group,[soc]);
  out_group:=f.val1;
  f:=f.val2;
  # =^= MULTIASSIGN =^=
  if Gcd(q+1,3)=1 then
    return rec(val1:=soc,
      val2:=-1);
  fi;
  if soc=group then
    return rec(val1:=soc,
      val2:=3);
  fi;
  fac:=CollectedFactors(q);
  p:=fac[1][1];
  e:=fac[1][2];
  if Gcd(e,3)=1 then
    if Size(out_group) mod 3=0 then
      return rec(val1:=soc,
        val2:=0);
    elif IsEvenInt(Size(out_group)) then
      return rec(val1:=soc,
        val2:=1);
    else
      return rec(val1:=soc,
        val2:=3);
    fi;
  fi;
  Assert(1,e mod 3=0);
  if not IsCyclic(out_group) or Size(out_group) mod 9=0 then
    return rec(val1:=soc,
      val2:=0);
  fi;
  if not (Size(out_group) mod 3=0) then
    if IsEvenInt(Size(out_group)) then
      return rec(val1:=soc,
        val2:=1);
    else
      return rec(val1:=soc,
        val2:=3);
    fi;
  fi;
  Assert(1,Size(out_group) mod 3=0);
  #  this final bit is somewhat time-consuming, but at least is
  #  guaranteed to be right: trying to distinguish between the
  #  (at least) 3 groups of type PSU.3m. The one which is a subgroup of
  #  PSigmaU has different splitting and fusion patterns to the others.
  Assert(1,Size(out_group) mod 3=0);
  m:=Size(out_group);
  s3:=SylowSubgroup(group,3);
  n:=NormalSubgroups(PSigmaU(3,q):OrderEqual:=Size(group));
  target:=n[1].subgroup;
  s3_sigma:=SylowSubgroup(target,3);
  cls_group:=Classes(s3);
  cls_sigma:=Classes(s3_sigma);
  if not Size(cls_group)=Size(cls_sigma) then
    return rec(val1:=soc,
      val2:=0);
  fi;
  info_group:=List([1..Size(cls_group)],i->[cls_group[i][1],cls_group[i][2]]);
  info_sigma:=List([1..Size(cls_sigma)],i->[cls_sigma[i][1],cls_sigma[i][2]]);
  if info_group=info_sigma then
    if IsEvenInt(Size(out_group)) then
      return rec(val1:=soc,
        val2:=1);
    else
      return rec(val1:=soc,
        val2:=3);
    fi;
  else
    return rec(val1:=soc,
      val2:=0);
  fi;
end;
;
#  *******************************************************************
#  This takes as input a group and its socle, which should be of
#  even index, and returns an outer involution.
InstallGlobalFunction(OuterInvol@,
function(group,socle)
local o,x;
  Assert(1,IsEvenInt(QuoInt(Size(group),Size(socle))));
  while true do
    x:=Random(group);
    o:=Order(x);
    if IsEvenInt(o) and not x^(QuoInt(o,2)) in socle then
      return x^(QuoInt(o,2));
    fi;
  od;
  return 0;
end);

#  ********************************************************************
#  this function takes a subgroup of SU(3, q) and makes three copies of
#  it which will be conjugate under GU but will not generally be
#  conjugate under SU:
CopiesInGU3@:=function(group,q,factor)
local groups,i,three_cyc,z;
  z:=PrimitiveElement(GF(q^2));
  three_cyc:=DiagonalMat([1,z^(q-1),1]) #CAST GL(3,q^2)
    ;
  groups:=[];
  for i in [0..2] do
    Add(groups,(group^(three_cyc^i))@factor);
  od;
  return groups;
end;
;
#  ********************************************************************
#  This takes a prime power q and returns the maximal imprimitive
#  subgroup   of SU(3, q).
Imprims@:=function(q)
local a,b,c,conj_mat,grp,half,t,z;
  z:=PrimitiveElement(GF(q^2))^(q-1);
  a:=DiagonalMat([z,1,z^-1]) #CAST GL(3,q^2)
    ;
  b:=[0,1,0,0,0,1,1,0,0] #CAST GL(3,q^2)
    ;
  c:=[-1,0,0,0,0,-1,0,-1,0] #CAST GL(3,q^2)
    ;
  if IsOddInt(q) then
    t:=Root((-1) #CAST GF(q^2)
      ,q+1);
    half:=(2^-1) #CAST GF(q^2)
      ;
    conj_mat:=[1,0,t,0,1,0,half,0,-half*t] #CAST GL(3,q^2)
      ;
  else
    conj_mat:=CorrectForm(MatrixByEntries(GF(q^2),3,3,[0,0,1,0,1,0,1,0,0])
     ,3,q^2,"unitary") #CAST GL(3,q^2)
      ;
  fi;
  grp:=SubStructure(GL(3,q^2),a,#TODO CLOSURE
    b,c);
  return grp^(conj_mat^-1);
end;
;
#  *****************************************************************
#  This takes the prime power q and returns the maximal semilinear
#  subgroup of SU(3, q).
Semilin@:=function(q)
#  /out:"making Singer Cycle";
local 
   bool,coeffs,cxp,cxp2,f2,field_auto,form,grp,mat,mat1,mat2,newelt,o,pol,quot,
   r,x;
  pol:=DefiningPolynomial(GF(q^6),GF(q^2));
  x:=Parent(pol).1;
  coeffs:=Coefficients(pol);
  mat:=[0,1,0,0,0,1,-coeffs[1],-coeffs[2],-coeffs[3]] #CAST GL(3,q^2)
    ;
  #  "forcing order of mat to be q^2 - q + 1";
  o:=Order(mat);
  # =v= MULTIASSIGN =v=
  r:=QuotientRemainder(o,q^2-q+1);
  quot:=r.val1;
  r:=r.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,r=0);
  newelt:=Eltseq(mat^quot) #CAST SL(3,q^2)
    ;
  #  find field automorphism - the reason that x^3 has been added to the
  #  argument below is to ensured that cxp[2] and cxp2[2] are always defined!
  cxp:=Coefficients(x^7+x^(q^2) mod pol);
  cxp2:=Coefficients(x^7+(x^2)^(q^2) mod pol);
  field_auto:=[1,0,0,cxp[1],cxp[2],cxp[3],cxp2[1],cxp2[2],cxp2[3]] #CAST 
   SL(3,q^2)
    ;
  #  "making the group preserve the correct form";
  grp:=SubStructure(SL(3,q^2),newelt,#TODO CLOSURE
    field_auto);
  # =v= MULTIASSIGN =v=
  form:=UnitaryForm(grp);
  bool:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,bool=true);
  mat1:=CorrectForm(form,3,q^2,"unitary") #CAST GL(3,q^2)
    ;
  f2:=MatrixByEntries(GF(q^2),3,3,[0,0,1,0,1,0,1,0,0]);
  mat2:=CorrectForm(f2,3,q^2,"unitary") #CAST GL(3,q^2)
    ;
  return grp^(mat1*mat2^-1);
end;
;
#  ********************************************************************
#  
#  * This function produces the subfield group SO(3, q) \leq SU(3, q).

SubfieldSO@:=function(q)
local form_mat,isit,mat1,mat2,newgrp;
  newgrp:=SubStructure(GL(3,q^2),Eltseq(SO(3,q).1),#TODO CLOSURE
    Eltseq(SO(3,q).2));
  # =v= MULTIASSIGN =v=
  form_mat:=UnitaryForm(newgrp);
  isit:=form_mat.val1;
  form_mat:=form_mat.val2;
  # =^= MULTIASSIGN =^=
  #  form_mat:= ClassicalForms(newgrp)`sesquilinearForm;
  mat1:=CorrectForm(form_mat,3,q^2,"unitary") #CAST GL(3,q^2)
    ;
  mat2:=CorrectForm(MatrixByEntries(GF(q^2),3,3,[0,0,1,0,1,0,1,0,0])
   ,3,q^2,"unitary") #CAST GL(3,q^2)
    ;
  return newgrp^(mat1*mat2^-1);
end;
;
#  ****************************************************************
#  This function produces the collection of subfield groups SU(3,
#  q^(1/b)).(b, d), where d:= (q+1, 3). It also returns Gcd(b, d) in
#  each case, as PSU has (b, d) copies of the group, which fuse under
#  PGU.
SubfieldSU@:=function(p,e)
local b,c,d,f,fac,facs,groups,newgrp,out_elt,prim_scal,scal,x,z;
  groups:=[];
  fac:=CollectedFactors(e);
  d:=Gcd(p^e+1,3);
  z:=PrimitiveElement(GF(p^(2*e)));
  prim_scal:=ScalarMat(3,z^(QuoInt((p^(2*e)-1),d)));
  for facs in fac do
    b:=facs[1];
    if IsPrimeInt(b) and IsOddInt(b) then
      f:=QuoInt(e,b);
      newgrp:=SubStructure(GL(3,p^(2*e)),Eltseq(SU(3,p^f).1),#TODO CLOSURE
        Eltseq(SU(3,p^f).2),prim_scal);
      c:=Gcd(b,Gcd(p^e+1,3));
      if c=3 then
        out_elt:=Eltseq(GU(3,p^f).-1) #CAST GL(3,p^(2*e))
          ;
        x:=QuoInt(((p^(2*e)-1)*p^f),((p^f+1)*3));
        scal:=ScalarMat(3,z^x) #CAST GL(3,p^(2*e))
          ;
        newgrp:=SubStructure(GL(3,p^(2*e)),newgrp,#TODO CLOSURE
          out_elt*scal);
      fi;
      Add(groups,[Gcd(b,d),newgrp]);
    fi;
  od;
  return groups;
end;
;
#  ****************************************************************
#  This is the main function. Takes as input a group with socle PSU(3,
#  q) and the integer q. q is assumed to be a proper prime power
#  (i.e. not prime). Returns the maximal subgroups of the input group.
InstallGlobalFunction(U3qIdentify@,
function(group,q)
local 
   F,Print,apsu,copies,copy_of_so,copy_of_x,e,fac,factor,gens,group,gu,homom,
   max,maximals,out_invol,p,phi,psu,so,soc,su,subfields,subgrp_copies,three_cyc,
   x,z;
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
  p:=fac[1][1];
  e:=fac[1][2];
  Assert(1,e > 1);
  if Print > 1 then
    Info(InfoWarning,1,"making standard group");
  fi;
  gu:=GU(3,q);
  su:=SU(3,q);
  apsu:=PGammaU(3,q);
  factor:=GroupHomomorphismByImages(gu,apsu,
    GeneratorsOfGroup(gu),List([1..Ngens(gu)],i->apsu.i));
  psu:=su@factor;
  if Print > 1 then
    Info(InfoWarning,1,"setting up isomorphism");
  fi;
  #  homom, soc, group := MakeHomom(group, q, psu, apsu : Print:=Print);
  # =v= MULTIASSIGN =v=
  group:=MakeSU3HomomGeneral@(group,p,e,psu,apsu,factor:Print:=Print);
  homom:=group.val1;
  soc:=group.val2;
  group:=group.val3;
  # =^= MULTIASSIGN =^=
  if Print > 1 then
    Print("Calling FPGroupStrong");
  fi;
  # =v= MULTIASSIGN =v=
  phi:=FPGroupStrong(SubStructure(psu,List([1..Ngens(soc)],i->soc.i@homom)));
  F:=phi.val1;
  phi:=phi.val2;
  # =^= MULTIASSIGN =^=
  if (q+1) mod 3=0 then
    gens:=[homom(group.1),homom(group.2),apsu.1,apsu.3];
  else
    gens:=[homom(group.1),homom(group.2),apsu.3];
  fi;
  apsu:=SubStructure(apsu,gens);
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=apsu,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  z:=PrimitiveElement(GF(q^2));
  # =v= MULTIASSIGN =v=
  subgrp_copies:=WhichGroup@(group,q);
  soc:=subgrp_copies.val1;
  subgrp_copies:=subgrp_copies.val2;
  # =^= MULTIASSIGN =^=
  if subgrp_copies > 0 then
    three_cyc:=(DiagonalMat([1,z^(q-1),1]) #CAST GL(3,q^2)
      )@factor;
  fi;
  if subgrp_copies=1 then
    out_invol:=OuterInvol@(group,soc)@homom;
  fi;
  if Print > 1 then
    Info(InfoWarning,1,"getting reducibles");
  fi;
  #  isotropic
  #  Append(~maximals, Stabiliser(psu, 1));
  Add(maximals,IsotropKStab@(3,q,1)@factor);
  #  nonisotropic.
  Add(maximals,NonisotropKStab@(3,q,1)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting imprimitives");
  fi;
  Add(maximals,Imprims@(q)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting semilinears");
  fi;
  Add(maximals,Semilin@(q)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting unitary subfields");
  fi;
  fac:=CollectedFactors(q);
  p:=fac[1][1];
  e:=fac[1][2];
  subfields:=SubfieldSU@(p,e);
  for x in subfields do
    if x[1]=1 then
      Add(maximals,x[2]@factor);
    elif x[1]=3 and subgrp_copies=1 then
      copy_of_x:=SelectGroupGeneral@(psu,x[2]@factor,three_cyc,out_invol);
      maximals:=Concatenation(maximals,[copy_of_x]);
    elif x[1]=3 and subgrp_copies=3 then
      copies:=CopiesInGU3@(x[2],q,factor);
      maximals:=Concatenation(maximals,copies);
    fi;
  od;
  if not IsEvenInt(q) and not subgrp_copies=0 then
    if Print > 1 then
      Info(InfoWarning,1,"getting orthogonal subfields");
    fi;
    so:=SubfieldSO@(q);
    if subgrp_copies=-1 then
      Add(maximals,so@factor);
    elif subgrp_copies=1 then
      copy_of_so:=SelectGroupGeneral@(psu,so@factor,three_cyc,out_invol);
      maximals:=Concatenation(maximals,[copy_of_so]);
    elif subgrp_copies=3 then
      copies:=CopiesInGU3@(so,q,factor);
      maximals:=Concatenation(maximals,copies);
    fi;
  fi;
  return rec(val1:=homom,
    val2:=apsu,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);


