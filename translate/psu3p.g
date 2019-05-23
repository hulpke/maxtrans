#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, AssertAttribute, Centraliser, Coefficients,
#  CoprimeMaximals, CorrectFormPSU3p, DefiningPolynomial, DerivedSubgroup,
#  DiagonalMatrix, Domain, Eltseq, FPGroupStrong, Factorisation, GF, GL,
#  Generators, GetAlt6, GetExtraspec, GetImprims, GetPSL2_7, GetReducibles,
#  GetSemilin, GetSubfield, GtoSU, Id, Identity, Integers, IsConjugate,
#  IsDiagonal, IsPrime, IsSquare, IsZero, ListMatToQ, MakeSU3HomomGeneral,
#  Ngens, NonCoprimeMaximals, Order, PGammaU, PSU, Parent, PrimitiveElement,
#  Quotrem, RSpace, Random, RandomSchreier, RecogniseSU3, Root, RootOfUnity,
#  SL, SO, SU, SelectGroup, Socle, SquareRoot, Stabiliser, Transpose,
#  UnitaryForm, homom

#  Defines: CoprimeMaximals, CorrectFormPSU3p, GetAlt6, GetExtraspec,
#  GetImprims, GetPSL2_7, GetReducibles, GetSemilin, GetSubfield, ListMatToQ,
#  MakeSU3HomomGeneral, NonCoprimeMaximals, SelectGroup, U3pIdentify

DeclareGlobalFunction("MakeSU3HomomGeneral@");

DeclareGlobalFunction("U3pIdentify@");

DeclareGlobalFunction("MakeSU3HomomGeneral@");

#  
#  Constructively recognise and find maximal subgroups of U(3,p).?
#  Recognition by Derek Holt.
#  Maximals by Colva Roney-Dougal.

ListMatToQ@:=function(a,q)
#  /out: raise every element of matrix A to q-th power.
local i,list;
  list:=Eltseq(a);
  for i in [1..Size(list)] do
    list[i]:=list[i]^q;
  od;
  return list;
end;
;
#  
#  * This function finds a conjugating matrix that sends a group
#  * preserving a unitary form to a group preserving a unitary form
#  * AntiDiag([1, 1, 1]);
#  *
#  * It could be made faster by doing row ops, and then using the fact
#  * that the form matrix is hermitian at each point, but I figure that
#  * in the 3\times3 case it really doesn't matter.

CorrectFormPSU3p@:=function(form,p)
local 
   conj,conj_1,conj_2,conj_3,conj_4,form,form1,form2,half,t,temp,temp1,
   tempconj;
  conj:=Identity(GL(3,p^2));
  temp:=form;
  while temp[1][1]=0 do
    conj:=Random(GL(3,p^2));
    temp:=conj*form*TransposedMat(ListMatToQ@(conj,p) #CAST GL(3,p^2)
      );
  od;
  form:=temp;
  #  "form = ", form;
  Assert(1,not form[1][1]=0);
  conj_1:=[1 #CAST GF(p^2)
    ,0,0,-form[2][1]/form[1][1],1 #CAST GF(p^2)
    ,0,-form[3][1]/form[1][1],0,1 #CAST GF(p^2)
    ] #CAST GL(3,p^2)
    ;
  form1:=conj_1*form*TransposedMat(ListMatToQ@(conj_1,p) #CAST GL(3,p^2)
    );
  #  "form1 = ", form1:Magma;
  Assert(1,form1[2][1]=0);
  Assert(1,form1[3][1]=0);
  temp1:=form1;
  tempconj:=Identity(GL(3,p^2));
  while temp1[2][2]=0 do
    temp:=Random(GL(2,p^2));
    tempconj:=[1,0,0,0,temp[1][1],temp[1][2],0,temp[2][1],temp[2][2]] #CAST 
     GL(3,p^2)
      ;
    temp1:=tempconj*form1*TransposedMat(ListMatToQ@(tempconj,p) #CAST GL(3,p^2)
      );
  od;
  conj_2:=[1,0,0,0,1,0,0,-form1[3][2]/form1[2][2],1] #CAST GL(3,p^2)
    ;
  form2:=conj_2*form1*TransposedMat(ListMatToQ@(conj_2,p) #CAST GL(3,p^2)
    );
  #  "form2= ", form2:Magma;
  Assert(1,IsDiagonal(form2));
  conj_3:=DiagonalMat(List([1..3],i->Root((form2[i][i] #CAST GF(p^2)
    )^-1,p+1))) #CAST GL(3,p^2)
    ;
  #  "form3= ", conj_3*form2*Transpose(GL(3, p^2)!ListMatToQ(conj_3, p)):Magma;
  t:=Root((-1) #CAST GF(p^2)
    ,p+1);
  half:=(2^(-1)) #CAST GF(p^2)
    ;
  conj_4:=[1,0,t,0,1,0,half,0,-t*half] #CAST GL(3,p^2)
    ;
  return (conj_4*conj_3*conj_2*conj_1)^-1;
end;
;
#  This function returns the C_9 group 3.Alt(6), which is
#  *a subgroup of U(3, p) whenever 5 is a square in GF(p) (i.e. p = \pm
#  *1 mod 5) and omega (a cube root of unity) is in GF(p^2) \setminus
#  *GF(p)  (i.e. p = -1 mod 3).
#  *
#  *These two conditions arise from the fact that a representation is
#  *unitary if and only if the map induced by the frobenius automorphism
#  *is equal to complex conjugation. Since b5 is real it must be fixed
#  *by the frobenius map, and so 5 must be a square in GF(p). Since
#  *omega is complex it is not fixed by the frobenius map, and so must
#  *lie in GF(p^2) \setminus GF(p).
#  *
#  *Has been shown to produce the correct unitary group in range p in
#  *[5..1000], that is, a unitary group with form the antidiagonal
#  * matrix [1, 1, 1].

GetAlt6@:=function(p)
local b5,group,h,half,hbar,mat,omega,q,r5,x;
  Assert(1,IsPrimeInt(p));
  Assert(1,IsSquare(5 #CAST GF(p)
    ));
  q:=p^2;
  r5:=SquareRoot(5 #CAST GF(q)
    );
  b5:=((-1+r5)/2) #CAST GF(q)
    ;
  omega:=RootOfUnity(3,GF(q));
  h:=omega-b5;
  hbar:=omega^2-b5;
  #  b5 real, omegabar = omega^2
  half:=(2^-1) #CAST GF(q)
    ;
  Assert(1,omega in GF(q));
  group:=SubStructure(GL(3,q),[-1,0,0,0,-1,0,0,0,1],#TODO CLOSURE
    [0,1,0,0,0,1,1,0,0],[-1,0,0,0,0,-1,0,-1,0]
   ,[half,-half,-h*half,-half,half,-h*half,hbar*half,hbar*half,0]);
  #   We now have a group with form matrix the identity matrix, this
  #  * needs to be conjugated so that it has form matrix AntiDiag([1, 1,
  #  * 1]), as this is the pre-defined unitary form in magma.
  
  x:=Root((-1) #CAST GF(q)
    ,p+1);
  mat:=[1,0,x,0,1,0,half,0,-x*half] #CAST GL(3,q)
    ;
  return group^(mat^-1);
end;
;
#   This is a maximal subgroup of SU whenever p+1 eq 0 mod 3. It
#  * would be nice to get rid of the SL intersection at some point
#  * The form of the matrix b ensures that the basis is always of
#  * orthonormal vectors, so we have to conjugate to make the matrix of
#  * sesquilinear form into AntiDiag[1, 1, 1].

GetExtraspec@:=function(p)
local a,b,c,conj_mat,d,grp,half,newgrp,ninth,omega,t,z;
  z:=PrimitiveElement(GF(p^2));
  omega:=z^((p^2-1)/3) #CAST Integers()
    ;
  if p^2 mod 9=1 then
    ninth:=z^((p^2-1)/9) #CAST Integers()
      ;
  fi;
  #  
  #  * matrix definitions. a and b generate the 3^(1+2), then c and
  #  * d are the normaliser.
  
  a:=DiagonalMat([1,omega,omega^2]) #CAST GL(3,p^2)
    ;
  b:=[0,1,0,0,0,1,1,0,0] #CAST GL(3,p^2)
    ;
  if p^2 mod 9=1 then
    c:=DiagonalMat([ninth^2,ninth^5,ninth^2]) #CAST GL(3,p^2)
      ;
  else
    c:=DiagonalMat([1,omega,1]) #CAST GL(3,p^2)
      ;
  fi;
  d:=[1,1,1,1,omega,omega^2,1,omega^2,omega] #CAST GL(3,p^2)
    ;
  #  
  #  * If p^2 mod 9 is not equal to 1 then the derived subgroup of
  #  * newgrp is equal to the intersection with SL. If p^2 mod 9 is
  #  * equal to 1 then the intersection is bigger than this.
  
  grp:=SubStructure(GL(3,p^2),a,#TODO CLOSURE
    b,c,d);
  if p^2 mod 9=1 then
    newgrp:=Intersection(grp,SL(3,p^2));
  else
    newgrp:=DerivedSubgroup(grp);
  fi;
  #  
  #  * Finally we conjugate so that the unitary form preserved by
  #  * the group is the correct one.
  
  t:=Root((-1) #CAST GF(p^2)
    ,p+1);
  half:=(2^(-1)) #CAST GF(p^2)
    ;
  conj_mat:=[1,0,t,0,1,0,half,0,-t*half] #CAST GL(3,p^2)
    ;
  return newgrp^(conj_mat^(-1));
end;
;
#  
#  * This makes the maximal imprimitive subgroup of SU(3, p). We
#  * make the matrices in the obvious way (just the same as in the
#  * linear case, only we use elements of order dividing p+1). We
#  * then conjugate the group so that it preserves AntiDiag([1, 1, 1]),
#  * the form matrix preserved by SU(3, p) in Magma.
#  * Tested for correct order in SL and form type for p in [3..500].

GetImprims@:=function(p)
local a,b,c,conj_mat,grp,half,t,z;
  z:=PrimitiveElement(GF(p^2))^(p-1);
  t:=Root((-1) #CAST GF(p^2)
    ,p+1);
  half:=(2^-1) #CAST GF(p^2)
    ;
  a:=DiagonalMat([z,1,z^-1]) #CAST GL(3,p^2)
    ;
  b:=[0,1,0,0,0,1,1,0,0] #CAST GL(3,p^2)
    ;
  c:=[-1,0,0,0,0,-1,0,-1,0] #CAST GL(3,p^2)
    ;
  conj_mat:=[1,0,t,0,1,0,half,0,-half*t] #CAST GL(3,p^2)
    ;
  grp:=SubStructure(GL(3,p^2),a,#TODO CLOSURE
    b,c);
  return grp^(conj_mat^(-1));
end;
;
#  This function produces the C_9 group PSL(2, 7), which is a subgroup
#  * U(3, p) whenever Sqrt(-7) lies in GF(p^2) \setminus GF(p).
#  *The matrices come from the Atlas "Reflection" construction.
#  * Tested on all appropriate p^2 in range [9..10000].

GetPSL2_7@:=function(q)
local bool,fac,form,group,half,p,quarter,sqrt,z;
  Assert(1,q > 3 and not q=7);
  fac:=CollectedFactors(q);
  p:=fac[1][1];
  z:=(-7) #CAST GF(q)
    ;
  Assert(1,IsSquare(z));
  sqrt:=SquareRoot(z);
  half:=(2^-1) #CAST GF(q)
    ;
  quarter:=(4^-1) #CAST GF(q)
    ;
  group:=SubStructure(SL(3,q),DiagonalMat([1,-1,-1]) #CAST SL(3,q)
    ,#TODO CLOSURE
    [-1,0,0,0,0,-1,0,-1,0] #CAST SL(3,q)
    ,[0,-1,0,-1,0,0,0,0,-1] #CAST SL(3,q)
    ,[-half,half,(-1+sqrt)*quarter,half,-half,(-1+sqrt)*quarter,(-1-sqrt)
   *quarter,(-1-sqrt)*quarter,0] #CAST SL(3,q)
    );
  #  assert #group eq 168;
  # =v= MULTIASSIGN =v=
  form:=UnitaryForm(group);
  bool:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,bool);
  return group^CorrectFormPSU3p@(form,p);
end;
;
#   This function gets the stabiliser of a nonisotropic point.
#  * It needs improving shortly - this is woefully inefficient.
#  * [0, 1, 0] is always a nonisotropic point.

GetReducibles@:=function(su,p)
return Stabiliser(su,SubStructure(RSpace(su),[0,1,0]));
end;
;
#   Tested for p in [5..11] 
GetSemilin@:=function(p)
#  /out:"making Singer Cycle";
local bool,coeffs,cxp,cxp2,field_auto,form,grp,mat,newelt,o,pol,q,r,x;
  pol:=DefiningPolynomial(GF(p^6),GF(p^2));
  x:=Parent(pol).1;
  coeffs:=Coefficients(pol);
  mat:=[0,1,0,0,0,1,-coeffs[1],-coeffs[2],-coeffs[3]] #CAST GL(3,p^2)
    ;
  #  "forcing order of mat to be p^2 - p + 1";
  o:=Order(mat);
  # =v= MULTIASSIGN =v=
  r:=QuotientRemainder(o,p^2-p+1);
  q:=r.val1;
  r:=r.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,r=0);
  newelt:=Eltseq(mat^q) #CAST SL(3,p^2)
    ;
  #  find field automorphism - the reason that x^7 has been added to the
  #  argument below is to ensured that cxp[2] and cxp2[2] are always defined!
  cxp:=Coefficients(x^7+x^(p^2) mod pol);
  cxp2:=Coefficients(x^7+(x^2)^(p^2) mod pol);
  field_auto:=[1,0,0,cxp[1],cxp[2],cxp[3],cxp2[1],cxp2[2],cxp2[3]] #CAST 
   SL(3,p^2)
    ;
  #  "making the group preserve the correct form";
  grp:=SubStructure(SL(3,p^2),newelt,#TODO CLOSURE
    field_auto);
  # =v= MULTIASSIGN =v=
  form:=UnitaryForm(grp);
  bool:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,bool=true);
  return grp^CorrectFormPSU3p@(form,p);
end;
;
#  
#  * This function produces the subfield group SO(3, p) \leq SU(3, p). It
#  * always appears to have form matrix AntiDiag[1, form_elt, 1], so
#  * conjugating by a Diag[1, x, 1], where x*x^p eq form_elt, turns
#  * it into a group with form matrix AntiDiag[1, 1, 1], i.e. a subgroup of
#  * the standard magma copy of SU(3, p).
#  *
#  * Update by billu : May 2006: make more robust
#  * new forms code from Derek => form_mat is AntiDiag[a,b,a] with a != 0,
#  * so we now scale by 1/a to get form_elt

GetSubfield@:=function(p)
local F,conj_elt,conj_mat,form_elt,form_mat,gl,isit,newgrp;
  F:=GF(p^2);
  gl:=GL(3,F);
  newgrp:=SubStructure(gl,Eltseq(SO(3,p).1),#TODO CLOSURE
    Eltseq(SO(3,p).2));
  #  form_mat:= ClassicalForms(newgrp)`bilinearForm;
  # =v= MULTIASSIGN =v=
  form_mat:=UnitaryForm(newgrp);
  isit:=form_mat.val1;
  form_mat:=form_mat.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,isit);
  Assert(1,IsZero(form_mat[1][1]));
  Assert(1,IsZero(form_mat[3][3]));
  Assert(1,IsZero(form_mat[1][2]));
  Assert(1,IsZero(form_mat[2][3]));
  Assert(1,not IsZero(form_mat[1][3]));
  form_elt:=form_mat[2][2]/form_mat[1][3];
  conj_elt:=Root(form_elt #CAST F
    ,p+1);
  conj_mat:=DiagonalMat([1,conj_elt,1]) #CAST gl
    ;
  return newgrp^conj_mat;
end;
;
#  ****************************************************
#  * The following function is used in the noncoprime   *
#  * case - we start by making 3 copies of a group,     *
#  * which are conjugate under the outer 3-cycle.       *
#  * a unique one of these will commute with our        *
#  * given involution, so in the case psl.2 we require  *
#  * this to be appended to the list of maximals        *
#  ****************************************************
SelectGroup@:=function(psu,initial,three_cyc,invol)
local group,i,looking;
  looking:=true;
  for i in [0..2] do
    group:=initial^(three_cyc^i);
    if IsConjugate(psu,group,group^invol) then
      looking:=false;
      break;
    fi;
  od;
  if looking then
    Info(InfoWarning,1,"Error normalising subgroup in PSL.2");
  fi;
  return group;
end;
;
#  ****************************************************
#  * First we do the case where 3 does not divide       *
#  * p+1, as this has much simpler behavour - Out = 2.  *
#  *                                                    *
#  *****************************************************
#  Forward declaration of MakeSU3HomomGeneral
CoprimeMaximals@:=function(group,p)
#  /out:
#  * 3 does not divide (p+1), so pgu = psu. Since all subgroups of
#  * PSU extend to PSigmaU there is no need for an outer involution.

local F,IsPSL,Print,apsu,dh,factor,g,group,homom,max,maximals,o,phi,psu,soc,su;
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
  su:=SU(3,p);
  psu:=PSU(3,p);
  apsu:=PGammaU(3,p);
  #   get generators to correspond!
  for g in Generators(apsu) do
    if not g in psu then
      apsu:=SubStructure(apsu,psu.1,#TODO CLOSURE
        psu.2,g);
      AssertAttribute(apsu,"Order",Size(psu)*2);
      break;
    fi;
  od;
  factor:=GroupHomomorphismByImages(su,apsu,
    GeneratorsOfGroup(su),[apsu.1,apsu.2]);
  o:=Order(group);
  IsPSL:=o=Size(psu);
  if Print > 1 then
    Print("Setting up homomorphism");
  fi;
  # =v= MULTIASSIGN =v=
  group:=MakeSU3HomomGeneral@(group,p,1,psu,apsu,factor:Print:=0);
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
  #  homom, F, phi := MakeHomom(dgroup, group, p, psu, apsu : Print:=Print);
  dh:=Domain(homom);
  apsu:=SubStructure(apsu,homom(dh.1),#TODO CLOSURE
    homom(dh.2),apsu.3);
  AssertAttribute(apsu,"Order",Size(psu)*2);
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=apsu,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  #  
  #  * Reducibles. We need the stabiliser of an isotropic and a
  #  * nonisotropic point. The istropic point is a point in the permutation
  #  * action of psu.
  
  if Print > 1 then
    Print("Getting reducibles");
  fi;
  #  isotropic
  Add(maximals,Stabiliser(psu,1));
  #  nonisotropic.
  Add(maximals,GetReducibles@(su,p)@factor);
  #  
  #  * The maximal imprimitive is unique, and extends. The function
  #  * returns a matrix group, so we factor by the centre before applying
  #  * homom.
  
  if Print > 1 then
    Print("Getting imprimitives");
  fi;
  Add(maximals,GetImprims@(p)@factor);
  #  
  #  * This needs doing.
  
  if Print > 1 then
    Print("Getting semilinears");
  fi;
  Add(maximals,GetSemilin@(p)@factor);
  #  
  #  * There is a subfield subgroup PSO(3, p), which extends
  
  if Print > 1 then
    Print("Getting classicals");
  fi;
  Add(maximals,GetSubfield@(p)@factor);
  #  
  #  * Finally, there is PSL(2, 7), which is a maximal C_9 group whenever
  #  * -7 is a nonsquare in GF(p). It extends.
  
  if p > 7 and not IsSquare((-7) #CAST GF(p)
    ) then
    if Print > 1 then
      Print("Getting PSL(2, 7)");
    fi;
    Add(maximals,GetPSL2_7@(p^2)@factor);
  fi;
  if Print > 1 then
    Print("Found maximals in standard copy");
  fi;
  return rec(val1:=homom,
    val2:=apsu,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end;
;
#  ***************************************************
#  * Now we do the case where 3 does divide p+1. This  *
#  * means that we get additional conjugacy classes    *
#  * of some groups, we get extraspecial groups, and   *
#  * we get alt_6 as a C_9 group whenever 5 is a       *
#  * square in GF(p) and psl2_7 whenever (-7) is a     *
#  * square in GF(p).                                  *
#  ****************************************************
NonCoprimeMaximals@:=function(group,p)
local 
   F,Print,apsu,dh,factor,g,gens,group,homom,initial,invol,max,maximals,o,
   orderpsu,phi,psu,soc,su,three_cyc,type;
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
  su:=SU(3,p);
  psu:=PSU(3,p);
  apsu:=PGammaU(3,p);
  #   get generators in desired order!
  gens:=[psu.1,psu.2];
  for g in Generators(apsu) do
    if g^3 in psu and not g in psu then
      Add(gens,g);
      break;
    fi;
  od;
  for g in Generators(apsu) do
    if g^2 in psu and not g in psu then
      Add(gens,g);
      break;
    fi;
  od;
  apsu:=SubStructure(apsu,gens);
  AssertAttribute(apsu,"Order",Size(psu)*6);
  factor:=GroupHomomorphismByImages(su,apsu,
    GeneratorsOfGroup(su),[apsu.1,apsu.2]);
  #  dgroup:= DerivedSubgroup(group);
  o:=Order(group);
  orderpsu:=Size(psu);
  if o=orderpsu then
    type:="psu";
  elif o=2*orderpsu then
    type:="psigmau";
  elif o=3*orderpsu then
    type:="pgu";
  elif o=6*orderpsu then
    type:="pgammau";
    #  dgroup:= DerivedSubgroup(dgroup);
  else
    Error("Function only accepts almost simple groups with socle PSU(3,p)");
  fi;
  if Print > 1 then
    Print("Group is type ",type);
  fi;
  #  Note - dgroup is actually the socle, not always the derived group!
  if Print > 1 then
    Print("Setting up homomorphism");
  fi;
  # =v= MULTIASSIGN =v=
  group:=MakeSU3HomomGeneral@(group,p,1,psu,apsu,factor:Print:=0);
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
  #  homom, F, phi := MakeHomom(dgroup, group, p, psu, apsu : Print:=Print);
  dh:=Domain(homom);
  if type="psu" or type="psigmau" then
    three_cyc:=apsu.3;
  else
    three_cyc:=homom(dh.3);
  fi;
  if type="psigmau" then
    invol:=homom(dh.3);
  elif type="pgammau" then
    invol:=homom(dh.4);
  else
    invol:=apsu.4;
  fi;
  apsu:=SubStructure(apsu,homom(dh.1),#TODO CLOSURE
    homom(dh.2),three_cyc,invol);
  AssertAttribute(apsu,"Order",Size(psu)*6);
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=apsu,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  #  
  #  * Reducibles. We need the stabiliser of an isotropic and a
  #  * nonisotropic point. The istropic point is a point in the permutation
  #  * action of psu. This could also be done with matrices, for
  #  * complexity analysis, as stabilising [1, 0, 0] would also do. In
  #  * practice however, this is faster.
  #  *
  #  * The reducibles extend in each case.
  
  if Print > 1 then
    Print("Getting reducibles");
  fi;
  #  isotropic
  Add(maximals,Stabiliser(psu,1));
  #  nonisotropic.
  Add(maximals,GetReducibles@(su,p)@factor);
  #  
  #  * The maximal imprimitive is unique, and extends in each case. The
  #  function
  #  * returns a matrix group, so we factor by the centre before applying
  #  * homom.
  
  if Print > 1 then
    Print("Getting imprimitives");
  fi;
  Add(maximals,GetImprims@(p)@factor);
  #  
  #  * This needs doing.
  
  if Print > 1 then
    Print("Getting semilinear");
  fi;
  Add(maximals,GetSemilin@(p)@factor);
  #  
  #  * There is a subfield subgroup PSO(3, p). In a similar fashion to the
  #  * PSL(3, p) code there are three copies of this, with Sym(3) acting
  #  * them. So for psu there are 3 intersections, for psigmau there is one,
  #  * and for pgu and pgammau there are none.
  
  if type="psu" then
    if Print > 1 then
      Info(InfoWarning,1,"Getting subfield");
    fi;
    initial:=GetSubfield@(p)@factor;
    Add(maximals,initial);
    Add(maximals,initial^three_cyc);
    Add(maximals,initial^(three_cyc^2));
  elif type="psigmau" then
    if Print > 1 then
      Info(InfoWarning,1,"Getting subfield");
    fi;
    initial:=(GetSubfield@(p)@factor);
    Add(maximals,SelectGroup@(psu,initial,three_cyc,invol));
  fi;
  #  
  #  * The final geometric subgroup is the extraspecials. If p^2 mod 9 is
  #  * not equal to 1 then there's a unique copy which extends all the way
  #  * up. If p^2 mod 9 = 1 then there's 3 copies with the Sym(3) thing
  #  * going on.
  
  if not (p^2 mod 9=1) then
    if Print > 1 then
      Print("Getting extraspecials");
    fi;
    Add(maximals,GetExtraspec@(p)@factor);
  elif type="psu" then
    if Print > 1 then
      Print("Getting extraspecials");
    fi;
    initial:=GetExtraspec@(p)@factor;
    Add(maximals,initial);
    Add(maximals,initial^three_cyc);
    Add(maximals,initial^(three_cyc^2));
  elif type="psigmau" then
    if Print > 1 then
      Print("Getting extraspecial");
    fi;
    initial:=GetExtraspec@(p)@factor;
    Add(maximals,SelectGroup@(psu,initial,three_cyc,invol));
  fi;
  #  
  #  * There is a C_9 subgroup isomorphic to 3.Alt(6). This exists and is
  #  * maximal whenever 5 is a square in GF(p) and p+1= 0 mod 3 (which is
  #  * always true in this function). As in the subfield case, there are
  #  * three copies in PSU, which Sym(3) acting on them. So for psu ther
  #  * are 3 intersections, for psigmau there is one, and for pgu and
  #  * pgammau there are none.
  
  if IsSquare(5 #CAST GF(p)
    ) and type="psu" then
    if Print > 1 then
      Print("Getting alt6");
    fi;
    initial:=GetAlt6@(p)@factor;
    Add(maximals,initial);
    Add(maximals,initial^three_cyc);
    Add(maximals,initial^(three_cyc^2));
  elif IsSquare(5 #CAST GF(p)
    ) and type="psigmau" then
    if Print > 1 then
      Print("Getting alt6");
    fi;
    initial:=GetAlt6@(p)@factor;
    Add(maximals,SelectGroup@(psu,initial,three_cyc,invol));
  fi;
  #  
  #  * Finally, there is PSL(2, 7), which is a maximal C_9 group whenever
  #  * -7 is a nonsquare in GF(p). Once again we have the Sym(3)
  #  * pattern as for O(3, p) and 3.Alt(6).
  
  if p > 7 and not IsSquare((-7) #CAST GF(p)
    ) and type="psu" then
    if Print > 1 then
      Print("Getting PSL(2, 7)");
    fi;
    initial:=GetPSL2_7@(p^2)@factor;
    Add(maximals,initial);
    Add(maximals,initial^three_cyc);
    Add(maximals,initial^(three_cyc^2));
  elif p > 7 and not IsSquare((-7) #CAST GF(p)
    ) and type="psigmau" then
    if Print > 1 then
      Print("Getting PSL(2, 7)");
    fi;
    initial:=(GetPSL2_7@(p^2)@factor);
    Add(maximals,SelectGroup@(psu,initial,three_cyc,invol));
  fi;
  if Print > 1 then
    Print("Found maximals in standard copy");
  fi;
  return rec(val1:=homom,
    val2:=apsu,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end;
;
#  ****************************************************
#  * This function ties all the rest together.          *
#  * The results have been compared with the ATLAS      *
#  * for p eq 7 and 11                                  *
#  *                                                    *
#  * NOTE: the input value is the prime p NOT p^2       *
#  *****************************************************
InstallGlobalFunction(U3pIdentify@,
function(group,p)
local Print,max;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  Assert(1,p > 5 and IsPrimeInt(p));
  if ((p+1) mod 3)=0 then
    if Print > 1 then
      Info(InfoWarning,1,"non coprime case");
    fi;
    return NonCoprimeMaximals@(group,p:max:=max,Print:=Print);
  else
    if Print > 1 then
      Info(InfoWarning,1,"coprime case");
    fi;
    return CoprimeMaximals@(group,p:max:=max,Print:=Print);
  fi;
end);

InstallGlobalFunction(MakeSU3HomomGeneral@,
function(group,p,e,psu,apsu,factor)
local 
   CG,GtoSU,Print,SUtoG,ce,d,g,group,h,homom,i,imgens,ims,isc,j,mat,newgens,
   psugens,soc,socle,subgp,subsoc,works;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  soc:=Socle(group);
  #   Reduce number of generators of soc, and
  #  * rearrange generators of group to get those of soc coming first
  
  d:=3;
  repeat
    newgens:=[Random(soc),Random(soc)];
    subsoc:=SubStructure(soc,newgens);
    RandomSchreier(subsoc);
    
  until subsoc=soc;
  #  
  #  while subsoc ne soc do
  #  x:=Random(soc);
  #  while x in subsoc do x:=Random(soc); end while;
  #  Append(~newgens,x); subsoc := sub<soc|newgens>; RandomSchreier(subsoc);
  #  end while;
  
  soc:=subsoc;
  subgp:=subsoc;
  for g in Generators(group) do
    if not g in subgp then
      Add(newgens,g);
      subgp:=SubStructure(group,newgens);
      RandomSchreier(subgp);
    fi;
  od;
  group:=subgp;
  works:=false;
  while not works do
    # =v= MULTIASSIGN =v=
    GtoSU:=RecogniseSU3(soc,p^e);
    works:=GtoSU.val1;
    GtoSU:=GtoSU.val2;
    # =^= MULTIASSIGN =^=
  od;
  psugens:=[];
  for i in [1..Ngens(soc)] do
    mat:=GtoSU(soc.i);
    Add(psugens,mat@factor);
  od;
  #  Now identify images of all generators of group in apsu.
  ims:=psugens;
  for i in [Ngens(soc)+1..Ngens(group)] do
    g:=group.i;
    CG:=apsu;
    ce:=One(apsu);
    for j in [1..Size(psugens)] do
      mat:=GtoSU(soc.j^g);
      # =v= MULTIASSIGN =v=
      h:=IsConjugate(CG,psugens[j]^ce,mat@factor);
      isc:=h.val1;
      h:=h.val2;
      # =^= MULTIASSIGN =^=
      if not isc then
        Error("Conjugation error in Aut(PSU(d,q))");
      fi;
      CG:=Centraliser(CG,mat@factor);
      ce:=ce*h;
    od;
    Add(ims,ce);
  od;
  return rec(val1:=GroupHomomorphismByImages(group,apsu,
    GeneratorsOfGroup(group),ims),
    val2:=soc,
    val3:=group);
end);


