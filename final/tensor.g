
#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.39, 1/28/16 by AH

#  Global Variables used: Append, CorrectForm, Determinant, DiagonalMatrix,
#  Factorisation, GF, GL, GO, GOMinus, GOPlus, GU, Gcd, Generators, GetAandB,
#  Id, Integers, IsEven, IsOdd, IsSquare, KroneckerProduct, Matrix, Ngens,
#  Nullspace, Omega, OmegaMinus, OmegaPlus, OrthogonalForm, PrimitiveElement,
#  SL, SO, SOMinus, SOPlus, SU, ScalarMatrix, Sp, SymplecticForm,
#  TransformForm

#  Defines: GetAandB, OrthSpTensor, OrthTensorEvenEven, OrthTensorEvenOdd,
#  OrthTensorOddOdd, SLTensor, SUTensor, SpTensors

DeclareGlobalFunction("OrthSpTensor@");

DeclareGlobalFunction("OrthTensorEvenEven@");

DeclareGlobalFunction("OrthTensorEvenOdd@");

DeclareGlobalFunction("OrthTensorOddOdd@");

DeclareGlobalFunction("SLTensor@");

DeclareGlobalFunction("SUTensor@");

DeclareGlobalFunction("SpTensors@");

InstallGlobalFunction(SLTensor@,
function(d1,d2,q)
local N,c,d,ext,g1,g2,general,i,i1,i2,k,k1,k2,mat,n,newgens,scal,z;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  Assert(1,IsPrimePowerInt(q));
  Assert(1,d2 >= d1);
  #  contained in C7 if d2=d1
  #  if d1 eq 2 then assert q gt 2; end if; why?
  k1:=Gcd(d1,q-1);
  k2:=Gcd(d2,q-1);
  c:=Gcd(k1,k2);
  d:=d1*d2;
  k:=Gcd(d,q-1);
  z:=PrimitiveElement(GF(q));
  scal:=z^(QuoInt((q-1),k))*IdentityMat(d,GF(q));
  i1:=One(SL(d1,q));
  i2:=One(SL(d2,q));
  if general then
    newgens:=[];
  else
    newgens:=[scal];
  fi;
  if general then
    for i in [1,2] do
      Add(newgens,KroneckerProduct(GL(d1,q).i,i2));
      Add(newgens,KroneckerProduct(i1,GL(d2,q).i));
    od;
  else
    for i in [1,2] do
      Add(newgens,KroneckerProduct(SL(d1,q).i,i2));
      Add(newgens,KroneckerProduct(i1,SL(d2,q).i));
    od;
  fi;
  ext:=QuoInt(k1*k2*c,k);
  if general or ext=1 then
    return SubgroupContaining(GL(d,q),newgens);
  fi;
  Assert(1,q > 2);
  g1:=GL(d1,q).1;
  g2:=GL(d2,q).1;
  Assert(1,DeterminantMat(g1)=DeterminantMat(g2));
  Assert(1,DeterminantMat(g1)=z);
  mat:=MatrixByEntries(Integers,3,1,[d2,d1,q-1]);
  N:=NullspaceMat(mat);
  for n in N do
    Add(newgens,KroneckerProduct(g1^n[1],g2^n[2]));
  od;
  return SubgroupContaining(SL(d,q),newgens);
  
end);

#  ******************************************************************

InstallGlobalFunction(SpTensors@,
function(d1,d2,q)
local a,b,d,deltaminus,deltaplus,deltasp,form,form_minus,gominus,i,i1,i2,isit,
   mat_minus,newgens,newgensm,newgensp,normaliser,trans,type,x,z;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,IsEvenInt(d1));
  #  assert d2 gt 2;
  #  if d2 eq 3 then assert not q eq 3; end if; //nonmaximal;
  Assert(1,IsOddInt(q));
  #   q even causes crashes
  Assert(1,IsPrimePowerInt(q));
  d:=d1*d2;
  i1:=SL(d1,q).0;
  i2:=SL(d2,q).0;
  if IsOddInt(d2) then
    newgens:=[];
    for i in [1..GeneratorsOfGroup(SO(d2,q))] do
      Add(newgens,KroneckerProduct(i1,i));
    od;
    for i in [1,2] do
      Add(newgens,KroneckerProduct(Sp(d1,q).i,i2));
    od;
    # =v= MULTIASSIGN =v=
    form:=SymplecticForm@(SubgroupContaining(SL(d,q),newgens));
    isit:=form.val1;
    form:=form.val2;
    # =^= MULTIASSIGN =^=
    Assert(1,isit);
    if normaliser then
      Add(newgens,KroneckerProduct(NormSpMinusSp@(d1,q),i2));
    fi;
    trans:=CorrectForm@(form,d,q,"symplectic");
    return rec(val1:=SubgroupContaining(GL(d,q),List(newgens,g->trans^-1*g*trans))
     ,
      val2:=fail);
  fi;
  #  form_minus:= SymmetricBilinearForm(GOMinus(d2, q));
  # =v= MULTIASSIGN =v=
  form_minus:=OrthogonalForm@(GOMinus(d2,q));
  isit:=form_minus.val1;
  type:=form_minus.val2;
  form_minus:=form_minus.val3;
  # =^= MULTIASSIGN =^=
  Assert(1,isit and type="orth-");
  #  this will conjugate the group so that it is in the form
  #  assumed by Kleidman and Liebeck.
  mat_minus:=CorrectForm@(form_minus,d2,q,"orth-");
  gominus:=GOMinus(d2,q)^mat_minus;
  newgensp:=[];
  newgensm:=[];
  for i in [1..GeneratorsOfGroup(GOPlus(d2,q))] do
    Add(newgensp,KroneckerProduct(i1,i));
  od;
  for i in [1..GeneratorsOfGroup(gominus)] do
    Add(newgensm,KroneckerProduct(i1,i));
  od;
  for i in GeneratorsOfGroup(Sp(d1,q){[1,2]}) do
    x:=KroneckerProduct(i,i2);
    Add(newgensp,x);
    Add(newgensm,x);
  od;
  z:=PrimitiveElement(GF(q));
  deltasp:=DiagonalMat(Concatenation(List([1..(QuoInt(d1,2))],i->z)
   ,List([1..(QuoInt(d1,2))],i->z^0)));
  deltaplus:=DiagonalMat(Concatenation(List([1..(QuoInt(d2,2))],i->z)
   ,List([1..(QuoInt(d2,2))],i->z^0)));
  # =v= MULTIASSIGN =v=
  b:=GetAandB@(q);
  a:=b.val1;
  b:=b.val2;
  # =^= MULTIASSIGN =^=
  if IsEvenInt(QuoInt((q-1)*d2,4)) then
    deltaminus:=MatrixByEntries(GF(q)
     ,d2,d2,Concatenation(List([0..((QuoInt(d2,2))-2)]
     ,i->[[2*i+1,2*i+1,a],[2*i+1,2*i+2,b],[2*i+2,2*i+1,b],[2*i+2,2*i+2,-a]])
     ,[[d2-1,d2,1],[d2,d2-1,z]]));
  else
    deltaminus:=MatrixByEntries(GF(q)
     ,d2,d2,Concatenation(List([0..((QuoInt(d2,2))-1)],i->[[2*i+1,2*i+1,a]
     ,[2*i+1,2*i+2,b],[2*i+2,2*i+1,b],[2*i+2,2*i+2,-a]])));
  fi;
  Add(newgensp,KroneckerProduct(deltasp,deltaplus^-1));
  Add(newgensm,KroneckerProduct(deltasp,deltaminus^-1));
  # =v= MULTIASSIGN =v=
  form:=SymplecticForm@(SubgroupContaining(GL(d,q),newgensp));
  isit:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,isit);
  trans:=CorrectForm@(form,d,q,"symplectic");
  if normaliser then
    Add(newgensp,KroneckerProduct(NormSpMinusSp@(d1,q),i2));
  fi;
  newgensp:=List(newgensp,g->trans^-1*g*trans);
  # =v= MULTIASSIGN =v=
  form:=SymplecticForm@(SubgroupContaining(GL(d,q),newgensm));
  isit:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,isit);
  trans:=CorrectForm@(form,d,q,"symplectic");
  if normaliser then
    Add(newgensm,KroneckerProduct(NormSpMinusSp@(d1,q),i2));
  fi;
  newgensm:=List(newgensm,g->trans^-1*g*trans);
  return rec(val1:=SubgroupContaining(GL(d,q),newgensp),
    val2:=SubgroupContaining(GL(d,q),newgensm));
  #  c=1
  
end);

InstallGlobalFunction(SUTensor@,
function(d1,d2,q)
local 
   N,c,d,ext,form,form1,form2,g1,g2,general,i,i1,i2,k,k1,k2,mat,n,newgens,
   normaliser,scal,trans,trans1,trans2,z;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,IsPrimePowerInt(q));
  Assert(1,d2 >= d1);
  #  contained in C7 if d2=d1
  if normaliser then
    general:=true;
  fi;
  k1:=Gcd(d1,q+1);
  k2:=Gcd(d2,q+1);
  c:=Gcd(k1,k2);
  d:=d1*d2;
  k:=Gcd(d,q+1);
  z:=PrimitiveElement(GF(q^2));
  if normaliser then
    scal:=z*IdentityMat(d,GF(q));
  else
    scal:=z^(QuoInt((q^2-1),k))*IdentityMat(d,GF(q));
  fi;
  i1:=One(SU(d1,q));
  i2:=One(SU(d2,q));
  #  scal preservesform I_d, but we want it to preserve antidiagonal
  form:=MatrixByEntries(GF(q^2),d,d,List([1..d],i->[i,d-i+1,1]));
  trans:=CorrectForm@(form,d,q^2,"unitary");
  if normaliser then
    newgens:=[scal];
  elif general then
    newgens:=[];
  else
    newgens:=[scal];
  fi;
  if general then
    for i in [1,2] do
      Add(newgens,KroneckerProduct(GU(d1,q).i,i2));
      Add(newgens,KroneckerProduct(i1,GU(d2,q).i));
    od;
  else
    for i in [1,2] do
      Add(newgens,KroneckerProduct(SU(d1,q).i,i2));
      Add(newgens,KroneckerProduct(i1,SU(d2,q).i));
    od;
  fi;
  ext:=QuoInt(k1*k2*c,k);
  if ext=1 or general then
    return SubgroupContaining(GL(d,q^2),newgens);
  fi;
  form1:=MatrixByEntries(GF(q^2),d1,d1,List([1..d1],i->[i,d1-i+1,1]));
  trans1:=CorrectForm@(form1,d1,q^2,"unitary");
  form2:=MatrixByEntries(GF(q^2),d2,d2,List([1..d2],i->[i,d2-i+1,1]));
  trans2:=CorrectForm@(form2,d2,q^2,"unitary");
  g1:=DiagonalMat(GF(q^2),Concatenation([z^(q-1)],List([1..d1-1],i->z^0)));
  g2:=DiagonalMat(GF(q^2),Concatenation([z^(q-1)],List([1..d2-1],i->z^0)));
  g1:=trans1*g1*trans1^-1;
  g2:=trans2*g2*trans2^-1;
  mat:=MatrixByEntries(Integers,3,1,[d2,d1,q+1]);
  N:=NullspaceMat(mat);
  for n in N do
    Add(newgens,KroneckerProduct(g1^n[1],g2^n[2]));
  od;
  return SubgroupContaining(SL(d,q^2),newgens);
  
end);

InstallGlobalFunction(OrthSpTensor@,
function(d1,d2,q)
local d,g1,g2,general,gp,grp,i,i1,i2,newgens,normaliser,special,tmat;
  special:=ValueOption("special");
  if special=fail then
    special:=false;
  fi;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,IsPrimePowerInt(q));
  Assert(1,IsEvenInt(d1) and IsEvenInt(d2));
  Assert(1,d2 >= d1);
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  d:=d1*d2;
  i1:=One(SL(d1,q));
  i2:=One(SL(d2,q));
  newgens:=[];
  for i in [1..GeneratorsOfGroup(Sp(d1,q))] do
    Add(newgens,KroneckerProduct(i,i2));
  od;
  for i in [1..GeneratorsOfGroup(Sp(d2,q))] do
    Add(newgens,KroneckerProduct(i1,i));
  od;
  if special or (IsOddInt(q) and d mod 8=0) then
    g1:=NormSpMinusSp@(d1,q);
    g2:=NormSpMinusSp@(d2,q);
    gp:=KroneckerProduct(g1,g2^-1);
    if general or (special and DeterminantMat(gp)=1) or (IsOddInt(q) and d 
       mod 8=0) then
      Add(newgens,KroneckerProduct(g1,g2^-1));
    fi;
  fi;
  grp:=SubgroupContaining(GL(d,q),newgens);
  tmat:=TransformForm@(grp);
  if normaliser then
    if IsOddInt(q) then
      Add(newgens,KroneckerProduct(g1,One(Sp(d2,q))));
    elif q > 2 then
      Add(newgens,PrimitiveElement(GF(q))*IdentityMat(d,GF(q)));
    fi;
    grp:=SubgroupContaining(GL(d,q),newgens);
  fi;
  return grp^tmat;
  #  if q odd and 8|d, c=4, go,so; o.w. c=2, so (q even), go-so (q odd)
  
end);

InstallGlobalFunction(OrthTensorOddOdd@,
function(d1,d2,q)
local 
   d,elt,fac1,fac2,general,grp,gso1,gso2,i,i1,i2,newgens,normaliser,special,
   tmat;
  special:=ValueOption("special");
  if special=fail then
    special:=false;
  fi;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  #  type O(d1,q) tensor O(d2,q), d1,d2 odd
  Assert(1,IsPrimePowerInt(q));
  Assert(1,IsOddInt(q));
  Assert(1,IsOddInt(d1) and IsOddInt(d2));
  Assert(1,d2 >= d1);
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  d:=d1*d2;
  i1:=One(SL(d1,q));
  i2:=One(SL(d2,q));
  newgens:=[];
  #fac1:=SELECT(general then GO(d1,q) else SELECT(special then SO(d1,q) else 
  # Omega(d1,q)));
  if general then
    fac1:=GO(d1,q);
  elif special then
    fac1:=SO(d1,q);
  else
    fac1:=Omega(d1,q);
  fi;
  #fac2:=SELECT(general then GO(d2,q) else SELECT(special then SO(d2,q) else 
  # Omega(d2,q)));
  if general then
    fac2:=GO(d2,q);
  elif special then
    fac2:=SO(d2,q);
  else
    fac2:=Omega(d2,q);
  fi;
  for i in [1..GeneratorsOfGroup(fac1)] do
    Add(newgens,KroneckerProduct(i,i2));
  od;
  for i in [1..GeneratorsOfGroup(fac2)] do
    Add(newgens,KroneckerProduct(i1,i));
  od;
  grp:=SubgroupContaining(GL(d,q),newgens);
  tmat:=TransformForm@(grp);
  newgens:=List(newgens,g->g^tmat);
  if not special then
    #  need 2 on top
    gso1:=SOMinusOmega@(d1,q,0);
    gso2:=SOMinusOmega@(d2,q,0);
    elt:=(KroneckerProduct(gso1,gso2))^tmat;
    Assert(1,InOmega@(elt,d,q,0));
    Add(newgens,elt);
  fi;
  if normaliser and q > 3 then
    Add(newgens,PrimitiveElement(GF(q))*IdentityMat(d,GF(q)));
  fi;
  return SubgroupContaining(GL(d,q),newgens);
  #  c=1.
  
end);

InstallGlobalFunction(OrthTensorEvenOdd@,
function(d1,d2,q,sign1)
local d,g1,general,grp,grp1,grp2,i,i1,i2,newgens,normaliser,special,tmat;
  special:=ValueOption("special");
  if special=fail then
    special:=false;
  fi;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  #  type O(d1,q) tensor O(d2,q), d1 even, d2 odd
  Assert(1,IsPrimePowerInt(q));
  Assert(1,IsOddInt(q));
  Assert(1,IsEvenInt(d1) and IsOddInt(d2));
  Assert(1,sign1 in Set([-1,1]));
  if sign1=1 and d1=2 then
    Error("Illegal parameters - Omega(2,q) is reducible");
  fi;
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  d:=d1*d2;
  i1:=One(SL(d1,q));
  i2:=One(SL(d2,q));
  newgens:=[];
  if general then
    #grp1:=SELECT(sign1=1 then GOPlus(d1,q) else GOMinus(d1,q));
    if sign1=1 then
      grp1:=GOPlus(d1,q);
    else
      grp1:=GOMinus(d1,q);
    fi;
  elif special then
    #grp1:=SELECT(sign1=1 then SOPlus(d1,q) else SOMinus(d1,q));
    if sign1=1 then
      grp1:=SOPlus(d1,q);
    else
      grp1:=SOMinus(d1,q);
    fi;
  else
    #grp1:=SELECT(sign1=1 then OmegaPlus(d1,q) else OmegaMinus(d1,q));
    if sign1=1 then
      grp1:=OmegaPlus(d1,q);
    else
      grp1:=OmegaMinus(d1,q);
    fi;
  fi;
  grp2:=SO(d2,q);
  for i in [1..GeneratorsOfGroup(grp1)] do
    Add(newgens,KroneckerProduct(i,i2));
  od;
  for i in [1..GeneratorsOfGroup(grp2)] do
    Add(newgens,KroneckerProduct(i1,i));
  od;
  grp:=SubgroupContaining(GL(d,q),newgens);
  tmat:=TransformForm@(grp);
  if normaliser then
    if IsOddInt(q) then
      g1:=NormGOMinusGO@(d1,q,sign1);
      Add(newgens,KroneckerProduct(g1,i2));
    elif q > 2 then
      Add(newgens,PrimitiveElement(GF(q))*IdentityMat(d,GF(q)));
    fi;
    grp:=SubgroupContaining(GL(d,q),newgens);
  fi;
  return grp^tmat;
  #  c=1.
  
end);

InstallGlobalFunction(OrthTensorEvenEven@,
function(d1,d2,q,sign1,sign2)
local 
   D1,D2,d,diag,gd1,gd2,general,ggl1,ggl2,grp,grp1,grp2,i,i1,i2,int1,int2,
   newgens,normaliser,special,t1,t2,tmat;
  special:=ValueOption("special");
  if special=fail then
    special:=false;
  fi;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  #  type O(d1,q) tensor O(d2,q), d1 d2 even - the most complicated case
  #  note result is always O^+
  Assert(1,IsPrimePowerInt(q));
  Assert(1,IsOddInt(q));
  Assert(1,IsEvenInt(d1) and IsEvenInt(d2));
  Assert(1,sign1 in Set([-1,1]) and sign2 in Set([-1,1]));
  Assert(1,sign1<>sign2 or d1 <= d2);
  Assert(1,sign1=1 or sign2=-1);
  #  use (+,-), not (-,+)
  if sign1=1 and d1=2 then
    Error("Illegal parameters - Omega(2,q) is reducible");
  fi;
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  d:=d1*d2;
  i1:=One(SL(d1,q));
  i2:=One(SL(d2,q));
  newgens:=[];
  if special then
    #grp1:=SELECT(sign1=1 then GOPlus(d1,q) else GOMinus(d1,q));
    if sign1=1 then
      grp1:=GOPlus(d1,q);
    else
      grp1:=GOMinus(d1,q);
    fi;
    #grp2:=SELECT(sign2=1 then GOPlus(d2,q) else GOMinus(d2,q));
    if sign2=1 then
      grp2:=GOPlus(d2,q);
    else
      grp2:=GOMinus(d2,q);
    fi;
  else
    #grp1:=SELECT(sign1=1 then SOPlus(d1,q) else SOMinus(d1,q));
    if sign1=1 then
      grp1:=SOPlus(d1,q);
    else
      grp1:=SOMinus(d1,q);
    fi;
    #grp2:=SELECT(sign2=1 then SOPlus(d2,q) else SOMinus(d2,q));
    if sign2=1 then
      grp2:=SOPlus(d2,q);
    else
      grp2:=SOMinus(d2,q);
    fi;
  fi;
  for i in [1..GeneratorsOfGroup(grp1)] do
    Add(newgens,KroneckerProduct(i,i2));
  od;
  for i in [1..GeneratorsOfGroup(grp2)] do
    Add(newgens,KroneckerProduct(i1,i));
  od;
  grp:=SubgroupContaining(GL(d,q),newgens);
  tmat:=TransformForm@(grp);
  newgens:=List(newgens,g->g^tmat);
  #  now difficult bit - stuff on top!
  ggl1:=GOMinusSO@(d1,q,sign1);
  gd1:=NormGOMinusGO@(d1,q,sign1);
  ggl2:=GOMinusSO@(d2,q,sign2);
  gd2:=NormGOMinusGO@(d2,q,sign2);
  t1:=(KroneckerProduct(ggl1,i2))^tmat;
  t2:=(KroneckerProduct(i1,ggl2))^tmat;
  diag:=(KroneckerProduct(gd1,gd2^-1))^tmat;
  if special then
    Add(newgens,diag);
  else
    #  for checking purposes, use KL's D function.
    if d1 mod 4=2 and q mod 4=3 then 
      D1:=-sign1;
    else 
      D1:=sign1;
    fi;
    if d2 mod 4=2 and q mod 4=3 then 
      D2:=-sign2;
    else 
      D2:=sign2;
    fi;
    if InOmega@(t1,d,q,1) then
      int1:=true;
      Add(newgens,t1);
    else
      int1:=false;
    fi;
    Assert(1,int1=(D2=1));
    if InOmega@(t2,d,q,1) then
      int2:=true;
      Add(newgens,t2);
    else
      int2:=false;
    fi;
    Assert(1,int2=(D1=1));
    if not int1 and not int2 then
      Assert(1,InOmega@(t1*t2,d,q,1));
      Add(newgens,t1*t2);
    fi;
    Assert(1,InOmega@(diag,d,q,1)=(d mod 8=0));
    if d mod 8=0 then
      Add(newgens,diag);
    elif not int1 then
      Assert(1,InOmega@(t1*diag,d,q,1));
      Add(newgens,t1*diag);
    elif not int2 then
      Assert(1,InOmega@(t2*diag,d,q,1));
      Add(newgens,t2*diag);
    fi;
  fi;
  if normaliser then
    Add(newgens,(KroneckerProduct(gd1,i2))^tmat);
  fi;
  return SubgroupContaining(GL(d,q),newgens);
  #  sign1=sign2=1: (q odd) d1 or d2 = 2 mod 4 and q = 3 mod 4, c=2, go.
  #                  d = 4 (mod 8), c=2, go; o.w. c=4, go,so
  #  sign1=sign2=-1: (q odd) c=2, go.
  #  sign1=1,sign2=-1: (q odd) 4|d1, d2 = 2 mod 4, q mod 4 = 3 c=4, so,go;
  #                             o.w. c=2, go.
  
end);

