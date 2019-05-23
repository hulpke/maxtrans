
#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.39, 1/28/16 by AH

#  Global Variables used: Append, CorrectForm, Determinant, DiagonalMatrix,
#  GF, GL, GO, GU, Gcd, Generators, IsEven, IsOdd, KroneckerProduct, Ngens,
#  Omega, PrimitiveElement, SL, SO, SOMinus, SOPlus, SU, ScalarMatrix, Sp,
#  Sym, SymplecticForm, TensorWreathProduct, TransformForm, UnitaryForm

#  Defines: OrthogSpTensorInd, OrthogTensorInd, SLTensorInd, SUTensorInd,
#  SpTensorInd

DeclareGlobalFunction("OrthogSpTensorInd@");

DeclareGlobalFunction("OrthogTensorInd@");

DeclareGlobalFunction("SLTensorInd@");

DeclareGlobalFunction("SUTensorInd@");

DeclareGlobalFunction("SpTensorInd@");

InstallGlobalFunction(SpTensorInd@,
function(m,t,q)
local bool,diag,f,grp,i,invol,main,mat,normaliser;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,IsEvenInt(m) and t > 1);
  Assert(1,IsOddInt(t*q));
  #   KL - q or t even orthogonal form
  #  assert not (<m, q> eq <2, 3>); KL
  main:=TensorWreathProduct(Sp(m,q),SymmetricGroup(t));
  #  z:= PrimitiveElement(GF(q));
  #  diag:= GL(m, q)!DiagonalMatrix([z: i in [1..m div 2]] cat [1 : i in
  #  [1..m div 2]]);
  diag:=NormSpMinusSp@(m,q);
  if normaliser then
    invol:=diag;
    for i in [2..t] do
      invol:=KroneckerProduct(invol,One(GL(m,q)));
    od;
  else
    invol:=KroneckerProduct(diag,diag^-1);
    for i in [3..t] do
      invol:=KroneckerProduct(invol,One(GL(m,q)));
    od;
  fi;
  grp:=SubgroupContaining(GL(m^t,q),main,invol);
  # =v= MULTIASSIGN =v=
  f:=SymplecticForm@(main);
  bool:=f.val1;
  f:=f.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,bool);
  mat:=CorrectForm@(f,m^t,q,"symplectic");
  return grp^(mat^-1);
end);

#  *******************************************************************
InstallGlobalFunction(SLTensorInd@,
function(m,t,q)
local d,d42,diag,diag4,exponent,general,gens,i,main,new_diag,out,s,x,z,power;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  #  assert m gt 2; KL - otherwise orthogonal
  Assert(1,t > 1);
  if general then
    return TensorWreathProduct(GL(m,q),SymmetricGroup(t));
  fi;
  d:=m^t;
  z:=PrimitiveElement(GF(q));
  diag:=DiagonalMat(Concatenation([z],List([1..m-1],i->z^0)));
  if (m=2) and (t=2) and (q mod 4=1) then
    #  kludge, but not maximal for m=2 anyway
    return Intersection(TensorWreathProduct(GL(m,q),SymmetricGroup(t))
     ,SL(4,q));
  fi;
  if ((t=2) and (m mod 4=2) and (q mod 4=3)) then
    gens:=Concatenation(List([1,2],i->KroneckerProduct(SL(m,q).i,One(SL(m,q))))
     ,List([1,2],i->KroneckerProduct(One(SL(m,q)),SL(m,q).i)));
  else
    main:=TensorWreathProduct(SL(m,q),SymmetricGroup(t));
    gens:=[];
    for x in GeneratorsOfGroup(main) do
      if DeterminantMat(x)=1 then
        Add(gens,x);
      else
        #  det = -1 for odd permutation
        if IsOddInt(m) then
	  Add(gens,x*-1*IdentityMat(d,GF(q)));
        else
          Assert(1,t=2 and m mod 4=2 and q mod 4=1);
          diag4:=diag^(QuoInt((q-1),4));
          #  has fourth root of 1
          d42:=KroneckerProduct(diag4,One(SL(m,q)));
          Add(gens,(x*d42));
        fi;
      fi;
    od;
  fi;
  out:=KroneckerProduct(diag,diag^-1);
  for i in [3..t] do
    out:=KroneckerProduct(out,One(GL(m,q)));
  od;
  exponent:=QuoInt(Gcd(q-1,d),Gcd(q-1,m^(t-1)));
  new_diag:=diag^exponent;
  for i in [2..t] do
    new_diag:=KroneckerProduct(new_diag,One(GL(m,q)));
  od;
  Assert(1,DeterminantMat(new_diag)=z^(exponent*m^(t-1)));
  power:=ForAny([1..q-1],e->z^(d*e)=z^(exponent*m^(t-1)));
  Assert(1,power<>fail);
  #  exists because
  #  exp*m^(t-1) is divisible by
  #  (q-1, d), can divide through
  #  by (q-1, d) then compute
  #  (d/(q-1, d))^-1 mod (q-1)/(q-1,d)
  s:=z^power*IdentityMat(d,GF(q));
  return SubgroupContaining(SL(d,q),gens, out,new_diag/s);
end);

#  ****************************************************************
InstallGlobalFunction(SUTensorInd@,
function(m,t,q)
local 
   bool,d,d42,diag,diag4,exponent,f,f2,general,gens,grp,i,main,mat1,mat2,
   new_diag,normaliser,out,s,x,z,power;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,t > 1);
  #  assert m gt 2; KL - C5?
  #  assert not IsSoluble(SU(m,q)); KL that would be too expensive!
  #  SU(m,q) is soluble only for (m,q)=(2,2), (2,3), (3,2)
  if normaliser then
    general:=true;
  fi;
  z:=PrimitiveElement(GF(q^2));
  d:=m^t;
  if general then
    if normaliser then
      return SubgroupContaining(GL(d,q^2),TensorWreathProduct(GU(m,q)
      ,SymmetricGroup(t)),z*IdentityMat(d,GF(q)));
    fi;
    return TensorWreathProduct(GU(m,q),SymmetricGroup(t));
  fi;
  if (m=2) and (t=2) and (q mod 4=3) then
    #  kludge, but not maximal for k=2 anyway
    return Intersection(TensorWreathProduct(GU(m,q),SymmetricGroup(t))
     ,SU(4,q));
  fi;
  diag:=DiagonalMat(Concatenation([z],List([1..m-2],i->z^0),[z^(-q)]));
  if ((t=2) and (m mod 4=2) and (q mod 4=1)) then
    gens:=Concatenation(List([1,2],i->KroneckerProduct(SU(m,q).i,One(SU(m,q))))
     ,List([1,2],i->KroneckerProduct(One(SU(m,q)),SU(m,q).i)));
  else
    main:=TensorWreathProduct(SU(m,q),SymmetricGroup(t));
    gens:=[];
    for x in GeneratorsOfGroup(main) do
      if DeterminantMat(x)=1 then
        Add(gens,x);
      else
        #  det = -1
        if IsOddInt(m) then
	  Add(gens,x*-1*IdentityMat(d,GF(q)));
        else
          Assert(1,t=2 and m mod 4=2 and q mod 4=3);
          diag4:=diag^(QuoInt((q+1),4));
          #  has fourth root of 1
          d42:=KroneckerProduct(diag4,SU(m,q).0);
          Add(gens,x*d42);
        fi;
      fi;
    od;
  fi;
  out:=KroneckerProduct(diag,diag^-1);
  for i in [3..t] do
    out:=KroneckerProduct(out,One(GL(m,q^2)));
  od;
  exponent:=QuoInt(Gcd(q+1,d),Gcd(q+1,m^(t-1)));
  new_diag:=diag^exponent;
  for i in [2..t] do
    new_diag:=KroneckerProduct(new_diag,One(GL(m,q^2)));
  od;
  Assert(1,DeterminantMat(new_diag)=z^((1-q)*exponent*m^(t-1)));
  power:=ForAny([1..q^2-1],e->z^(d*e*(q-1))=z^((1-q)*exponent*m^(t-1)));
  Assert(1,power<>fail);
  #  exists because
  #  exp*m^(t-1) is divisible by
  #  (q-1)(q+1, d), can divide through
  #  by (q-1)(q+1, d) then compute
  #  (d/(q+1, d))^-1 mod (q+1)/(q+1,d)
  s:=z^(power*(q-1))*IdentityMat(d,GF(q));
  grp:=SubgroupContaining(SL(d,q^2),gens,out,new_diag*(s^-1));
  # =v= MULTIASSIGN =v=
  f:=UnitaryForm@(grp);
  bool:=f.val1;
  f:=f.val2;
  # =^= MULTIASSIGN =^=
  #  f;
  if not bool then
    Error("ERROR: group not unitary");
  fi;
  # =v= MULTIASSIGN =v=
  f2:=UnitaryForm@(SU(d,q));
  bool:=f2.val1;
  f2:=f2.val2;
  # =^= MULTIASSIGN =^=
  if f=f2 then
    return grp;
  fi;
  mat1:=CorrectForm@(f,d,q^2,"unitary");
  mat2:=CorrectForm@(f2,d,q^2,"unitary");
  return grp^(mat1*mat2^-1);
end);

InstallGlobalFunction(OrthogSpTensorInd@,
function(m,t,q)
local diag,ex,general,gens,i,invol,ng,normaliser,odd,special,tmat,twp;
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
  #  Sp(m,q) wr Sym(t)
  Assert(1,IsEvenInt(m) and t > 1);
  Assert(1,IsEvenInt(t*q));
  #  assert not (<m, q> eq <2, 3>); KL
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  ex:=t=2 and m mod 4=2;
  twp:=TensorWreathProduct(Sp(m,q),SymmetricGroup(t));
  tmat:=TransformForm@(twp);
  twp:=twp^tmat;
  ng:=Length(GeneratorsOfGroup(twp));
  odd:=twp.(ng); # AH: last generator
  #  coming from odd permutation when t=2
  if ex and not general and not (IsEvenInt(q) and special) then
    gens:=Concatenation(List([1..ng-1],i->twp.i),List([1..ng-1],i->(twp.i)^odd)); 
  else 
    gens:=List([1..ng],i->twp.i);
  fi;

  if IsOddInt(q) and (not ex or special) then
    diag:=NormSpMinusSp@(m,q);
    if normaliser then
      invol:=diag;
      for i in [2..t] do
	invol:=KroneckerProduct(invol,One(GL(m,q)));
      od;
    else
      invol:=KroneckerProduct(diag,diag^-1);
      for i in [3..t] do
        invol:=KroneckerProduct(invol,One(GL(m,q)));
      od;
    fi;
    invol:=(invol)^tmat;
    Add(gens,invol);
  fi;
  if normaliser and IsEvenInt(q) and q > 2 then
    Add(gens,PrimitiveElement(GF(q))*IdentityMat(m^t,One(GF(q))));
  fi;
  return SubgroupContaining(GL(m^t,q),gens);
  #  ex (t=2, m=2 (mod 4)): c=1
  #  else q odd: c=4, so,go; q even: c=2, so.
end);

InstallGlobalFunction(OrthogTensorInd@,
function(m,t,q,sign)
local 
   cmat,diag,ex1,ex1m,ex2,g1,g2,general,gens,ggl,grp1,gsl,i,inom,invol,ng,
   normaliser,odd,special,symt,tmat,twp,x,y;
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
  #  O^sign(m,q) wr Sym(t), s even
  Assert(1,(IsEvenInt(m) and sign in Set([-1,1])) or (IsOddInt(m) and 
   sign=0));
  Assert(1,t > 1);
  Assert(1,m^t > 4);
  if sign=1 and m=2 then
    Error("Illegal parameters - OmegaPlus(2,q) is reducible");
  fi;
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  if IsOddInt(m) then
    if general then
      twp:=TensorWreathProduct(GO(m,q),SymmetricGroup*(t));
    elif special then
      twp:=TensorWreathProduct(SO(m,q),SymmetricGroup*(t));
    else
      twp:=TensorWreathProduct(Omega(m,q),SymmetricGroup*(t));
    fi;

    cmat:=TransformForm@(twp);
    twp:=twp^cmat;
    gsl:=SOMinusOmega@(m,q,0);
    g1:=KroneckerProduct(gsl,One(GL(m,q)));
    g2:=KroneckerProduct(gsl,gsl^-1);
    for i in [3..t] do
      g1:=KroneckerProduct(g1,One(GL(m,q)));
      g2:=KroneckerProduct(g2,One(GL(m,q)));
    od;
    g1:=(g1)^cmat;
    g2:=(g2)^cmat;
    gens:=[];
    for x in GeneratorsOfGroup(twp) do
      y:=x;
      if not general and DeterminantMat(y)<>1 then
	y:=y*(-IdentityMat(m^t,One(GF(q))));
      fi;
      if not special and not InOmega@(y,m^t,q,0) then
        y:=y*g1;
      fi;
      Add(gens,y);
    od;
    if not special then
      Add(gens,g2);
    fi;
    twp:=SubgroupContaining(GL(m^t,q),gens);
    #  twp := twp^TransformForm(twp);
    if normaliser and q > 3 then
      twp:=SubgroupContaining(GL(m^t,q),twp,
	    PrimitiveElement(GF(q))*IdentityMat(m^t,One(GF(q))));
    fi;
    return twp;
    #  c=1
  fi;
  ex1:=t=2 and m mod 4=2;
  ex1m:=IsOddInt(q) and (t=2 and m mod 4=0 and sign=-1);
  ex2:=t=3 and m mod 4=2 and ((sign=1 and q mod 4=3) or (sign=-1 and q mod 
   4=1));
  if sign=1 then 
    grp1:=SOPlus(m,q);
  else
    grp1:=SOMinus(m,q);
  fi;
  if t=3 then
    symt:=Group((1,2,3),(1,2));
  else 
    symt:=SymmetricGroup(t);
  fi;
  twp:=TensorWreathProduct(grp1,symt);
  tmat:=TransformForm@(twp);
  twp:=twp^tmat;
  ng:=Length(GeneratorsOfGroup(twp));
  odd:=twp.(ng);
  #  coming from odd permutation when t=2 or 3
  if ex1 and general then
    gens:=GeneratorsOfGroup(twp);
  elif ex1 then
    gens:=Concatenation(GeneratorsOfGroup(twp){[1..ng-1]},
	   List(GeneratorsOfGroup(twp){[1..ng-1]},x->x^odd));
  elif ex1m or ex2 then
    gens:=GeneratorsOfGroup(twp){[1..ng-1]};
  else
    gens:=GeneratorsOfGroup(twp);
  fi;

  if IsOddInt(q) then
    ggl:=GOMinusSO@(m,q,sign);
    for i in [2..t] do
      ggl:=KroneckerProduct(ggl,One(GL(m,q)));
    od;
    ggl:=(ggl)^tmat;
    if special or InOmega@(ggl,m^t,q,1) then
      inom:=true;
      Add(gens,ggl);
      if ex1 then
        Add(gens,ggl^odd);
      fi;
    else
      Assert(1,t=2);
      inom:=false;
      Add(gens,ggl*ggl^odd);
    fi;
    diag:=NormGOMinusGO@(m,q,sign);
    if normaliser then
      invol:=diag;
      for i in [2..t] do
        invol:=KroneckerProduct(invol,One(GL(m,q)));
      od;
    else
      invol:=KroneckerProduct(diag,diag^-1);
      for i in [3..t] do
        invol:=KroneckerProduct(invol,One(GL(m,q)));
      od;
    fi;
    invol:=(invol)^tmat;
    if special or InOmega@(invol,m^t,q,1) then
      inom:=true;
      Add(gens,invol);
    else
      Assert(1,t=2);
      if not inom then
        Add(gens,ggl*invol);
      fi;
    fi;
    if (special and ex2) or ex1m then
      if special or InOmega@(odd,m^t,q,1) then
        Add(gens,odd);
      else
        Assert(1,inom);
        Add(gens,ggl*odd);
      fi;
    fi;
  fi;
  if normaliser and IsEvenInt(q) and q > 2 then
    Add(gens,PrimitiveElement(GF(q))*IdentityMat(m^t,One(GF(q))));
  fi;
  return SubgroupContaining(GL(m^t,q),gens);
  #  ex1 (t=2, m=2 (mod 4)): c=1
  #  ex2 (t=3, m=2 (mod 4), sign=1 & q=3 (mod 4) or sign=-1 & q=1 (mod 4)):
  #   OR ex1m t=2, sign=-1, m=0 (mod 4)): c=2, go
  #  else c=4, so,go;
end);


