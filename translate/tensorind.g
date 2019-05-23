#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, CorrectForm, Determinant, DiagonalMatrix, GF,
#  GL, GO, GU, Gcd, Generators, IsEven, IsOdd, KroneckerProduct, Ngens, Omega,
#  PrimitiveElement, SL, SO, SOMinus, SOPlus, SU, ScalarMatrix, Sp, Sym,
#  SymplecticForm, TensorWreathProduct, TransformForm, UnitaryForm

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
  main:=TensorWreathProduct(SP(m,q),SymmetricGroup(t));
  #  z:= PrimitiveElement(GF(q));
  #  diag:= GL(m, q)!DiagonalMatrix([z: i in [1..m div 2]] cat [1 : i in
  #  [1..m div 2]]);
  diag:=NormSpMinusSp@(m,q);
  if normaliser then
    invol:=diag;
    for i in [2..t] do
      invol:=KroneckerProduct(invol,GL(m,q).0);
    od;
  else
    invol:=KroneckerProduct(diag,diag^-1);
    for i in [3..t] do
      invol:=KroneckerProduct(invol,GL(m,q).0);
    od;
  fi;
  grp:=SubStructure(GL(m^t,q),main,#TODO CLOSURE
    invol);
  # =v= MULTIASSIGN =v=
  f:=SymplecticForm@(main);
  bool:=f.val1;
  f:=f.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,bool);
  mat:=CorrectForm(f,m^t,q,"symplectic");
  return grp^(mat^-1);
end);

#  *******************************************************************
InstallGlobalFunction(SLTensorInd@,
function(m,t,q)
#  /out:assert m gt 2; KL - otherwise orthogonal
local d,d42,diag,diag4,exponent,general,gens,i,main,new_diag,out,s,x,z;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  Assert(1,t > 1);
  if general then
    return TensorWreathProduct(GL(m,q),SymmetricGroup(t));
  fi;
  d:=m^t;
  z:=PrimitiveElement(GF(q));
  diag:=DiagonalMat(Concatenation([z],List([1..m-1],i->1))) #CAST GL(m,q)
    ;
  if (m=2) and (t=2) and (q mod 4=1) then
    #  kludge, but not maximal for m=2 anyway
    return Intersection(TensorWreathProduct(GL(m,q),SymmetricGroup(t)),SL(4,q))
     ;
  fi;
  if ((t=2) and (m mod 4=2) and (q mod 4=3)) then
    gens:=Concatenation(List([1,2],i->KroneckerProduct(SL(m,q).i,SL(m,q).0))
     ,List([1,2],i->KroneckerProduct(SL(m,q).0,SL(m,q).i)));
  else
    main:=TensorWreathProduct(SL(m,q),SymmetricGroup(t));
    gens:=[];
    for x in Generators(main) do
      if DeterminantMat(x)=1 then
        Add(gens,x #CAST SL(d,q)
          );
      else
        #  det = -1 for odd permutation
        if IsOddInt(m) then
          Add(gens,(x*ScalarMat(d,(-1) #CAST GF(q)
            )) #CAST SL(d,q)
            );
        else
          Assert(1,t=2 and m mod 4=2 and q mod 4=1);
          diag4:=diag^(QuoInt((q-1),4));
          #  has fourth root of 1
          d42:=KroneckerProduct(diag4,SL(m,q).0);
          Add(gens,(x*d42) #CAST SL(d,q)
            );
        fi;
      fi;
    od;
  fi;
  out:=KroneckerProduct(diag,diag^-1);
  for i in [3..t] do
    out:=KroneckerProduct(out,GL(m,q).0);
  od;
  out:=out #CAST SL(d,q)
    ;
  exponent:=QuoInt(Gcd(q-1,d),Gcd(q-1,m^(t-1)));
  new_diag:=diag^exponent;
  for i in [2..t] do
    new_diag:=KroneckerProduct(new_diag,GL(m,q).0);
  od;
  Assert(1,DeterminantMat(new_diag)=z^(exponent*m^(t-1)));
  Assert(1,power:=ForAny([1..q-1],e->z^(d*e)=z^(exponent*m^(t-1))));
  #  exists because
  #  exp*m^(t-1) is divisible by
  #  (q-1, d), can divide through
  #  by (q-1, d) then compute
  #  (d/(q-1, d))^-1 mod (q-1)/(q-1,d)
  s:=ScalarMat(d,z^power) #CAST GL(d,q)
    ;
  return SubStructure(SL(d,q),gens,#TODO CLOSURE
    out,new_diag*(s^-1));
end);

#  ****************************************************************
InstallGlobalFunction(SUTensorInd@,
function(m,t,q)
local 
   bool,d,d42,diag,diag4,exponent,f,f2,general,gens,grp,i,main,mat1,mat2,
   new_diag,normaliser,out,s,x,z;
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
      return SubStructure(GL(d,q^2),TensorWreathProduct(GU(m,q)
       ,SymmetricGroup(t)),#TODO CLOSURE
        ScalarMat(d,z));
    fi;
    return TensorWreathProduct(GU(m,q),SymmetricGroup(t));
  fi;
  if (m=2) and (t=2) and (q mod 4=3) then
    #  kludge, but not maximal for k=2 anyway
    return Intersection(TensorWreathProduct(GU(m,q),SymmetricGroup(t)),SU(4,q))
     ;
  fi;
  diag:=DiagonalMat(Concatenation([z],List([1..m-2],i->1),[z^(-q)])) #CAST 
   GL(m,q^2)
    ;
  if ((t=2) and (m mod 4=2) and (q mod 4=1)) then
    gens:=Concatenation(List([1,2],i->KroneckerProduct(SU(m,q).i,SU(m,q).0))
     ,List([1,2],i->KroneckerProduct(SU(m,q).0,SU(m,q).i)));
  else
    main:=TensorWreathProduct(SU(m,q),SymmetricGroup(t));
    gens:=[];
    for x in Generators(main) do
      if DeterminantMat(x)=1 then
        Add(gens,x #CAST SL(d,q^2)
          );
      else
        #  det = -1
        if IsOddInt(m) then
          Add(gens,(x*ScalarMat(d,(-1) #CAST GF(q^2)
            )) #CAST SL(d,q^2)
            );
        else
          Assert(1,t=2 and m mod 4=2 and q mod 4=3);
          diag4:=diag^(QuoInt((q+1),4));
          #  has fourth root of 1
          d42:=KroneckerProduct(diag4,SU(m,q).0);
          Add(gens,(x*d42) #CAST SL(d,q^2)
            );
        fi;
      fi;
    od;
  fi;
  out:=KroneckerProduct(diag,diag^-1);
  for i in [3..t] do
    out:=KroneckerProduct(out,GL(m,q^2).0);
  od;
  out:=out #CAST SL(d,q^2)
    ;
  exponent:=QuoInt(Gcd(q+1,d),Gcd(q+1,m^(t-1)));
  new_diag:=diag^exponent;
  for i in [2..t] do
    new_diag:=KroneckerProduct(new_diag,GL(m,q^2).0);
  od;
  Assert(1,DeterminantMat(new_diag)=z^((1-q)*exponent*m^(t-1)));
  Assert(1,power:=ForAny([1..q^2-1],e->z^(d*e*(q-1))=z^((1-q)*exponent*m^(t-1)))
   );
  #  exists because
  #  exp*m^(t-1) is divisible by
  #  (q-1)(q+1, d), can divide through
  #  by (q-1)(q+1, d) then compute
  #  (d/(q+1, d))^-1 mod (q+1)/(q+1,d)
  s:=ScalarMat(d,z^(power*(q-1))) #CAST GL(d,q^2)
    ;
  grp:=SubStructure(SL(d,q^2),gens,#TODO CLOSURE
    out,new_diag*(s^-1));
  # =v= MULTIASSIGN =v=
  f:=UnitaryForm(grp);
  bool:=f.val1;
  f:=f.val2;
  # =^= MULTIASSIGN =^=
  #  f;
  if not bool then
    Error("ERROR: group not unitary");
  fi;
  # =v= MULTIASSIGN =v=
  f2:=UnitaryForm(SU(d,q));
  bool:=f2.val1;
  f2:=f2.val2;
  # =^= MULTIASSIGN =^=
  if f=f2 then
    return grp;
  fi;
  mat1:=CorrectForm(f,d,q^2,"unitary");
  mat2:=CorrectForm(f2,d,q^2,"unitary");
  return grp^(mat1*mat2^-1);
end);

InstallGlobalFunction(OrthogSpTensorInd@,
function(m,t,q)
#  /out:Sp(m,q) wr Sym(t)
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
  twp:=TensorWreathProduct(SP(m,q),SymmetricGroup(t));
  tmat:=TransformForm(twp);
  twp:=twp^tmat;
  ng:=Ngens(twp);
  odd:=twp.ng;
  #  coming from odd permutation when t=2
  # rewritten select statement
  if ex and not general and not (IsEvenInt(q) and special) then
    gens:=Concatenation(List([1..ng-1],i->twp.i),List([1..ng-1],i->(twp.i)^odd))
     ;
  else
    gens:=List([1..ng],i->twp.i);
  fi;
  if IsOddInt(q) and (not ex or special) then
    diag:=NormSpMinusSp@(m,q);
    if normaliser then
      invol:=diag;
      for i in [2..t] do
        invol:=KroneckerProduct(invol,GL(m,q).0);
      od;
    else
      invol:=KroneckerProduct(diag,diag^-1);
      for i in [3..t] do
        invol:=KroneckerProduct(invol,GL(m,q).0);
      od;
    fi;
    invol:=(invol #CAST GL(m^t,q)
      )^tmat;
    Add(gens,invol);
  fi;
  if normaliser and IsEvenInt(q) and q > 2 then
    Add(gens,ScalarMat(m^t,PrimitiveElement(GF(q))));
  fi;
  return SubStructure(GL(m^t,q),gens);
  #  ex (t=2, m=2 (mod 4)): c=1
  #  else q odd: c=4, so,go; q even: c=2, so.
end);

InstallGlobalFunction(OrthogTensorInd@,
function(m,t,q,sign)
#  /out:O^sign(m,q) wr Sym(t), s even
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
  Assert(1,(IsEvenInt(m) and sign in Set([-1,1])) or (IsOddInt(m) and sign=0));
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
    # rewritten select statement
    if general then
      twp:=TensorWreathProduct(GO(m,q),SymmetricGroup(t));
    else
      # rewritten select statement
      if special then
        twp:=TensorWreathProduct(SO(m,q),SymmetricGroup(t));
      else
        twp:=TensorWreathProduct(Omega(m,q),SymmetricGroup(t));
      fi;
    fi;
    cmat:=TransformForm(twp);
    twp:=twp^cmat;
    gsl:=SOMinusOmega@(m,q,0);
    g1:=KroneckerProduct(gsl,GL(m,q).0);
    g2:=KroneckerProduct(gsl,gsl^-1);
    for i in [3..t] do
      g1:=KroneckerProduct(g1,GL(m,q).0);
      g2:=KroneckerProduct(g2,GL(m,q).0);
    od;
    g1:=(g1 #CAST GL(m^t,q)
      )^cmat;
    g2:=(g2 #CAST GL(m^t,q)
      )^cmat;
    gens:=[];
    for x in List([1..Ngens(twp)],i->twp.i) do
      y:=x;
      if not general and DeterminantMat(y)<>1 then
        y:=y*ScalarMat(m^t,(-1) #CAST GF(q)
          ) #CAST GL(m^t,q)
          ;
      fi;
      if not special and not InOmega@(y,m^t,q,0) then
        y:=y*g1;
      fi;
      Add(gens,y);
    od;
    if not special then
      Add(gens,g2);
    fi;
    twp:=SubStructure(GL(m^t,q),gens);
    #  twp := twp^TransformForm(twp);
    if normaliser and q > 3 then
      twp:=SubStructure(GL(m^t,q),twp,#TODO CLOSURE
        ScalarMat(m^t,PrimitiveElement(GF(q))));
    fi;
    return twp;
    #  c=1
  fi;
  ex1:=t=2 and m mod 4=2;
  ex1m:=IsOddInt(q) and (t=2 and m mod 4=0 and sign=-1);
  ex2:=t=3 and m mod 4=2 and ((sign=1 and q mod 4=3) or (sign=-1 and q mod 4=1))
   ;
  # rewritten select statement
  if sign=1 then
    grp1:=SOPlus(m,q);
  else
    grp1:=SOMinus(m,q);
  fi;
  # rewritten select statement
  if t=3 then
    symt:=SubStructure(SymmetricGroup(t),(1,2,3),#TODO CLOSURE
      Tuple([1,2]));
  else
    symt:=SymmetricGroup(t);
  fi;
  twp:=TensorWreathProduct(grp1,symt);
  tmat:=TransformForm(twp);
  twp:=twp^tmat;
  ng:=Ngens(twp);
  odd:=twp.ng;
  #  coming from odd permutation when t=2 or 3
  # rewritten select statement
  if ex1 and general then
    gens:=List([1..ng],i->twp.i);
  else
    # rewritten select statement
    if ex1 then
      gens:=Concatenation(List([1..ng-1],i->twp.i),List([1..ng-1],i->(twp.i)
       ^odd));
    else
      # rewritten select statement
      if ex1m or ex2 then
        gens:=List([1..ng-1],i->twp.i);
      else
        gens:=List([1..ng],i->twp.i);
      fi;
    fi;
  fi;
  if IsOddInt(q) then
    ggl:=GOMinusSO@(m,q,sign);
    for i in [2..t] do
      ggl:=KroneckerProduct(ggl,GL(m,q).0);
    od;
    ggl:=(ggl #CAST GL(m^t,q)
      )^tmat;
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
        invol:=KroneckerProduct(invol,GL(m,q).0);
      od;
    else
      invol:=KroneckerProduct(diag,diag^-1);
      for i in [3..t] do
        invol:=KroneckerProduct(invol,GL(m,q).0);
      od;
    fi;
    invol:=(invol #CAST GL(m^t,q)
      )^tmat;
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
    Add(gens,ScalarMat(m^t,PrimitiveElement(GF(q))));
  fi;
  return SubStructure(GL(m^t,q),gens);
  #  ex1 (t=2, m=2 (mod 4)): c=1
  #  ex2 (t=3, m=2 (mod 4), sign=1 & q=3 (mod 4) or sign=-1 & q=1 (mod 4)):
  #   OR ex1m t=2, sign=-1, m=0 (mod 4)): c=2, go
  #  else c=4, so,go;
end);


