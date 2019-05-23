#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.37, 12/20/15 by AH

#  Global Variables used: Abs, CorrectForm, Determinant, DiagonalJoin,
#  DiagonalMatrix, GCD, GF, GL, GO, GOMinus, GOMinusSO, GOPlus, GU,
#  Generators, Integers, IsEven, IsOdd, IsSquare, Matrix, Ngens,
#  NormGOMinusGO, NormSpMinusSp, Nullspace, OrthogonalForm, PrimitiveElement,
#  SL, SO, SOMinus, SOPlus, SU, ScalarMatrix, Sp, SymmetricBilinearForm

#  Defines: GLMinusSL, GOMinusSO, GUMinusSU, NormGOMinusGO, NormOfO,
#  NormOfSU, NormOfSp, NormSpMinusSp, SOMinusOmega

DeclareGlobalFunction("GLMinusSL@");

DeclareGlobalFunction("GOMinusSO@");

DeclareGlobalFunction("GUMinusSU@");

DeclareGlobalFunction("NormGOMinusGO@");

DeclareGlobalFunction("NormOfO@");

DeclareGlobalFunction("NormOfSU@");

DeclareGlobalFunction("NormOfSp@");

DeclareGlobalFunction("NormSpMinusSp@");

DeclareGlobalFunction("SOMinusOmega@");

InstallGlobalFunction(GLMinusSL@,
function(d,q)
#  A generating element of GL - SL.
  Assert(1,not IsOne(DeterminantMat(GL(d,1).1)));
  return GL(d,q).1;
  
end);

InstallGlobalFunction(GUMinusSU@,
function(d,q)
#  A generating element of GU - SU.
  Assert(1,not IsOne(DeterminantMat(GU(d,1).1)));
  return GU(d,q).1;
  
end);

InstallGlobalFunction(NormSpMinusSp@,
function(d,q)
local hd,z;
  #  An element of Normaliser(GL(d,q),Sp(d,q)) - Sp(d,q);
  #  Determinant = z^(d/2).
  Assert(1,IsEvenInt(d));
  z:=PrimitiveElement(GF(q));
  hd:=QuoInt(d,2);
  return DiagonalMat(Concatenation(List([1..hd],i->z),List([1..hd],i->Z(q)^0)));
end);

InstallGlobalFunction(SOMinusOmega@,
function(d,q,eps)
local Y,i;
  #  An element of SO^eps(d,q) - Omega^eps(d,q).
  Assert(1,eps in [-1,0,1]);
  if IsOddInt(d) then 
    Y:=SO(d,q);
  elif eps=1 then 
    Y:=SOPlus(d,q);
  else
    Y:=SOMinus(d,q);
  fi;
  for i in GeneratorsOfGroup(Y) do
    if not InOmega@(i,d,q,eps) then
      return i;
      #break;
    fi;
  od;
  
end);

InstallGlobalFunction(GOMinusSO@,
function(d,q,eps)
local G,g;
  #  An element of GO^eps(d,q) - SO^eps(d,q); determinant -1.
  Assert(1,IsOddInt(q));
  Assert(1,eps in Set([-1,0,1]));
  if eps=0 then
    return -1*IdentityMat(d,GF(q));
  fi;
  if eps=1 then
    G:=GOPlus(d,q);
  else 
    G:=GOMinus(d,q);
  fi;
  for g in GeneratorsOfGroup(G) do
    if DeterminantMat(g)<>1 then
      return g;
    fi;
  od;
  
end);

InstallGlobalFunction(NormGOMinusGO@,
function(d,q,eps)
local AandB,a,b,form,g,hd,isit,mat,type,z;
  #  An element of Normaliser(GL(d,q),GO^eps(d,q)) - GO^eps(d,q);
  #  Determinant = z^(d/2).
  AandB:=function(q,z)
  local a,b,bool;
    z:=z*One(GF(q));
    #  find elements of GF(q) with a^2+b^2=z.
    for b in GF(q) do
      a:=RootFFE(z-b^2,2);
      if a<>fail then
        return rec(val1:=a,
          val2:=b);
      fi;
    od;
    Error("ERROR: couldn't find a and b in GF(",q,")");
    
  end;

  Assert(1,IsEvenInt(d));
  Assert(1,IsOddInt(q) or eps=1);
  Assert(1,eps in Set([-1,1]));
  z:=PrimitiveElement(GF(q));
  if eps=1 then
    hd:=QuoInt(d,2);
    return
      DiagonalMat(Concatenation(List([1..hd],i->z),List([1..hd],i->Z(q)^0)));
  fi;
  # =v= MULTIASSIGN =v=
  b:=AandB(q,z);
  a:=b.val1;
  b:=b.val2;
  # =^= MULTIASSIGN =^=
  if d mod 4=0 or (q-1) mod 4=0 then 
   g:=DirectSumMat(Concatenation(
       List([1..QuoInt(d,2)-1],i->MatrixByEntries(GF(q),2,2,[a,-b,b,a])),
	[MatrixByEntries(GF(q) ,2,2,[0,-1,z,0])]));
  else 
    g:=DirectSumMat(
	List([1..QuoInt(d,2)],i->MatrixByEntries(GF(q),2,2,[a,-b,b,a])));
  fi;
  # =v= MULTIASSIGN =v=
  form:=SymmetricBilinearForm@(GOMinus(d,q));
  isit:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  mat:=CorrectForm@(form,d,q,"orth-");
  return mat*g*mat^-1;
  
end);

InstallGlobalFunction(NormOfSU@,
function(d,q)
local Y,varZ,general,mform,trans,ypow,z,zpow;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  #  returns the normaliser of SU(d,q) in SL(d,q^2) (or in GL(d,q^2) if
  #  general)
  z:=PrimitiveElement(GF(q^2));
  varZ:=z*IdentityMat(d,GF(q^2));
  if general then
    return SubgroupContaining(GL(d,q^2),GU(d,q),varZ);
  fi;
  mform:=MatrixByEntries(GF(q^2),d,d,List([1..d],i->[i,d+1-i,1]));
  trans:=CorrectForm@(mform,d,q^2,"unitary");
  Y:=DiagonalMat(Concatenation([z^(q-1)],List([1..d-1],i->z^0)));
  Y:=trans*Y*trans^-1;
  #  Y is generator of GU/SU
  zpow:=QuoInt((q-1),Gcd(d,q-1));
  ypow:=(QuoInt(-d*zpow,(q-1))) mod (q+1);
  return SubgroupContaining(SL(d,q^2),SU(d,q),varZ^zpow*Y^ypow);
end);

InstallGlobalFunction(NormOfSp@,
function(d,q)
local I,Y,varZ,general,hd,x,y,ypow,z,zpow;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  #  returns the normaliser of Sp(d,q) in SL(d,q) (or in GL(d,q) if general)
   
  if general then
    return SubgroupContaining(GL(d,q),Sp(d,q),NormSpMinusSp@(d,q));
  fi;
  z:=PrimitiveElement(GF(q));
  varZ:=z*IdentityMat(GF(q),d);
  hd:=QuoInt(d,2);
  if IsEvenInt(q) or Gcd(q-1,d)<>Gcd(q-1,hd) then
    zpow:=QuoInt((q-1),Gcd(d,q-1));
    return SubgroupContaining(SL(d,q),Sp(d,q),varZ^zpow);
  else
    Y:=NormSpMinusSp@(d,q);
    ypow:=QuoInt((q-1),Gcd(hd,q-1));
    return SubgroupContaining(SL(d,q),Sp(d,q),Y^ypow);
  fi;
  
end);

InstallGlobalFunction(NormOfO@,
function(d,q,eps)
local N,W,varX,Y,varZ,form,general,gens,hd,isit,trans,type,ypow,z,zpow;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  #  returns the normaliser of O^eps(d,q) in SL(d,q) (or in GL(d,q) if
  #  general)
  #  not maximal in SL for q even  - subgroups of Sp if q is even.
  #  also need d>2 in maximals.
  Assert(1,(IsOddInt(d) and eps=0) or (IsEvenInt(d) and AbsInt(eps)=1));
  if d=2 and q=3 and eps=1 then
    if general then
      return GL(d,q);
    fi;
    return SL(d,q);
  fi;
  z:=PrimitiveElement(GF(q));
  varZ:=z*IdentityMat(GF(q),d);
  zpow:=QuoInt((q-1),Gcd(d,q-1));
  if IsOddInt(d) then
    if general then
      return SubgroupContaining(GL(d,q),GO(d,q),varZ);
    fi;
    return SubgroupContaining(SL(d,q),SO(d,q),varZ^zpow);
  fi;
  if IsEvenInt(q) then
    if general then
      if eps=1 then
        return SubgroupContaining(GL(d,q),GOPlus(d,q),varZ);
      fi;
      return SubgroupContaining(GL(d,q),GOMinus(d,q),varZ);
    else
      if eps=1 then
        return SubgroupContaining(SL(d,q),SOPlus(d,q),varZ^zpow);
      fi;
      return SubgroupContaining(SL(d,q),SOMinus(d,q),varZ^zpow);
    fi;
  fi;
  hd:=QuoInt(d,2);
  #  get transforming matrix
  if eps=1 then
    # =v= MULTIASSIGN =v=
    form:=OrthogonalForm@(GOPlus(d,q));
    isit:=form.val1;
    type:=form.val2;
    form:=form.val3;
    # =^= MULTIASSIGN =^=
  else
    # =v= MULTIASSIGN =v=
    form:=OrthogonalForm@(GOMinus(d,q));
    isit:=form.val1;
    type:=form.val2;
    form:=form.val3;
    # =^= MULTIASSIGN =^=
  fi;
  varX:=GOMinusSO@(d,q,eps);
  Y:=NormGOMinusGO@(d,q,eps);
  #  Normaliser in GL = <SO, X, Y, Z > (Z redundant)
  if general then
    if eps=1 then
      return SubgroupContaining(GL(d,q),SOPlus(d,q),varX,Y);
    fi;
    return SubgroupContaining(GL(d,q),SOMinus(d,q),varX,Y);
  fi;
  #  Normaliser in SL is generated by SO together with elements
  #  X^x Y^y Z^z with x(q-1)/2 + yd/2 + zd = 0 mod q-1
  W:=MatrixByEntries(Integers(),4,1,[QuoInt((q-1),2),hd,d,q-1]);
  N:=NullspaceMat(W);
  gens:=List(GeneratorsOfGroup(N),n->varX^n[1]*Y^n[2]*varZ^n[3]);
  if eps=1 then
    return SubgroupContaining(SL(d,q),SOPlus(d,q),gens);
  else
    return SubgroupContaining(SL(d,q),SOMinus(d,q),gens);
  fi;
  
end);


