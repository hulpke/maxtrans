#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: AandB, Abs, CorrectForm, Determinant, DiagonalJoin,
#  DiagonalMatrix, GCD, GF, GL, GO, GOMinus, GOMinusSO, GOPlus, GU, Generators,
#  Integers, IsEven, IsOdd, IsSquare, Matrix, Ngens, NormGOMinusGO,
#  NormSpMinusSp, Nullspace, OrthogonalForm, PrimitiveElement, SL, SO, SOMinus,
#  SOPlus, SU, ScalarMatrix, Sp, SymmetricBilinearForm

#  Defines: GLMinusSL, GOMinusSO, GUMinusSU, NormGOMinusGO, NormOfO, NormOfSU,
#  NormOfSp, NormSpMinusSp, SOMinusOmega

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
#  /out:A generating element of GL - SL.
return GL(d,q).1;
end);

InstallGlobalFunction(GUMinusSU@,
function(d,q)
#  /out:A generating element of GU - SU.
return GU(d,q).1;
end);

InstallGlobalFunction(NormSpMinusSp@,
function(d,q)
#  /out:An element of Normaliser(GL(d,q),Sp(d,q)) - Sp(d,q);/out:Determinant =
#  z^(d/2).
local hd,z;
  Assert(1,IsEvenInt(d));
  z:=PrimitiveElement(GF(q));
  hd:=QuoInt(d,2);
  return DiagonalMat(GF(q),d,Concatenation(List([1..hd],i->z),List([1..hd],i->1)
   )) #CAST GL(d,q)
    ;
end);

InstallGlobalFunction(SOMinusOmega@,
function(d,q,eps)
#  /out:An element of SO^eps(d,q) - Omega^eps(d,q).
local varX,i;
  Assert(1,eps in Set([-1,0,1]));
  # rewritten select statement
  if IsOddInt(d) then
    varX:=SO(d,q);
  else
    # rewritten select statement
    if eps=1 then
      varX:=SOPlus(d,q);
    else
      varX:=SOMinus(d,q);
    fi;
  fi;
  for i in [1..Ngens(varX)] do
    if not InOmega@(varX.i,d,q,eps) then
      return varX.i;
      break;
    fi;
  od;
end);

InstallGlobalFunction(GOMinusSO@,
function(d,q,eps)
#  /out:An element of GO^eps(d,q) - SO^eps(d,q); determinant -1.
local G,g;
  Assert(1,IsOddInt(q));
  Assert(1,eps in Set([-1,0,1]));
  if eps=0 then
    return ScalarMat(GF(q),d,-1) #CAST GL(d,q)
      ;
  fi;
  # rewritten select statement
  if eps=1 then
    G:=GOPlus(d,q);
  else
    G:=GOMinus(d,q);
  fi;
  for g in List([1..Ngens(G)],i->G.i) do
    if DeterminantMat(g)<>1 then
      return g;
    fi;
  od;
end);

InstallGlobalFunction(NormGOMinusGO@,
function(d,q,eps)
#  /out:An element of Normaliser(GL(d,q),GO^eps(d,q)) -
#  GO^eps(d,q);/out:Determinant = z^(d/2).
local AandB@,a,b,form,g,hd,isit,mat,type,z;
  AandB@:=function(q,z)
  #  /out:find elements of GF(q) with a^2+b^2=z.
  local a,b,bool;
    for b in GF(q) do
      # =v= MULTIASSIGN =v=
      a:=IsSquare(z-b #CAST GF(q)
        ^2);
      bool:=a.val1;
      a:=a.val2;
      # =^= MULTIASSIGN =^=
      if bool then
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
    return DiagonalMat(GF(q),d,Concatenation(List([1..hd],i->z),List([1..hd]
     ,i->1))) #CAST GL(d,q)
      ;
  fi;
  # =v= MULTIASSIGN =v=
  b:=AandB@(q,z);
  a:=b.val1;
  b:=b.val2;
  # =^= MULTIASSIGN =^=
  # rewritten select statement
  if d mod 4=0 or (q-1) mod 4=0 then
    g:=DirectSumMat(Concatenation(List([1..QuoInt(d,2)-1]
     ,i->MatrixByEntries(GF(q),2,2,[a,-b,b,a])),[MatrixByEntries(GF(q)
     ,2,2,[0,-1,z,0])]));
  else
    g:=DirectSumMat(List([1..QuoInt(d,2)],i->MatrixByEntries(GF(q)
     ,2,2,[a,-b,b,a])));
  fi;
  # =v= MULTIASSIGN =v=
  form:=SymmetricBilinearForm(GOMinus(d,q));
  isit:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  mat:=CorrectForm(form,d,q,"orth-");
  return (mat*g*mat^-1) #CAST GL(d,q)
    ;
end);

InstallGlobalFunction(NormOfSU@,
function(d,q)
#  /out:returns the normaliser of SU(d,q) in SL(d,q^2) (or in GL(d,q^2) if
#  general)
local Y,varZ,general,mform,trans,ypow,z,zpow;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  z:=PrimitiveElement(GF(q^2));
  varZ:=ScalarMat(GF(q^2),d,z) #CAST GL(d,q^2)
    ;
  if general then
    return SubStructure(GL(d,q^2),GU(d,q),#TODO CLOSURE
      varZ);
  fi;
  mform:=MatrixByEntries(GF(q^2),d,d,List([1..d],i->[i,d+1-i,1]));
  trans:=CorrectForm(mform,d,q^2,"unitary");
  Y:=DiagonalMat(GF(q^2),Concatenation([z^(q-1)],List([1..d-1],i->1)));
  Y:=trans*Y*trans^-1;
  #  Y is generator of GU/SU
  zpow:=QuoInt((q-1),Gcd(d,q-1));
  ypow:=(QuoInt(-d*zpow,(q-1))) mod (q+1);
  return SubStructure(SL(d,q^2),SU(d,q),#TODO CLOSURE
    varZ^zpow*Y^ypow);
end);

InstallGlobalFunction(NormOfSp@,
function(d,q)
#  /out:returns the normaliser of Sp(d,q) in SL(d,q) (or in GL(d,q) if general)
local I,Y,varZ,general,hd,x,y,ypow,z,zpow;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  if general then
    return SubStructure(GL(d,q),SP(d,q),#TODO CLOSURE
      NormSpMinusSp@(d,q));
  fi;
  z:=PrimitiveElement(GF(q));
  varZ:=ScalarMat(GF(q),d,z);
  hd:=QuoInt(d,2);
  if IsEvenInt(q) or Gcd(q-1,d)<>Gcd(q-1,hd) then
    zpow:=QuoInt((q-1),Gcd(d,q-1));
    return SubStructure(SL(d,q),SP(d,q),#TODO CLOSURE
      varZ^zpow);
  else
    Y:=NormSpMinusSp@(d,q);
    ypow:=QuoInt((q-1),Gcd(hd,q-1));
    return SubStructure(SL(d,q),SP(d,q),#TODO CLOSURE
      Y^ypow);
  fi;
end);

InstallGlobalFunction(NormOfO@,
function(d,q,eps)
#  /out:returns the normaliser of O^eps(d,q) in SL(d,q) (or in GL(d,q) if
#  general)/out:not maximal in SL for q even  - subgroups of Sp if q is
#  even./out:also need d>2 in maximals.
local N,W,varX,Y,varZ,form,general,gens,hd,isit,trans,type,ypow,z,zpow;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  Assert(1,(IsOddInt(d) and eps=0) or (IsEvenInt(d) and Abs(eps)=1));
  if d=2 and q=3 and eps=1 then
    if general then
      return GL(d,q);
    fi;
    return SL(d,q);
  fi;
  z:=PrimitiveElement(GF(q));
  varZ:=ScalarMat(GF(q),d,z);
  zpow:=QuoInt((q-1),Gcd(d,q-1));
  if IsOddInt(d) then
    if general then
      return SubStructure(GL(d,q),GO(d,q),#TODO CLOSURE
        varZ);
    fi;
    return SubStructure(SL(d,q),SO(d,q),#TODO CLOSURE
      varZ^zpow);
  fi;
  if IsEvenInt(q) then
    if general then
      if eps=1 then
        return SubStructure(GL(d,q),GOPlus(d,q),#TODO CLOSURE
          varZ);
      fi;
      return SubStructure(GL(d,q),GOMinus(d,q),#TODO CLOSURE
        varZ);
    else
      if eps=1 then
        return SubStructure(SL(d,q),SOPlus(d,q),#TODO CLOSURE
          varZ^zpow);
      fi;
      return SubStructure(SL(d,q),SOMinus(d,q),#TODO CLOSURE
        varZ^zpow);
    fi;
  fi;
  hd:=QuoInt(d,2);
  #  get transforming matrix
  if eps=1 then
    # =v= MULTIASSIGN =v=
    form:=OrthogonalForm(GOPlus(d,q));
    isit:=form.val1;
    type:=form.val2;
    form:=form.val3;
    # =^= MULTIASSIGN =^=
  else
    # =v= MULTIASSIGN =v=
    form:=OrthogonalForm(GOMinus(d,q));
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
      return SubStructure(GL(d,q),SOPlus(d,q),#TODO CLOSURE
        varX,Y);
    fi;
    return SubStructure(GL(d,q),SOMinus(d,q),#TODO CLOSURE
      varX,Y);
  fi;
  #  Normaliser in SL is generated by SO together with elements
  #  X^x Y^y Z^z with x(q-1)/2 + yd/2 + zd = 0 mod q-1
  W:=MatrixByEntries(Integers(),4,1,[QuoInt((q-1),2),hd,d,q-1]);
  N:=NullspaceMat(W);
  gens:=List(Generators(N),n->varX^n[1]*Y^n[2]*varZ^n[3]);
  if eps=1 then
    return SubStructure(SL(d,q),SOPlus(d,q),#TODO CLOSURE
      gens);
  else
    return SubStructure(SL(d,q),SOMinus(d,q),#TODO CLOSURE
      gens);
  fi;
end);


