#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.34, 10/22/15 by AH

#  Global Variables used: Append, Coefficients, Determinant, DiagonalJoin,
#  DiagonalMatrix, Factorisation, GF, GL, GammaL1, IsEven, IsOdd, IsPrime,
#  IsSemiLinear, Matrix, Modexp, Ngens, Parent, PrimitiveElement,
#  PrimitivePolynomial, SL, Sym, WreathProduct

#  Defines: GammaL, GammaL1, GammaLMeetSL, ImprimsMeetSL

DeclareGlobalFunction("GammaL@");

DeclareGlobalFunction("GammaL1@");

DeclareGlobalFunction("GammaLMeetSL@");

DeclareGlobalFunction("ImprimsMeetSL@");

#  
#  function names:
#  ImprimsMeetSL(d, p, t)
#  GammaL1(s,p)
#  GammaL(d, p, s)
#  GammaLMeetSL(d, p, s)

#  ***************************************************************
#  to construct SL(d/t, p)^t.(p-1)^(t-1).\Sym(t)
InstallGlobalFunction(ImprimsMeetSL@,
function(d,p,t)
local det,detmat,gens,i,new_gen,newgens,subgroup,z,general;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  Assert(1,IsPrimePowerInt(p));
  Assert(1,(d mod t)=0);
  Assert(1,t > 1);
  if general then
    return MatWreathProduct(GL(QuoInt(d,t),p),SymmetricGroup(t));
  fi;
  subgroup:=MatWreathProduct(SL(QuoInt(d,t),p),SymmetricGroup(t));
  gens:=GeneratorsOfGroup(subgroup);
  newgens:=[];
  for i in [1..Length(gens)] do
    det:=Determinant(gens[i]);
    Assert(1,det=1 or det=-1);
    if det=1 then
      Add(newgens,gens[i]);
    else
      new_gen:=gens[i]
        *DiagonalMat(Z(p)^0*Concatenation([-1],List([2..d],i->1)));
      Add(newgens,new_gen);
    fi;
  od;
  #subgroup:=SubgroupNC(SL(d,p),newgens);
  z:=PrimitiveElement(GF(p));
  detmat:=DiagonalMat(Concatenation([z],List([2..QuoInt(d,t)],i->z^0),
	   [z^-1],List([QuoInt(d,t)+2..d],i->z^0)));
  Add(newgens,detmat);
  return Group(newgens);
end);

#  ***************************************************************
#  This produces GammaL(1, p^s) \leq GL(s, p)
InstallGlobalFunction(GammaL1@,
function(s,q)
local coeffs,cxp,field_auto,grp,mat,pol,x,xq;
  Assert(1,IsPrimePowerInt(q));
  #  "making singer cycle for GL(1, q) in GL(s, q)";
  pol:=MinimalPolynomial(GF(q),Z(q^s));
  x:=IndeterminateOfUnivariateRationalFunction(pol);
  mat:=TransposedMat(CompanionMat(pol));
  
  #  find field automorphism - the reason that x^s has been added to the
  #  argument below is to ensure that cxp[i] and cxp2[i] are always defined!
  #  The basis of the field is [1, x, x^2, \ldots, x^(s-1)]
  xq:=PowerMod(x,q,pol);

  cxp:=List([0..s-1],i->CoefficientsOfUnivariatePolynomial(x^s+(PowerMod(xq,i,pol))){[1..s]});
  grp:=Group(mat,cxp);
  return grp;
  
end);

#  ********************************************************************
#  This uses previous function to produce GammaL(d/s, q^s) \leq GL(d, q)
#  take singer cycle from gammal1(s, q). take gens from gl(d/s,
#  p). make block matrices with singer as blocks inside gens from
#  gl. if entry is in GF(q) then have a block of identity. else
#  take that power. make blocks with id as blocks inside field aut
#  entries.
InstallGlobalFunction(GammaL@,
function(d,q,s)
local dim,i,frob,gammal1,gens4,newmat1,newmat2,newmat3,singer,ran;
  Assert(1,IsPrimePowerInt(q));
  Assert(1,d mod s=0);
  dim:=QuoInt(d,s);
  gammal1:=GammaL1@(s,q);
  if dim=1 then
    return gammal1;
  fi;
  singer:=gammal1.1;
  frob:=gammal1.2;
  gens4:=GL(dim,q).2; # use explicit generator form from paper

  #  "putting singer cycle as block into gens for GL(dim, p)";
  #  newmat1:= Matrix(GF(q), d, d,
  #                [<i, j, singer[i][j]> : i, j in [1..s]] cat [<i, i,
  #                GF(q)!1> : i in [s+1..d]]);
  newmat1:=IdentityMat(d,GF(q));
  newmat1{[1..s]}{[1..s]}:=singer;

  #  newmat2:= Matrix(GF(q), d, d,
  #                &cat[[<k + i*s, k+ j*s, gens4[i+1][j+1]> : i, j in
  #                [0..dim-1]] : k in [1..s]]);
  newmat2:=KroneckerProduct(gens4,IdentityMat(s,GF(q)));


  #  "putting frobenius aut as block into gens for GL(dim, p)";
  #  newmat3:= Matrix(GF(q), d, d,
  #                &cat[[<i+k*s, j+k*s, frob[i][j]> : i, j in [1..s]]
  #                 : k in [0..dim-1]] );
  newmat3:=IdentityMat(d,GF(q));
  for i in [0..dim-1] do
    ran:=[i*s+1..(i+1)*s];
    newmat3{ran}{ran}:=frob;
  od;

  return Group(newmat1,newmat2,newmat3);
  
end);

#  ********************************************************************
#  
#  * This final function returns only the part of the group which
#  * intersects with SL.

InstallGlobalFunction(GammaLMeetSL@,
function(d,q,s)
local detmat,dim,fac,frob,gammal1,gl2,grp,newmat1,newmat2,newmat3,scal,singer,
   singerSL,singer_inv,two_part,i,ran;
  Assert(1,IsPrimePowerInt(q)); Assert(1,d mod s=0);
  if not IsPrime(s) then
    Info(InfoWarning,1,"warning: this function was designed for PRIME field extensions:");
    Info(InfoWarning,1,"results may be inaccurate");
  fi;
  dim:=QuoInt(d,s);
  gammal1:=GammaL1@(s,q);
  singer:=gammal1.1;
  singer_inv:=singer^-1;
  singerSL:=singer^(q-1);
  #frob:=SELECT((((d=2) and q) mod 2)=1 then (singer^(QuoInt((q-1),2))
  # *gammal1).2 else gammal1.2);
  if d=2 and q mod 2=1 then 
    frob:=singer^QuoInt(q-1,2)*gammal1.2;
  else
    frob:=gammal1.2;
  fi;

  #  "determinant frob =", Determinant(frob);
  if dim=1 then
    return Group(singerSL,frob);
  fi;
  gl2:=GL(dim,q^s).2;
  #  "putting singer cycle as block into gens for SL(dim, q)";
  newmat1:=IdentityMat(d,GF(q));
  newmat1{[1..s]}{[1..s]}:=singer;
  newmat1{[d-s+1..d]}{[d-s+1..d]}:=singer_inv;

  newmat2:=KroneckerProduct(gl2,IdentityMat(s,GF(q)));

  detmat:=IdentityMat(d,GF(q));
  detmat{[1..s]}{[1..s]}:=singerSL;

  #  "putting frobenius aut as block into gens for GL(dim, q)";
  newmat3:=IdentityMat(d,GF(q));
  for i in [0..dim-1] do
    ran:=[i*s+1..(i+1)*s];
    newmat3{ran}{ran}:=frob;
  od;

  if IsEvenInt(s) and IsOddInt(dim) and IsOddInt(q) then
    Assert(1,DeterminantMat(frob)=-1);
    fac:=Factors(q-1);
    two_part:=2^Number(fac,x->x=2);
    scal:=singer^QuoInt(q-1,2);
    Assert(1,DeterminantMat(scal)=-1);
    newmat3:=IdentityMat(d,GF(q));
    for i in [0..dim-1] do
      ran:=[i*s+1..(i+1)*s];
      newmat3{ran}{ran}:=scal*frob;
    od;
  fi;
  grp:=Group(newmat1,newmat2,newmat3,detmat);
  #Assert(1,IsSemiLinear(grp));
  return grp;
end);

