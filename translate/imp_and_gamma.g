#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

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
local det,detmat,general,gens,i,new_gen,newgens,subgroup,z;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  Assert(1,Size(CollectedFactors(p))=1);
  Assert(1,d mod t=0);
  Assert(1,t > 1);
  if general then
    return WreathProduct(GL(QuoInt(d,t),p),SymmetricGroup(t));
  fi;
  subgroup:=WreathProduct(SL(QuoInt(d,t),p),SymmetricGroup(t));
  gens:=List([1..Ngens(subgroup)],i->subgroup.i);
  newgens:=[];
  for i in [1..Size(gens)] do
    det:=DeterminantMat(gens[i]);
    Assert(1,((det=1) or (det=-1)));
    if det=1 then
      Add(newgens,gens[i] #CAST GL(d,p)
        );
    else
      new_gen:=gens[i]*DiagonalMat(Concatenation([-1],List([2..d],i->1))) #CAST 
       GL(d,p)
        ;
      Add(newgens,new_gen);
    fi;
  od;
  subgroup:=SubStructure(SL(d,p),newgens);
  z:=PrimitiveElement(GF(p));
  detmat:=DiagonalMat(Concatenation([z],List([2..(QuoInt(d,t))],i->1),[z^-1]
   ,List([(QuoInt(d,t))+2..d],i->1)));
  return SubStructure(SL(d,p),subgroup,#TODO CLOSURE
    detmat);
end);

#  ***************************************************************
#  This produces GammaL(1, p^s) \leq GL(s, p)
InstallGlobalFunction(GammaL1@,
function(s,q)
local coeffs,cxp,fac,field_auto,grp,mat,pol,x,xq;
  fac:=CollectedFactors(q);
  Assert(1,Size(fac)=1);
  #  "making singer cycle for GL(1, q) in GL(s, q)";
  pol:=PrimitivePolynomial(GF(q),s);
  x:=Parent(pol).1;
  coeffs:=Coefficients(pol);
  mat:=MatrixByEntries(GF(q),s,s,Concatenation(List([1..s-1],i->[i,i+1,1])
   ,List([1..s],i->[s,i,-coeffs[i]]))) #CAST GL(s,q)
    ;
  #  find field automorphism - the reason that x^s has been added to the
  #  argument below is to ensure that cxp[i] and cxp2[i] are always defined!
  #  The basis of the field is [1, x, x^2, \ldots, x^(s-1)]
  xq:=PowerMod(x,q,pol);
  #  cxp:= [Coefficients(x^s + x^(i*q) mod pol) : i in [1..s-1]];
  cxp:=List([1..s-1],i->Coefficients(x^s+xq^i mod pol));
  field_auto:=MatrixByEntries(GF(q),s,s,Concatenation([[1,1,1]]
   ,Concatenation(List([1..s],j->List([1..s-1],i->[i+1,j,cxp[i][j]]))))) #CAST 
   GL(s,q)
    ;
  grp:=SubStructure(GL(s,q),mat,#TODO CLOSURE
    field_auto);
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
local dim,fac,frob,gammal1,gens4,newmat1,newmat2,newmat3,singer;
  fac:=CollectedFactors(q);
  Assert(1,Size(fac)=1);
  Assert(1,d mod s=0);
  dim:=QuoInt(d,s);
  gammal1:=GammaL1@(s,q);
  if dim=1 then
    return SubStructure(GL(d,q),gammal1);
  fi;
  singer:=gammal1.1;
  frob:=gammal1.2;
  gens4:=GL(dim,q^s).2;
  #  "putting singer cycle as block into gens for GL(dim, p)";
  newmat1:=MatrixByEntries(GF(q),d,d,Concatenation(Concatenation(List([1..s],
    i->List([1..s],
      j->[i,j,singer[i][j]])),List([s+1..d],i->[i,i,1 #CAST GF(q)
    ])));
  newmat2:=MatrixByEntries(GF(q),d,d,Concatenation(List([1..s]
     ,k->Concatenation(List([0..dim-1],
    i->List([0..dim-1],
      j->[k+i*s,k+j*s,gens4[i+1][j+1]])))));
  #  "putting frobenius aut as block into gens for GL(dim, p)";
  newmat3:=MatrixByEntries(GF(q),d,d,Concatenation(List([0..dim-1]
     ,k->Concatenation(List([1..s],
    i->List([1..s],
      j->[i+k*s,j+k*s,frob[i][j]])))));
  return SubStructure(GL(d,q),newmat1,#TODO CLOSURE
    newmat2,newmat3);
end);

#  ********************************************************************
#  
#  * This final function returns only the part of the group which
#  * intersects with SL.

InstallGlobalFunction(GammaLMeetSL@,
function(d,q,s)
local 
   detmat,dim,fac,frob,gammal1,gl2,grp,newmat1,newmat2,newmat3,scal,singer,
   singerSL,singer_inv,two_part;
  fac:=CollectedFactors(q);
  Assert(1,Size(fac)=1);
  Assert(1,d mod s=0);
  if not IsPrimeInt(s) then
    Info(InfoWarning,1,
      "warning: this function was designed for PRIME field extensions:");
    Info(InfoWarning,1,"results may be inaccurate");
  fi;
  dim:=QuoInt(d,s);
  gammal1:=GammaL1@(s,q);
  singer:=gammal1.1;
  singer_inv:=singer^-1;
  singerSL:=singer^(q-1);
  # rewritten select statement
  if d=2 and q mod 2=1 then
    frob:=singer^(QuoInt((q-1),2))*gammal1.2;
  else
    frob:=gammal1.2;
  fi;
  #  "determinant frob =", Determinant(frob);
  if dim=1 then
    return SubStructure(GL(d,q),singerSL,#TODO CLOSURE
      frob);
  fi;
  gl2:=GL(dim,q^s).2;
  #  "putting singer cycle as block into gens for SL(dim, q)";
  newmat1:=MatrixByEntries(GF(q),d,d,Concatenation(Concatenation(List([1..s],
    i->List([1..s],
      j->[i,j,singer[i][j]])),List([s+1..d-1],i->[i,i,1])
     ,Concatenation(List([1..s],
    i->List([1..s],
      j->[i+(d-s),j+(d-s),singer_inv[i][j]]))));
  newmat2:=MatrixByEntries(GF(q),d,d,Concatenation(List([1..s]
     ,k->Concatenation(List([0..(dim-1)],
    i->List([0..(dim-1)],
      j->[k+i*s,k+j*s,gl2[i+1][j+1]])))));
  detmat:=MatrixByEntries(GF(q),d,d,Concatenation(Concatenation(List([1..s],
    i->List([1..s],
      j->[i,j,singerSL[i][j]])),List([s+1..d],i->[i,i,1])));
  #  "putting frobenius aut as block into gens for GL(dim, q)";
  newmat3:=MatrixByEntries(GF(q),d,d,Concatenation(List([0..dim-1]
     ,k->Concatenation(List([1..s],
    i->List([1..s],
      j->[i+k*s,j+k*s,frob[i][j]])))));
  if IsEvenInt(s) and IsOddInt(dim) and IsOddInt(q) then
    Assert(1,DeterminantMat(frob)=-1);
    fac:=CollectedFactors(q-1);
    two_part:=2^fac[1][2];
    scal:=singer^(QuoInt((q-1),2));
    Assert(1,DeterminantMat(scal)=-1);
    newmat3:=DirectSumMat(List([1..dim],i->scal*frob));
  fi;
  grp:=SubStructure(SL(d,q),newmat1,#TODO CLOSURE
    newmat2,newmat3,detmat);
  Assert(1,IsSemiLinear(grp));
  return grp;
end);


