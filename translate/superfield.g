#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, BaseRing, BlockPowers, ConjIntoSU,
#  CorrectForm, Determinant, DiagonalJoin, Factorisation, GF, GL, GO, GOMinus,
#  GOPlus, GU, HorizontalJoin, IsEven, IsOdd, IsPrime, Log, MatToQ, Matrix,
#  MatrixAlgebra, MinimalPolynomial, Ncols, Ngens, Nrows, Omega, OmegaMinus,
#  OmegaPlus, Order, PolynomialRing, PrimitiveElement, QuadraticForm, Roots,
#  SL, SO, SOMinus, SOPlus, SU, ScalarMatrix, Sp, SymmetricBilinearForm,
#  SymplecticForm, TransformForm, UnitaryForm, VerticalJoin, mylog

#  Defines: BlockPowers, ConjIntoSU, GammaOdimEven, GammaOdimOdd, GammaOsOdd,
#  GammaSU, GammaSp, GammaUMeetOmega, GammaUMeetSp, MatToQ, mylog

DeclareGlobalFunction("BlockPowers@");

DeclareGlobalFunction("ConjIntoSU@");

DeclareGlobalFunction("GammaOdimEven@");

DeclareGlobalFunction("GammaOdimOdd@");

DeclareGlobalFunction("GammaOsOdd@");

DeclareGlobalFunction("GammaSU@");

DeclareGlobalFunction("GammaSp@");

DeclareGlobalFunction("GammaUMeetOmega@");

DeclareGlobalFunction("GammaUMeetSp@");

DeclareGlobalFunction("MatToQ@");

InstallGlobalFunction(MatToQ@,
function(A,q)
#  /out: raise every element of matrix A to q-th power
local B,i,j;
  B:=0 #CAST MatrixAlgebra(BaseRing(A),Length(A))
    ;
  for i in [1..Length(A)] do
    for j in [1..Ncols(A)] do
      B[i][j]:=A[i][j]^q;
    od;
  od;
  return B;
end);

mylog@:=function(z,x)
if x=0 then
    return -1;
  else
    return Log(z,x);
  fi;
end;
;
#  ***************************************************************
#  This makes a block matrix, with all blocks either zero or powers of
#  block_matrix, where the (i, j)-th block is block_matrix^i iff
#  source_matrix[i][j] = z^i.
InstallGlobalFunction(BlockPowers@,
function(block_matrix,source_matrix,pow)
local K,dim,final,i,j,mats,mp,mpp,power,prim,rowmat,z,zero;
  prim:=ValueOption("prim");
  if prim=fail then
    prim:=false;
  fi;
  dim:=Length(source_matrix);
  zero:=MatrixByEntries(BaseRing(block_matrix),Length(block_matrix)
   ,Length(block_matrix),[]);
  mats:=# [*-list:
  [];
  K:=BaseRing(source_matrix);
  if prim then
    z:=PrimitiveElement(K);
  else
    mp:=MinimalPolynomial(block_matrix);
    mpp:=mp #CAST PolynomialRing(K)
      ;
    z:=RootsOfUPol(mpp)[1][1];
  fi;
  for i in [1..dim] do
    for j in [1..dim] do
      power:=mylog@(z,source_matrix[i][j]);
      if power=-1 then
        Add(mats,zero);
      else
        Add(mats,block_matrix^(power*pow));
      fi;
    od;
  od;
  for i in [1..dim] do
    rowmat:=mats[(i-1)*dim+1];
    for j in [2..dim] do
      rowmat:=HorizontalJoin(rowmat,mats[(i-1)*dim+j]);
    od;
    if i=1 then
      final:=rowmat;
    else
      final:=VerticalJoin(final,rowmat);
    fi;
  od;
  return final;
end);

#  *************************************************************
#  Makes Sp(d/s, q^s).s \leq Sp(d, q).
InstallGlobalFunction(GammaSp@,
function(d,q,s)
local A,B,C,bool,dim,form,frob,gammal1,grp,mat,normaliser,singer,sp1,sp2;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,d mod s=0);
  dim:=QuoInt(d,s);
  Assert(1,IsEvenInt(dim));
  #  else Sp(dim, q^s) does not exist.
  gammal1:=GammaL1@(s,q);
  singer:=gammal1.1;
  frob:=gammal1.2;
  sp1:=SP(dim,q^s).1;
  sp2:=SP(dim,q^s).2;
  #  "putting singer cycle as block into gens for Sp(dim, p)";
  #  we use the fact that Sp(d, q).1 is Diag[z, 1, \ldots, z^-1]
  A:=BlockPowers@(singer,sp1,1);
  B:=BlockPowers@(singer,sp2,1);
  C:=DirectSumMat(List([1..dim],i->frob));
  grp:=SubStructure(SL(d,q),A,#TODO CLOSURE
    B,C);
  # =v= MULTIASSIGN =v=
  form:=SymplecticForm@(grp);
  bool:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,bool);
  mat:=CorrectForm(form,d,q,"symplectic");
  if normaliser then
    grp:=SubStructure(GL(d,q),grp,#TODO CLOSURE
      NormSpMinusSp@(d,q));
  fi;
  return grp^mat;
end);

#  ************************************************************
InstallGlobalFunction(GammaUMeetSp@,
function(d,q)
#  /out:assert IsOdd(q); orthogonal
local 
   A,B,C,bool,conjmat,epsilon,f,fac,frob,frob_diag,frob_scal,gammal1,grp,gu,gu1,
   gu2,half,mock_scalar,normaliser,power,sc,two_power,z,zero;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  half:=QuoInt(d,2);
  gammal1:=GammaL1@(2,q);
  epsilon:=gammal1.1;
  frob:=gammal1.2;
  #  "frob is", frob;
  zero:=MatrixByEntries(GF(q),2,2,[]);
  gu1:=GU(half,q).1;
  gu2:=GU(half,q).2;
  #  first we make a group isomorphic to GU(half, q).
  A:=BlockPowers@(epsilon,gu1,1) #CAST GL(d,q)
    ;
  B:=BlockPowers@(epsilon,gu2,1) #CAST GL(d,q)
    ;
  gu:=SubStructure(GL(d,q),A,#TODO CLOSURE
    B);
  #  now we want to extend by the field automorphism x->x^q,
  #  multiplied by whatever power of epsilon will give it
  #  determinant 1, as an element of GL(2, q).
  frob_diag:=DirectSumMat(List([1..half],i->frob));
  #  we have to multiply the frobenius thingy by a "scalar" to get
  #  it to have determinant 1 on each block.
  fac:=CollectedFactors(q+1);
  if IsOddInt(q) then
    two_power:=2^fac[1][2];
    #  safe because q must be odd.
  else
    two_power:=1;
  fi;
  power:=QuoInt((q^2-1),(two_power*2));
  mock_scalar:=epsilon^power;
  #  "mock_scalar is", mock_scalar;
  frob_scal:=DirectSumMat(List([1..half],i->mock_scalar));
  C:=frob_diag*frob_scal;
  #  following assertion is only in for testing purposes.
  #  assert not C in gu;
  grp:=SubStructure(GL(d,q),gu,#TODO CLOSURE
    C);
  # =v= MULTIASSIGN =v=
  f:=SymplecticForm@(grp);
  bool:=f.val1;
  f:=f.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,bool);
  #  "original form is", f;
  conjmat:=CorrectForm(f,d,q,"symplectic") #CAST GL(d,q)
    ;
  if normaliser then
    z:=PrimitiveElement(GF(q^2));
    sc:=ScalarMat(half,z);
    grp:=SubStructure(GL(d,q),grp,#TODO CLOSURE
      BlockPowers@(epsilon,sc,1) #CAST GL(d,q)
      );
  fi;
  return grp^conjmat;
end);

#  ********************************************************************
InstallGlobalFunction(ConjIntoSU@,
function(grp,d,q)
local bool,f,f2,mat1,mat2;
  # =v= MULTIASSIGN =v=
  f:=UnitaryForm(grp);
  bool:=f.val1;
  f:=f.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,bool);
  #  "f =", f;
  mat1:=CorrectForm(f,d,q^2,"unitary");
  # =v= MULTIASSIGN =v=
  f2:=UnitaryForm(SU(d,q));
  bool:=f2.val1;
  f2:=f2.val2;
  # =^= MULTIASSIGN =^=
  mat2:=CorrectForm(f2,d,q^2,"unitary");
  return mat1 #CAST GL(d,q^2)
    *mat2 #CAST GL(d,q^2)
    ^-1;
end);

#  *********************************************************************
InstallGlobalFunction(GammaSU@,
function(d,q,s)
local 
   detmat,dim,fac,frob,frobmat,gammal1,general,grp,gu1,mat,normaliser,sc,singer,
   singerGU,singerSU,su1,su2,sugen1,sugen2,z;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  fac:=CollectedFactors(q);
  Assert(1,Size(fac)=1);
  Assert(1,d > 2);
  Assert(1,d mod s=0);
  Assert(1,not s=2);
  #  o.w. don't get subgroup
  if not IsPrimeInt(s) then
    Info(InfoWarning,1,
      "warning: this function was designed for PRIME field extensions");
  fi;
  if normaliser then
    general:=true;
  fi;
  dim:=QuoInt(d,s);
  gammal1:=GammaL1@(s,q^2);
  singer:=gammal1.1;
  singerGU:=singer^(q^s-1);
  #  has order (q^s+1).
  #  "Order(Det(singerGU))=", Order(Determinant(singerGU));
  singerSU:=singerGU^(q+1);
  #  |Det(GU)| = q+1;
  #  "Order singer SU = ", Order(singerSU);
  frob:=gammal1.2;
  if dim=1 then
    # rewritten select statement
    if general then
      grp:=SubStructure(GL(d,q^2),singerGU,#TODO CLOSURE
        frob);
    else
      grp:=SubStructure(GL(d,q^2),singerSU,#TODO CLOSURE
        frob);
    fi;
    mat:=ConjIntoSU@(grp,d,q);
    if normaliser then
      z:=PrimitiveElement(GF(q^2));
      sc:=ScalarMat(d,z);
      grp:=SubStructure(GL(d,q^2),grp,#TODO CLOSURE
        sc);
    fi;
    return grp^mat;
  fi;
  su1:=SU(dim,q^s).1;
  su2:=SU(dim,q^s).2;
  gu1:=GU(dim,q^s).1;
  sugen1:=BlockPowers@(singer,su1,1);
  sugen2:=BlockPowers@(singer,su2,1);
  # rewritten select statement
  if general then
    detmat:=BlockPowers@(singer,gu1,1);
  else
    detmat:=BlockPowers@(singer,gu1,q+1);
  fi;
  frobmat:=DirectSumMat(List([1..dim],i->frob));
  grp:=SubStructure(GL(d,q^2),sugen1,#TODO CLOSURE
    sugen2,detmat,frobmat);
  mat:=ConjIntoSU@(grp,d,q);
  if normaliser then
    z:=PrimitiveElement(GF(q^2));
    sc:=ScalarMat(d,z);
    grp:=SubStructure(GL(d,q^2),grp,#TODO CLOSURE
      sc);
  fi;
  return grp^mat;
end);

#  *************************************************************
#  Make O^e(d/s, q^s).s \leq O^e(d, q).
#  It is convenient to split into various cases.
InstallGlobalFunction(GammaOsOdd@,
function(d,q,s,sign)
local 
   cmat1,cmat2,dim,form1,forms,frob,frobgen,gammal1,general,gens,ggens,ggrp,go1,
   grp,isf,ngo1,normaliser,om1,sgens,sgrp,sign1,singer,so1,special,tmat,z;
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
  Assert(1,d mod s=0);
  Assert(1,(IsOddInt(d) and sign=0) or (IsEvenInt(d) and sign in Set([-1,1])));
  Assert(1,IsEvenInt(d) or IsOddInt(q));
  Assert(1,IsOddInt(s));
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  dim:=QuoInt(d,s);
  Assert(1,dim > 1);
  # rewritten select statement
  if IsEvenInt(dim) then
    sign1:=sign;
  else
    sign1:=0;
  fi;
  # rewritten select statement
  if sign1=0 then
    go1:=GO(dim,q^s);
  else
    # rewritten select statement
    if sign1=1 then
      go1:=GOPlus(dim,q^s);
    else
      go1:=GOMinus(dim,q^s);
    fi;
  fi;
  # rewritten select statement
  if sign1=0 then
    so1:=SO(dim,q^s);
  else
    # rewritten select statement
    if sign1=1 then
      so1:=SOPlus(dim,q^s);
    else
      so1:=SOMinus(dim,q^s);
    fi;
  fi;
  # rewritten select statement
  if sign1=0 then
    om1:=Omega(dim,q^s);
  else
    # rewritten select statement
    if sign1=1 then
      om1:=OmegaPlus(dim,q^s);
    else
      om1:=OmegaMinus(dim,q^s);
    fi;
  fi;
  #  In the minus case we need to conjugate to get the form fixed to be in the
  #  subfield
  if sign=-1 then
    if IsEvenInt(q) then
      # =v= MULTIASSIGN =v=
      form1:=QuadraticForm(go1);
      isf:=form1.val1;
      form1:=form1.val2;
      # =^= MULTIASSIGN =^=
      # =v= MULTIASSIGN =v=
      forms:=QuadraticForm(GOMinus(dim,q));
      isf:=forms.val1;
      forms:=forms.val2;
      # =^= MULTIASSIGN =^=
      forms:=forms #CAST MatrixAlgebra(GF(q^s),dim)
        ;
    else
      # =v= MULTIASSIGN =v=
      form1:=SymmetricBilinearForm(go1);
      isf:=form1.val1;
      form1:=form1.val2;
      # =^= MULTIASSIGN =^=
      # =v= MULTIASSIGN =v=
      forms:=SymmetricBilinearForm(GOMinus(dim,q));
      isf:=forms.val1;
      forms:=forms.val2;
      # =^= MULTIASSIGN =^=
      forms:=forms #CAST MatrixAlgebra(GF(q^s),dim)
        ;
    fi;
    cmat1:=CorrectForm(form1,dim,q^s,"orth-");
    cmat2:=CorrectForm(forms,dim,q^s,"orth-");
    tmat:=(cmat1*cmat2^-1) #CAST GL(dim,q^s)
      ;
    go1:=go1^tmat;
    so1:=so1^tmat;
    om1:=om1^tmat;
  fi;
  gammal1:=GammaL1@(s,q);
  singer:=gammal1.1;
  frob:=gammal1.2;
  gens:=List([1..Ngens(om1)],i->BlockPowers@(singer,om1.i,1));
  sgens:=List([1..Ngens(so1)],i->BlockPowers@(singer,so1.i,1));
  ggens:=List([1..Ngens(go1)],i->BlockPowers@(singer,go1.i,1));
  frobgen:=DirectSumMat(List([1..dim],i->frob));
  grp:=SubStructure(SL(d,q),gens,#TODO CLOSURE
    frobgen);
  sgrp:=SubStructure(SL(d,q),sgens,#TODO CLOSURE
    frobgen);
  ggrp:=SubStructure(GL(d,q),ggens,#TODO CLOSURE
    frobgen);
  #  We will need to transform our generators to fix Magma's quadratic form.
  tmat:=TransformForm(ggrp);
  if normaliser then
    if IsEvenInt(d) and IsOddInt(q) then
      ngo1:=NormGOMinusGO@(dim,q,sign) #CAST GL(dim,q^s)
        ;
      ggrp:=SubStructure(GL(d,q),ggrp,#TODO CLOSURE
        BlockPowers@(singer,ngo1,1));
    elif q > 3 then
      z:=PrimitiveElement(GF(q));
      ggrp:=SubStructure(GL(d,q),ggrp,#TODO CLOSURE
        ScalarMat(d,z));
    fi;
  fi;
  if general then
    return ggrp^tmat;
  fi;
  if special then
    return sgrp^tmat;
  fi;
  return grp^tmat;
end);

InstallGlobalFunction(GammaOdimOdd@,
function(d,q,sign)
local 
   absirred,det,dim,frob,frobgen,gammal1,general,gens,ggrp,go1,gsl,gsl2,m1,ngo,
   normaliser,om1,ord,s,scal,scal2,sign1,singer,so1,special,tmat;
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
  Assert(1,IsEvenInt(d) and sign in Set([-1,1]));
  Assert(1,IsOddInt(q));
  s:=2;
  dim:=QuoInt(d,s);
  Assert(1,IsOddInt(dim));
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  sign1:=0;
  absirred:=(sign=1 and q mod 4=1) or (sign=-1 and q mod 4=3);
  #  in these cases group constructed will be absolutely irreducible
  #  equivalent to D = square (KL).
  go1:=GO(dim,q^s);
  so1:=SO(dim,q^s);
  om1:=Omega(dim,q^s);
  gammal1:=GammaL1@(s,q);
  singer:=gammal1.1;
  frob:=gammal1.2;
  gens:=List([1..Ngens(om1)],i->BlockPowers@(singer,om1.i,1));
  frobgen:=DirectSumMat(List([1..dim],i->frob));
  #  det = -1
  scal:=ScalarMat(GF(q^2),dim,PrimitiveElement(GF(q^2)));
  if absirred then
    #  frobgen has determinant -1, so we need to multiply by a scalar in GF(q^2)
     
    scal2:=BlockPowers@(singer,scal,1);
    det:=DeterminantMat(scal2);
    scal2:=scal2^(QuoInt(Order(det),2));
    frobgen:=frobgen*scal2;
    #  get rid of any odd parts of frobgen
    ord:=Order(frobgen);
    Assert(1,fac[1][1]^fac[1][2]=4);
    #  POSTPONED `where'
    fac:=CollectedFactors(ord);
    frobgen:=frobgen^(QuoInt(ord,4));
  fi;
  ggrp:=SubStructure(GL(d,q),gens,#TODO CLOSURE
    frobgen);
  #  We will need to transform our generators to fix Magma's quadratic form.
  tmat:=TransformForm(ggrp);
  gens:=List(gens,g->g^tmat);
  #  locate an element in SO(dim,q^2) - Omega(dim,q^2).
  gsl:=SOMinusOmega@(dim,q^2,sign1);
  gsl2:=BlockPowers@(singer,gsl,1) #CAST GL(d,q)
    ;
  gsl2:=gsl2^tmat;
  frobgen:=(frobgen #CAST GL(d,q)
    )^tmat;
  if absirred then
    if not InOmega@(frobgen,d,q,sign) then
      #  "adjusted frobgen";
      frobgen:=frobgen*gsl2;
    fi;
    Assert(1,InOmega@(frobgen,d,q,sign));
    Add(gens,frobgen);
    if special then
      Add(gens,gsl2);
    fi;
  else
    m1:=ScalarMat(d,(-1) #CAST GF(q)
      );
    if not InOmega@(gsl2,d,q,sign) then
      #  "sign wrong";
      gsl2:=m1*gsl2;
    fi;
    Assert(1,InOmega@(gsl2,d,q,sign));
    Add(gens,gsl2);
    if special then
      Add(gens,m1);
    fi;
    if general then
      Add(gens,frobgen);
    fi;
  fi;
  if normaliser then
    ngo:=BlockPowers@(singer,scal,1);
    ngo:=(ngo #CAST GL(d,q)
      )^tmat;
    ngo:=ngo^(QuoInt((q+1),2));
    Add(gens,ngo);
  fi;
  return SubStructure(GL(d,q),gens);
  #  if abs irred then c=2, go; o.w. c=1.
end);

InstallGlobalFunction(GammaOdimEven@,
function(d,q,sign)
local 
   biggens,biggp1,biggrp,cform,cgens,cmat1,dim,form,frob,frobgen,gammal1,
   general,gens,ggl,ggl2,gp1,gsl,gsl2,isf,ngo,normaliser,s,scal,sign1,singer,
   special,tmat,z;
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
  Assert(1,IsEvenInt(d) and sign in Set([-1,1]));
  s:=2;
  dim:=QuoInt(d,s);
  Assert(1,IsEvenInt(dim));
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  sign1:=sign;
  # rewritten select statement
  if sign1=1 then
    biggp1:=GOPlus(dim,q^s);
  else
    biggp1:=GOMinus(dim,q^s);
  fi;
  # rewritten select statement
  if sign1=1 then
    gp1:=OmegaPlus(dim,q^s);
  else
    gp1:=OmegaMinus(dim,q^s);
  fi;
  #  In the -1 case, the field automorphism will change the form, so
  #  we will need to conjugate it back.
  if sign=-1 then
    if IsEvenInt(q) then
      # =v= MULTIASSIGN =v=
      form:=QuadraticForm(biggp1);
      isf:=form.val1;
      form:=form.val2;
      # =^= MULTIASSIGN =^=
    else
      # =v= MULTIASSIGN =v=
      form:=SymmetricBilinearForm(biggp1);
      isf:=form.val1;
      form:=form.val2;
      # =^= MULTIASSIGN =^=
    fi;
    cform:=MatToQ@(form,q);
    cmat1:=TransformForm(cform,"orth-");
  fi;
  #  We need elements of ggl, gsl in sl-omega
  gsl:=SOMinusOmega@(dim,q^2,sign1);
  if IsOddInt(q) then
    ggl:=GOMinusSO@(dim,q^2,sign1);
  fi;
  gammal1:=GammaL1@(s,q);
  singer:=gammal1.1;
  frob:=gammal1.2;
  gens:=List([1..Ngens(gp1)],i->BlockPowers@(singer,gp1.i,1));
  biggens:=List([1..Ngens(biggp1)],i->BlockPowers@(singer,biggp1.i,1));
  gsl2:=BlockPowers@(singer,gsl,1) #CAST GL(d,q)
    ;
  if IsOddInt(q) then
    ggl2:=BlockPowers@(singer,ggl,1) #CAST GL(d,q)
      ;
  fi;
  frobgen:=DirectSumMat(List([1..dim],i->frob)) #CAST GL(d,q)
    ;
  if sign=-1 then
    frobgen:=frobgen*BlockPowers@(singer,cmat1,1) #CAST GL(d,q)
      ;
    Assert(1,DeterminantMat(frobgen)=(-1) #CAST GF(q)
      );
    #   not really why that works - must be just the way TransformForm works.
  fi;
  biggrp:=SubStructure(GL(d,q),biggens,#TODO CLOSURE
    frobgen);
  #  We will need to transform our generators to fix Magma's quadratic form.
  tmat:=TransformForm(biggrp);
  cgens:=List(gens,g->g^tmat);
  gsl2:=gsl2^tmat;
  #  find extra generator in Omega
  if IsOddInt(q) then
    ggl2:=ggl2^tmat;
    if InOmega@(ggl2,d,q,sign) then
      Add(cgens,ggl2);
    else
      Assert(1,InOmega@(ggl2*gsl2,d,q,sign));
      Add(cgens,ggl2*gsl2);
    fi;
    if special then
      Add(cgens,gsl2);
    fi;
  else
    Assert(1,InOmega@(gsl2,d,q,sign));
    Add(cgens,gsl2);
  fi;
  frobgen:=frobgen^tmat;
  if sign=1 then
    #  need Frobenius generator also
    if InOmega@(frobgen,d,q,sign) then
      Add(cgens,frobgen);
    else
      Assert(1,InOmega@(frobgen*gsl2,d,q,sign));
      Add(cgens,frobgen*gsl2);
    fi;
  elif general or (special and IsEvenInt(q)) then
    Add(cgens,frobgen);
  fi;
  if normaliser then
    if IsOddInt(q) then
      scal:=ScalarMat(GF(q^2),dim,PrimitiveElement(GF(q^2)));
      ngo:=BlockPowers@(singer,scal,1);
      ngo:=(ngo #CAST GL(d,q)
        )^tmat;
      ngo:=ngo^(QuoInt((q+1),2));
      Add(cgens,ngo);
    elif q > 2 then
      z:=PrimitiveElement(GF(q));
      Add(cgens,ScalarMat(d,z));
    fi;
  fi;
  return SubStructure(GL(d,q),cgens);
  #  if sign=1, c=2, so (q even) or go (q odd); o.w. c=1.
end);

#   Here is a function to compute the field automorphism of OmegaMinus(d,q^2)
#  * May need it some time.
#  FFSOM := function(d,q)
#  local Om, cmat1, cmat2, isf, form, formt, cOm, cOmT, tmat;
#  Om := OmegaMinus(d,q^2);
#  if IsEven(q) then
#  isf, form := QuadraticForm(Om);
#  else
#  isf, form := SymmetricBilinearForm(Om);
#  end if;
#  cmat1 := CorrectForm(form,d,q^2,"orth-");
#  cOm := Om^cmat1;
#  cOmT :=  sub< GL(d,q^2) | [MatToQ(cOm.i, q) : i in [1..Ngens(cOm)]] >;
#  if IsEven(q) then
#  isf, formt := QuadraticForm(cOmT);
#  else
#  isf, formt := SymmetricBilinearForm(cOmT);
#  end if;
#  cmat2 := CorrectForm(formt,d,q^2,"orth-");
#  tmat := cmat2*cmat1^-1;
#  return hom< Om -> Om |
#  [ tmat^-1*MatToQ(cOm.i, q)*tmat : i in [1..Ngens(Om)]] >;
#  end function;

#  ************************************************************
InstallGlobalFunction(GammaUMeetOmega@,
function(d,q)
local 
   epsilon,frob,frob_diag,gammal1,general,gens,grp,gu1,gu1e,gun,gune,half,
   normaliser,sign,special,su1,su1e,su2,su2e,tmat,x,zero;
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
  Assert(1,IsEvenInt(d));
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  half:=QuoInt(d,2);
  # rewritten select statement
  if IsEvenInt(half) then
    sign:=1;
  else
    sign:=-1;
  fi;
  gammal1:=GammaL1@(2,q);
  epsilon:=gammal1.1;
  frob:=gammal1.2;
  zero:=MatrixByEntries(GF(q),2,2,[]);
  gu1:=GU(half,q).1;
  #  generates GU mod SU
  su1:=SU(half,q).1;
  su2:=SU(half,q).2;
  gu1e:=BlockPowers@(epsilon,gu1,1) #CAST GL(d,q)
    ;
  su1e:=BlockPowers@(epsilon,su1,1) #CAST GL(d,q)
    ;
  su2e:=BlockPowers@(epsilon,su2,1) #CAST GL(d,q)
    ;
  #  all of the above have determinant 1
  #  now we want to extend by the field automorphism x->x^q,
  frob_diag:=DirectSumMat(List([1..half],i->frob)) #CAST GL(d,q)
    ;
  #  This already seems to fix the right type of form - it has determinant
  #  -1 (or is in SO-Omega when q=2) when half is odd.
  grp:=SubStructure(GL(d,q),gu1e,#TODO CLOSURE
    su1e,su2e,frob_diag);
  #  We will need to transform our generators to fix Magma's quadratic form.
  tmat:=TransformForm(grp);
  #  Now just need to intersect with Omega.
  gens:=List([su1e,su2e],g->g^tmat);
  x:=gu1e^tmat;
  Assert(1,DeterminantMat(x)=1);
  if special then
    Add(gens,x);
  elif InOmega@(x,d,q,sign) then
    Assert(1,IsEvenInt(q));
    Add(gens,x);
  else
    Assert(1,(InOmega@(x^2,d,q,sign)));
    Assert(1,IsOddInt(q));
    Add(gens,x^2);
  fi;
  frob_diag:=frob_diag^tmat;
  if sign=1 then
    if special or InOmega@(frob_diag,d,q,sign) then
      Add(gens,frob_diag);
    else
      Assert(1,(InOmega@(x*frob_diag,d,q,sign)));
      Add(gens,frob_diag*x);
    fi;
  elif (general and IsOddInt(q)) or (special and IsEvenInt(q)) then
    Add(gens,frob_diag);
  fi;
  if normaliser then
    gun:=ScalarMat(half,PrimitiveElement(GF(q^2)));
    gune:=BlockPowers@(epsilon,gun,1) #CAST GL(d,q)
      ;
    Add(gens,gune^tmat);
  fi;
  return SubStructure(GL(d,q),gens);
  #  if sign=1 (i.e. half even), c=2 so(q even ) go(q odd); o.w. c=1.
end);


