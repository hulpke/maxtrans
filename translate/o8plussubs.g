#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: ATtoG1, ActionGenerator, ActionGroup, Alt, Append,
#  BaseRing, Constituents, CorrectForm, DJ, Determinant, DiagonalJoin,
#  DiagonalMatrix, Dimension, Eltseq, ExtendBasis, ExtractBlock, Factorisation,
#  G2, GF, GHom, GL, GModule, GOMinus, GOPlus, GU, Id, IdentityMatrix, Image,
#  IsAbsolutelyIrreducible, IsEven, IsIsomorphic, IsOdd, IsOverSmallerField,
#  IsPrime, IsSquare, KroneckerProduct, Matrix, MatrixAlgebra,
#  MatrixTensorFactors, MinimalSubmodules, Morphism, Ngens, O8qMapToCover, Om,
#  OmegaMinus, OmegaPlus, Order, PermutationMatrix, PolynomialRing, Position,
#  PrimitiveElement, QF, QuadraticForm, Random, RecogniseClassical, Roots, SL,
#  ScalarMatrix, Solution, SquareRoot, Sym, SymmetricBilinearForm,
#  TransformForm, Transpose, VectorSpace, ZeroMatrix, phi

#  Defines: KlLine15, KlLine22, KlLine26, KlLine4, KlLine51, KlLine61, KlLine7,
#  MatrixTensorFactors, O8qMapToCover, TwoO7, TwoO72, TwoOminus8, TwoOminus82

DeclareGlobalFunction("KlLine15@");

DeclareGlobalFunction("KlLine22@");

DeclareGlobalFunction("KlLine26@");

DeclareGlobalFunction("KlLine4@");

DeclareGlobalFunction("KlLine51@");

DeclareGlobalFunction("KlLine61@");

DeclareGlobalFunction("KlLine7@");

DeclareGlobalFunction("TwoO7@");

DeclareGlobalFunction("TwoO72@");

DeclareGlobalFunction("TwoOminus8@");

DeclareGlobalFunction("TwoOminus82@");

InstallGlobalFunction(TwoOminus8@,
function(q)
#  /out: 2.O^-(8,q) as C9-subgroup of O^+(8,q^2) 
local G;
  G:=Spin8Minus@(q);
  G:=ActionGroup(Constituents(GModule(G))[1]);
  return G^TransformForm(G);
end);

InstallGlobalFunction(TwoO7@,
function(q)
#  /out: 2.O^7(q) as C9-subgroup of O^+(8,q) 
local G,H,t;
  G:=Spin8Minus@(q);
  G:=ActionGroup(Constituents(GModule(G))[1]);
  # rewritten select statement
  if q=2 then
    H:=SubStructure(G,G.1*G.5,#TODO CLOSURE
      G.3,G.4,G.6);
  else
    H:=SubStructure(G,G.1*G.5,#TODO CLOSURE
      G.3,G.4,G.6,G.7);
  fi;
  # =v= MULTIASSIGN =v=
  H:=IsOverSmallerField(H);
  t:=H.val1;
  H:=H.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,t);
  return H^TransformForm(H);
end);

MatrixTensorFactors@:=function(A,m,n)
#  /out: A should be an (mn) x (mn) matrix of form KroneckerProduct(B,C),
#  * for mxm and nxn matrices B,C. Return B,C (up to multiplication by scalar).

local B,BC,C,K,fac,haveC,i,j,k,l,ni,nj;
  K:=BaseRing(A);
  B:=ZeroMatrix@(K,m,m);
  C:=ZeroMatrix@(K,n,n);
  haveC:=false;
  ni:=0;
  nj:=0;
  fac:=0;
  for i in [1..m] do
    for j in [1..m] do
      BC:=ExtractBlock(A,(i-1)*n+1,(j-1)*n+1,n,n);
      if haveC then
        B[i][j]:=BC[ni][nj]*fac;
      elif BC<>ZeroMatrix@(K,n,n) then
        C:=BC;
        haveC:=true;
        for k in [1..n] do
          for l in [1..n] do
            if C[k][l]<>0 then
              ni:=k;
              nj:=l;
              fac:=C[k][l]^-1;
              break k;
            fi;
          od;
        od;
        B[i][j]:=BC[ni][nj]*fac;
      fi;
    od;
  od;
  Assert(1,A=KroneckerProduct(B,C));
  return rec(val1:=B,
    val2:=C);
end;
;
O8qMapToCover@:=function(q)
#  /out: return map from Magma rep of O^-(8,q) to 2.O^-(8,q) over GF(q^2), q
#  odd.
#  * may be wrong by scalar factor -1, but correct on elements of odd order.

local 
   AT,ATtoG1,C,CT,G,G1,G2,G56,G8,G8g,M28,M28g,M56,M56b,M56bg,M56btoM56,M8,M8b,
   M8btoM8,M8g,MT,SG56,SG8,SG8toG1,SM56,T,TT,V,extbas,form,formi,gh,imM28,imM56,
   imM56b,imM8,inds,isf,isit,ng,trans28,trans28i,trans56,trans56i,trans64;
  Assert(1,IsOddInt(q));
  G:=Spin8Minus@(q);
  C:=Constituents(GModule(G));
  G1:=ActionGroup(C[1]);
  #  domain of returned map
  G2:=ActionGroup(C[2]);
  ng:=Ngens(G);
  #  form tensor product of two 8-dimensional modules
  T:=GModule(G,List([1..ng],i->KroneckerProduct(G1.i,G2.i)));
  AT:=ActionGroup(T);
  #  first construct map from AT to G1
  # =v= MULTIASSIGN =v=
  form:=SymmetricBilinearForm(G1);
  isf:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,isf);
  formi:=form^-1;
  ATtoG1:=function(m)
  local formx,mu,mum,x,y;
    # =v= MULTIASSIGN =v=
    y:=MatrixTensorFactors@(m,8,8);
    x:=y.val1;
    y:=y.val2;
    # =^= MULTIASSIGN =^=
    #  x should fix form mod scalars
    formx:=x*form*TransposedMat(x);
    mum:=formx*formi^-1;
    mu:=mum[1][1];
    Assert(1,mum=ScalarMat(8,mu));
    x:=x*ScalarMat(8,SquareRoot(mu^-1));
    if IsOddInt(Order(m)) and IsEvenInt(Order(x)) then
      x:=x*ScalarMat(8,-1);
    fi;
    return x;
  end;
  ;
  MT:=MinimalSubmodules(T);
  M8:=Filtered(MT,m->DimensionOfMatrixGroup(m)=8)[1];
  M56:=Filtered(MT,m->DimensionOfMatrixGroup(m)=56)[1];
  imM8:=Morphism(M8,T);
  imM56:=Morphism(M56,T);
  trans64:=MatrixByEntries(Concatenation(List([1..8],i->imM8[i]),List([1..56]
   ,i->imM56[i])));
  #  Need horrible hack to deal with case when some action generators
  #  of M8 are trivial or equal.
  G8:=ActionGroup(M8);
  G8g:=List([1..Ngens(G8)],i->G8.i);
  # rewritten select statement
  if IdentityMatrix(GF(q^2),8) then
    inds:=List([1..ng],i->ag=0);
  else
    inds:=List([1..ng],i->ag=Position(G8g,ag));
  fi;
  #  POSTPONED `where'
  ag:=ActionGenerator(M8,i);
  # =v= MULTIASSIGN =v=
  SG8:=IsOverSmallerField(G8);
  isf:=SG8.val1;
  SG8:=SG8.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,isf);
  SG8:=SG8^TransformForm(SG8);
  #  should not be standard copy of O^-(8,q);
  # rewritten select statement
  if 0 then
    M8g:=List([1..ng],i->inds[i]=IdentityMatrix(GF(q^2),8));
  else
    M8g:=List([1..ng],i->inds[i]=SG8.inds[i]);
  fi;
  M8b:=GModule(G,M8g);
  # =v= MULTIASSIGN =v=
  M8btoM8:=IsIsomorphic(M8b,M8);
  isit:=M8btoM8.val1;
  M8btoM8:=M8btoM8.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,isit);
  #  more efficient to go back to working over GF(q)
  # rewritten select statement
  if 0 then
    M8g:=List([1..ng],i->inds[i]=IdentityMatrix(GF(q),8));
  else
    M8g:=List([1..ng],i->inds[i]=SG8.inds[i]);
  fi;
  #  Our next aim is to construct the homomorphism SG8 -> SG56
  #  We construct SG56 from SG8 in following.
  TT:=GModule(G,List([1..ng],i->KroneckerProduct(M8g[i],M8g[i])));
  CT:=Constituents(TT);
  M28:=Filtered(CT,c->DimensionOfMatrixGroup(c)=28)[1];
  M28:=MinimalSubmodules(TT,M28)[1];
  imM28:=Morphism(M28,TT);
  V:=VectorSpace(GF(q),64);
  extbas:=MatrixByEntries(ExtendBasis(List([1..28],i->imM28[i] #CAST V
    ),V));
  trans28:=ExtractBlock(extbas,1,1,28,64);
  trans28i:=ExtractBlock(extbas^-1,1,1,64,28);
  #   Get from element g in SG8 to element in action group of M28 by
  #   g -> trans28 * KroneckerProduct(g,g) * trans28i
  #   and extracting
  M28g:=List([1..ng],i->ActionGenerator(M28,i));
  TT:=GModule(G,List([1..ng],i->KroneckerProduct(M8g[i],M28g[i])));
  #  get 56-dimensional module M56 over GF(q)
  G56:=ActionGroup(M56);
  # =v= MULTIASSIGN =v=
  SG56:=IsOverSmallerField(G56);
  isf:=SG56.val1;
  SG56:=SG56.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,isf);
  # rewritten select statement
  if 0 then
    SM56:=GModule(G,List([1..ng],i->inds[i]=IdentityMatrix(GF(q),56)));
  else
    SM56:=GModule(G,List([1..ng],i->inds[i]=SG56.inds[i]));
  fi;
  gh:=GHom(SM56,TT);
  #  time CT := Constituents(TT);
  #  M56b := [ c : c in CT | Dimension(c) eq 56 ][1];
  #  time M56b := MinimalSubmodules(TT, M56b)[1];
  M56b:=Image(gh.1);
  imM56:=Morphism(M56b,TT);
  V:=VectorSpace(GF(q),224);
  extbas:=MatrixByEntries(ExtendBasis(List([1..56],i->imM56[i] #CAST V
    ),V));
  trans56:=ExtractBlock(extbas,1,1,56,224);
  trans56i:=ExtractBlock(extbas^-1,1,1,224,56);
  #   Get from element g in G8 mapping to gg in action group of M28
  #   to action group of M56 by
  #   g -> trans56 * KroneckerProduct(g,gg) * trans56i;
  #  now need to get M56b back over to GF(q^2)
  M56bg:=List([1..ng],i->ActionGenerator(M56b,i));
  M56b:=GModule(G,M56bg);
  # =v= MULTIASSIGN =v=
  M56btoM56:=IsIsomorphic(M56b,M56);
  isit:=M56btoM56.val1;
  M56btoM56:=M56btoM56.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,isit);
  #  Now we are ready to define the required map!
  SG8toG1:=function(g)
  #  /out:g in SG8 = Omega^-(8,q)
  local g,gg,ggg,m64;
    gg:=trans28*KroneckerProduct(g,g)*trans28i;
    ggg:=trans56*KroneckerProduct(g,gg)*trans56i;
    g:=g #CAST MatrixAlgebra(GF(q^2),8)
      ;
    ggg:=ggg #CAST MatrixAlgebra(GF(q^2),56)
      ;
    m64:=DirectSumMat(M8btoM8^-1*g*M8btoM8,M56btoM56^-1*ggg*M56btoM56);
    m64:=trans64^-1*m64*trans64;
    return ATtoG1(m64);
  end;
  ;
  return SG8toG1;
end;
;
InstallGlobalFunction(TwoO72@,
function(q)
#  /out: 2.O^7(q).2 as C9-subgroup of normaliser in GL(8,q) of O^+(8,q) 
local H,phi,t;
  H:=NonDegenStabOmega@(8,q,-1,7,0);
  phi:=O8qMapToCover@(q);
  H:=SubStructure(GL(8,q^2),List([1..Ngens(H)],i->phi(H.i)));
  # =v= MULTIASSIGN =v=
  H:=IsOverSmallerField(H:Scalars:=true);
  t:=H.val1;
  H:=H.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,t);
  H:=H^TransformForm(H:Scalars:=true);
  return SubStructure(GL(8,q),H,#TODO CLOSURE
    ScalarMat(8,PrimitiveElement(GF(q))));
end);

InstallGlobalFunction(TwoOminus82@,
function(q)
#  /out: 2.O^-(8,q).2 as C9-subgroup of normaliser in GL(8,q^2) of O^+(8,q^2) 
local G,H,Hg,Hgc,Hgc2,Hgc2i,Hgci,Hgi,M,M2i,Mi,f,g,go,isi,ngo,phi,x;
  go:=GOMinusSO@(8,q,-1);
  ngo:=NormGOMinusGO@(8,q,-1);
  G:=OmegaMinus(8,q);
  #  need generating set of odd order elements
  repeat
    g:=Random(G);
    f:=CollectedFactors(Order(g));
    
  until Size(f) > 1 or (Size(f)=1 and f[1][1]<>2);
  if f[1][1]=2 then
    g:=g^(2^f[1][2]);
  fi;
  H:=SubStructure(GL(8,q),g,#TODO CLOSURE
    g^Random(G));
  while not IsAbsolutelyIrreducible(H) do
    H:=SubStructure(GL(8,q),H,#TODO CLOSURE
      g^Random(G));
  od;
  while not RecogniseClassical(H) do
    H:=SubStructure(GL(8,q),H,#TODO CLOSURE
      g^Random(G));
  od;
  Hg:=List([1..Ngens(H)],i->H.i);
  Hgc:=List(Hg,h->h^ngo);
  #  now map over to 2.O^-(8,q) in GO^+(8,q^2)
  phi:=O8qMapToCover@(q);
  Hgi:=List(Hg,h->phi(h));
  Hgci:=List(Hgc,h->phi(h));
  G:=SubStructure(GL(8,q^2),Hgi);
  M:=GModule(G);
  Mi:=GModule(G,Hgci);
  # =v= MULTIASSIGN =v=
  x:=IsIsomorphic(M,Mi);
  isi:=x.val1;
  x:=x.val2;
  # =^= MULTIASSIGN =^=
  if not isi then
    Info(InfoWarning,1,"try other one");
    Hgc2:=List(Hg,h->h^(ngo*go));
    Hgc2i:=List(Hgc2,h->phi(h));
    M2i:=GModule(G,Hgc2i);
    # =v= MULTIASSIGN =v=
    x:=IsIsomorphic(M,M2i);
    isi:=x.val1;
    x:=x.val2;
    # =^= MULTIASSIGN =^=
    Assert(1,isi);
  fi;
  G:=SubStructure(GL(8,q^2),Hgi,#TODO CLOSURE
    x);
  G:=G^TransformForm(G:Scalars:=true);
  return SubStructure(GL(8,q^2),G,#TODO CLOSURE
    ScalarMat(8,PrimitiveElement(GF(q^2))));
end);

InstallGlobalFunction(KlLine4@,
function(q)
#  /out:P_2 In IsotropicStabOmega(8, q, 3, 1) replace/out:GL(3,q) by
#  q^2:(GL(1,q)xGL(2,q))
local 
   Om,d,diag,elt,form,gen,general,gens,go,i,k,normaliser,sign,special,stab,t,u,
   v,x,y,z;
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
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  d:=8;
  k:=3;
  sign:=1;
  Om:=OmegaPlus;
  #  We need an element go in SO(d-2*k,q) - Omega.
  go:=SOMinusOmega@(d-2*k,q,sign);
  z:=PrimitiveElement(GF(q));
  form:=MatrixByEntries(GF(q),k,k,List([1..k],i->[i,k-i+1,1])) #CAST GL(k,q)
    ;
  diag:=List([1..d],i->[i,i,1]);
  gens:=[];
  #  q^2:(GL(1,q)xGL(2,q)) on <e_1..e_k>, balanced on <f_k..f_1>.
  gens:=[];
  stab:=GLStabOfNSpace@(3,q,1);
  for i in [1..Ngens(stab)] do
    gen:=stab.i;
    elt:=DirectSumMat([gen,IdentityMatrix(GF(q),d-2*k)
     ,form*TransposedMat(gen^-1)*form]);
    if IsEvenInt(q) or (IsOddInt(q) and IsSquare(DeterminantMat(gen)) or 
       InOmega@(elt,d,q,sign) or special) then
      Add(gens,elt);
      continue;
    fi;
    if d-2*k > 1 then
      elt:=DirectSumMat([gen,go,form*TransposedMat(gen^-1)*form]);
      #  gen didn't work with IdentityMatrix in middle section, so
      #  will work with element from SO\Omega.
      Add(gens,elt);
    elif elt^2<>elt^0 then
      Add(gens,elt^2);
      #  square will be in Omega
      #  elif i ne Ngens(GL(k,q)) then //only for case q=3, k>1
      #    gen := (GL(k,q).(i+1))^gen;
      #    elt := DiagonalJoin(< gen, IdentityMatrix(GF(q),d-2*k),
      #                                 form*Transpose(gen^-1)*form > );
      #    Append(~gens, elt );
    fi;
  od;
  if d-2*k > 1 then
    #   orthogonal group acting on a (d-2k) space.
    gens:=Concatenation(gens,List([1..Ngens(Om(d-2*k,q))]
     ,i->DirectSumMat([IdentityMatrix(GF(q),k),Om(d-2*k,q)
     .i,IdentityMatrix(GF(q),k)])));
    if special then
      Add(gens,DirectSumMat([IdentityMatrix(GF(q),k),SOMinusOmega@(d-2*k,q,sign)
       ,IdentityMatrix(GF(q),k)]));
    fi;
    if general and IsOddInt(q) then
      Add(gens,DirectSumMat([IdentityMatrix(GF(q),k),GOMinusSO@(d-2*k,q,sign)
       ,IdentityMatrix(GF(q),k)]));
    fi;
  fi;
  #  don't know where I got the generators below from - did I calculate them?
  if k > 1 then
    Add(gens,MatrixByEntries(GF(q),d,d,Concatenation([[d-1,1,1],[d,2,-1]],diag))
      #CAST GL(d,q)
      );
  fi;
  if (d > 2*k+2) or (d=2*k+2 and sign=1) then
    Add(gens,MatrixByEntries(GF(q),d,d,Concatenation([[k+1,1,1],[d,d-k,-1]]
     ,diag)) #CAST GL(d,q)
      );
    if d=2*k+2 and sign=1 then
      Add(gens,MatrixByEntries(GF(q),d,d,Concatenation([[k+2,1,1],[d,d-k-1,-1]]
       ,diag)) #CAST GL(d,q)
        );
    fi;
  fi;
  if normaliser then
    if IsOddInt(q) and IsEvenInt(d) and d<>2*k then
      Add(gens,DirectSumMat([ScalarMat(k,z),NormGOMinusGO@(d-2*k,q,sign)
       ,IdentityMatrix(GF(q),k)]));
    elif q > 3 then
      Add(gens,ScalarMat(d,z));
    fi;
  fi;
  return SubStructure(GL(d,q),gens);
  #  c=1.
end);

#  Line 6: R_{s3} = IsotropicStabOmega(d, q, 3, sign)
InstallGlobalFunction(KlLine7@,
function(q)
#  /out:P_1 In IsotropicStabOmega(8, q, 1, 1) replace/out:OmegaPlus(6,q) by
#  q^3:(GL(3,q)) = IsotropicStabOmega(6,q,3,1).
local 
   Om,d,diag,elt,form,form3,gen,general,gens,go,i,k,normaliser,sign,special,
   stab,t,u,v,x,y,z;
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
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  d:=8;
  sign:=1;
  k:=1;
  Om:=OmegaPlus;
  z:=PrimitiveElement(GF(q));
  form:=MatrixByEntries(GF(q),k,k,List([1..k],i->[i,k-i+1,1])) #CAST GL(k,q)
    ;
  diag:=List([1..d],i->[i,i,1]);
  gens:=[];
  #  will also need form for constructing IsotropicStabOmega(6,q,3,1)
  form3:=MatrixByEntries(GF(q),3,3,List([1..3],i->[i,3-i+1,1])) #CAST GL(3,q)
    ;
  #  element go in SOPlus(6,q)-OmegaPlus(6,q) in IsotropicStabOmega(6,q,3,1)
  if IsOddInt(q) then
    gen:=GL(3,q).1;
    go:=DirectSumMat([gen,form3*TransposedMat(gen^-1)*form3]);
  fi;
  #  GL(k, q) on <e_1..e_k>, balanced on <f_k..f_1>.
  gens:=[];
  for i in [1..Ngens(GL(k,q))] do
    gen:=GL(k,q).i;
    elt:=DirectSumMat([gen,IdentityMatrix(GF(q),d-2*k)
     ,form*TransposedMat(gen^-1)*form]);
    if IsEvenInt(q) or (IsOddInt(q) and IsSquare(DeterminantMat(gen)) or 
       InOmega@(elt,d,q,sign) or special) then
      Add(gens,elt);
      continue;
    fi;
    Assert(1,IsOddInt(q));
    elt:=DirectSumMat([gen,go,form*TransposedMat(gen^-1)*form]);
    Assert(1,InOmega@(elt,d,q,sign));
    #  gen didn't work with IdentityMatrix in middle section, so
    #  will work with element from SO\Omega.
    Add(gens,elt);
  od;
  if d-2*k > 1 then
    #  IsotropicStabOmega(6,q,3,1) acting on a (d-2k) space.
    stab:=IsotropicStabOmega@(6,q,3,1);
    gens:=Concatenation(gens,List([1..Ngens(stab)]
     ,i->DirectSumMat([IdentityMatrix(GF(q),k),stab.i,IdentityMatrix(GF(q),k)]))
     );
    if special and IsOddInt(q) then
      Add(gens,DirectSumMat([IdentityMatrix(GF(q),k),go,IdentityMatrix(GF(q),k)]
       ));
    fi;
  fi;
  #  don't know where I got the generators below from - did I calculate them?
  Add(gens,MatrixByEntries(GF(q),d,d,Concatenation([[k+1,1,1],[d,d-k,-1]],diag))
    #CAST GL(d,q)
    );
  if normaliser then
    if IsOddInt(q) then
      Add(gens,DirectSumMat([ScalarMat(k,z),NormGOMinusGO@(6,q,sign)
       ,IdentityMatrix(GF(q),k)]));
    elif q > 3 then
      Add(gens,ScalarMat(d,z));
    fi;
  fi;
  return SubStructure(GL(d,q),gens);
  #  c=2, so (q even), go-so (q odd)
end);

InstallGlobalFunction(KlLine15@,
function(q)
#  /out:G_2(q)
local 
   C,Omdq,P,QF,U,V,W,bf,c,cmat,cmat1,cmat2,d,eqns,form1,form2,formt,g2,gen,
   general,gens,ggl1,ggl2,gp1,gp2,i,ims,isf,k,mat,newgen,normaliser,qf,rts,sign,
   sign1,sign2,special,tmat,type,v,w,x,z;
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
  d:=8;
  sign:=1;
  type:="orth+";
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  if IsOddInt(q) then
    k:=7;
    sign1:=0;
    sign2:=0;
    gp1:=G2(q);
    gp2:=SubStructure(GL(1,q),[-1]);
    # =v= MULTIASSIGN =v=
    form1:=SymmetricBilinearForm(gp1);
    isf:=form1.val1;
    form1:=form1.val2;
    # =^= MULTIASSIGN =^=
    form2:=MatrixByEntries(GF(q),1,1,[1]);
    #  We need elements of ggl1/2, gsl1/2 in sl-omega (d-k>1) and gl-sl(p odd)
    ggl1:=(-GL(k,q).0) #CAST GL(k,q)
      ;
    ggl2:=GOMinusSO@(d-k,q,sign2);
    gp1:=SubStructure(GL(k,q),gp1,#TODO CLOSURE
      ggl1);
    w:=PrimitiveElement(GF(q));
    formt:=1 #CAST MatrixAlgebra(GF(q),k)
      ;
    cmat1:=CorrectForm(form1,k,q,"orth");
    cmat2:=CorrectForm(formt,k,q,"orth");
    gp1:=gp1^(cmat1*cmat2^-1);
    form1:=formt;
    #  We will need to transform our generators to fix Magma's quadratic form.
    tmat:=TransformForm(DirectSumMat(form1,form2),type);
    #  Now we can start constructing the generators
    gens:=[];
    for gen in List([1..Ngens(gp1)],i->gp1.i) do
      if DeterminantMat(gen)<>1 then
        if general then
          newgen:=DirectSumMat(gen,One(gp2)) #CAST GL(d,q)
            ^tmat;
          Add(gens,newgen);
        fi;
        newgen:=DirectSumMat(gen,ggl2) #CAST GL(d,q)
          ^tmat;
        Assert(1,InOmega@(newgen,d,q,sign));
        Add(gens,newgen);
      else
        newgen:=DirectSumMat(gen,IdentityMatrix(GF(q),d-k)) #CAST GL(d,q)
          ^tmat;
        Assert(1,InOmega@(newgen,d,q,sign));
        Add(gens,newgen);
      fi;
    od;
    if normaliser and q > 3 then
      Add(gens,ScalarMat(d,PrimitiveElement(GF(q))));
    fi;
    return SubStructure(GL(d,q),gens);
  fi;
  #  q even
  QF:=function(v,qf)
    return (MatrixByEntries(v)*qf*TransposedMat(MatrixByEntries(v)))[1][1];
  end;
  #  QF(v) = value of quadratic form on vector v
  if normaliser then
    special:=true;
  fi;
  #  find action of G2(q) on 6 dimensional space
  C:=Constituents(GModule(G2(q)));
  C:=Filtered(C,c->DimensionOfMatrixGroup(c)=6);
  g2:=ActionGroup(C[1]);
  Omdq:=OmegaPlus(d,q);
  # =v= MULTIASSIGN =v=
  qf:=QuadraticForm(Omdq);
  isf:=qf.val1;
  qf:=qf.val2;
  # =^= MULTIASSIGN =^=
  # =v= MULTIASSIGN =v=
  bf:=SymmetricBilinearForm(Omdq);
  isf:=bf.val1;
  bf:=bf.val2;
  # =^= MULTIASSIGN =^=
  #  normalize qf and bf
  qf:=qf[1][d]^-1*qf;
  bf:=bf[1][d]^-1*bf;
  V:=VectorSpace(GF(q),d);
  U:=VectorSpace(GF(q),d-2);
  W:=VectorSpace(GF(q),d-1);
  v:=(Concatenation([1],List([1..d-2],i->0),[1])) #CAST V
    ;
  #  (1, 0, ... 0, 1) - this is the ns fixed vector of the group constructed
  Assert(1,QF(v,qf)=1);
  cmat:=MatrixByEntries(GF(q),d,d,Concatenation([[1,d,1],[d,1,1]],List([2..d-1]
   ,i->[i,i,1]))) #CAST GL(d,q)
    ;
  #  cmat = element centralising group to be constructed that is SO - Omega
  #  called  r_omega in KL Prop 4.1.7
  gens:=[];
  #   Now we calculate embedding of g2 into G.
  #  Unfortunately bf is not always just antidiagonal 1, so need to transform
  #  generators of g2 to make them fix bf
  #  when bf is not antidiagonal 1, it's the cetnral 2 \times 2 that's wrong
  mat:=DiagonalMat(GF(q),Concatenation(List([2..QuoInt(d,2)],i->bf[i][d+1-i]^-1)
   ,List([2..QuoInt(d,2)],i->1))) #CAST GL(d-2,q)
    ;
  for gen in List([1..Ngens(g2)],i->(g2.i)^mat) do
    ims:=[];
    for i in [1..d-2] do
      w:=(Concatenation([0],Eltseq(U.i^gen),[0])) #CAST V
        ;
      #  next line from KL Prop 4.1.7
      c:=(QF(V.(i+1),qf)+QF(w,qf))^(QuoInt(q,2));
      #  ^(q div 2) = sqrt.
      w:=w+c*v;
      #  image of V.(i+1) under generator
      Assert(1,QF(w,qf)=QF(V.(i+1),qf));
      Add(ims,w);
    od;
    #  did I do next few lines?
    eqns:=TransposedMat(MatrixByEntries(Concatenation(ims,[v])));
    z:=SolutionMat(bf*eqns,W.(d-1));
    P:=PolynomialRing(GF(q));
    # Implicit generator Assg from previous line.
    x:=P.1;
    rts:=RootsOfUPol(x^2+x+QF(z,qf));
    if rts=[] then
      Error("Cannot solve quadratic");
    fi;
    z:=z+rts[1][1]*v;
    newgen:=MatrixByEntries(Concatenation([z],ims,[z+v])) #CAST GL(d,q)
      ;
    if not special and not InOmega@(newgen,d,q,sign) then
      newgen:=newgen*cmat;
    fi;
    Add(gens,newgen);
  od;
  if special then
    Add(gens,cmat);
  fi;
  if normaliser and q > 2 then
    Add(gens,ScalarMat(d,PrimitiveElement(GF(q))));
  fi;
  return SubStructure(GL(d,q),gens);
  #  c=1 (q even), 4 (q odd) (ngo-go, so-omega)
end);

InstallGlobalFunction(KlLine22@,
function(q)
#  /out:NonDegenStabOmega(8,q,1,2,1) with Omega^+(6,2) replaced by
#  maximal/out:imprimitive subgroup of type GL(3,q).
local 
   DJ,d,form1,form2,gen,general,gens,ggl1,ggl2,gnl1,gnl2,gp1,gp2,gsl1,gsl2,isf,
   k,mat1,mat2,newgen,normaliser,sign,sign1,sign2,special,swapmat,tmat,type,z;
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
  d:=8;
  sign:=1;
  type:="orth+";
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  k:=2;
  sign1:=1;
  sign2:=1;
  gp1:=GOPlus(k,q);
  gp2:=GOPlus(d-k,q);
  #  Note that we use GO  (rather than SO, Omega) to calculate the forms
  #  to ensure absolute irreducibility of gp1, gp2 in dimension 2.
  if IsEvenInt(q) then
    if q=2 and k=2 then
      form1:=MatrixByEntries(GF(q),2,2,[0,1,0,0]);
    else
      # =v= MULTIASSIGN =v=
      form1:=QuadraticForm(gp1);
      isf:=form1.val1;
      form1:=form1.val2;
      # =^= MULTIASSIGN =^=
    fi;
    # =v= MULTIASSIGN =v=
    form2:=QuadraticForm(gp2);
    isf:=form2.val1;
    form2:=form2.val2;
    # =^= MULTIASSIGN =^=
  else
    if q=3 then
      form1:=MatrixByEntries(GF(q),2,2,[0,1,1,0]);
    else
      # =v= MULTIASSIGN =v=
      form1:=SymmetricBilinearForm(gp1);
      isf:=form1.val1;
      form1:=form1.val2;
      # =^= MULTIASSIGN =^=
    fi;
    # =v= MULTIASSIGN =v=
    form2:=SymmetricBilinearForm(gp2);
    isf:=form2.val1;
    form2:=form2.val2;
    # =^= MULTIASSIGN =^=
  fi;
  #  Now construct imprimitive subgp of OmegaPlus(6,q) of type GL(3,q).
  z:=PrimitiveElement(GF(q));
  DJ:=function(mat,f,q)
  local cb;
    cb:=MatrixByEntries(GF(q),f,f,List([1..f],i->[i,f+1-i,1])) #CAST GL(f,q)
      ;
    return DirectSumMat(mat,TransposedMat(cb*mat^-1*cb));
  end;
  #  want matrices to generate GL(d,q) for q even or GL(d,q)/2
  #  for q odd (see KL (4.2.7)).
  # rewritten select statement
  if q=3 then
    mat1:=DJ(SL(3,q).1,3,q);
  else
    # rewritten select statement
    if IsEvenInt(q) then
      mat1:=DJ(GL(3,q).1,3,q);
    else
      mat1:=DJ((GL(3,q).1)^2,3,q);
    fi;
  fi;
  # rewritten select statement
  if q=3 then
    mat2:=DJ(SL(3,q).2,3,q);
  else
    mat2:=DJ((GL(3,q).2),3,q);
  fi;
  #  also will need elements of so-omega and (for q>2) go-so
  swapmat:=MatrixByEntries(GF(q),6,6,List([1..6],i->[i,7-i,1])) #CAST GL(6,q)
    ;
  #  antidiag
  if IsOddInt(q) then
    gsl2:=DJ(GL(3,q).1,3,q);
    ggl2:=swapmat;
  else
    gsl2:=swapmat;
  fi;
  #  We need elements of ggl1/2, gsl1/2 in sl-omega (d-k>1) and gl-sl(p odd)
  #  WE laready have ggl2, gsl2
  gsl1:=SOMinusOmega@(k,q,sign1);
  if IsOddInt(q) then
    ggl1:=GOMinusSO@(k,q,sign1);
  fi;
  #  now redefine gp1, gp2 to include generators of Omega + gsl, ggl
  #  "fewer adjusting elements": Omega, gsl1, ggl1, ggl1 \times gsl1
  gp1:=OmegaPlus(k,q);
  gp1:=SubStructure(GL(k,q),gp1,#TODO CLOSURE
    gsl1);
  if IsOddInt(q) then
    gp1:=SubStructure(GL(k,q),gp1,#TODO CLOSURE
      ggl1);
  fi;
  gp2:=SubStructure(GL(d-k,q),mat1,#TODO CLOSURE
    mat2,gsl2);
  #  We will need to transform our generators to fix Magma's quadratic form.
  tmat:=TransformForm(DirectSumMat(form1,form2),type);
  #  Now we can start constructing the generators
  gens:=[];
  for gen in List([1..Ngens(gp1)],i->gp1.i) do
    if DeterminantMat(gen)<>1 then
      if general then
        newgen:=DirectSumMat(gen,One(gp2)) #CAST GL(d,q)
          ^tmat;
        Add(gens,newgen);
      fi;
      #  use ggl2 to adjust it and make determinant 1
      newgen:=DirectSumMat(gen,ggl2) #CAST GL(d,q)
        ^tmat;
      if special or InOmega@(newgen,d,q,sign) then
        Add(gens,newgen);
      elif d-k > 1 then
        #  adjust again using gsl2.
        newgen:=DirectSumMat(gen,ggl2*gsl2) #CAST GL(d,q)
          ^tmat;
        Assert(1,InOmega@(newgen,d,q,sign));
        Add(gens,newgen);
      fi;
    else
      newgen:=DirectSumMat(gen,IdentityMatrix(GF(q),d-k)) #CAST GL(d,q)
        ^tmat;
      if special or InOmega@(newgen,d,q,sign) then
        Add(gens,newgen);
      elif d-k > 1 then
        #  adjust using gsl2.
        newgen:=DirectSumMat(gen,gsl2) #CAST GL(d,q)
          ^tmat;
        Assert(1,InOmega@(newgen,d,q,sign));
        Add(gens,newgen);
      fi;
    fi;
  od;
  for gen in List([1..Ngens(gp2)],i->gp2.i) do
    newgen:=DirectSumMat(IdentityMatrix(GF(q),k),gen) #CAST GL(d,q)
      ^tmat;
    if special or InOmega@(newgen,d,q,sign) then
      Add(gens,newgen);
    fi;
  od;
  if normaliser then
    if IsOddInt(q) and IsEvenInt(d) then
      gnl1:=NormGOMinusGO@(k,q,sign1);
      gnl2:=NormGOMinusGO@(d-k,q,sign2);
      newgen:=(DirectSumMat(gnl1,gnl2) #CAST GL(d,q)
        )^tmat;
      Add(gens,newgen);
    elif q > 3 then
      Add(gens,ScalarMat(d,PrimitiveElement(GF(q))));
    fi;
  fi;
  return SubStructure(GL(d,q),gens);
  #  c=1
end);

InstallGlobalFunction(KlLine26@,
function(q)
#  /out:NonDegenStabOmega(8,q,1,2,-1) with Omega^-(6,2) replaced by
#  maximal/out:imprimitive subgroup of type GU(3,q).
local 
   d,epsilon,form1,form2,frob,frob_diag,gammal1,gen,general,gens,ggl1,ggl2,gnl1,
   gp1,gp2,grp,gsl1,gsl2,gu1,gu1e,gu2,gu2e,gun,gune,isf,k,mat1,mat2,newgen,
   normaliser,sign,sign1,sign2,special,tmat,type,zero;
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
  d:=8;
  sign:=1;
  type:="orth+";
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  k:=2;
  sign1:=-1;
  sign2:=-1;
  gp1:=GOMinus(k,q);
  gp2:=GOMinus(d-k,q);
  #  Note that we use GO  (rather than SO, Omega) to calculate the forms
  #  to ensure absolute irreducibility of gp1, gp2 in dimension 2.
  if IsEvenInt(q) then
    # =v= MULTIASSIGN =v=
    form1:=QuadraticForm(gp1);
    isf:=form1.val1;
    form1:=form1.val2;
    # =^= MULTIASSIGN =^=
    # =v= MULTIASSIGN =v=
    form2:=QuadraticForm(gp2);
    isf:=form2.val1;
    form2:=form2.val2;
    # =^= MULTIASSIGN =^=
  else
    # =v= MULTIASSIGN =v=
    form1:=SymmetricBilinearForm(gp1);
    isf:=form1.val1;
    form1:=form1.val2;
    # =^= MULTIASSIGN =^=
    # =v= MULTIASSIGN =v=
    form2:=SymmetricBilinearForm(gp2);
    isf:=form2.val1;
    form2:=form2.val2;
    # =^= MULTIASSIGN =^=
  fi;
  #  Now construct semilinear subgp of OmegaMinus(6,q) of type GU(3,q).
  gammal1:=GammaL1@(2,q);
  epsilon:=gammal1.1;
  frob:=gammal1.2;
  zero:=MatrixByEntries(GF(q),2,2,[]);
  gu1:=GU(3,q).1;
  #  generates GU mod SU
  gu2:=GU(3,q).2;
  gu1e:=BlockPowers@(epsilon,gu1,1) #CAST GL(6,q)
    ;
  gu2e:=BlockPowers@(epsilon,gu2,1) #CAST GL(6,q)
    ;
  #  all of the above have determinant 1
  #  now we want to extend by the field automorphism x->x^q,
  frob_diag:=DirectSumMat(List([1..3],i->frob)) #CAST GL(6,q)
    ;
  grp:=SubStructure(GL(6,q),gu1e,#TODO CLOSURE
    gu2e,frob_diag);
  #  We will need to transform our generators to fix Magma's quadratic form.
  tmat:=TransformForm(grp);
  #  Now just need to intersect with Omega.
  if IsEvenInt(q) then
    mat1:=gu1e^tmat;
    mat2:=gu2e^tmat;
  else
    mat1:=(gu1e^tmat)^2;
    mat2:=gu2e^tmat;
  fi;
  Assert(1,InOmega@(mat1,6,q,-1) and InOmega@(mat2,6,q,-1));
  frob_diag:=frob_diag^tmat;
  if normaliser then
    gun:=ScalarMat(3,PrimitiveElement(GF(q^2)));
    gune:=BlockPowers@(epsilon,gun,1) #CAST GL(6,q)
      ;
    gune:=gune^tmat;
  fi;
  #  also will need elements of so-omega and (for q>2) go-so
  if IsOddInt(q) then
    gsl2:=gu1e^tmat;
    ggl2:=frob_diag;
  else
    gsl2:=frob_diag;
  fi;
  #  We need elements of ggl1/2, gsl1/2 in sl-omega (d-k>1) and gl-sl(p odd)
  #  WE laready have ggl2, gsl2
  gsl1:=SOMinusOmega@(k,q,sign1);
  if IsOddInt(q) then
    ggl1:=GOMinusSO@(k,q,sign1);
  fi;
  #  now redefine gp1, gp2 to include generators of Omega + gsl, ggl
  #  "fewer adjusting elements": Omega, gsl1, ggl1, ggl1 \times gsl1
  gp1:=OmegaMinus(k,q);
  gp1:=SubStructure(GL(k,q),gp1,#TODO CLOSURE
    gsl1);
  if IsOddInt(q) then
    gp1:=SubStructure(GL(k,q),gp1,#TODO CLOSURE
      ggl1);
  fi;
  gp2:=SubStructure(GL(d-k,q),mat1,#TODO CLOSURE
    mat2,gsl2);
  #  We will need to transform our generators to fix Magma's quadratic form.
  tmat:=TransformForm(DirectSumMat(form1,form2),type);
  #  Now we can start constructing the generators
  gens:=[];
  for gen in List([1..Ngens(gp1)],i->gp1.i) do
    if DeterminantMat(gen)<>1 then
      if general then
        newgen:=DirectSumMat(gen,One(gp2)) #CAST GL(d,q)
          ^tmat;
        Add(gens,newgen);
      fi;
      #  use ggl2 to adjust it and make determinant 1
      newgen:=DirectSumMat(gen,ggl2) #CAST GL(d,q)
        ^tmat;
      if special or InOmega@(newgen,d,q,sign) then
        Add(gens,newgen);
      elif d-k > 1 then
        #  adjust again using gsl2.
        newgen:=DirectSumMat(gen,ggl2*gsl2) #CAST GL(d,q)
          ^tmat;
        Assert(1,InOmega@(newgen,d,q,sign));
        Add(gens,newgen);
      fi;
    else
      newgen:=DirectSumMat(gen,IdentityMatrix(GF(q),d-k)) #CAST GL(d,q)
        ^tmat;
      if special or InOmega@(newgen,d,q,sign) then
        Add(gens,newgen);
      elif d-k > 1 then
        #  adjust using gsl2.
        newgen:=DirectSumMat(gen,gsl2) #CAST GL(d,q)
          ^tmat;
        Assert(1,InOmega@(newgen,d,q,sign));
        Add(gens,newgen);
      fi;
    fi;
  od;
  for gen in List([1..Ngens(gp2)],i->gp2.i) do
    newgen:=DirectSumMat(IdentityMatrix(GF(q),k),gen) #CAST GL(d,q)
      ^tmat;
    if special or InOmega@(newgen,d,q,sign) then
      Add(gens,newgen);
    fi;
  od;
  if normaliser then
    if IsOddInt(q) and IsEvenInt(d) then
      gnl1:=NormGOMinusGO@(k,q,sign1);
      newgen:=(DirectSumMat(gnl1,gune) #CAST GL(d,q)
        )^tmat;
      Add(gens,newgen);
    elif q > 3 then
      Add(gens,ScalarMat(d,PrimitiveElement(GF(q))));
    fi;
  fi;
  return SubStructure(GL(d,q),gens);
  #  c=1
end);

InstallGlobalFunction(KlLine51@,
function(q)
#  /out:2^9:L_3(2) as subgp of imrprimitive group 2^6:A_8.
local 
   d,form1,gen,general,gens,ggl1,gp1,id,isf,k,newgen,normaliser,sgens,sign,
   sign1,special,t,tmat,type;
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
  Assert(1,IsOddInt(q) and IsPrimeInt(q));
  d:=8;
  sign:=1;
  type:="orth+";
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  k:=1;
  sign1:=0;
  t:=QuoInt(d,k);
  #  Check parameters are compatible.
  gp1:=SubStructure(GL(k,q),[-1]);
  #  Note that we use GO  (rather than SO, Omega) to calculate the forms
  #  to ensure absolute irreducibility of gp1, gp2 in dimension 2.
  # =v= MULTIASSIGN =v=
  form1:=SymmetricBilinearForm(gp1);
  isf:=form1.val1;
  form1:=form1.val2;
  # =^= MULTIASSIGN =^=
  ggl1:=GOMinusSO@(k,q,sign1);
  #  We will need to transform our generators to fix Magma's quadratic form.
  tmat:=TransformForm(DirectSumMat(List([1..t],i->form1)),type);
  id:=IdentityMatrix(GF(q),k) #CAST GL(k,q)
    ;
  #  Now we can start constructing the generators
  gens:=[];
  for gen in List([1..Ngens(gp1)],i->gp1.i) do
    Assert(1,DeterminantMat(gen)<>1);
    #  use ggl1 to adjust it and make determinant 1
    if general then
      newgen:=DirectSumMat(Concatenation([gen],List([1..t-1],i->id))) #CAST 
       GL(d,q)
        ^tmat;
      Add(gens,newgen);
    fi;
    newgen:=DirectSumMat(Concatenation([gen,ggl1],List([1..t-2],i->id))) #CAST 
     GL(d,q)
      ^tmat;
    if special or InOmega@(newgen,d,q,sign) then
      Add(gens,newgen);
    fi;
  od;
  #  Now generators of 2^3.L_3(2)
  sgens:=[(1,2,6,8,3,5,4),(2,6,8,7,4,5,3)];
  for gen in sgens do
    newgen:=PermutationMatrix@(GF(q),gen) #CAST GL(d,q)
      ^tmat;
    Assert(1,InOmega@(newgen,d,q,sign));
    Add(gens,newgen);
  od;
  if normaliser and q > 3 then
    Add(gens,ScalarMat(d,PrimitiveElement(GF(q))));
  fi;
  return SubStructure(GL(d,q),gens);
  #  c=4 so-omega, ngo-go
end);

InstallGlobalFunction(KlLine61@,
function(q)
#  /out:(D_2(q^2+1)xD_2(q^2+1).2^2) as subgp of imprim OmegaMinus(4,2) wr 2.
local 
   bigsgens,bigsgp1,bigsgrp,cform,cmat1,csgens,d,dim,form1,frob,frobgen,gammal1,
   gen,general,gens,ggl1,gp1,gsl1,id,isf,k,newgen,ngo,normaliser,s,scal,sform,
   sgens,sggl,sggl2,sgp1,sgsl,sgsl2,sign,sign1,singer,special,t,tmat,type;
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
  d:=8;
  sign:=1;
  type:="orth+";
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  k:=4;
  sign1:=-1;
  t:=QuoInt(d,k);
  gp1:=GOMinus(k,q);
  #  Note that we use GO  (rather than SO, Omega) to calculate the forms
  #  to ensure absolute irreducibility of gp1, gp2 in dimension 2.
  if IsEvenInt(q) then
    # =v= MULTIASSIGN =v=
    form1:=QuadraticForm(gp1);
    isf:=form1.val1;
    form1:=form1.val2;
    # =^= MULTIASSIGN =^=
  else
    # =v= MULTIASSIGN =v=
    form1:=SymmetricBilinearForm(gp1);
    isf:=form1.val1;
    form1:=form1.val2;
    # =^= MULTIASSIGN =^=
  fi;
  #  now construct semilinear subgroup
  s:=2;
  dim:=2;
  bigsgp1:=GOMinus(dim,q^s);
  sgp1:=OmegaMinus(dim,q^s);
  #  In the -1 case, the field automorphism will change the form, so
  #  we will need to conjugate it back.
  if IsEvenInt(q) then
    # =v= MULTIASSIGN =v=
    sform:=QuadraticForm(bigsgp1);
    isf:=sform.val1;
    sform:=sform.val2;
    # =^= MULTIASSIGN =^=
  else
    # =v= MULTIASSIGN =v=
    sform:=SymmetricBilinearForm(bigsgp1);
    isf:=sform.val1;
    sform:=sform.val2;
    # =^= MULTIASSIGN =^=
  fi;
  cform:=MatToQ@(sform,q);
  cmat1:=TransformForm(cform,"orth-");
  #  We need elements of ggl, gsl in sl-omega
  sgsl:=SOMinusOmega@(dim,q^2,sign1);
  if IsOddInt(q) then
    sggl:=GOMinusSO@(dim,q^2,sign1);
  fi;
  gammal1:=GammaL1@(s,q);
  singer:=gammal1.1;
  frob:=gammal1.2;
  sgens:=List([1..Ngens(sgp1)],i->BlockPowers@(singer,sgp1.i,1));
  bigsgens:=List([1..Ngens(bigsgp1)],i->BlockPowers@(singer,bigsgp1.i,1));
  sgsl2:=BlockPowers@(singer,sgsl,1) #CAST GL(k,q)
    ;
  if IsOddInt(q) then
    sggl2:=BlockPowers@(singer,sggl,1) #CAST GL(k,q)
      ;
  fi;
  frobgen:=DirectSumMat(List([1..dim],i->frob)) #CAST GL(k,q)
    ;
  #  det(frobgen) = det(frob)^2 = 1.
  frobgen:=frobgen*BlockPowers@(singer,cmat1,1) #CAST GL(k,q)
    ;
  Assert(1,DeterminantMat(frobgen)=(-1) #CAST GF(q)
    );
  bigsgrp:=SubStructure(GL(k,q),bigsgens,#TODO CLOSURE
    frobgen);
  #  We will need to transform our generators to fix Magma's quadratic form.
  tmat:=TransformForm(bigsgrp);
  csgens:=List(sgens,g->g^tmat);
  sgsl2:=sgsl2^tmat;
  #  find extra generator in Omega
  if IsOddInt(q) then
    sggl2:=sggl2^tmat;
    if InOmega@(sggl2,k,q,sign1) then
      Add(csgens,sggl2);
    else
      Assert(1,InOmega@(sggl2*sgsl2,k,q,sign1));
      Add(csgens,sggl2*sgsl2);
    fi;
    gsl1:=sgsl2;
  else
    Assert(1,InOmega@(sgsl2,k,q,sign1));
    Add(csgens,sgsl2);
  fi;
  frobgen:=frobgen^tmat;
  if IsOddInt(q) then
    ggl1:=frobgen;
  else
    gsl1:=frobgen;
  fi;
  if normaliser and IsOddInt(q) then
    scal:=ScalarMat(GF(q^2),dim,PrimitiveElement(GF(q^2)));
    ngo:=BlockPowers@(singer,scal,1);
    ngo:=(ngo #CAST GL(k,q)
      )^tmat;
    ngo:=ngo^(QuoInt((q+1),2));
  fi;
  #  We have already defined elements of in sl-omega and gl-sl(p odd)
  #  now redefine gp1
  gp1:=SubStructure(GL(k,q),csgens,#TODO CLOSURE
    gsl1);
  if IsOddInt(q) then
    gp1:=SubStructure(GL(k,q),gp1,#TODO CLOSURE
      ggl1);
  fi;
  #  We will need to transform our generators to fix Magma's quadratic form.
  tmat:=TransformForm(DirectSumMat(List([1..t],i->form1)),type);
  id:=IdentityMatrix(GF(q),k) #CAST GL(k,q)
    ;
  #  Now we can start constructing the generators
  gens:=[];
  for gen in List([1..Ngens(gp1)],i->gp1.i) do
    if DeterminantMat(gen)<>1 then
      #  use ggl1 to adjust it and make determinant 1
      if general then
        newgen:=DirectSumMat(Concatenation([gen],List([1..t-1],i->id))) #CAST 
         GL(d,q)
          ^tmat;
        Add(gens,newgen);
      fi;
      newgen:=DirectSumMat(Concatenation([gen,ggl1],List([1..t-2],i->id))) 
       #CAST GL(d,q)
        ^tmat;
      if special or InOmega@(newgen,d,q,sign) then
        Add(gens,newgen);
      else
        #  adjust again using gsl1.
        newgen:=DirectSumMat(Concatenation([gen,ggl1*gsl1],List([1..t-2],i->id))
         ) #CAST GL(d,q)
          ^tmat;
        Assert(1,InOmega@(newgen,d,q,sign));
        Add(gens,newgen);
      fi;
    else
      newgen:=DirectSumMat(Concatenation([gen],List([1..t-1],i->id))) #CAST 
       GL(d,q)
        ^tmat;
      if special or InOmega@(newgen,d,q,sign) then
        Add(gens,newgen);
      elif k > 1 then
        #  adjust using gsl1.
        newgen:=DirectSumMat(Concatenation([gen,gsl1],List([1..t-2],i->id))) 
         #CAST GL(d,q)
          ^tmat;
        Assert(1,InOmega@(newgen,d,q,sign));
        Add(gens,newgen);
      fi;
    fi;
  od;
  #  Now generators of S_n
  for gen in List([1..Ngens(AlternatingGroup(t))],i->AlternatingGroup(t).i) do
    newgen:=KroneckerProduct(PermutationMatrix@(GF(q),gen),id) #CAST GL(d,q)
      ^tmat;
    Assert(1,InOmega@(newgen,d,q,sign));
    Add(gens,newgen);
  od;
  newgen:=KroneckerProduct(PermutationMatrix@(GF(q),Tuple([1,2]) #CAST 
   SymmetricGroup(t)
    ),id) #CAST GL(d,q)
    ^tmat;
  #  if Determinant(newgen) neq 1: the ggl1 matrix always has det -1
  if DeterminantMat(newgen)<>1 then
    newgen:=newgen*DirectSumMat(Concatenation([ggl1],List([1..t-1],i->id))) 
     #CAST GL(d,q)
      ^tmat;
  fi;
  if special or InOmega@(newgen,d,q,sign) then
    Add(gens,newgen);
  else
    #  gsl1 has det 1 spinor +1
    newgen:=newgen*DirectSumMat(Concatenation([gsl1],List([1..t-1],i->id))) 
     #CAST GL(d,q)
      ^tmat;
    Assert(1,InOmega@(newgen,d,q,sign));
    Add(gens,newgen);
  fi;
  if normaliser then
    if IsOddInt(q) then
      newgen:=DirectSumMat(List([1..t],i->ngo)) #CAST GL(d,q)
        ^tmat;
      Add(gens,newgen);
    elif q > 2 then
      Add(gens,ScalarMat(d,PrimitiveElement(GF(q))));
    fi;
  fi;
  return SubStructure(GL(d,q),gens);
  #  c=1
end);


