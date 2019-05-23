#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: AandB, ActionGenerator, Append, AssertAttribute,
#  AutPSp4, BaseRing, CorrectForm, Degree, Depth, DiagonalJoin, DiagonalMatrix,
#  DirectSum, Factorisation, Fix, GF, GL, GL2, GModule, GOMinus, GOPlus, GSp,
#  GU, Group, Identity, Image, InsertBlock, Integers, IsConjugate, IsEven,
#  IsIsomorphic, IsOdd, IsPrimePower, IsSquare, Log, MatToQ, Matrix,
#  MatrixAlgebra, NF, Ncols, Ngens, Nrows, OrbitAction, OrbitImage, PGL2, PGSp,
#  PGammaSp, PrimitiveElement, RSpace, Random, RepresentationSum,
#  Representative, SL, SL2, SU, Sp, Stabiliser, Sym, SymmetricBilinearForm,
#  TransformForm, Transpose, VNO, VectorSpace, act

#  Defines: AutPSp, AutPSp4, AutSp4, GL2, GLT2, GSp, GU2, GammaL, GammaL2,
#  GammaOMinus, GammaOPlus, GammaSp, GammaU, MatToQ, ModToQ, PGL2, PGSp,
#  PGammaL2, PGammaLD2, PGammaSp, PSL2, SL2, SU2, SigmaU

DeclareGlobalFunction("AutPSp4@");

DeclareGlobalFunction("GL2@");

DeclareGlobalFunction("GSp@");

DeclareGlobalFunction("GU2@");

DeclareGlobalFunction("ModToQ@");

DeclareGlobalFunction("PGL2@");

DeclareGlobalFunction("PGammaL2@");

DeclareGlobalFunction("PGammaLD2@");

DeclareGlobalFunction("PGammaSp@");

DeclareGlobalFunction("PSL2@");

#   Code to produce various decorations of L(n,q)
#   Written by Derek Holt - 2002
MatToQ@:=function(A,q)
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
end;
;
InstallGlobalFunction(GL2@,
function(n,q)
#  /out: Extension of GL(n,q) by graph isomorphisms - degree is twice as large.
local G,G2,gens,mat;
  if n < 3 then
    Error("n must be at least 3 in GL2");
  fi;
  G:=GL(n,q);
  gens:=List(List([1..Ngens(G)],i->G.i),g->DirectSum(g,TransposedMat(g^-1)));
  mat:=0 #CAST MatrixAlgebra(GF(q),2*n)
    ;
  InsertBlock(mat,Identity(G),1,n+1);
  InsertBlock(mat,Identity(G),n+1,1);
  Add(gens,mat);
  G2:=SubStructure(GL(2*n,q),gens);
  AssertAttribute(G2,"Order",2*Size(G));
  return G2;
end);

SL2@:=function(n,q)
#  /out: Extension of SL(n,q) by graph isomorphisms - degree is twice as large.
local G,G2,gens,mat;
  if n < 3 then
    Error("n must be at least 3 in SL2");
  fi;
  G:=SL(n,q);
  gens:=List(List([1..Ngens(G)],i->G.i),g->DirectSum(g,TransposedMat(g^-1)));
  mat:=0 #CAST MatrixAlgebra(GF(q),2*n)
    ;
  InsertBlock(mat,Identity(G),1,n+1);
  InsertBlock(mat,Identity(G),n+1,1);
  Add(gens,mat);
  G2:=SubStructure(GL(2*n,q),gens);
  AssertAttribute(G2,"Order",2*Size(G));
  return G2;
end;
;
GammaL@:=function(n,q)
local varX,e,f,gen,gens,j,mat,p;
  f:=CollectedFactors(q);
  p:=f[1][1];
  e:=f[1][2];
  varX:=GL(n,q);
  if e=1 then
    return varX;
  fi;
  gens:=[];
  for gen in List([1..Ngens(varX)],i->varX.i) do
    Add(gens,DirectSumMat(List([0..e-1],j->MatToQ@(gen,p^j))));
  od;
  mat:=0 #CAST MatrixAlgebra(GF(q),n*e)
    ;
  for j in [1..e-1] do
    InsertBlock(mat,Identity(varX),(j-1)*n+1,j*n+1);
  od;
  InsertBlock(mat,Identity(varX),(e-1)*n+1,1);
  Add(gens,mat);
  return SubStructure(GL(n*e,q),gens);
end;
;
GammaL2@:=function(n,q)
local varX,e,f,gen,gens,j,mat,p;
  f:=CollectedFactors(q);
  p:=f[1][1];
  e:=f[1][2];
  varX:=GL2@(n,q);
  if e=1 then
    return varX;
  fi;
  gens:=[];
  for gen in List([1..Ngens(varX)],i->varX.i) do
    Add(gens,DirectSumMat(List([0..e-1],j->MatToQ@(gen,p^j))));
  od;
  mat:=0 #CAST MatrixAlgebra(GF(q),2*n*e)
    ;
  for j in [1..e-1] do
    InsertBlock(mat,Identity(varX),(j-1)*2*n+1,j*2*n+1);
  od;
  InsertBlock(mat,Identity(varX),(e-1)*2*n+1,1);
  Add(gens,mat);
  return SubStructure(GL(2*n*e,q),gens);
end;
;
InstallGlobalFunction(GU2@,
function(n,q)
#  /out: Extension of GU(n,q) by frobenius isomorphism - degree is twice as
#  large.
local G,G2,gens,mat;
  if n < 3 then
    Error("n must be at least 3 in GU2");
  fi;
  G:=GU(n,q);
  gens:=List(List([1..Ngens(G)],i->G.i),g->DirectSum(g,MatToQ@(g,q)));
  mat:=0 #CAST MatrixAlgebra(GF(q^2),2*n)
    ;
  InsertBlock(mat,Identity(G),1,n+1);
  InsertBlock(mat,Identity(G),n+1,1);
  Add(gens,mat);
  G2:=SubStructure(GL(2*n,q^2),gens);
  AssertAttribute(G2,"Order",2*Size(G));
  return G2;
end);

SU2@:=function(n,q)
#  /out: Extension of SU(n,q) by frobenius isomorphism - degree is twice as
#  large.
local G,G2,gens,mat;
  if n < 3 then
    Error("n must be at least 3 in SU2");
  fi;
  G:=SU(n,q);
  gens:=List(List([1..Ngens(G)],i->G.i),g->DirectSum(g,MatToQ@(g,q)));
  mat:=0 #CAST MatrixAlgebra(GF(q^2),2*n)
    ;
  InsertBlock(mat,Identity(G),1,n+1);
  InsertBlock(mat,Identity(G),n+1,1);
  Add(gens,mat);
  G2:=SubStructure(GL(2*n,q^2),gens);
  AssertAttribute(G2,"Order",2*Size(G));
  return G2;
end;
;
GammaU@:=function(n,q)
local varX,e,f,gen,gens,j,mat,p;
  f:=CollectedFactors(q);
  p:=f[1][1];
  e:=f[1][2];
  varX:=GU(n,q);
  gens:=[];
  for gen in List([1..Ngens(varX)],i->varX.i) do
    Add(gens,DirectSumMat(List([0..2*e-1],j->MatToQ@(gen,p^j))));
  od;
  mat:=0 #CAST MatrixAlgebra(GF(q^2),2*n*e)
    ;
  for j in [1..2*e-1] do
    InsertBlock(mat,Identity(varX),(j-1)*n+1,j*n+1);
  od;
  InsertBlock(mat,Identity(varX),(2*e-1)*n+1,1);
  Add(gens,mat);
  return SubStructure(GL(2*n*e,q^2),gens);
end;
;
SigmaU@:=function(n,q)
local varX,e,f,gen,gens,j,mat,p;
  f:=CollectedFactors(q);
  p:=f[1][1];
  e:=f[1][2];
  varX:=SU(n,q);
  gens:=[];
  for gen in List([1..Ngens(varX)],i->varX.i) do
    Add(gens,DirectSumMat(List([0..2*e-1],j->MatToQ@(gen,p^j))));
  od;
  mat:=0 #CAST MatrixAlgebra(GF(q^2),2*n*e)
    ;
  for j in [1..2*e-1] do
    InsertBlock(mat,Identity(varX),(j-1)*n+1,j*n+1);
  od;
  InsertBlock(mat,Identity(varX),(2*e-1)*n+1,1);
  Add(gens,mat);
  return SubStructure(GL(2*n*e,q^2),gens);
end;
;
InstallGlobalFunction(PGL2@,
function(n,q)
#  /out: Extension of PGL(n,q) by graph isomorphisms - degree is twice as 
 large.
local G,V;
  if n < 3 then
    Error("n must be at least 3 in PGL2");
  fi;
  G:=GL2@(n,q);
  V:=VectorSpace(G);
  return OrbitImage(G,SubStructure(V,V.1));
end);

InstallGlobalFunction(PSL2@,
function(n,q)
#  /out: Extension of PGL(n,q) by graph isomorphisms - degree is twice as 
 large.
local G,V;
  if n < 3 then
    Error("n must be at least 3 in PSL2");
  fi;
  G:=SL2@(n,q);
  V:=VectorSpace(G);
  return OrbitImage(G,SubStructure(V,V.1));
end);

InstallGlobalFunction(PGammaL2@,
function(n,q)
#  /out:Extension of PGammaL by graph automorphism
local F,G,NF,V,VNO,varZ,c,ct,d,g,gti,i,lv,ng,np,p,perm,perms,v,vi,w;
  if n < 3 then
    Error("n must be at least 3 in PGammaL2");
  fi;
  varZ:=Integers();
  p:=CollectedFactors(q)[1][1];
  if p=q then
    return PGL2@(n,q);
  fi;
  np:=QuoInt((q^n-1),(q-1));
  F:=GF(q);
  # Implicit generator Assg from previous line.
  w:=F.1;
  G:=GL(n,F);
  ng:=Ngens(G);
  perms:=List([1..ng+2],i->[]);
  lv:=w^(q-2);
  V:=VectorSpace(G);
  # rewritten select statement
  if 0 then
    NF:=function(x)
      return x=0;
    end;
  else
    NF:=function(x)
      return x=Log(x)+1;
    end;
  fi;
  VNO:=function(v)
  local d,vn,vv;
    d:=Depth(v);
    vv:=v*v[d]^-1;
    vn:=1+QuoInt((q^(n-d)-1),(q-1))+Sum(List([d+1..n],i->q^(n-i)*NF(vv[i])));
    return vn;
  end;
  #  loop through point and determine action of generators
  v:=(Concatenation(List([1..n-1],i->0),[1])) #CAST V
    ;
  d:=n;
  ct:=1;
  while true do
    for i in [1..ng] do
      g:=G.i;
      gti:=TransposedMat(g^-1);
      perms[i][ct]:=VNO(v^g);
      perms[i][ct+np]:=VNO(v^gti)+np;
    od;
    #   field automorphism:
    vi:=VNO(List([1..n],i->v[i]^p) #CAST V
      );
    perms[ng+1][ct]:=vi;
    perms[ng+1][ct+np]:=vi+np;
    #   graph automorphism:
    perms[ng+2][ct]:=ct+np;
    perms[ng+2][ct+np]:=ct;
    #  move on to next vector
    ct:=ct+1;
    c:=n;
    while c > d and v[c]=lv do
      v[c]:=0;
      c:=c-1;
    od;
    if c=d then
      if d=1 then
        break;
      fi;
      v[d]:=0;
      d:=d-1;
      v[d]:=1;
    else
      # rewritten select statement
      if v[c]=0 then
        v[c]:=1;
      else
        v[c]:=v[c]*w;
      fi;
    fi;
  od;
  return SubStructure(SymmetricGroup(2*np),perms);
end);

InstallGlobalFunction(PGammaLD2@,
function(q)
#  /out:This is a version of PGammaL2 in dimension 2, where we have
#  no/out:graph isomorphism, and the result has degree q+1 as normal./out:We
#  need this because it allows us easily to set/out:up a monomorphism GL(2,q)
#  -> PGammaL(2,q).
local F,G,NF,V,VNO,varZ,c,ct,d,g,gti,i,lv,ng,np,p,perm,perms,v,vi,w;
  varZ:=Integers();
  p:=CollectedFactors(q)[1][1];
  if p=q then
    Error("q must be a proper prime power in PGammaLD2");
  fi;
  np:=q+1;
  F:=GF(q);
  # Implicit generator Assg from previous line.
  w:=F.1;
  G:=GL(2,F);
  ng:=Ngens(G);
  perms:=List([1..ng+1],i->[]);
  lv:=w^(q-2);
  V:=VectorSpace(G);
  # rewritten select statement
  if 0 then
    NF:=function(x)
      return x=0;
    end;
  else
    NF:=function(x)
      return x=Log(x)+1;
    end;
  fi;
  VNO:=function(v)
  local d,vn,vv;
    d:=Depth(v);
    vv:=v*v[d]^-1;
    vn:=1+QuoInt((q^(2-d)-1),(q-1))+Sum(List([d+1..2],i->q^(2-i)*NF(vv[i])));
    return vn;
  end;
  #  loop through point and determine action of generators
  v:=([0,1]) #CAST V
    ;
  d:=2;
  ct:=1;
  while true do
    for i in [1..ng] do
      perms[i][ct]:=VNO(v^G.i);
    od;
    #   field automorphism:
    vi:=VNO(List([1..2],i->v[i]^p) #CAST V
      );
    perms[ng+1][ct]:=vi;
    #  move on to next vector
    ct:=ct+1;
    c:=2;
    while c > d and v[c]=lv do
      v[c]:=0;
      c:=c-1;
    od;
    if c=d then
      if d=1 then
        break;
      fi;
      v[d]:=0;
      d:=d-1;
      v[d]:=1;
    else
      # rewritten select statement
      if v[c]=0 then
        v[c]:=1;
      else
        v[c]:=v[c]*w;
      fi;
    fi;
  od;
  return SubStructure(SymmetricGroup(np),perms);
end);

InstallGlobalFunction(ModToQ@,
function(M,q)
#  /out: same as MatToQ for GModule M
local G;
  G:=Group(M);
  return GModule(G,List(List([1..Ngens(G)],i->ActionGenerator(M,i))
   ,m->MatToQ@(m,q)));
end);

GLT2@:=function(n,q)
#  /out: Extension of GL(n,q^2) by twisted .2 - embeds in U(2*n,q)
local A,G,G2,gens,mat;
  G:=GL(n,q^2);
  A:=MatrixAlgebra(GF(q^2),n);
  gens:=List(List([1..Ngens(G)],i->G.i)
   ,g->DirectSum(g,MatToQ@(TransposedMat(g^-1) #CAST A
    ,q)));
  mat:=0 #CAST MatrixAlgebra(GF(q^2),2*n)
    ;
  InsertBlock(mat,Identity(G),1,n+1);
  InsertBlock(mat,Identity(G),n+1,1);
  Add(gens,mat);
  G2:=SubStructure(GL(2*n,q^2),gens);
  AssertAttribute(G2,"Order",2*Size(G));
  return G2;
end;
;
#   Code to produce various decorations of Sp(n,q)
InstallGlobalFunction(GSp@,
function(n,q)
#  /out: Extension of Sp(n,q) by diagonal isomorphism (and scalar matrices)
local G,m,o,w;
  G:=SP(n,q);
  if q mod 2=0 then
    return G;
  fi;
  w:=PrimitiveElement(GF(q));
  m:=QuoInt(n,2);
  o:=DiagonalMat(Concatenation(List([1..m],i->w),List([1..m],i->1))) #CAST 
   GL(n,q)
    ;
  return SubStructure(GL(n,q),G.1,#TODO CLOSURE
    G.2,o);
end);

GammaSp@:=function(n,q)
#  /out:Extension of Sp(n,q) by diagonal isomorphism and field autos
local varX,e,f,gen,gens,j,m,mat,o,p,w;
  Assert(1,IsEvenInt(n));
  f:=CollectedFactors(q);
  p:=f[1][1];
  e:=f[1][2];
  if q mod 2=0 then
    varX:=SP(n,q);
  else
    w:=PrimitiveElement(GF(q));
    m:=QuoInt(n,2);
    o:=DiagonalMat(Concatenation(List([1..m],i->w),List([1..m],i->1))) #CAST 
     GL(n,q)
      ;
    varX:=SubStructure(GL(n,q),SP(n,q).1,#TODO CLOSURE
      SP(n,q).2,o);
  fi;
  gens:=[];
  for gen in List([1..Ngens(varX)],i->varX.i) do
    Add(gens,DirectSumMat(List([0..e-1],j->MatToQ@(gen,p^j))));
  od;
  mat:=0 #CAST MatrixAlgebra(GF(q),n*e)
    ;
  for j in [1..e-1] do
    InsertBlock(mat,Identity(varX),(j-1)*n+1,j*n+1);
  od;
  InsertBlock(mat,Identity(varX),(e-1)*n+1,1);
  Add(gens,mat);
  return SubStructure(GL(n*e,q),gens);
end;
;
GammaOPlus@:=function(n,q)
#  /out:Extension of GO+(n,q) by diagonal isomorphism and field autos
local varX,e,f,gen,gens,j,m,mat,o,p,w;
  Assert(1,IsEvenInt(n));
  f:=CollectedFactors(q);
  p:=f[1][1];
  e:=f[1][2];
  w:=PrimitiveElement(GF(q));
  if q mod 2=0 then
    varX:=GOPlus(n,q);
  else
    m:=QuoInt(n,2);
    o:=DiagonalMat(Concatenation(List([1..m],i->w),List([1..m],i->1))) #CAST 
     GL(n,q)
      ;
    varX:=SubStructure(GL(n,q),GOPlus(n,q),#TODO CLOSURE
      o);
  fi;
  gens:=[];
  for gen in List([1..Ngens(varX)],i->varX.i) do
    Add(gens,DirectSumMat(List([0..e-1],j->MatToQ@(gen,p^j))));
  od;
  mat:=0 #CAST MatrixAlgebra(GF(q),n*e)
    ;
  for j in [1..e-1] do
    InsertBlock(mat,Identity(varX),(j-1)*n+1,j*n+1);
  od;
  InsertBlock(mat,Identity(varX),(e-1)*n+1,1);
  Add(gens,mat);
  return SubStructure(GL(n*e,q),gens);
end;
;
GammaOMinus@:=function(n,q)
#  /out:Extension of GO-(n,q) by diagonal isomorphism and field autos- this is
#  harder
local 
   AandB@,GC,M1,M2,varX,a,b,cmat,comps,e,f,form,g,gen,gens,gensc1,gensc2,gom,i,
   isit,j,m,mat,mate,o,p,w;
  Assert(1,IsEvenInt(n));
  f:=CollectedFactors(q);
  p:=f[1][1];
  e:=f[1][2];
  w:=PrimitiveElement(GF(q));
  gom:=GOMinus(n,q);
  if q mod 2=0 then
    varX:=gom;
  else
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
    ;
    # =v= MULTIASSIGN =v=
    b:=AandB@(q,w);
    a:=b.val1;
    b:=b.val2;
    # =^= MULTIASSIGN =^=
    m:=QuoInt(n,2);
    # rewritten select statement
    if n mod 4=0 or (q-1) mod 4=0 then
      o:=DirectSumMat(Concatenation(List([1..m-1],i->MatrixByEntries(GF(q)
       ,2,2,[a,-b,b,a])),[MatrixByEntries(GF(q),2,2,[0,-1,w,0])]));
    else
      o:=DirectSumMat(List([1..m],i->MatrixByEntries(GF(q),2,2,[a,-b,b,a])));
    fi;
    # =v= MULTIASSIGN =v=
    form:=SymmetricBilinearForm(GOMinus(n,q));
    isit:=form.val1;
    form:=form.val2;
    # =^= MULTIASSIGN =^=
    mat:=CorrectForm(form,n,q,"orth-");
    o:=(mat*o*mat^-1) #CAST GL(n,q)
      ;
    varX:=SubStructure(GL(n,q),gom,#TODO CLOSURE
      o);
  fi;
  #  work out correcting matrix to follow field automorphism
  GC:=SubStructure(GL(n,q),List(List([1..Ngens(gom)],i->gom.i),g->MatToQ@(g,p)))
   ;
  cmat:=TransformForm(GC);
  #  identify (gal*cmat)^e
  gensc1:=[];
  gensc2:=[];
  for i in [1..Ngens(gom)] do
    g:=gom.i;
    for i in [1..e-1] do
      g:=cmat^-1*MatToQ@(g,p)*cmat;
    od;
    Add(gensc1,g);
    g:=gom.i;
    g:=MatToQ@(cmat*g*cmat^-1,p^(e-1));
    Add(gensc2,g);
  od;
  M1:=GModule(gensc1);
  M2:=GModule(gom,gensc2);
  # =v= MULTIASSIGN =v=
  mate:=IsIsomorphic(M1,M2);
  isit:=mate.val1;
  mate:=mate.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,isit);
  gens:=[];
  for gen in List([1..Ngens(varX)],i->varX.i) do
    comps:=[gen];
    for i in [2..e] do
      comps[i]:=cmat^-1*MatToQ@(comps[i-1],p)*cmat;
    od;
    Add(gens,DirectSumMat(comps));
  od;
  mat:=0 #CAST MatrixAlgebra(GF(q),n*e)
    ;
  for j in [1..e-1] do
    InsertBlock(mat,Identity(varX),(j-1)*n+1,j*n+1);
  od;
  InsertBlock(mat,mate,(e-1)*n+1,1);
  Add(gens,mat);
  return rec(val1:=SubStructure(GL(n*e,q),gens),
    val2:=cmat);
end;
;
PGSp@:=function(n,q)
#  /out: Extension of PSp(n,q) by diagonal isomorphism
local G,V;
  G:=GSp@(n,q);
  V:=VectorSpace(G);
  return OrbitImage(G,SubStructure(V,V.1));
end;
;
InstallGlobalFunction(PGammaSp@,
function(n,q)
#  /out:Extension of PGSp by field automorphism
local F,G,NF,V,VNO,varZ,c,ct,d,g,gti,i,lv,ng,np,p,perm,perms,v,vi,w;
  varZ:=Integers();
  p:=CollectedFactors(q)[1][1];
  if p=q then
    return PGSp@(n,q);
  fi;
  np:=QuoInt((q^n-1),(q-1));
  F:=GF(q);
  # Implicit generator Assg from previous line.
  w:=F.1;
  G:=GSp@(n,q);
  ng:=Ngens(G);
  perms:=List([1..ng+1],i->[]);
  lv:=w^(q-2);
  V:=VectorSpace(G);
  # rewritten select statement
  if 0 then
    NF:=function(x)
      return x=0;
    end;
  else
    NF:=function(x)
      return x=Log(x)+1;
    end;
  fi;
  VNO:=function(v)
  local d,vn,vv;
    d:=Depth(v);
    vv:=v*v[d]^-1;
    vn:=1+QuoInt((q^(n-d)-1),(q-1))+Sum(List([d+1..n],i->q^(n-i)*NF(vv[i])));
    return vn;
  end;
  #  loop through point and determine action of generators
  v:=(Concatenation(List([1..n-1],i->0),[1])) #CAST V
    ;
  d:=n;
  ct:=1;
  while true do
    for i in [1..ng] do
      g:=G.i;
      perms[i][ct]:=VNO(v^g);
    od;
    #   field automorphism:
    vi:=VNO(List([1..n],i->v[i]^p) #CAST V
      );
    perms[ng+1][ct]:=vi;
    #  move on to next vector
    ct:=ct+1;
    c:=n;
    while c > d and v[c]=lv do
      v[c]:=0;
      c:=c-1;
    od;
    if c=d then
      if d=1 then
        break;
      fi;
      v[d]:=0;
      d:=d-1;
      v[d]:=1;
    else
      # rewritten select statement
      if v[c]=0 then
        v[c]:=1;
      else
        v[c]:=v[c]*w;
      fi;
    fi;
  od;
  return SubStructure(SymmetricGroup(np),perms);
end);

AutSp4@:=function(q)
#  /out: Full automorphism group of PSp(4,q) for q=2^e./out: Socle quotient is
#  cyclic, and it has PSigmaSp(4,q) with index 2.
local 
   G,K,S,varX,act,agens,comps,d,diag,e,fac,g,gens,h,h2,i,id,im,im2,imgens,isc,j,
   mat,op,op2,sp2rep,w,x;
  Assert(1,q mod 2=0);
  fac:=CollectedFactors(q);
  e:=fac[1][2];
  K:=GF(q);
  varX:=GL(4,q);
  w:=PrimitiveElement(K);
  diag:=List([1..4],i->[i,i,1]);
  #  make Chevalley generators of Sp(4,q)
  gens:=[MatrixByEntries(K,4,4,Concatenation(diag,[[1,2,w],[3,4,-w]])) #CAST 
   varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[4,3,-w],[2,1,w]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[1,3,w],[2,4,w]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[4,2,w],[3,1,w]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[1,4,w]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[4,1,w]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[2,3,w]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[3,2,w]])) #CAST varX
    ];
  #  a
  #  -a
  #  a+b
  #  -a-b
  #  2a+b
  #  -2a-b
  #  b
  #  -b
  #  images under graph automorphism (q even)
  imgens:=[MatrixByEntries(K,4,4,Concatenation(diag,[[2,3,w^2]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[3,2,w^2]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[1,4,w^2]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[4,1,w^2]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[1,3,w],[2,4,w]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[4,2,w],[3,1,w]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[1,2,w],[3,4,-w]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[4,3,-w],[2,1,w]])) #CAST varX
    ];
  #  b
  #  -b
  #  2a+b
  #  -2a-b
  #  a+b
  #  -a-b
  #  a
  #  -a
  agens:=[];
  for i in [1..Size(gens)] do
    comps:=[gens[i],imgens[i]];
    for j in [1..e-1] do
      comps[2*j+1]:=MatToQ@(comps[2*j-1],2);
      comps[2*j+2]:=MatToQ@(comps[2*j],2);
    od;
    Add(agens,DirectSumMat(comps));
  od;
  mat:=0 #CAST MatrixAlgebra(GF(q),8*e)
    ;
  for j in [1..2*e-1] do
    InsertBlock(mat,Identity(varX),(j-1)*4+1,j*4+1);
  od;
  InsertBlock(mat,Identity(varX),(2*e-1)*4+1,1);
  Add(agens,mat);
  return SubStructure(GL(8*e,q),agens);
end;
;
InstallGlobalFunction(AutPSp4@,
function(q)
#  /out: Full automorphism group of PSp(4,q) for q=2^e./out: Socle quotient is
#  cyclic, and it has PSigmaSp(4,q) with index 2.
local 
   G,K,S,varX,act,d,diag,g,gens,h,h2,i,id,im,im2,imgens,isc,j,op,op2,sp2rep,w,
   x;
  Assert(1,q mod 2=0);
  K:=GF(q);
  varX:=GL(4,q);
  w:=PrimitiveElement(K);
  diag:=List([1..4],i->[i,i,1]);
  #  make Chevalley generators of Sp(4,q)
  gens:=[MatrixByEntries(K,4,4,Concatenation(diag,[[1,2,w],[3,4,-w]])) #CAST 
   varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[4,3,-w],[2,1,w]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[1,3,w],[2,4,w]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[4,2,w],[3,1,w]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[1,4,w]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[4,1,w]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[2,3,w]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[3,2,w]])) #CAST varX
    ];
  #  a
  #  -a
  #  a+b
  #  -a-b
  #  2a+b
  #  -2a-b
  #  b
  #  -b
  #  images under graph automorphism (q even)
  imgens:=[MatrixByEntries(K,4,4,Concatenation(diag,[[2,3,w^2]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[3,2,w^2]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[1,4,w^2]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[4,1,w^2]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[1,3,w],[2,4,w]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[4,2,w],[3,1,w]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[1,2,w],[3,4,-w]])) #CAST varX
    ,MatrixByEntries(K,4,4,Concatenation(diag,[[4,3,-w],[2,1,w]])) #CAST varX
    ];
  #  b
  #  -b
  #  2a+b
  #  -2a-b
  #  a+b
  #  -a-b
  #  a
  #  -a
  G:=SubStructure(GL(4,q),gens);
  #  Sp(4,q)
  # =v= MULTIASSIGN =v=
  im:=OrbitAction(G,SubStructure(RSpace(K,4),[1,0,0,0]));
  act:=im.val1;
  im:=im.val2;
  # =^= MULTIASSIGN =^=
  id:=GroupHomomorphismByImages(im,im,
    GeneratorsOfGroup(im),List([1..Ngens(im)],i->im.i));
  h:=GroupHomomorphismByImages(im,im,
    GeneratorsOfGroup(im),List(imgens,i->act(i)));
  h2:=h^2;
  #  make PSp(4,q).2 as permutation group with normal gens of PSp first
  sp2rep:=RepresentationSum(im,[id,h]);
  im2:=Image(sp2rep);
  d:=Degree(im);
  #  construct permutation op inducing outer automorphism
  #  first get action of op^2 on [1..d]
  S:=Stabiliser(im,1);
  x:=Random(S);
  while Size(Fix(x)) > 1 do
    x:=Random(S);
  od;
  op2:=[];
  for i in [1..d] do
    # =v= MULTIASSIGN =v=
    g:=IsConjugate(im,1,i);
    isc:=g.val1;
    g:=g.val2;
    # =^= MULTIASSIGN =^=
    op2[i]:=Representative(Fix((x^g)@h2));
  od;
  op:=[];
  for i in [1..d] do
    # =v= MULTIASSIGN =v=
    g:=IsConjugate(im,1,i);
    isc:=g.val1;
    g:=g.val2;
    # =^= MULTIASSIGN =^=
    j:=d+1^(g@h2);
    op[i]:=j;
    op[j]:=op2[i];
  od;
  op:=op #CAST SymmetricGroup(2*d)
    ;
  return SubStructure(SymmetricGroup(2*d),Concatenation(List([1,2],i->(SP(4,q)
   .i)@act@sp2rep),[op]));
end);

AutPSp@:=function(n,q)
#  -> ,GrpPerm  The full automorphism group of PSp ( n , q )
local fl,k,p;
  if not n >= 4 and IsEvenInt(n) then
    Error("First argument must be even and >= 4");
  fi;
  if not q >= 2 then
    Error("Second argument must be a finite field size");
  fi;
  # =v= MULTIASSIGN =v=
  k:=IsPrimePower(q);
  fl:=k.val1;
  p:=k.val2;
  k:=k.val3;
  # =^= MULTIASSIGN =^=
  if not fl then
    Error("Second argument must be a finite field size");
  fi;
  if IsOddInt(p) then
    if k=1 then
      return PGSp@(n,q);
    else
      return PGammaSp@(n,q);
    fi;
  else
    if n=4 then
      return AutPSp4@(q);
    else
      return PGammaSp@(n,q);
    fi;
  fi;
end;
;

