#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.34, 10/22/15 by AH

#  Global Variables used: AandB, ActionGenerator, Append, AssertAttribute,
#  AutPSp4, BaseRing, CorrectForm, Degree, Depth, DiagonalJoin,
#  DiagonalMatrix, DirectSum, Factorisation, Fix, GF, GL, GL2, GModule,
#  GOMinus, GOPlus, GSp, GU, Group, Identity, Image, InsertBlock, Integers,
#  IsConjugate, IsEven, IsIsomorphic, IsOdd, IsPrimePower, IsSquare, Log,
#  MatToQ, Matrix, MatrixAlgebra, NF, Ncols, Ngens, Nrows, OrbitAction,
#  OrbitImage, PGL2, PGSp, PGammaSp, PrimitiveElement, RSpace, Random,
#  RepresentationSum, Representative, SL, SL2, SU, Sp, Stabiliser, Sym,
#  SymmetricBilinearForm, TransformForm, Transpose, VNO, VectorSpace, act

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
local B,i,j;
  #   raise every element of matrix A to q-th power
  B:=MutableCopyMat(A);
  for i in [1..Length(A)] do
    for j in [1..Length(A[1])] do
      B[i][j]:=(A[i][j])^q;
    od;
  od;
  return B;
  
end;

InstallGlobalFunction(GL2@,
function(n,q)
local G,G2,gens,mat,i,m;
  #   Extension of GL(n,q) by graph isomorphisms - degree is twice as large.
  if n < 3 then
    Error("n must be at least 3 in GL2");
  fi;
  G:=GL(n,q);
  gens:=[];
  for i in GeneratorsOfGroup(G) do
    m:=IdentityMat(2*n,GF(q));
    m{[1..n]}{[1..n]}:=i;
    m{[n+1..2*n]}{[n+1..2*n]}:=TransposedMat(i^-1);
    Add(gens,m);
  od;

  mat:=MutableNullMat(2*n,2*n,GF(q));
  mat{[1..n]}{[n+1..2*n]}:=One(G);
  mat{[n+1..2*n]}{[1..n]}:=One(G);
  Add(gens,mat);
  G2:=Group(gens);
  Assert(1,Size(G2)=2*Size(G));
  return G2;
  
end);

SL2@:=function(n,q)
local G,G2,gens,mat,m,i;
  #   Extension of SL(n,q) by graph isomorphisms - degree is twice as large.
  if n < 3 then
    Error("n must be at least 3 in SL2");
  fi;
  G:=SL(n,q);
  gens:=[];
  for i in GeneratorsOfGroup(G) do
    m:=IdentityMat(2*n,GF(q));
    m{[1..n]}{[1..n]}:=i;
    m{[n+1..2*n]}{[n+1..2*n]}:=TransposedMat(i^-1);
    Add(gens,m);
  od;

  mat:=MutableNullMat(2*n,2*n,GF(q));
  mat{[1..n]}{[n+1..2*n]}:=One(G);
  mat{[n+1..2*n]}{[1..n]}:=One(G);
  Add(gens,mat);
  G2:=Group(gens);
  Assert(1,Size(G2)=2*Size(G));
  return G2;
  
end;

GammaL@:=function(n,q)
local X,e,f,gens,mat,p,m,i,j,gen;
  f:=Factors(q);
  p:=f[1];
  e:=Length(f);
  X:=GL(n,q);
  if e=1 then
    return X;
  fi;
  gens:=[];
  for gen in GeneratorsOfGroup(X) do
    #Append(~TILDE~gens,DiagonalJoin(List([0..e-1],j->MatToQ@(gen,p^j))));
    m:=IdentityMat(n*e,GF(q));
    for i in [0..e-1] do
      m{[i*n+1..(1+i)*n]}{[i*n+1..(1+i)*n]}:=MatToQ@(gen,p^i);
    od;
    Add(gens,m);
  od;
  mat:=MutableNullMat(n*e,n*e,GF(q));
  for j in [1..e-1] do
    #InsertBlock(~TILDE~mat,Identity(X),(j-1)*n+1,j*n+1);
    mat{[(j-1)*n+1..j*n]}{[j*n+1..(j+1)*n]}:=One(X);
  od;
  #InsertBlock(~TILDE~mat,Identity(X),(e-1)*n+1,1);
  mat{[(e-1)*n+1..j*n]}{[1..n]}:=One(X);
  Add(gens,mat);
  return Group(gens);
  
end;

# still TODO, but not yet needed

#@A GammaL2@:=function(n,q)
#@A local X,e,f,gens,mat,p;
#@A   f:=Factorisation(q);
#@A   p:=f[1][1];
#@A   e:=f[1][2];
#@A   X:=GL2@(n,q);
#@A   if e=1 then
#@A     return X;
#@A   fi;
#@A   gens:=[];
#@A   for gen in List([1..Ngens(X)],i->X.i) do
#@A     Append(~TILDE~gens,DiagonalJoin(List([0..e-1],j->MatToQ@(gen,p^j))));
#@A   od;
#@A   mat:=0*FORCEOne(MatrixAlgebra(GF(q),2*n*e));
#@A   for j in [1..e-1] do
#@A     InsertBlock(~TILDE~mat,Identity(X),(j-1*2*n)+1,(j*2*n)+1);
#@A   od;
#@A   InsertBlock(~TILDE~mat,Identity(X),(e-1*2*n)+1,1);
#@A   Append(~TILDE~gens,mat);
#@A   return SubStructure(GL(2*n*e,q),gens);
#@A   
#@A end;
#@A ;
#@A InstallGlobalFunction(GU2@,
#@A function(n,q)
#@A local G,G2,gens,mat;
#@A   #   Extension of GU(n,q) by frobenius isomorphism - degree is twice as
#@A   #  large.
#@A   if n < 3 then
#@A     Error("n must be at least 3 in GU2");
#@A   fi;
#@A   G:=GU(n,q);
#@A   gens:=List(List([1..Ngens(G)],i->G.i),g->DirectSum(g,MatToQ@(g,q)));
#@A   mat:=0*FORCEOne(MatrixAlgebra(GF(q^2),2*n));
#@A   InsertBlock(~TILDE~mat,Identity(G),1,n+1);
#@A   InsertBlock(~TILDE~mat,Identity(G),n+1,1);
#@A   Append(~TILDE~gens,mat);
#@A   G2:=SubStructure(GL(2*n,q^2),gens);
#@A   AssertAttribute(G2,"Order",2*Size(G));
#@A   return G2;
#@A   
#@A end;
#@A );
#@A SU2@:=function(n,q)
#@A local G,G2,gens,mat;
#@A   #   Extension of SU(n,q) by frobenius isomorphism - degree is twice as
#@A   #  large.
#@A   if n < 3 then
#@A     Error("n must be at least 3 in SU2");
#@A   fi;
#@A   G:=SU(n,q);
#@A   gens:=List(List([1..Ngens(G)],i->G.i),g->DirectSum(g,MatToQ@(g,q)));
#@A   mat:=0*FORCEOne(MatrixAlgebra(GF(q^2),2*n));
#@A   InsertBlock(~TILDE~mat,Identity(G),1,n+1);
#@A   InsertBlock(~TILDE~mat,Identity(G),n+1,1);
#@A   Append(~TILDE~gens,mat);
#@A   G2:=SubStructure(GL(2*n,q^2),gens);
#@A   AssertAttribute(G2,"Order",2*Size(G));
#@A   return G2;
#@A   
#@A end;
#@A ;
#@A GammaU@:=function(n,q)
#@A local X,e,f,gens,mat,p;
#@A   f:=Factorisation(q);
#@A   p:=f[1][1];
#@A   e:=f[1][2];
#@A   X:=GU(n,q);
#@A   gens:=[];
#@A   for gen in List([1..Ngens(X)],i->X.i) do
#@A     Append(~TILDE~gens,DiagonalJoin(List([0..(2*e)-1],j->MatToQ@(gen,p^j))))
#@A      ;
#@A   od;
#@A   mat:=0*FORCEOne(MatrixAlgebra(GF(q^2),2*n*e));
#@A   for j in [1..(2*e)-1] do
#@A     InsertBlock(~TILDE~mat,Identity(X),(j-1*n)+1,(j*n)+1);
#@A   od;
#@A   InsertBlock(~TILDE~mat,Identity(X),((2*e)-1*n)+1,1);
#@A   Append(~TILDE~gens,mat);
#@A   return SubStructure(GL(2*n*e,q^2),gens);
#@A   
#@A end;
#@A ;
#@A SigmaU@:=function(n,q)
#@A local X,e,f,gens,mat,p;
#@A   f:=Factorisation(q);
#@A   p:=f[1][1];
#@A   e:=f[1][2];
#@A   X:=SU(n,q);
#@A   gens:=[];
#@A   for gen in List([1..Ngens(X)],i->X.i) do
#@A     Append(~TILDE~gens,DiagonalJoin(List([0..(2*e)-1],j->MatToQ@(gen,p^j))))
#@A      ;
#@A   od;
#@A   mat:=0*FORCEOne(MatrixAlgebra(GF(q^2),2*n*e));
#@A   for j in [1..(2*e)-1] do
#@A     InsertBlock(~TILDE~mat,Identity(X),(j-1*n)+1,(j*n)+1);
#@A   od;
#@A   InsertBlock(~TILDE~mat,Identity(X),((2*e)-1*n)+1,1);
#@A   Append(~TILDE~gens,mat);
#@A   return SubStructure(GL(2*n*e,q^2),gens);
#@A   
#@A end;
#@A ;
#@A InstallGlobalFunction(PGL2@,
#@A function(n,q)
#@A local G,V;
#@A   #   Extension of PGL(n,q) by graph isomorphisms - degree is twice as 
#@A    large.
#@A   if n < 3 then
#@A     Error("n must be at least 3 in PGL2");
#@A   fi;
#@A   G:=GL2@(n,q);
#@A   V:=VectorSpace(G);
#@A   return OrbitImage(G,SubStructure(V,V.1));
#@A   
#@A end;
#@A );
#@A InstallGlobalFunction(PSL2@,
#@A function(n,q)
#@A local G,V;
#@A   #   Extension of PGL(n,q) by graph isomorphisms - degree is twice as 
#@A    large.
#@A   if n < 3 then
#@A     Error("n must be at least 3 in PSL2");
#@A   fi;
#@A   G:=SL2@(n,q);
#@A   V:=VectorSpace(G);
#@A   return OrbitImage(G,SubStructure(V,V.1));
#@A   
#@A end;
#@A );
#@A InstallGlobalFunction(PGammaL2@,
#@A function(n,q)
#@A local F,G,NF,V,VNO,Z,c,ct,d,g,gti,lv,ng,np,p,perm,perms,v,vi,w;
#@A   #  Extension of PGammaL by graph automorphism
#@A   if n < 3 then
#@A     Error("n must be at least 3 in PGammaL2");
#@A   fi;
#@A   Z:=Integers();
#@A   p:=Factorisation(q)[1][1];
#@A   if p=q then
#@A     return PGL2@(n,q);
#@A   fi;
#@A   np:=QuoInt((q^n)-1,q-1);
#@A   F:=GF(q);
#@A   # Implicit generator Assg from previous line.
#@A   w:=F.1
#@A   G:=GL(n,F);
#@A   ng:=Ngens(G);
#@A   perms:=List([1..ng+2],i->[]);
#@A   lv:=w^(q-2);
#@A   V:=VectorSpace(G);
#@A   NF:=Subfunc(x,[x=(SELECT(0 then 0 else (Log(x))+1))]);
#@A   VNO:=function(v)
#@A   local d,vn,vv;
#@A     d:=Depth(v);
#@A     vv:=(v*v[d])^(-1);
#@A     vn:=(QuoInt(1+((q^(n-d))-1),q-1))+(Sum(List([d+1..n],i->q^(n-i)*NF(vv[i]
#@A      ))));
#@A     return vn;
#@A     
#@A   end;
#@A   ;
#@A   #  loop through point and determine action of generators
#@A   v:=Concatenation(List([1..n-1],i->0),[1])*FORCEOne(V);
#@A   d:=n;
#@A   ct:=1;
#@A   while true do
#@A     for i in [1..ng] do
#@A       g:=G.i;
#@A       gti:=Transpose(g^(-1));
#@A       perms[i][ct]:=VNO(v^g);
#@A       perms[i][ct+np]:=(VNO(v^gti))+np;
#@A     od;
#@A     #   field automorphism:
#@A     vi:=VNO(List([1..n],i->(v[i])^p)*FORCEOne(V));
#@A     perms[ng+1][ct]:=vi;
#@A     perms[ng+1][ct+np]:=vi+np;
#@A     #   graph automorphism:
#@A     perms[ng+2][ct]:=ct+np;
#@A     perms[ng+2][ct+np]:=ct;
#@A     #  move on to next vector
#@A     ct:=ct+1;
#@A     c:=n;
#@A     while ((c > d) and (v[c]))=lv do
#@A       v[c]:=0;
#@A       c:=c-1;
#@A     od;
#@A     if c=d then
#@A       if d=1 then
#@A         break;
#@A       fi;
#@A       v[d]:=0;
#@A       d:=d-1;
#@A       v[d]:=1;
#@A     else
#@A       v[c]:=SELECT((v[c])=0 then 1 else v[c]*w);
#@A     fi;
#@A   od;
#@A   return SubStructure(Sym(2*np),perms);
#@A   
#@A end;
#@A );
#@A InstallGlobalFunction(PGammaLD2@,
#@A function(q)
#@A local F,G,NF,V,VNO,Z,c,ct,d,g,gti,lv,ng,np,p,perm,perms,v,vi,w;
#@A   #  This is a version of PGammaL2 in dimension 2, where we have no
#@A   #  graph isomorphism, and the result has degree q+1 as normal.
#@A   #  We need this because it allows us easily to set
#@A   #  up a monomorphism GL(2,q) -> PGammaL(2,q).
#@A   Z:=Integers();
#@A   p:=Factorisation(q)[1][1];
#@A   if p=q then
#@A     Error("q must be a proper prime power in PGammaLD2");
#@A   fi;
#@A   np:=q+1;
#@A   F:=GF(q);
#@A   # Implicit generator Assg from previous line.
#@A   w:=F.1
#@A   G:=GL(2,F);
#@A   ng:=Ngens(G);
#@A   perms:=List([1..ng+1],i->[]);
#@A   lv:=w^(q-2);
#@A   V:=VectorSpace(G);
#@A   NF:=Subfunc(x,[x=(SELECT(0 then 0 else (Log(x))+1))]);
#@A   VNO:=function(v)
#@A   local d,vn,vv;
#@A     d:=Depth(v);
#@A     vv:=(v*v[d])^(-1);
#@A     vn:=(QuoInt(1+((q^(2-d))-1),q-1))+(Sum(List([d+1..2],i->q^(2-i)*NF(vv[i]
#@A      ))));
#@A     return vn;
#@A     
#@A   end;
#@A   ;
#@A   #  loop through point and determine action of generators
#@A   v:=[0,1]*FORCEOne(V);
#@A   d:=2;
#@A   ct:=1;
#@A   while true do
#@A     for i in [1..ng] do
#@A       perms[i][ct]:=VNO((v^G).i);
#@A     od;
#@A     #   field automorphism:
#@A     vi:=VNO(List([1..2],i->(v[i])^p)*FORCEOne(V));
#@A     perms[ng+1][ct]:=vi;
#@A     #  move on to next vector
#@A     ct:=ct+1;
#@A     c:=2;
#@A     while ((c > d) and (v[c]))=lv do
#@A       v[c]:=0;
#@A       c:=c-1;
#@A     od;
#@A     if c=d then
#@A       if d=1 then
#@A         break;
#@A       fi;
#@A       v[d]:=0;
#@A       d:=d-1;
#@A       v[d]:=1;
#@A     else
#@A       v[c]:=SELECT((v[c])=0 then 1 else v[c]*w);
#@A     fi;
#@A   od;
#@A   return SubStructure(Sym(np),perms);
#@A   
#@A end;
#@A );
#@A InstallGlobalFunction(ModToQ@,
#@A function(M,q)
#@A local G;
#@A   #   same as MatToQ for GModule M
#@A   G:=Group(M);
#@A   return GModule(G,List(List([1..Ngens(G)],i->ActionGenerator(M,i))
#@A    ,m->MatToQ@(m,q)));
#@A   
#@A end;
#@A );
#@A GLT2@:=function(n,q)
#@A local A,G,G2,gens,mat;
#@A   #   Extension of GL(n,q^2) by twisted .2 - embeds in U(2*n,q)
#@A   G:=GL(n,q^2);
#@A   A:=MatrixAlgebra(GF(q^2),n);
#@A   gens:=List(List([1..Ngens(G)],i->G.i)
#@A    ,g->DirectSum(g,MatToQ@(Transpose(g^(-1))*FORCEOne(A),q)));
#@A   mat:=0*FORCEOne(MatrixAlgebra(GF(q^2),2*n));
#@A   InsertBlock(~TILDE~mat,Identity(G),1,n+1);
#@A   InsertBlock(~TILDE~mat,Identity(G),n+1,1);
#@A   Append(~TILDE~gens,mat);
#@A   G2:=SubStructure(GL(2*n,q^2),gens);
#@A   AssertAttribute(G2,"Order",2*Size(G));
#@A   return G2;
#@A   
#@A end;
#@A ;
#@A #   Code to produce various decorations of Sp(n,q)
#@A InstallGlobalFunction(GSp@,
#@A function(n,q)
#@A local G,m,o,w;
#@A   #   Extension of Sp(n,q) by diagonal isomorphism (and scalar matrices)
#@A   G:=Sp(n,q);
#@A   if (q mod 2)=0 then
#@A     return G;
#@A   fi;
#@A   w:=PrimitiveElement(GF(q));
#@A   m:=QuoInt(n,2);
#@A   o:=DiagonalMatrix(Concatenation(List([1..m],i->w),List([1..m],i->1)))
#@A    *FORCEOne(GL(n,q));
#@A   return SubStructure(GL(n,q),G.1,#TODO CLOSURE
#@A     G.2o);
#@A   
#@A end;
#@A );
#@A GammaSp@:=function(n,q)
#@A local X,e,f,gens,m,mat,o,p,w;
#@A   #  Extension of Sp(n,q) by diagonal isomorphism and field autos
#@A   Assert(1,IsEven(n));
#@A   f:=Factorisation(q);
#@A   p:=f[1][1];
#@A   e:=f[1][2];
#@A   if (q mod 2)=0 then
#@A     X:=Sp(n,q);
#@A   else
#@A     w:=PrimitiveElement(GF(q));
#@A     m:=QuoInt(n,2);
#@A     o:=DiagonalMatrix(Concatenation(List([1..m],i->w),List([1..m],i->1)))
#@A      *FORCEOne(GL(n,q));
#@A     X:=SubStructure(GL(n,q),(Sp(n,q)).1,#TODO CLOSURE
#@A       (Sp(n,q)).2o);
#@A   fi;
#@A   gens:=[];
#@A   for gen in List([1..Ngens(X)],i->X.i) do
#@A     Append(~TILDE~gens,DiagonalJoin(List([0..e-1],j->MatToQ@(gen,p^j))));
#@A   od;
#@A   mat:=0*FORCEOne(MatrixAlgebra(GF(q),n*e));
#@A   for j in [1..e-1] do
#@A     InsertBlock(~TILDE~mat,Identity(X),(j-1*n)+1,(j*n)+1);
#@A   od;
#@A   InsertBlock(~TILDE~mat,Identity(X),(e-1*n)+1,1);
#@A   Append(~TILDE~gens,mat);
#@A   return SubStructure(GL(n*e,q),gens);
#@A   
#@A end;
#@A ;
#@A GammaOPlus@:=function(n,q)
#@A local X,e,f,gens,m,mat,o,p,w;
#@A   #  Extension of GO+(n,q) by diagonal isomorphism and field autos
#@A   Assert(1,IsEven(n));
#@A   f:=Factorisation(q);
#@A   p:=f[1][1];
#@A   e:=f[1][2];
#@A   w:=PrimitiveElement(GF(q));
#@A   if (q mod 2)=0 then
#@A     X:=GOPlus(n,q);
#@A   else
#@A     m:=QuoInt(n,2);
#@A     o:=DiagonalMatrix(Concatenation(List([1..m],i->w),List([1..m],i->1)))
#@A      *FORCEOne(GL(n,q));
#@A     X:=SubStructure(GL(n,q),GOPlus(n,q),#TODO CLOSURE
#@A       o);
#@A   fi;
#@A   gens:=[];
#@A   for gen in List([1..Ngens(X)],i->X.i) do
#@A     Append(~TILDE~gens,DiagonalJoin(List([0..e-1],j->MatToQ@(gen,p^j))));
#@A   od;
#@A   mat:=0*FORCEOne(MatrixAlgebra(GF(q),n*e));
#@A   for j in [1..e-1] do
#@A     InsertBlock(~TILDE~mat,Identity(X),(j-1*n)+1,(j*n)+1);
#@A   od;
#@A   InsertBlock(~TILDE~mat,Identity(X),(e-1*n)+1,1);
#@A   Append(~TILDE~gens,mat);
#@A   return SubStructure(GL(n*e,q),gens);
#@A   
#@A end;
#@A ;
#@A GammaOMinus@:=function(n,q)
#@A local 
#@A    AandB,GC,M1,M2,X,a,cmat,comps,e,f,g,gens,gensc1,gensc2,gom,isit,m,mat,o,
#@A    p,w;
#@A   #  Extension of GO-(n,q) by diagonal isomorphism and field autos- this is
#@A   #  harder
#@A   Assert(1,IsEven(n));
#@A   f:=Factorisation(q);
#@A   p:=f[1][1];
#@A   e:=f[1][2];
#@A   w:=PrimitiveElement(GF(q));
#@A   gom:=GOMinus(n,q);
#@A   if (q mod 2)=0 then
#@A     X:=gom;
#@A   else
#@A     AandB@:=function(q,z)
#@A     local bool;
#@A       #  find elements of GF(q) with a^2+b^2=z.
#@A       for b in GF(q) do
#@A         # =v= MULTIASSIGN =v=
#@A         a:=IsSquare((b*FORCEOne(z-(GF(q))))^2);
#@A         bool:=a.val1;
#@A         a:=a.val2;
#@A         # =^= MULTIASSIGN =^=
#@A         if bool then
#@A           return rec(val1:=a,
#@A             val2:=b);
#@A         fi;
#@A       od;
#@A       Error("ERROR: couldn't find a and b in GF(",q,")");
#@A       
#@A     end;
#@A     ;
#@A     # =v= MULTIASSIGN =v=
#@A     b:=AandB@(q,w);
#@A     a:=b.val1;
#@A     b:=b.val2;
#@A     # =^= MULTIASSIGN =^=
#@A     m:=QuoInt(n,2);
#@A     o:=SELECT(((((n mod 4)=0) or (q-1)) mod 4)=0 then 
#@A      DiagonalJoin(Concatenation(List([1..m-1],i->Matrix(GF(q),2,2,[a,-b,b,a]
#@A      )),[Matrix(GF(q),2,2,[0,-1,w,0])])) else DiagonalJoin(List([1..m]
#@A      ,i->Matrix(GF(q),2,2,[a,-b,b,a]))));
#@A     # =v= MULTIASSIGN =v=
#@A     form:=SymmetricBilinearForm(GOMinus(n,q));
#@A     isit:=form.val1;
#@A     form:=form.val2;
#@A     # =^= MULTIASSIGN =^=
#@A     mat:=CorrectForm(form,n,q,"orth-");
#@A     o:=(mat*o*mat)^(-1)*FORCEOne(GL(n,q));
#@A     X:=SubStructure(GL(n,q),gom,#TODO CLOSURE
#@A       o);
#@A   fi;
#@A   #  work out correcting matrix to follow field automorphism
#@A   GC:=SubStructure(GL(n,q),List(List([1..Ngens(gom)],i->gom.i)
#@A    ,g->MatToQ@(g,p)));
#@A   cmat:=TransformForm(GC);
#@A   #  identify (gal*cmat)^e
#@A   gensc1:=[];
#@A   gensc2:=[];
#@A   for i in [1..Ngens(gom)] do
#@A     g:=gom.i;
#@A     for i in [1..e-1] do
#@A       g:=cmat^(-1)*MatToQ@(g,p)*cmat;
#@A     od;
#@A     Append(~TILDE~gensc1,g);
#@A     g:=gom.i;
#@A     g:=MatToQ@((cmat*g*cmat)^(-1),p^(e-1));
#@A     Append(~TILDE~gensc2,g);
#@A   od;
#@A   M1:=GModule(gensc1);
#@A   M2:=GModule(gom,gensc2);
#@A   # =v= MULTIASSIGN =v=
#@A   mate:=IsIsomorphic(M1,M2);
#@A   isit:=mate.val1;
#@A   mate:=mate.val2;
#@A   # =^= MULTIASSIGN =^=
#@A   Assert(1,isit);
#@A   gens:=[];
#@A   for gen in List([1..Ngens(X)],i->X.i) do
#@A     comps:=[gen];
#@A     for i in [2..e] do
#@A       comps[i]:=cmat^(-1)*MatToQ@(comps[i-1],p)*cmat;
#@A     od;
#@A     Append(~TILDE~gens,DiagonalJoin(comps));
#@A   od;
#@A   mat:=0*FORCEOne(MatrixAlgebra(GF(q),n*e));
#@A   for j in [1..e-1] do
#@A     InsertBlock(~TILDE~mat,Identity(X),(j-1*n)+1,(j*n)+1);
#@A   od;
#@A   InsertBlock(~TILDE~mat,mate,(e-1*n)+1,1);
#@A   Append(~TILDE~gens,mat);
#@A   return rec(val1:=SubStructure(GL(n*e,q),gens),
#@A     val2:=cmat);
#@A   
#@A end;
#@A ;
#@A PGSp@:=function(n,q)
#@A local G,V;
#@A   #   Extension of PSp(n,q) by diagonal isomorphism
#@A   G:=GSp@(n,q);
#@A   V:=VectorSpace(G);
#@A   return OrbitImage(G,SubStructure(V,V.1));
#@A   
#@A end;
#@A ;
#@A InstallGlobalFunction(PGammaSp@,
#@A function(n,q)
#@A local F,G,NF,V,VNO,Z,c,ct,d,g,gti,lv,ng,np,p,perm,perms,v,vi,w;
#@A   #  Extension of PGSp by field automorphism
#@A   Z:=Integers();
#@A   p:=Factorisation(q)[1][1];
#@A   if p=q then
#@A     return PGSp@(n,q);
#@A   fi;
#@A   np:=QuoInt((q^n)-1,q-1);
#@A   F:=GF(q);
#@A   # Implicit generator Assg from previous line.
#@A   w:=F.1
#@A   G:=GSp@(n,q);
#@A   ng:=Ngens(G);
#@A   perms:=List([1..ng+1],i->[]);
#@A   lv:=w^(q-2);
#@A   V:=VectorSpace(G);
#@A   NF:=Subfunc(x,[x=(SELECT(0 then 0 else (Log(x))+1))]);
#@A   VNO:=function(v)
#@A   local d,vn,vv;
#@A     d:=Depth(v);
#@A     vv:=(v*v[d])^(-1);
#@A     vn:=(QuoInt(1+((q^(n-d))-1),q-1))+(Sum(List([d+1..n],i->q^(n-i)*NF(vv[i]
#@A      ))));
#@A     return vn;
#@A     
#@A   end;
#@A   ;
#@A   #  loop through point and determine action of generators
#@A   v:=Concatenation(List([1..n-1],i->0),[1])*FORCEOne(V);
#@A   d:=n;
#@A   ct:=1;
#@A   while true do
#@A     for i in [1..ng] do
#@A       g:=G.i;
#@A       perms[i][ct]:=VNO(v^g);
#@A     od;
#@A     #   field automorphism:
#@A     vi:=VNO(List([1..n],i->(v[i])^p)*FORCEOne(V));
#@A     perms[ng+1][ct]:=vi;
#@A     #  move on to next vector
#@A     ct:=ct+1;
#@A     c:=n;
#@A     while ((c > d) and (v[c]))=lv do
#@A       v[c]:=0;
#@A       c:=c-1;
#@A     od;
#@A     if c=d then
#@A       if d=1 then
#@A         break;
#@A       fi;
#@A       v[d]:=0;
#@A       d:=d-1;
#@A       v[d]:=1;
#@A     else
#@A       v[c]:=SELECT((v[c])=0 then 1 else v[c]*w);
#@A     fi;
#@A   od;
#@A   return SubStructure(Sym(np),perms);
#@A   
#@A end;
#@A );
#@A AutSp4@:=function(q)
#@A local 
#@A    G,K,S,X,act,agens,comps,d,diag,e,fac,g,gens,h,h2,id,im,im2,imgens,isc,j,
#@A    mat,op,op2,sp2rep,w,x;
#@A   #   Full automorphism group of PSp(4,q) for q=2^e.
#@A   #   Socle quotient is cyclic, and it has PSigmaSp(4,q) with index 2.
#@A   Assert(1,(q mod 2)=0);
#@A   fac:=Factorisation(q);
#@A   e:=fac[1][2];
#@A   K:=GF(q);
#@A   X:=GL(4,q);
#@A   w:=PrimitiveElement(K);
#@A   diag:=List([1..4],i->Span(i,i,1));
#@A   #  make Chevalley generators of Sp(4,q)
#@A   gens:=[Matrix(K,4,4,Concatenation(diag,[Span(1,2,w),Span(3,4,-w)]))
#@A    *FORCEOne(X),Matrix(K,4,4,Concatenation(diag,[Span(4,3,-w),Span(2,1,w)]))
#@A    *FORCEOne(X),Matrix(K,4,4,Concatenation(diag,[Span(1,3,w),Span(2,4,w)]))
#@A    *FORCEOne(X),Matrix(K,4,4,Concatenation(diag,[Span(4,2,w),Span(3,1,w)]))
#@A    *FORCEOne(X),Matrix(K,4,4,Concatenation(diag,[Span(1,4,w)]))*FORCEOne(X)
#@A    ,Matrix(K,4,4,Concatenation(diag,[Span(4,1,w)]))*FORCEOne(X)
#@A    ,Matrix(K,4,4,Concatenation(diag,[Span(2,3,w)]))*FORCEOne(X)
#@A    ,Matrix(K,4,4,Concatenation(diag,[Span(3,2,w)]))*FORCEOne(X)];
#@A   #  a
#@A   #  -a
#@A   #  a+b
#@A   #  -a-b
#@A   #  2a+b
#@A   #  -2a-b
#@A   #  b
#@A   #  -b
#@A   #  images under graph automorphism (q even)
#@A   imgens:=[Matrix(K,4,4,Concatenation(diag,[Span(2,3,w^2)]))*FORCEOne(X)
#@A    ,Matrix(K,4,4,Concatenation(diag,[Span(3,2,w^2)]))*FORCEOne(X)
#@A    ,Matrix(K,4,4,Concatenation(diag,[Span(1,4,w^2)]))*FORCEOne(X)
#@A    ,Matrix(K,4,4,Concatenation(diag,[Span(4,1,w^2)]))*FORCEOne(X)
#@A    ,Matrix(K,4,4,Concatenation(diag,[Span(1,3,w),Span(2,4,w)]))*FORCEOne(X)
#@A    ,Matrix(K,4,4,Concatenation(diag,[Span(4,2,w),Span(3,1,w)]))*FORCEOne(X)
#@A    ,Matrix(K,4,4,Concatenation(diag,[Span(1,2,w),Span(3,4,-w)]))*FORCEOne(X)
#@A    ,Matrix(K,4,4,Concatenation(diag,[Span(4,3,-w),Span(2,1,w)]))*FORCEOne(X)
#@A    ];
#@A   #  b
#@A   #  -b
#@A   #  2a+b
#@A   #  -2a-b
#@A   #  a+b
#@A   #  -a-b
#@A   #  a
#@A   #  -a
#@A   agens:=[];
#@A   for i in [1..Size(gens)] do
#@A     comps:=[gens[i],imgens[i]];
#@A     for j in [1..e-1] do
#@A       comps[(2*j)+1]:=MatToQ@(comps[(2*j)-1],2);
#@A       comps[(2*j)+2]:=MatToQ@(comps[2*j],2);
#@A     od;
#@A     Append(~TILDE~agens,DiagonalJoin(comps));
#@A   od;
#@A   mat:=0*FORCEOne(MatrixAlgebra(GF(q),8*e));
#@A   for j in [1..(2*e)-1] do
#@A     InsertBlock(~TILDE~mat,Identity(X),(j-1*4)+1,(j*4)+1);
#@A   od;
#@A   InsertBlock(~TILDE~mat,Identity(X),((2*e)-1*4)+1,1);
#@A   Append(~TILDE~agens,mat);
#@A   return SubStructure(GL(8*e,q),agens);
#@A   
#@A end;
#@A ;
#@A InstallGlobalFunction(AutPSp4@,
#@A function(q)
#@A local 
#@A    G,K,S,X,act,d,diag,g,gens,h,h2,id,im,im2,imgens,isc,j,op,op2,sp2rep,w,x;
#@A   #   Full automorphism group of PSp(4,q) for q=2^e.
#@A   #   Socle quotient is cyclic, and it has PSigmaSp(4,q) with index 2.
#@A   Assert(1,(q mod 2)=0);
#@A   K:=GF(q);
#@A   X:=GL(4,q);
#@A   w:=PrimitiveElement(K);
#@A   diag:=List([1..4],i->Span(i,i,1));
#@A   #  make Chevalley generators of Sp(4,q)
#@A   gens:=[Matrix(K,4,4,Concatenation(diag,[Span(1,2,w),Span(3,4,-w)]))
#@A    *FORCEOne(X),Matrix(K,4,4,Concatenation(diag,[Span(4,3,-w),Span(2,1,w)]))
#@A    *FORCEOne(X),Matrix(K,4,4,Concatenation(diag,[Span(1,3,w),Span(2,4,w)]))
#@A    *FORCEOne(X),Matrix(K,4,4,Concatenation(diag,[Span(4,2,w),Span(3,1,w)]))
#@A    *FORCEOne(X),Matrix(K,4,4,Concatenation(diag,[Span(1,4,w)]))*FORCEOne(X)
#@A    ,Matrix(K,4,4,Concatenation(diag,[Span(4,1,w)]))*FORCEOne(X)
#@A    ,Matrix(K,4,4,Concatenation(diag,[Span(2,3,w)]))*FORCEOne(X)
#@A    ,Matrix(K,4,4,Concatenation(diag,[Span(3,2,w)]))*FORCEOne(X)];
#@A   #  a
#@A   #  -a
#@A   #  a+b
#@A   #  -a-b
#@A   #  2a+b
#@A   #  -2a-b
#@A   #  b
#@A   #  -b
#@A   #  images under graph automorphism (q even)
#@A   imgens:=[Matrix(K,4,4,Concatenation(diag,[Span(2,3,w^2)]))*FORCEOne(X)
#@A    ,Matrix(K,4,4,Concatenation(diag,[Span(3,2,w^2)]))*FORCEOne(X)
#@A    ,Matrix(K,4,4,Concatenation(diag,[Span(1,4,w^2)]))*FORCEOne(X)
#@A    ,Matrix(K,4,4,Concatenation(diag,[Span(4,1,w^2)]))*FORCEOne(X)
#@A    ,Matrix(K,4,4,Concatenation(diag,[Span(1,3,w),Span(2,4,w)]))*FORCEOne(X)
#@A    ,Matrix(K,4,4,Concatenation(diag,[Span(4,2,w),Span(3,1,w)]))*FORCEOne(X)
#@A    ,Matrix(K,4,4,Concatenation(diag,[Span(1,2,w),Span(3,4,-w)]))*FORCEOne(X)
#@A    ,Matrix(K,4,4,Concatenation(diag,[Span(4,3,-w),Span(2,1,w)]))*FORCEOne(X)
#@A    ];
#@A   #  b
#@A   #  -b
#@A   #  2a+b
#@A   #  -2a-b
#@A   #  a+b
#@A   #  -a-b
#@A   #  a
#@A   #  -a
#@A   G:=SubStructure(GL(4,q),gens);
#@A   #  Sp(4,q)
#@A   # =v= MULTIASSIGN =v=
#@A   im:=OrbitAction(G,SubStructure(RSpace(K,4),[1,0,0,0]));
#@A   act:=im.val1;
#@A   im:=im.val2;
#@A   # =^= MULTIASSIGN =^=
#@A   id:=GroupHomomorphismByImages(im,im,
#@A     GeneratorsOfGroup(im),List([1..Ngens(im)],i->im.i));
#@A   h:=GroupHomomorphismByImages(im,im,
#@A     GeneratorsOfGroup(im),List(imgens,i->act(i)));
#@A   h2:=h^2;
#@A   #  make PSp(4,q).2 as permutation group with normal gens of PSp first
#@A   sp2rep:=RepresentationSum(im,[id,h]);
#@A   im2:=Image(sp2rep);
#@A   d:=Degree(im);
#@A   #  construct permutation op inducing outer automorphism
#@A   #  first get action of op^2 on [1..d]
#@A   S:=Stabiliser(im,1);
#@A   x:=Random(S);
#@A   while Size(Fix(x)) > 1 do
#@A     x:=Random(S);
#@A   od;
#@A   op2:=[];
#@A   for i in [1..d] do
#@A     # =v= MULTIASSIGN =v=
#@A     g:=IsConjugate(im,1,i);
#@A     isc:=g.val1;
#@A     g:=g.val2;
#@A     # =^= MULTIASSIGN =^=
#@A     op2[i]:=Representative(Fix(x^g@h2));
#@A   od;
#@A   op:=[];
#@A   for i in [1..d] do
#@A     # =v= MULTIASSIGN =v=
#@A     g:=IsConjugate(im,1,i);
#@A     isc:=g.val1;
#@A     g:=g.val2;
#@A     # =^= MULTIASSIGN =^=
#@A     j:=(d+1)^(g@h2);
#@A     op[i]:=j;
#@A     op[j]:=op2[i];
#@A   od;
#@A   op:=op*FORCEOne(Sym(2*d));
#@A   return SubStructure(Sym(2*d),Concatenation(List([1,2],i->(Sp(4,q))
#@A    .i@act@sp2rep),[op]));
#@A   
#@A end;
#@A );
#@A AutPSp@:=function(n,q)
#@A #  -> ,GrpPerm  The full automorphism group of PSp ( n , q )
#@A local fl;
#@A   if not (n >= 4) and (IsEven(n))then
#@A     Error("First argument must be even and >= 4");
#@A   if not q >= 2then
#@A     Error("Second argument must be a finite field size");
#@A   # =v= MULTIASSIGN =v=
#@A   k:=IsPrimePower(q);
#@A   fl:=k.val1;
#@A   p:=k.val2;
#@A   k:=k.val3;
#@A   # =^= MULTIASSIGN =^=
#@A   if not flthen
#@A     Error("Second argument must be a finite field size");
#@A   if IsOdd(p) then
#@A     if k=1 then
#@A       return PGSp@(n,q);
#@A     else
#@A       return PGammaSp@(n,q);
#@A     fi;
#@A   else
#@A     if n=4 then
#@A       return AutPSp4@(q);
#@A     else
#@A       return PGammaSp@(n,q);
#@A     fi;
#@A   fi;
#@A   
#@A end;
#@A ;
#@A 
