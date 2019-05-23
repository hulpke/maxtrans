#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: ActionGenerators, Append, AssertAttribute,
#  Centraliser, ChangeForm, ChangeMat, ChangeRing, Coefficients,
#  CompositionFactors, CorrectDiag, DefiningPolynomial, DerivedSubgroup,
#  Determinant, DiagonalMatrix, Dimension, Domain, Dual, Eltseq, FPGroupStrong,
#  GF, GL, GModule, GammaL1, GammaSpMeetSp, GammaUMeetSp, Generators, GetAlt6,
#  GetAltSix, GetConjMat, GetCoords, GetExtraSpec, GetImprims, GetL2p,
#  GetLineStab, GetPointStab, GetRandomConj, GetReducibles, GetSemilins,
#  GetSym6, GtoSp, Id, Identity, IndecomposableSummands, IntegerRing,
#  IsAbsolutelyIrreducible, IsConjugate, IsDiagonal, IsEven, IsIsomorphic,
#  IsOdd, IsPrime, IsSquare, ListMatToQ, MakeSpHomomGeneral, Matrix,
#  MatrixAlgebra, Ngens, Orbit, OrbitAction, Order, PSp, Parent,
#  PrimitiveElement, Quotrem, RSpace, Random, RandomSchreier, RecogniseSpOdd,
#  Root, SL, Socle, Sp, Sp4pMaximals, Sym, SymplecticForm, TensorPower,
#  Transpose, WreathProduct, homom

#  Defines: ChangeForm, ChangeMat, CorrectDiag, GammaL1, GammaSpMeetSp,
#  GammaUMeetSp, GetAlt6, GetAltSix, GetConjMat, GetCoords, GetExtraSpec,
#  GetImprims, GetL2p, GetLineStab, GetPointStab, GetRandomConj, GetReducibles,
#  GetSemilins, GetSym6, ListMatToQ, MakeSpHomomGeneral, PSp4pIdentify,
#  Sp4pMaximals, SymplecticForm

DeclareGlobalFunction("MakeSpHomomGeneral@");

DeclareGlobalFunction("PSp4pIdentify@");

DeclareGlobalFunction("MakeSpHomomGeneral@");

#  
#  Constructively recognise and find maximal subgroups  of S(4,p).
#  Recognition by Derek Holt.
#  Maximals by Colva Roney-Dougal.

SymplecticForm@:=function(G)
#  /out:G should be matrix group acting (absolutely?) irreducibly./out:Decide
#  whether G preserves symplectic form.
local D,M,bool,mat;
  M:=GModule(G);
  if not IsAbsolutelyIrreducible(G) then
    Info(InfoWarning,1,"group is not absolutely irreducible");
  fi;
  D:=Dual(M);
  # =v= MULTIASSIGN =v=
  mat:=IsIsomorphic(M,D);
  bool:=mat.val1;
  mat:=mat.val2;
  # =^= MULTIASSIGN =^=
  if bool then
    if mat=-TransposedMat(mat) then
      return rec(val1:=bool,
        val2:=mat);
    fi;
  fi;
  return rec(val1:=false,
    val2:=_);
end;
;
ListMatToQ@:=function(a,q)
#  /out: raise every element of matrix A to q-th power.
local i,list;
  list:=Eltseq(a);
  for i in [1..Size(list)] do
    list[i]:=list[i]^q;
  od;
  return list;
end;
;
#  ********************************************************************
ChangeMat@:=function(mat,type,d,p)
if type="unitary" then
    return TransposedMat(ListMatToQ@(mat,p) #CAST GL(d,p^2)
      );
  else
    return TransposedMat(mat);
  fi;
end;
;
#  *********************************************************************
#  * GetCoords returns the column number in which row i of the form must
#  * be nonzero for conjugation.

GetCoords@:=function(i,d,q,type)
if type="unitary" then
    return i;
  elif type="symplectic" then
    return d-i+1;
  elif type="orth+" then
    if IsOddInt(q) then
      return i;
    else
      return d-i+1;
    fi;
  elif type="orth-" then
    if IsOddInt(q) then
      return i;
    else
      return d-i+1;
    fi;
  elif type="orth" then
    if IsOddInt(q) then
      return i;
    else
      return d-i+1;
    fi;
  fi;
  return 0;
end;
;
#  *********************************************************************
#  * CorrectInTorus takes a (diagonal or antidiagonal)
#  * form matrix, and the type of form that
#  * it is supposed to represent, and finds a conjugating element such
#  * that the group will now preserve a form matrix consisting of all
#  * +1s and -1s.
#  * In the case of an orthogonal form of type "oplus" it turns
#  * everything into 1s and zs, where z is a primitive element of the
#  * field.
#  * q is a prime power.

CorrectDiag@:=function(form,d,q,type)
local 
   a,b,bool,final,i,list,mat1,mat2,mat3,mat4,newform,newlist,nonsquares,ns,p,
   quot,rem,temp,x,z;
  if type="unitary" then
    # =v= MULTIASSIGN =v=
    p:=IsSquare(q);
    bool:=p.val1;
    p:=p.val2;
    # =^= MULTIASSIGN =^=
    return DiagonalMat(List([1..d],i->Root(form[i][i],p+1)^-1)) #CAST GL(d,q)
      ;
  elif type="symplectic" or IsEvenInt(q) then
    list:=List([1..QuotientRemainder(d,2)],i->(form[i][d-i+1])^-1);
    return DiagonalMat(Concatenation(list,List([1..QuotientRemainder(d,2)],i->1 
     #CAST GF(q)
      ))) #CAST GL(d,q)
      ;
  else
    z:=PrimitiveElement(GF(q));
    list:=[];
    nonsquares:=[];
    for i in [1..d] do
      # =v= MULTIASSIGN =v=
      b:=IsSquare(form[i][i]);
      a:=b.val1;
      b:=b.val2;
      # =^= MULTIASSIGN =^=
      if a then
        Add(list,(b^-1));
      else
        # =v= MULTIASSIGN =v=
        b:=IsSquare(form[i][i]*(z^-1));
        a:=b.val1;
        b:=b.val2;
        # =^= MULTIASSIGN =^=
        Add(list,(b^-1));
        Add(nonsquares,i);
      fi;
    od;
    mat1:=DiagonalMat(list) #CAST GL(d,q)
      ;
    #  "checking for nonsquare entries";
    ns:=Size(nonsquares);
    if ns=0 then
      return mat1;
    fi;
    if type="orth" and IsOddInt(ns) then
      temp:=Filtered([1..d],x->not x in nonsquares);
      nonsquares:=temp;
      ns:=Size(nonsquares);
    fi;
    #  "turning pairs of nonsquares into squares";
    x:=false;
    while not x do
      b:=Random(GF(q));
      # =v= MULTIASSIGN =v=
      a:=IsSquare(z^-1-b^2);
      x:=a.val1;
      a:=a.val2;
      # =^= MULTIASSIGN =^=
      if type="orth" and x then
        a:=a^-1;
      fi;
    od;
    # =v= MULTIASSIGN =v=
    rem:=QuotientRemainder(ns,2);
    quot:=rem.val1;
    rem:=rem.val2;
    # =^= MULTIASSIGN =^=
    list:=[];
    #  nonsquares;
    #  mat1*form*Transpose(mat1);
    for i in [1..d] do
      if not i in nonsquares then
        Add(list,[i,i,1]);
      fi;
    od;
    for i in [1..quot] do
      Add(list,[nonsquares[2*i-1],nonsquares[2*i-1],a]);
      Add(list,[nonsquares[2*i-1],nonsquares[2*i],b]);
      Add(list,[nonsquares[2*i],nonsquares[2*i-1],b]);
      Add(list,[nonsquares[2*i],nonsquares[2*i],-a]);
    od;
    if rem=1 then
      final:=nonsquares[ns];
      Add(list,[nonsquares[ns],nonsquares[ns],1]);
    fi;
    mat2:=MatrixByEntries(GF(q),d,d,list) #CAST GL(d,q)
      ;
    #  "after mat2 form is", mat2*mat1*form*Transpose(mat1)*Transpose(mat2);
    #  "moving final nonsquare entry to (d, d) position";
    mat3:=Identity(GL(d,q));
    if rem=1 then
      if not final=d then
        newlist:=Concatenation(List(Filtered([1..d],i->not i=final and not i=d)
         ,i->[i,i,1]),[[final,d,1],[d,final,1]]);
        mat3:=MatrixByEntries(GF(q),d,d,newlist) #CAST GL(d,q)
          ;
      fi;
    fi;
    #  "after mat3 form is";
    newform:=mat3*mat2*mat1*form*TransposedMat(mat1)*TransposedMat(mat2)
     *TransposedMat(mat3);
    #  newform;
    #  "converting matrix into 1s and primitives";
    list:=[];
    for i in [1..d] do
      # =v= MULTIASSIGN =v=
      b:=IsSquare(newform[i][i]);
      a:=b.val1;
      b:=b.val2;
      # =^= MULTIASSIGN =^=
      if a then
        Add(list,(b^-1));
      else
        # =v= MULTIASSIGN =v=
        b:=IsSquare(newform[i][i]*(z^-1));
        a:=b.val1;
        b:=b.val2;
        # =^= MULTIASSIGN =^=
        Add(list,(b^-1));
      fi;
    od;
    mat4:=DiagonalMat(list) #CAST GL(d,q)
      ;
    return mat4*mat3*mat2*mat1;
  fi;
end;
;
#  **************************************************************
#  
#  * This function returns a matrix that is the identity on the
#  * first i rows and columns, and a random (invertible) matrix on
#  * the bottom d \times d block.
#  * in the symplectic case, or orthogonals over even fields,
#  * it's the first rows and final columns that are zero.

GetRandomConj@:=function(i,d,q,type)
local j,k,newelt,startelt;
  startelt:=Random(GL(d-i,q));
  newelt:=DiagonalMat(List([1..d],j->1 #CAST GF(q)
    ));
  if type="unitary" or (not (type="symplectic") and IsOddInt(q)) then
    for j in [1..d-i] do
      for k in [1..d-i] do
        newelt[i+j][i+k]:=startelt[j][k];
      od;
    od;
  else
    for j in [1..d-i] do
      for k in [1..d-i] do
        newelt[i+j][k]:=startelt[j][k];
      od;
    od;
  fi;
  return newelt;
end;
;
#  **************************************************************
GetConjMat@:=function(form,col,d,q,type)
local conjmat,i,vec;
  conjmat:=DiagonalMat(List([1..d],i->1 #CAST GF(q)
    ));
  vec:=form[col];
  if type="unitary" or (not type="symplectic" and IsOddInt(q)) then
    for i in [(col+1)..d] do
      conjmat[i][col]:=-form[i][col]*(form[col][col]^-1);
    od;
  elif type="symplectic" or IsEvenInt(q) then
    for i in Concatenation([1..(d-col)],[(d-col+2)..d]) do
      conjmat[i][d-col+1]:=-form[i][col]*(form[d-col+1][col]^-1);
    od;
  fi;
  return conjmat #CAST GL(d,q)
    ;
end;
;
#  *********************************************************************
#  
#  * finds a matrix that will conjugate group1 (preserving form1) to
#  * group2 (preserving form2). group1 and group2 are not currently
#  * used by the function, but have been left in for testing purposes.
#  * q is a prime power.

ChangeForm@:=function(form1,form2,d,q,type,group1,group2)
#  /out:"at beginning of ChangeForm, form1 is", form1:Magma;/out:"At beginning
#  of ChangeForm, form2 is", form2:Magma;/out:"type is", type;
local 
   bool,conj1,conj2,conj_torus1,conj_torus2,conjmat1,conjmat2,coords,form1,
   form2,i,j,mat1,mat2,p,temp1,temp2;
  if type="unitary" then
    # =v= MULTIASSIGN =v=
    p:=IsSquare(q);
    bool:=p.val1;
    p:=p.val2;
    # =^= MULTIASSIGN =^=
  else
    p:=q;
  fi;
  conj1:=Identity(GL(d,q));
  conj2:=Identity(GL(d,q));
  for i in [1..d-1] do
    #   First we have to deal with the problem that the relevant matrix
    #  * entry (entry [coords][i]) may be zero.
    #  * In the unitary case this is entry [i][i].
    #  * In the symplectic case it's entry [d-i+1][i].
    #  * In orth+ case it's also [d-i+1][i]. We also need [i][i] to be zero.
    
    temp1:=form1;
    temp2:=form2;
    mat1:=Identity(GL(d,q));
    mat2:=Identity(GL(d,q));
    coords:=GetCoords@(i,d,q,type);
    if type="unitary" or type="symplectic" or type="orth+" or type="orth-" or 
       type="orth" then
      while temp1[coords][i]=0 do
        mat1:=GetRandomConj@(i-1,d,q,type);
        #  "mat1 is", mat1;
        temp1:=mat1*form1*ChangeMat@(mat1,type,d,p);
        #  "at step ", i, "temp1 is ", temp1;
      od;
    fi;
    form1:=temp1;
    #  "after removing zeros, form1 is", form1;
    conj1:=mat1*conj1;
    if type="unitary" or type="symplectic" or type="orth+" or type="orth-" or 
       type="orth" then
      while temp2[coords][i]=0 do
        mat2:=GetRandomConj@(i-1,d,q,type);
        temp2:=mat2*form2*ChangeMat@(mat2,type,d,p);
        #  "temp2 is ", temp2;
      od;
    fi;
    form2:=temp2;
    #  "after removing zeros, form2 is", form2:Magma;
    conj2:=mat2*conj2;
    #   So by this stage the relevant entry is guaranteed to be nonzero
    
    conjmat1:=GetConjMat@(form1,i,d,q,type);
    conjmat2:=GetConjMat@(form2,i,d,q,type);
    form1:=conjmat1*form1*ChangeMat@(conjmat1,type,d,p);
    form2:=conjmat2*form2*ChangeMat@(conjmat2,type,d,p);
    conj1:=conjmat1*conj1;
    conj2:=conjmat2*conj2;
    #  "conjmat1 = ", conjmat1;
    #  "conjmat2 = ", conjmat2;
    #  "form1 after step", i, "is ", form1;
    #  "form2 after step", i, "is ", form2;
  od;
  #   By now the matrix should either be diagonal or antidiagonal.
  
  if type="unitary" or (IsOddInt(q) and (type="orth+" or type="orth-" or 
     type="orth")) then
    Assert(1,IsDiagonal(form1));
    Assert(1,IsDiagonal(form2));
  elif type="symplectic" or IsEvenInt(q) then
    for i in [1..d] do
      for j in [1..d] do
        if not i=(d-j+1) then
          Assert(1,form1[i][j]=0);
          Assert(1,form2[i][j]=0);
        fi;
      od;
    od;
  fi;
  #  "before conj_torus, form1 is", form1;
  #  "before conj_torus, form2 is", form2;
  conj_torus1:=CorrectDiag@(form1,d,p,type);
  conj_torus2:=CorrectDiag@(form2,d,p,type);
  #  "conj_torus1 is", conj_torus1;
  #  "conj_torus2 is", conj_torus2;
  form1:=conj_torus1*form1*ChangeMat@(conj_torus1,type,d,p);
  form2:=conj_torus2*form2*ChangeMat@(conj_torus2,type,d,p);
  conj1:=conj_torus1*conj1;
  conj2:=conj_torus2*conj2;
  #   conj1 maps group preserving form1 to the group preserving
  #  * identity (in unitary case) or AntiDiag([1..1-1..-1]) (in symplectic
  #  * case). conj2 does the same to the group preserving form2.
  #  * so conj2(-1)conj1 should map group preserving form1 to group
  #  * preserving form2.
  
  return (conj1^-1)*conj2;
end;
;
#  tested on primes up to about 100.
#  REQUIRE P>3.
#  point stab isomorphic to p^3:(p-1) \times Sp(2, p).
GetPointStab@:=function(p)
local a,b,c,d,e,f,z;
  z:=PrimitiveElement(GF(p));
  #  act as scalar on stabilised point [1, 0, 0, 0]
  a:=DiagonalMat([z,1,1,z^-1]) #CAST GL(4,p)
    ;
  #  Sp(2, q) on <[0, 1, 0, 0], [0, 0, 1, 0]>
  b:=[1,0,0,0,0,z,0,0,0,0,z^-1,0,0,0,0,1] #CAST GL(4,p)
    ;
  c:=[1,0,0,0,0,-1,1,0,0,-1,0,0,0,0,0,1] #CAST GL(4,p)
    ;
  #  and the p-gunk, fixed so preserves symplectic form.
  d:=[1,0,0,0,1,1,0,0,0,0,1,0,0,0,-1,1] #CAST GL(4,p)
    ;
  e:=[1,0,0,0,0,1,0,0,1,0,1,0,0,1,0,1] #CAST GL(4,p)
    ;
  f:=[1,0,0,0,0,1,0,0,0,0,1,0,1,0,0,1] #CAST GL(4,p)
    ;
  return SubStructure(GL(4,p),a,#TODO CLOSURE
    b,c,d,e,f);
end;
;
#  line stab isomorphic to p^3:GL(2, p). Stabilise a totally isotropic
#  2-space. <[1, 0, 0,0], [0, 1, 0, 0]>
GetLineStab@:=function(p)
local a,b,c,d,e,f,z;
  z:=PrimitiveElement(GF(p));
  #  torus
  a:=DiagonalMat([z,1,1,z^-1]);
  b:=DiagonalMat([1,z,z^-1,1]);
  #  p-gunk.
  c:=[1,0,0,0,0,1,0,0,1,0,1,0,0,1,0,1] #CAST GL(4,p)
    ;
  d:=[1,0,0,0,0,1,0,0,0,1,1,0,0,0,0,1] #CAST GL(4,p)
    ;
  e:=[1,0,0,0,0,1,0,0,0,0,1,0,1,0,0,1] #CAST GL(4,p)
    ;
  #  remaining required generator for GL (this+torus=gl);
  f:=[-1,1,0,0,-1,0,0,0,0,0,-1,-1,0,0,1,0] #CAST GL(4,p)
    ;
  return SubStructure(GL(4,p),a,#TODO CLOSURE
    b,c,d,e,f);
end;
;
GetReducibles@:=function(p)
Assert(1,p > 3 and IsPrimeInt(p));
  return rec(val1:=GetPointStab@(p),
    val2:=GetLineStab@(p));
end;
;
#  
#  * To make the 2nd group we use the fact that
#  * GL(2, q) = <Diag[gamma, 1], [-1, 1, -1, 0]>;
#  * idea is to act as gens of gl on (e1, e2) and compensate on f1, f2,
#  * or swap the subspaces over.

GetImprims@:=function(q)
local 
   bool,e,form,g,gamma,imprim1,imprim2,newmat1,newmat2,newmat3,standard_form,x;
  gamma:=PrimitiveElement(GF(q));
  e:=1 #CAST GF(q)
    ;
  g:=WreathProduct(SP(2,q),SymmetricGroup(2));
  # =v= MULTIASSIGN =v=
  form:=SymplecticForm@(g);
  bool:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  #  "form_g = ", form;
  standard_form:=[0,0,0,e,0,0,e,0,0,-e,0,0,-e,0,0,0] #CAST GL(4,q)
    ;
  x:=ChangeForm@(form,standard_form,4,q,"symplectic",g,SP(4,q)) #CAST GL(4,q)
    ;
  imprim1:=g^x;
  newmat1:=DiagonalMat([gamma,e,e,gamma^-1]) #CAST GL(4,q)
    ;
  newmat2:=[-e,e,0,0,-e,0,0,0,0,0,-e,-e,0,0,e,0] #CAST GL(4,q)
    ;
  newmat3:=[0,0,-e,0,0,0,0,-e,e,0,0,0,0,e,0,0] #CAST GL(4,q)
    ;
  imprim2:=SubStructure(GL(4,q),newmat1,#TODO CLOSURE
    newmat2,newmat3);
  return rec(val1:=imprim1,
    val2:=imprim2);
end;
;
#  This produces GammaL(1, p^s) \leq GL(s, p)
GammaL1@:=function(s,p)
#  /out:"making singer cycle for GL(1, p^s) in GL(s, p)";
local coeffs,cxp,field_auto,grp,mat,pol,x;
  pol:=DefiningPolynomial(GF(p^s));
  x:=Parent(pol).1;
  coeffs:=Coefficients(pol);
  mat:=MatrixByEntries(GF(p),s,s,Concatenation(List([1..s-1],i->[i,i+1,1])
   ,List([1..s],i->[s,i,-coeffs[i]]))) #CAST GL(s,p)
    ;
  #  
  #  * find field automorphism - the reason that x^s has been added to the
  #  * argument below is to ensured that cxp[i] and cxp2[i] are always defined!
  #  * The basis of the field is [1, x, x^2, \ldots, x^(s-1)]
  
  cxp:=List([1..s-1],i->Coefficients(x^s+x^(i*p) mod pol));
  field_auto:=MatrixByEntries(GF(p),s,s,Concatenation([[1,1,1]]
   ,Concatenation(List([1..s],j->List([1..s-1],i->[i+1,j,cxp[i][j]]))))) #CAST 
   GL(s,p)
    ;
  grp:=SubStructure(GL(s,p),mat,#TODO CLOSURE
    field_auto);
  return grp;
end;
;
#   This uses previous function to produce Sp(d/2, p^2).2 \leq Sp(d, p)
#  * take singer cycle from gammal1(s, p). use known generators for
#  * Sp(d/2, p^2).  make block matrices with singer as blocks inside gens from
#  * gl.

#   We use the fact that Sp(d, q).1 = DiagonalMatrix([z, 1, \ldots,
#  * z^-1]), where z is a primitive element of GF(q), and that entries
#  * of Sp(d, q).2 all lie in the base field.

#  ****************************************************************
GammaSpMeetSp@:=function(d,s,p)
local dim,g1,gammal1,gens1,gens1_inv,gens2,gens4,newmat1,newmat2,newmat3,o;
  Assert(1,d mod s=0);
  dim:=QuoInt(d,s);
  Assert(1,IsEvenInt(dim));
  gammal1:=GammaL1@(s,p);
  g1:=gammal1.1;
  o:=Order(DeterminantMat(g1));
  gens1:=g1^o;
  gens1_inv:=gens1^-1;
  gens2:=gammal1.2;
  gens4:=SP(dim,p^s).2;
  #   "putting singer cycle as block into gens for GL(dim, p)";
  newmat1:=MatrixByEntries(GF(p),d,d,Concatenation(Concatenation(List([1..s],
    i->List([1..s],
      j->[i,j,gens1[i][j]])),List([s+1..(d-s)],i->[i,i,1 #CAST GF(p)
    ]),Concatenation(List([1..s],
    i->List([1..s],
      j->[i+d-s,j+d-s,gens1_inv[i][j]]))));
  newmat2:=MatrixByEntries(GF(p),d,d,Concatenation(List([1..dim]
     ,k->Concatenation(List([0..s-1],
    i->List([0..s-1],
      j->[k+i*s,k+j*s,gens4[i+1][j+1]])))));
  #   "putting frobenius aut as block into gens for GL(dim, p)";
  newmat3:=MatrixByEntries(GF(p),d,d,Concatenation(List([0..dim-1]
     ,k->Concatenation(List([1..s],
    i->List([1..s],
      j->[i+k*s,j+k*s,gens2[i][j]])))));
  return SubStructure(GL(d,p),newmat1,#TODO CLOSURE
    newmat2,newmat3);
end;
;
#  *****************************************************************
#  
#  * This makes GU(d/2, p).2 \leq Sp(d, p).
#  * we take the description of generators for GU from Don's paper -
#  * "Pairs of generators for Matrix groups, I".
#  * Submatrices are named accordingly.

GammaUMeetSp@:=function(d,p)
local 
   beta,epsilon,epsilon_conj_inv,frob_aut,frobmat1,frobmat2,gammal1,
   gens1_power4,half,minus_beta_inv,minus_nu_inv,newmat1,newmat2,newmat2_list,
   newmat3,nu,nu_inv,power,temp,two_power;
  half:=QuoInt(d,2);
  gammal1:=GammaL1@(2,p);
  epsilon:=gammal1.1;
  #  
  #  * to be substitued into first generator of GU;
  
  epsilon_conj_inv:=epsilon^(-p);
  #  
  #  * to be substituted into second generatror of GU if half is even;
  
  if half=2 then
    beta:=epsilon^(QuoInt((p+1),2));
    minus_beta_inv:=-(beta^-1);
  elif IsEvenInt(half) then
    power:=epsilon^(p-1);
    temp:=[power[1][1]+1,power[1][2],power[2][1],power[2][2]+1] #CAST GL(2,p)
      ^-1;
    beta:=-temp;
  fi;
  #  
  #  * to be substituted into second generator of GU if half is odd.
  
  if not IsEvenInt(half) then
    nu:=epsilon^(QuoInt((p+1),2));
    nu_inv:=nu^(-1);
    minus_nu_inv:=-(nu^(-1));
  fi;
  #  
  #  * putting powers of the singer cycle as blocks into the
  #  * generators for GU(half, p);
  
  if half=2 then
    newmat1:=[epsilon[1][1],epsilon[1][2],0,0,epsilon[2][1],epsilon[2][2]
     ,0,0,0,0,epsilon_conj_inv[1][1],epsilon_conj_inv[1][2]
     ,0,0,epsilon_conj_inv[2][1],epsilon_conj_inv[2][2]] #CAST GL(4,p)
      ;
    newmat2:=[-1,0,beta[1][1],beta[1][2],0,-1,beta[2][1],beta[2][2]
     ,minus_beta_inv[1][1],minus_beta_inv[1][2],0,0,minus_beta_inv[2][1]
     ,minus_beta_inv[2][2],0,0] #CAST GL(4,p)
      ;
  elif half=4 then
    newmat1:=MatrixByEntries(GF(p),8,8,Concatenation(Concatenation(List([1,2],
      i->List([1,2],
        j->[i,j,epsilon[i][j]])),List([3..6],i->[i,i,1])
       ,Concatenation(List([1..2],
      i->List([1..2],
        j->[6+i,6+j,epsilon_conj_inv[i][j]]))));
    newmat2:=MatrixByEntries(GF(p),8,8,Concatenation(Concatenation(List([0,2]
       ,s->List([1,2],i->[i+s,i,1])),Concatenation(List([1,2],
      i->List([1,2],
        j->[i,j+4,nu[i][j]])),Concatenation(List([1,2],
      i->List([1,2],
        j->[i+4,j+2,nu_inv[i][j]])),List([1,2],i->[i+4,i+6,1])
       ,Concatenation(List([1,2],
      i->List([1,2],
        j->[i+6,j+2,minus_nu_inv[i][j]])))));
  elif IsOddInt(half) then
    newmat1:=MatrixByEntries(GF(p),d,d,Concatenation(Concatenation(List([1,2],
      i->List([1,2],
        j->[i+half-3,j+half-3,epsilon[i][j]])),List(Concatenation([1..(half-3)]
     ,[half,half+1],[half+4..d]),i->[i,i,1 #CAST GF(p)
      ]),Concatenation(List([1,2],
      i->List([1,2],
        j->[i+half+1,j+half+1,epsilon_conj_inv[i][j]]))));
    newmat2_list:=Concatenation(List([1..half-3],i->[i,i+2,1]),[[half-2,d-1,1]
       ,[half-1,d,1],[half+2,1,1],[half+3,2,1],[half-2,half,-1]
       ,[half-1,half+1,-1],[half,half,-1],[half+1,half+1,-1],[half,1,-1]
       ,[half+1,2,-1]],List([half+4..d],i->[i,i-2,1]),Concatenation(List([1,2],
      i->List([1,2],
        j->[half-3+i,j,beta[i][j]])));
    newmat2:=MatrixByEntries(GF(p),d,d,newmat2_list);
  else
    #  half is even and > 4.
    newmat1:=MatrixByEntries(GF(p),d,d,Concatenation(Concatenation(List([1,2],
      i->List([1,2],
        j->[i,j,epsilon[i][j]])),List([3..(d-2)],i->[i,i,1 #CAST GF(p)
      ]),Concatenation(List([1,2],
      i->List([1,2],
        j->[i+d-2,j+d-2,epsilon_conj_inv[i][j]]))));
    newmat2:=MatrixByEntries(GF(p),d,d,Concatenation([[1,1,1 #CAST GF(p)
      ],[2,2,1 #CAST GF(p)
      ]],List([3..half],i->[i,i-2,1 #CAST GF(p)
      ]),List([(half+1)..d-2],i->[i,i+2,1 #CAST GF(p)
      ]),Concatenation(List([1,2],
      i->List([1,2],
        j->[i,j+half,nu[i][j]])),Concatenation(List([1,2],
      i->List([1,2],
        j->[i+d-4,j+half-2,nu_inv[i][j]])),Concatenation(List([1,2],
      i->List([1,2],
        j->[i+d-2,j+half-2,minus_nu_inv[i][j]]))));
  fi;
  #  
  #  * Now we substitute the (2 \times 2) matrix representing the
  #  * frobenius automorphism as blocks down the diagonal, and then
  #  * multiply it by the matrix representing a 2-power scalar in GL(2,
  #  * p^2)\setminusGU(2, p) whose square lies in GU(2, p).
  
  frob_aut:=gammal1.2;
  #  
  #  * "putting frobenius aut as block into identity matris";
  
  frobmat1:=MatrixByEntries(GF(p),d,d,Concatenation(List([0..half-1]
     ,k->Concatenation(List([1..2],
    i->List([1..2],
      j->[i+k*2,j+k*2,frob_aut[i][j]])))));
  #  
  #  * "finding highest 2-power order of a scalar in GU(2, p)";
  
  two_power:=1;
  temp:=p+1;
  while IsEvenInt(temp) do
    temp:=QuoInt(temp,2);
    two_power:=two_power*2;
  od;
  #  
  #  * "finding a scalar in GL(2, p^2) of twice this order2-power order";
  
  power:=QuoInt((p^2-1),(two_power*2));
  gens1_power4:=epsilon^power;
  frobmat2:=MatrixByEntries(GF(p),d,d,Concatenation(List([0..half-1]
     ,k->Concatenation(List([1..2],
    i->List([1..2],
      j->[i+k*2,j+k*2,gens1_power4[i][j]])))));
  #  
  #  * the product is now our third generator.
  
  newmat3:=frobmat1*frobmat2;
  #  "newmat1="; GL(d, p)!newmat1;
  #  "newmat2="; GL(d, p)!newmat2;
  #  "newmat3="; GL(d, p)!newmat3;
  return SubStructure(GL(d,p),newmat1,#TODO CLOSURE
    newmat2,newmat3);
end;
;
#  *****************************************************************
#  
#  * and now the main function for Sp(4, p). This has maximal subgroups
#  * Sp(2, p^2).2 and GU(2, p).2

GetSemilins@:=function(p)
local bool,form,g1,g2,semilin1,semilin2,standard_form,x;
  Assert(1,IsPrimeInt(p));
  standard_form:=[0,0,0,1,0,0,1,0,0,-1,0,0,-1,0,0,0] #CAST GL(4,p)
    ;
  g1:=GammaSpMeetSp@(4,2,p);
  # =v= MULTIASSIGN =v=
  form:=SymplecticForm@(g1);
  bool:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,bool);
  x:=ChangeForm@(form,standard_form,4,p,"symplectic",g1,SP(4,p)) #CAST GL(4,p)
    ;
  semilin1:=g1^x;
  g2:=GammaUMeetSp@(4,p);
  # =v= MULTIASSIGN =v=
  form:=SymplecticForm@(g2);
  bool:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,bool);
  x:=ChangeForm@(form,standard_form,4,p,"symplectic",g2,SP(4,p)) #CAST GL(4,p)
    ;
  semilin2:=g2^x;
  return rec(val1:=semilin1,
    val2:=semilin2);
end;
;
GetExtraSpec@:=function(p)
local 
   bool,dergroup,form1,form2,found,fullgroup,group,newder,newgens,newgroup,
   overgroup,power_odd,power_two,runs,tripgens,x;
  group:=NormaliserOfExtraSpecialGroupMinus@(4,p);
  dergroup:=DerivedSubgroup(group);
  if p mod 8=1 or p mod 8=7 then
    power_two:=1;
    power_odd:=p-1;
    while IsEvenInt(power_odd) do
      power_two:=2*power_two;
      power_odd:=QuoInt(power_odd,2);
    od;
    newgens:=List(Generators(group),x->x^(power_odd));
    tripgens:=List(newgens,x->x^Order(DeterminantMat(x)));
    newgroup:=SubStructure(GL(4,p),dergroup,#TODO CLOSURE
      tripgens);
    #  "group ="; ChiefFactors(group);
    #  "newgroup ="; ChiefFactors(newgroup);
  else
    newgroup:=dergroup;
  fi;
  #   The derived subgroup is guaranteed to preserve a form; newgroup
  #   may be too big if p mod 8 eq 1.
  # =v= MULTIASSIGN =v=
  form1:=SymplecticForm@(dergroup);
  bool:=form1.val1;
  form1:=form1.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,bool);
  form2:=[0,0,0,1,0,0,1,0,0,-1,0,0,-1,0,0,0] #CAST GL(4,p)
    ;
  x:=ChangeForm@(form1,form2,4,p,"symplectic",dergroup,SP(4,p)) #CAST GL(4,p)
    ;
  overgroup:=newgroup^x;
  newder:=dergroup^x;
  if ((p mod 8=3) or (p mod 8=5) or (p mod 8=7) or SymplecticForm@(overgroup)) 
     then
    return overgroup;
  fi;
  #  
  #  * we are now in the situation where we have a subgroup of SL that
  #  * is twice as big as what we want. we need to find an element that
  #  * does *not* lie in the derived subgroup (which is of index 4) but
  #  * *does* lie in this subgroup (index 2).
  
  found:=false;
  runs:=0;
  while not found do
    x:=Random(overgroup);
    if not (x in newder) then
      fullgroup:=SubStructure(GL(4,p),newder,#TODO CLOSURE
        x);
      if SymplecticForm@(fullgroup) then
        found:=true;
      fi;
    fi;
    #  "runs =", runs;
    runs:=runs+1;
  od;
  return fullgroup;
end;
;
#  tested on i in [5..1000]
GetL2p@:=function(p)
local bool,form1,form2,g,group,indecs,module,newgroup,power,x;
  g:=SL(2,p);
  module:=GModule(g);
  power:=TensorPower(module,3);
  indecs:=IndecomposableSummands(power);
  Assert(1,newmod:=ForAny(indecs,x->DimensionOfMatrixGroup(x)=4));
  group:=SubStructure(GL(4,p),ActionGenerators(newmod));
  # =v= MULTIASSIGN =v=
  form1:=SymplecticForm@(group);
  bool:=form1.val1;
  form1:=form1.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,bool);
  form2:=[0,0,0,1,0,0,1,0,0,-1,0,0,-1,0,0,0] #CAST GL(4,p)
    ;
  x:=ChangeForm@(form1,form2,4,p,"symplectic",group,SP(4,p)) #CAST GL(4,p)
    ;
  newgroup:=group^x;
  return newgroup;
end;
;
#   This function makes a matrix group isomorphic to 2.Sym(6)
#  * whenever 3 is square in GF(p). Tested on all suitable p in range
#  * [10..1000];

GetSym6@:=function(p)
local M,bool,comp_factors,form1,form2,grp,x;
  Assert(1,IsPrimeInt(p));
  M:=GModule(SubPermutationGroup(80,[(2,5)(4,8)(6,13)(7,11)(9,16)(10,17)(12,21)
   (14,24)(15,22)(18,30)(19,28)(20,31)(23,34)(25,38)(26,27)(29,42)(32,45)(35,52)
   (36,50)(37,54)(39,58)(40,59)(41,60)(43,64)(44,65)(47,68)(48,69)(49,67)(51,62)
   (53,71)(55,72)(56,73)(57,66)(61,77)(63,76)(70,80),(1,2,6,9,4)(3,7,14,15,8)
   (5,10,18,22,12)(11,19,26,16,20)(13,23,35,39,25)(17,27,40,43,29)
   (21,32,47,48,33)(24,36,53,55,37)(28,30,44,61,41)(31,45,66,67,46)
   (34,49,68,54,51)(38,56,50,69,57)(42,62,65,78,63)(52,70,64,79,72)
   (58,71,80,77,74)(59,75,76,60,73)]),[[[0,0,0,0,1,0,1,0,0,1,0,0,0,0,0,0]
   ,[0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0],[0,0,0,0,0,1,1,0,0,-1,0,0,0,0,-1,1]
   ,[0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],[1,-1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0]
   ,[1,-1,0,-1,0,0,0,0,0,0,1,0,0,0,0,0],[0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
   ,[0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,0],[0,1,0,0,0,0,0,0,0,0,0,-1,1,1,0,0]
   ,[0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0]
   ,[0,0,0,0,0,0,0,0,-1,1,0,0,0,0,-1,0],[0,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0]
   ,[0,0,0,0,0,0,0,-1,0,1,0,0,0,0,-1,0],[0,0,0,0,0,0,0,0,0,0,0,0,-1,-1,0,0]
   ,[-1,2,1,0,0,0,0,0,0,0,-1,0,-1,-1,0,0]]
,[[0,0,0,0,0,0,0,0,0,0,0,-1,0,1,0,0],[0,-1,0,0,0,0,0,0,0,0,0,0,0,1,0,0]
   ,[-1,3,1,1,0,0,0,0,0,0,-1,-1,0,-1,0,0],[0,0,0,-1,0,0,0,0,0,0,0,0,-1,-1,0,0]
   ,[0,0,0,0,-1,0,0,1,1,-1,0,0,0,0,1,0],[0,0,0,0,-1,0,0,1,1,-1,0,0,0,0,0,0]
   ,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0]
   ,[0,0,0,0,-1,0,0,0,1,-1,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,1,-1,0,0,0,0,0,0]
   ,[-1,1,0,0,0,0,0,0,0,0,-1,0,0,0,0,0],[0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0]
   ,[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[-1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0]
   ,[0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0],[0,0,0,0,1,-1,-1,0,0,0,0,0,0,0,1,-1]]
]);
  #   order = 1440 = 2^5 * 3^2 * 5 
  comp_factors:=CompositionFactors(ChangeRing(M,GF(p)));
  if not Size(comp_factors)=4 then
    Info(InfoWarning,1,"unable to decompose module");
    return rec(val1:=false,
      val2:=_);
  fi;
  grp:=SubMatrixGroup(4,GF(p),[ActionGenerators(comp_factors[1])]);
  # =v= MULTIASSIGN =v=
  form1:=SymplecticForm@(grp);
  bool:=form1.val1;
  form1:=form1.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,bool);
  form2:=[0,0,0,1,0,0,1,0,0,-1,0,0,-1,0,0,0] #CAST GL(4,p)
    ;
  x:=ChangeForm@(form1,form2,4,p,"symplectic",grp,SP(4,p)) #CAST GL(4,p)
    ;
  return rec(val1:=true,
    val2:=grp^x);
end;
;
#  ***************************************************************
#  
#  * The following function finds the 4 dimensional symplectic
#  * representation of 2.Alt6 that is maximal whenever 2.Sym6 doesn't
#  * exist.

GetAltSix@:=function(p)
local M,bool,comp_factors,form1,form2,grp,x;
  Assert(1,IsPrimeInt(p));
  M:=GModule(SubPermutationGroup(80,[(1,49,55,32,22,3,69,39,45,16)
   (2,30,58,67,34,7,27,72,48,50)(4,12,41,51,33,8,20,29,56,46)
   (5,24,80,78,61,11,13,70,75,43)(6,65,64,38,28,14,59,77,54,17)
   (9,21,25,10,62,15,31,37,19,73)(18,66,52,36,42,26,47,71,23,60)
   (35,68,79,44,76,53,57,74,40,63),(1,38,24,3,54,13)(2,53,57,7,35,68)
   (4,36,14,8,23,6)(5,11)(9,15)(10,79,20,19,74,12)(16,58,67,22,72,48)
   (17,32,61,28,45,43)(18,33,64,26,46,77)(21,30,70,31,27,80)(25,56,63,37,51,76)
   (29,41)(34,73,75,50,62,78)(39,42,49,55,60,69)(40,47,71,44,66,52)(59,65)])
   ,[[[0,1,0,0,0,0,0,0,0,0,0,-1,1,0,0,0],[2,-3,-1,-1,0,0,0,0,0,0,1,0,0,1,0,0]
   ,[-1,2,0,1,0,0,0,0,0,0,-1,0,1,0,0,0],[-2,4,2,1,0,0,0,0,0,0,-1,-1,0,-1,0,0]
   ,[0,0,0,0,1,-1,0,0,0,1,0,0,0,0,0,-1],[0,0,0,0,1,-1,-1,-1,0,1,0,0,0,0,0,-1]
   ,[0,0,0,0,-1,1,0,1,1,-2,0,0,0,0,1,1],[0,0,0,0,1,0,0,-1,-1,2,0,0,0,0,-1,-1]
   ,[0,0,0,0,1,-1,0,-1,0,2,0,0,0,0,0,-1],[0,0,0,0,1,0,0,-2,-1,2,0,0,0,0,-1,-1]
   ,[1,-2,0,-1,0,0,0,0,0,0,1,0,0,1,0,0],[2,-3,-1,0,0,0,0,0,0,0,1,1,0,1,0,0]
   ,[-1,2,0,1,0,0,0,0,0,0,0,0,1,0,0,0],[1,-2,-1,0,0,0,0,0,0,0,0,0,0,1,0,0]
   ,[0,0,0,0,0,0,-1,0,0,-1,0,0,0,0,1,0],[0,0,0,0,1,0,1,-1,-1,1,0,0,0,0,-1,0]]
,[[1,-3,-1,-1,0,0,0,0,0,0,1,1,-1,0,0,0],[-1,1,0,0,0,0,0,0,0,0,-1,0,-1,-1,0,0]
   ,[0,0,0,0,0,0,0,0,0,0,1,-1,1,1,0,0],[2,-3,-1,-1,0,0,0,0,0,0,1,1,0,0,0,0]
   ,[0,0,0,0,-1,0,-1,1,1,-2,0,0,0,0,1,1],[0,0,0,0,-1,0,0,1,0,-1,0,0,0,0,0,1]
   ,[0,0,0,0,1,0,0,-2,-1,2,0,0,0,0,-1,-1],[0,0,0,0,-1,-1,-1,1,1,-1,0,0,0,0,1,0]
   ,[0,0,0,0,0,-1,-1,1,0,-1,0,0,0,0,1,0],[0,0,0,0,0,-1,0,1,0,0,0,0,0,0,0,0]
   ,[0,1,0,0,0,0,0,0,0,0,-1,0,-1,-1,0,0],[-1,1,0,0,0,0,0,0,0,0,-1,-1,0,0,0,0]
   ,[1,-2,0,0,0,0,0,0,0,0,1,0,0,1,0,0],[-2,3,1,0,0,0,0,0,0,0,-1,-1,0,-1,0,0]
   ,[0,0,0,0,0,1,1,-1,-1,1,0,0,0,0,-2,0],[0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0]]
]);
  #   order = 720 = 2^4 * 3^2 * 5 
  comp_factors:=CompositionFactors(ChangeRing(M,GF(p)));
  if not Size(comp_factors)=4 then
    Info(InfoWarning,1,"unable to decompose module");
    return rec(val1:=false,
      val2:=_);
  fi;
  grp:=SubMatrixGroup(4,GF(p),[ActionGenerators(comp_factors[1])]);
  # =v= MULTIASSIGN =v=
  form1:=SymplecticForm@(grp);
  bool:=form1.val1;
  form1:=form1.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,bool);
  form2:=[0,0,0,1,0,0,1,0,0,-1,0,0,-1,0,0,0] #CAST GL(4,p)
    ;
  x:=ChangeForm@(form1,form2,4,p,"symplectic",grp,SP(4,p)) #CAST GL(4,p)
    ;
  return rec(val1:=true,
    val2:=grp^x);
end;
;
#  *****************************************************************
#  
#  * main function. tested on 5 \leq p \leq 1000.

GetAlt6@:=function(p)
local bool,grp;
  if p mod 12=1 or p mod 12=11 then
    # =v= MULTIASSIGN =v=
    grp:=GetSym6@(p);
    bool:=grp.val1;
    grp:=grp.val2;
    # =^= MULTIASSIGN =^=
    if not bool then
      Info(InfoWarning,1,"error making sym 6");
      return 0;
    fi;
    return grp;
  elif p mod 12=5 or p mod 12=7 then
    # =v= MULTIASSIGN =v=
    grp:=GetAltSix@(p);
    bool:=grp.val1;
    grp:=grp.val2;
    # =^= MULTIASSIGN =^=
    if not bool then
      Info(InfoWarning,1,"error making alt 6");
      return 0;
    fi;
    return grp;
  else
    Info(InfoWarning,1,"incorrectly called get alt6");
    return 0;
  fi;
end;
;
#  ******************************************************************
#  *                   The main function                              *
#  *******************************************************************
#  Forward declaration of MakeSpHomomGeneral
Sp4pMaximals@:=function(group,p)
#  /out:out eq  2;
local 
   F,IsPSp,Print,a,alt_7,b,conj_invol,dh,factor,group,gsp,homom,max,maximals,o,
   pgsp,phi,psp,soc,sp,w;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  Assert(1,IsPrimeInt(p));
  Assert(1,p > 3);
  if Print > 1 then
    Info(InfoWarning,1,"Making standard sp.2");
  fi;
  sp:=SP(4,p);
  w:=PrimitiveElement(GF(p));
  gsp:=SubStructure(GL(4,p),sp.1,#TODO CLOSURE
    sp.2,DiagonalMat(GF(p),[w,w,1,1]));
  # =v= MULTIASSIGN =v=
  pgsp:=OrbitAction(gsp,Orbit(gsp,SubStructure(RSpace(gsp),[1,0,0,0])));
  factor:=pgsp.val1;
  pgsp:=pgsp.val2;
  # =^= MULTIASSIGN =^=
  psp:=sp@factor;
  AssertAttribute(psp,"Order",Size(PSp(4,p)));
  conj_invol:=pgsp.3;
  o:=Size(group);
  IsPSp:=o=Size(psp);
  #  dgroup :=  DerivedSubgroup(group);
  if Print > 1 then
    Info(InfoWarning,1,"Setting up homomorphism");
  fi;
  # =v= MULTIASSIGN =v=
  group:=MakeSpHomomGeneral@(group,4,p,1,psp,pgsp,factor:Print:=0);
  homom:=group.val1;
  soc:=group.val2;
  group:=group.val3;
  # =^= MULTIASSIGN =^=
  if Print > 1 then
    Print("Calling FPGroupStrong");
  fi;
  # =v= MULTIASSIGN =v=
  phi:=FPGroupStrong(SubStructure(psp,List([1..Ngens(soc)],i->soc.i@homom)));
  F:=phi.val1;
  phi:=phi.val2;
  # =^= MULTIASSIGN =^=
  #  homom, F, phi:= MakeHomom(dgroup, group, p, psp, pgsp:Print:=Print);
  dh:=Domain(homom);
  pgsp:=SubStructure(pgsp,homom(dh.1),#TODO CLOSURE
    homom(dh.2),conj_invol);
  AssertAttribute(pgsp,"Order",Size(psp)*2);
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=pgsp,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  #  
  #  * Reducibles. We need the stabiliser of a point and of a totally
  #  * isotropic subspace <e_1, e_2>.
  
  if Print > 1 then
    Print("Getting reducibles");
  fi;
  # =v= MULTIASSIGN =v=
  b:=GetReducibles@(p);
  a:=b.val1;
  b:=b.val2;
  # =^= MULTIASSIGN =^=
  Add(maximals,a@factor);
  Add(maximals,b@factor);
  #  
  #  * There are two maximal imprimitives - one is sp(2, p) \wreath 2; the
  #  * other is GL(2, p).2., where we act freely as GL on <e_1, e_2> and
  #  * then correct as required by the form on <f_1, f_2>.
  
  if Print > 1 then
    Print("Getting imprimitives");
  fi;
  # =v= MULTIASSIGN =v=
  b:=GetImprims@(p);
  a:=b.val1;
  b:=b.val2;
  # =^= MULTIASSIGN =^=
  Add(maximals,a@factor);
  Add(maximals,b@factor);
  #  
  #  * There are two maximal semilinears. Sp(2, p^2).2 and GU(2, p).2,
  #  * where in the symplectic case the .2 is simply a field automorphism,
  #  * and in the unitary case the .2 is field aut*scalar from GL(2, p^2)
  #  * of 2-power order that squares into GU(2, p).
  
  if Print > 1 then
    Print("Getting semilinears");
  fi;
  # =v= MULTIASSIGN =v=
  b:=GetSemilins@(p);
  a:=b.val1;
  b:=b.val2;
  # =^= MULTIASSIGN =^=
  Add(maximals,a@factor);
  Add(maximals,b@factor);
  #  
  #  * Now the extraspecials - if p mod 8 = 1 or -1 and we're in case
  #  * IsPSp then there are 2 conjugacy classes of
  #  * extraspecials. If p mod 8 eq 1 or -1 and we're not in case IsPSp
  #  * then there are no extraspecials.
  
  if Print > 1 then
    Print("Getting extraspecs");
  fi;
  a:=GetExtraSpec@(p);
  if p mod 8=3 or p mod 8=5 then
    Add(maximals,a@factor);
  elif IsPSp then
    Add(maximals,a@factor);
    Add(maximals,(a@factor)^conj_invol);
  fi;
  #  
  #  * There is a maximal C_9 subgroup isomorphic to PSL(2, p) whenever
  #  * p \geq 7.
  
  if p > 7 or (p=7 and not IsPSp) then
    if Print > 1 then
      Print("Getting L(2, p)");
    fi;
    a:=GetL2p@(p);
    Add(maximals,a@factor);
  fi;
  #  
  #  * There is a maximal C_9 subgroup isomorphic to Alt(6) when p = \pm 5
  #  * mod 12. There is a pair of maximal C_9 subgroups isomorphic to
  #  * Sym(6) when p = \pm 1 mod 12.
  
  if (p mod 12=1 or p mod 12=11) and IsPSp then
    if Print > 1 then
      Print("Getting Sym(6)");
    fi;
    a:=GetAlt6@(p);
    Add(maximals,a@factor);
    Add(maximals,(a@factor)^conj_invol);
  elif (p mod 12=5 or p mod 12=7) and p<>7 then
    if Print > 1 then
      Print("Getting Alt(6)");
    fi;
    a:=GetAlt6@(p);
    Add(maximals,a@factor);
  fi;
  #  only for p=7.
  if p=7 then
    if Print > 1 then
      Print("Getting Alt(7)");
    fi;
    alt_7:=SubMatrixGroup(4,GF(7),[[[0,0,2,1],[3,2,1,2],[0,0,4,0],[6,0,4,6]]
,[[0,3,1,2],[0,6,2,1],[5,1,6,5],[4,2,6,1]]
]);
    #   order = 5040 = 2^4 * 3^2 * 5 * 7 
    Add(maximals,alt_7@factor);
  fi;
  if Print > 1 then
    Print("Found maximals in standard copy");
  fi;
  return rec(val1:=homom,
    val2:=pgsp,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end;
;
InstallGlobalFunction(PSp4pIdentify@,
function(group,p)
local Print,max;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  Assert(1,p > 3);
  return Sp4pMaximals@(group,p:max:=max,Print:=Print);
end);

#   This function uses the black-box Sp recognition code to set up an
#  * isomorphism between an unknown group isomorphic to PSp(d,p^e) and
#  * the standard copy - curerently it only works for odd p.
#  * Input parameters:
#  * group is the almost simple group, where it is  known that
#  * Socle(group) ~= PSp(d,p^e).
#  * psp < apsp where apsp is the standard copy of Aut(PSp(d,p^e)).
#  * factor is a homomorphism from the standard copy of GSp(d,p^e) to apsp.
#  * homom, socle and group are returned, where group is the same
#  * group but with generators redefined to make those of socle come first.
#  * group is

#   the Black-Box constructive recognition code.
InstallGlobalFunction(MakeSpHomomGeneral@,
function(group,d,p,e,psp,apsp,factor)
local 
   CG,GtoSp,Print,SptoG,ce,g,group,h,homom,i,imgens,ims,isc,j,mat,newgens,
   pspgens,soc,socle,subgp,subsoc,works;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  soc:=Socle(group);
  #   Reduce number of generators of soc, and
  #  * rearrange generators of group to get those of soc coming first
  
  repeat
    newgens:=[Random(soc),Random(soc)];
    subsoc:=SubStructure(soc,newgens);
    RandomSchreier(subsoc);
    
  until subsoc=soc;
  soc:=subsoc;
  subgp:=subsoc;
  for g in Generators(group) do
    if not g in subgp then
      Add(newgens,g);
      subgp:=SubStructure(group,newgens);
      RandomSchreier(subgp);
    fi;
  od;
  group:=subgp;
  works:=false;
  while not works do
    # =v= MULTIASSIGN =v=
    SptoG:=RecogniseSpOdd(soc,d,p^e);
    works:=SptoG.val1;
    GtoSp:=SptoG.val2;
    SptoG:=SptoG.val3;
    # =^= MULTIASSIGN =^=
  od;
  pspgens:=[];
  for i in [1..Ngens(soc)] do
    mat:=GtoSp(soc.i);
    Add(pspgens,mat@factor);
  od;
  #  Now identify images of all generators of group in apsp.
  ims:=pspgens;
  for i in [Ngens(soc)+1..Ngens(group)] do
    g:=group.i;
    CG:=apsp;
    ce:=One(apsp);
    for j in [1..Size(pspgens)] do
      mat:=GtoSp(soc.j^g);
      # =v= MULTIASSIGN =v=
      h:=IsConjugate(CG,pspgens[j]^ce,mat@factor);
      isc:=h.val1;
      h:=h.val2;
      # =^= MULTIASSIGN =^=
      if not isc then
        Error("Conjugation error in Aut(PSp(d,q))");
      fi;
      CG:=Centraliser(CG,mat@factor);
      ce:=ce*h;
    od;
    Add(ims,ce);
  od;
  return rec(val1:=GroupHomomorphismByImages(group,apsp,
    GeneratorsOfGroup(group),ims),
    val2:=soc,
    val3:=group);
end);


