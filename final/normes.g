#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.35, 12/15/15 by AH

#  Global Variables used: Append, BaseRing, Degree, Determinant,
#  DiagonalMatrix, DirectSum, ElementToSequence, Factorisation, GCD, GF, GL,
#  IsConjugate, IsPower, IsSquare, M, MakeDeterminantOne, MakeSymplectic,
#  Matrix, MatrixAlgebra, Nrows, OmegaPlus, PermInducingAut,
#  PrimitiveElement, RMatrixSpace, Root, ScalarMatrix,
#  Sym, SymmetricBilinearForm, TransformForm, Transpose, UnitaryForm,
#  VectorSpace, phi

#  Defines: MakeDeterminantOne, NormaliserOfExtraSpecialGroup,
#  NormaliserOfExtraSpecialGroupMinus, NormaliserOfSymplecticGroup,
#  PermInducingAut

DeclareGlobalFunction("NormaliserOfExtraSpecialGroup@");

DeclareGlobalFunction("NormaliserOfExtraSpecialGroupMinus@");

DeclareGlobalFunction("NormaliserOfSymplecticGroup@");

#  
#  Construct normalizer of extra-special group in GL(n,q).
#  Written by Derek Holt

PermInducingAut@:=function(R,phi)
local d,g,i,perm;
  #  Given automorphism phi of regular permutation group R, and an
  #  automorphism
  #  phi of R, return unique permutation fixing 1, normalising R and
  #  inducing phi on R
  d:=NrMovedPoints(R);
  perm:=[1];
  for i in [2..d] do
    g:=RepresentativeAction(R,1,i);
    perm[i]:=1^ImagesRepresentative(phi,g);
  od;
  return PermList(perm);
end;

MakeDeterminantOne@:=function(mat)
local K,d,det,isp,r;
  #  If possible multiply matrix mat by scalar matrix to make determinant 1
  d:=Length(mat);
  K:=DefaultFieldOfMatrix(mat);
  det:=DeterminantMat(mat);
  if IsOne(det) then
    return mat;
  fi;

  # dth root of det^-1
  r:=RootFFE(det^-1,d);

  if r<>fail then
    return mat*r;
  else
    return mat;
  fi;
end;

InstallGlobalFunction(NormaliserOfExtraSpecialGroup@,
function(d,q)
local 
   G,M,d,cmat,diag_list,det,dp,ee,esg,esn,exp,fac,first,form,general,gl,i,insl,isit,
   isp,j,k,l,mat,n,north,r,perm,phi,pp,qfac,r2,rno,rq,rt,scal,slm1,slm2,
   slm3,w,z,zz,normaliser,unitary,orthogonal;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  unitary:=ValueOption("unitary");
  if unitary=fail then
    unitary:=false;
  fi;
  orthogonal:=ValueOption("orthogonal");
  if orthogonal=fail then
    orthogonal:=false;
  fi;
  #   Construct complete normaliser of extraspecial group as subgroup of
  #  * GL(d,q). d must be a prime power r^n with r | q-1.
  #  * Extraspecial group has order r^(2n+1) and exponent r for r odd,
  #  * and is of + type - central product of dihedrals - for r=2.
  #  *
  #  * If general is false then intersection with SL(d,q) is returned
  #  * normaliser only applies when unitary or orthogonal set, and
  #  * returns full normaliser fixing form mod scalars
  #  *
  #  * orthogonal option returns intersection with OmegaPlus(diag_list,q) when diag_list =
  #  2^d
  #  * (this is always same as intersection with SOPlus and GOPlus).
  
  if d <= 2 then
    Error("Degree must be at least 3 in NormaliserOfExtraSpecialGroup");
  fi;
  if normaliser then
    general:=true;
  fi;
  insl:=true;
  fac:=Collected(Factors(d));
  if Length(fac)<>1 then
    Error("First argument must be a prime power in NormaliserOfExtraSpecialGroup");
  fi;
  r:=fac[1][1];
  n:=fac[1][2];
  if ((q-1) mod r)<>0 then
    Error("Divisibility condition not satisfied in NormaliserOfExtraSpecialGroup");
  fi;
  if unitary then
    qfac:=Collected(Factors(q));
    pp:=qfac[1][1];
    ee:=qfac[1][2];
    rq:=pp^(QuoInt(ee,2));
    if (ee mod 2)<>0 or ((rq-1) mod r)=0 then
      Error("Inappropriate field for unitary option");
    fi;
  fi;
  if orthogonal and (r<>2) then
    Error("orthogonal option only applicable for even degrees");
  fi;
  z:=PrimitiveElement(GF(q));
  w:=z^QuoInt(q-1,r);
  #   w is a primitive r-th root of 1
  gl:=GL(d,q);
  #   first make generators of extraspecial group
  esg:=[];
  #  diagonal generators:
  for i in [0..n-1] do
    diag_list:=[];
    for j in [1..r^(n-1-i)] do
      for k in [0..r-1] do
        for l in [1..r^i] do
          Add(diag_list,w^k);
        od;
      od;
    od;
    Add(esg,DiagonalMat(GF(q),diag_list));
  od;
  #  permutation matrix generators
  M:=function(d,r) if d mod r=0 then return r; else return d mod r;fi;end;
  dp:=[];
  #   we will collect the permutations for use later.
  for i in [0..n-1] do
    perm:=[];
    for j in [1..r^(n-1-i)] do
      for l in [1..r^(i+1)] do
        perm[(j-1)*r^(i+1)+l]:=(j-1)*r^(i+1)+M(l+(r^i),r^(i+1));
      od;
    od;
    perm:=PermList(perm);
    Add(dp,perm);
    Add(esg,PermutationMat(perm,n,GF(q)));
  od;
  #  esg now generates extraspecial group of order r^(2n+1).
  #  Now normaliser gens.
  esn:=[];
  #  First diagonals.
  for i in [0..n-1] do
    diag_list:=[];
    for j in [1..r^((n-1)-i)] do
      exp:=0;
      for k in [0..r-1] do
        exp:=exp+k;
        for l in [1..r^i] do
          Add(diag_list,w^exp);
        od;
      od;
    od;
    slm1:=MakeDeterminantOne@(DiagonalMat(GF(q),diag_list));
    if DeterminantMat(slm1)<>w^0 then
      if d<>3 then
        Error("Bug A");
      fi;
      insl:=false;
    fi;
    if DeterminantMat(slm1)=w^0 or general then
      Add(esn,slm1);
    fi;
  od;
  slm2:=[];
  first:=true;
  for i in [0..n-1] do
    mat:=NullMat(r^(i+1),r^(i+1),GF(q));
    rno:=0;
    for k in [0..r-1] do
      for j in [1..r^i] do
        rno:=rno+1;
        for l in [0..r-1] do
          mat[rno][j+(l*r^i)]:=w^(k*l);
        od;
      od;
    od;
    mat:=DirectSumMat(List([1..r^((n-1)-i)],j->mat));

    if r=2 and q mod 8 in [1,7] then
      #  2 is a square mod r - make determinant 1 and also make orthogonal
      r2:=RootFFE(2*Z(q)^0,2);
      mat:=mat*r2^-1;
    else
      #  in orthogonal case we need a consistent multiplier.
      if first then
        det:=DeterminantMat(mat);
        if IsOne(det) then
          isp:=true;
          rt:=det^0;
        else
          rt:=RootFFE(det^-1,d);
          isp:=rt<>fail;
        fi;
      fi;
      if isp then
        mat:=mat*rt;
      fi;
    fi;
    slm2[i+1]:=mat;
    #  slm2[i+1] := MakeDeterminantOne(mat);
    if d=3 and not insl then
      Add(esn,slm1^-1*slm2[i+1]*slm1);
    fi;
    if DeterminantMat(slm2[i+1])<>w^0 then
      if d<>4 then
        Error("Bug B");
      fi;
      if insl then
        insl:=false;
        if general then
          Add(esn,slm2[i+1]);
        fi;
      else
        Add(esn,(slm2[i])^-1*slm2[i+1]);
      fi;
    else
      if orthogonal and d > 4 and q mod 8 in [3,5] then
        if not first then
          Add(esn,slm2[i]^-1*slm2[i+1]);
        else
          if normaliser then
            north:=slm2[i+1];
          fi;
        fi;
      else
        Add(esn,slm2[i+1]);
      fi;
    fi;
    first:=false;
  od;
  #  Finally some permutation matrices that normalise it.
  d:=Group(dp,());
  for i in [2..n] do
    phi:=GroupHomomorphismByImagesNC(d,d,
      GeneratorsOfGroup(d),Concatenation([d.1*d.i],List([2..n],j->d.j)));
    slm3:=MakeDeterminantOne@(PermutationMat(PermInducingAut@(d,phi),GF(q)));
    if DeterminantMat(slm3)=w^0 or general then
      Add(esn,slm3);
    fi;
    if insl and DeterminantMat(slm3)<>w^0 then
      #   q  = 3 or 7 mod 8
      if d<>4 then
        Error("Bug C");
      fi;
      Add(esn,slm3^-1*slm2[1]*slm3);
      Add(esn,slm3^-1*slm2[2]*slm3);
    fi;
    if not insl then
      #   q = 5 mod 8
      Add(esn,MakeDeterminantOne@(slm2[1]*slm3));
    fi;
  od;
  G:=Group(Concatenation(esg,esn),One(gl));
  if orthogonal then
    if d=4 then
      scal:=true;
    else
      scal:=false;
    fi;
    #  d = 4 handled separately
    # =v= MULTIASSIGN =v=
    form:=SymmetricBilinearForm@(G:Scalars:=scal);
    isit:=form.val1;
    form:=form.val2;
    # =^= MULTIASSIGN =^=
    cmat:=TransformForm@(form,"orthogonalplus");
    if d > 4 and normaliser and q mod 8 in [3,5] then
      Add(esn,north);
    fi;
  else
    if unitary then
      # =v= MULTIASSIGN =v=
      form:=UnitaryForm@(G);
      isit:=form.val1;
      form:=form.val2;
      # =^= MULTIASSIGN =^=
      cmat:=TransformForm@(form,"unitary");
    fi;
  fi;
  #  Better adjoin a generating scalar!
  if unitary and not normaliser then
    zz:=z^(rq-1);
    if general then
      Add(esn,zz*IdentityMat(d,GF(q)));
    else
      Add(esn,zz^(QuoInt((rq+1),Gcd(rq+1,d)))*IdentityMat(d,GF(q)));
    fi;
  else
    if normaliser or not orthogonal then
      if general then
	Add(esn,z*IdentityMat(d,GF(q)));
      else
	Add(esn,z^(QuoInt((q-1),Gcd(q-1,d)))*IdentityMat(d,GF(q)));
      fi;
    fi;
  fi;
  G:=Group(Concatenation(esg,esn),One(gl));
  if unitary or orthogonal then
    G:=G^cmat;
    if orthogonal and d=4 and not normaliser then
      G:=Intersection(G,OmegaPlus(d,q));
    fi;
  fi;
  return G;
  #  in orthogonal case: r=3,5 mod 8, c=4 (go,so), r=1,7 mod 8, c=8
  
end);

InstallGlobalFunction(NormaliserOfSymplecticGroup@,
function(r,q)
local 
   G,M,R,cmat,d,det,dp,ee,esg,esn,exp,fac,form,gl,got,i,insl,isit,
   isp,j,k,l,mat,n,p,perm,phi,pp,qfac,rno,rq,rt,scal,slm,slmk,slmk2,w,w4,z,
   zz,general,normaliser,unitary;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  unitary:=ValueOption("unitary");
  if unitary=fail then
    unitary:=false;
  fi;
  #   Construct complete normaliser of extraspecial group as subgroup of
  #  * GL(r,q). r must be a prime power p^n with p | q-1.
  #  * Extraspecial group has order p^(2n+1) and exponent p.
  #  *
  #  * If general is false then intersection with SL(r,q) is returned
  #  *
  #  * The unitary option is only intended to be called when q is a square
  #  and
  #  * sqrt(q) = 3 mod 4.
  #  *
  #  * normaliser only applies when orthogonal set, and
  #  * returns full normaliser fixing form mod scalars
  
  if r <= 2 then
    Error("Degree must be at least 3 in NormaliserOfSymplecticGroup");
  fi;
  if normaliser then
    general:=true;
  fi;
  fac:=Collected(Factors(r));
  if Size(fac)<>1 then
    Error("First argument must be a prime power in NormaliserOfSymplecticGroup");
  fi;
  p:=fac[1][1];
  n:=fac[1][2];
  if p<>2 then
    Error("Prime must be 2 in NormaliserOfSymplecticGroup");
  fi;
  if (q-1) mod 4<>0 then
    Error("Divisibility condition not satisfied in NormaliserOfSymplecticGroup");
  fi;
  if unitary then
    qfac:=Collected(Factors(q));
    pp:=qfac[1][1];
    ee:=qfac[1][2];
    rq:=pp^(QuoInt(ee,2));
    if ee mod 2<>0 or rq mod 4=1 then
      Error("Inappropriate field for unitary option");
    fi;
  fi;
  z:=PrimitiveElement(GF(q));
  w:=z^QuoInt(q-1,p);
  #   since p=2, w = -1
  gl:=GL(r,q);
  #   first make generators of extraspecial group
  esg:=[];
  insl:=true;
  #  diagonal generators:
  for i in [0..n-1] do
    d:=[];
    for j in [1..p^(n-1-i)] do
      for k in [0..p-1] do
        for l in [1..p^i] do
          Add(d,w^k);
        od;
      od;
    od;
    Add(esg,DiagonalMat(GF(q),d));
  od;
  #  permutation matrix generators
  M:=function(r,p) if r mod p=0 then return p; else return r mod p;fi;end;
  dp:=[];
  #   we will collect the permutations for use later.
  for i in [0..n-1] do
    perm:=[];
    for j in [1..p^(n-1-i)] do
      for l in [1..p^(i+1)] do
        perm[(j-1)*p^(i+1)+l]:=(j-1)*p^(i+1)+M(l+p^i,p^(i+1));
      od;
    od;
    Add(dp,perm);
    Add(esg,PermutationMat(perm,GF(q)));
  od;
  #  We also take a scalar of order 4, although this seems to be there anyway!
  w4:=z^QuoInt(q-1,4);
  Add(esg,DiagonalMat(List([1..r],i->w4)));
  #  esg now generates symplectic group of order p^(2n+2).
  #  Now normaliser gens.
  esn:=[];
  #  diagonals different for symplectic
  for i in [0..n-1] do
    d:=[];
    for j in [1..p^(n-1-i)] do
      exp:=0;
      for k in [0..p-1] do
        exp:=exp+k;
        for l in [1..p^i] do
          Add(d,w4^exp);
        od;
      od;
    od;
    #  determinant is w4^(d/2) = 1 for d>4, -1 for d=4
    #  slm := MakeDeterminantOne(DiagonalMatrix(GF(q),d));
    slm:=DiagonalMat(d);
    if DeterminantMat(slm)<>w^0 then
      if r<>4 then
        Error("Bug B");
      fi;
      if insl then
        insl:=false;
        if general then
          Add(esn,slm);
        fi;
        slmk:=slm;
      else
        Add(esn,slmk^-1*slm);
      fi;
    else
      Add(esn,slm);
    fi;
  od;
  got:=false;
  if unitary then
    #  multiply by scal to preserve unitary form
    scal:=RootFFE(2*Z(q)^0,rq+1)^-1;
  else
    scal:=Z(q)^0;
  fi;
  for i in [0..n-1] do
    mat:=NullMat(p^(i+1),p^(i+1),GF(q));
    rno:=0;
    for k in [0..p-1] do
      for j in [1..p^i] do
        rno:=rno+1;
        for l in [0..p-1] do
          mat[rno][j+l*p^i]:=w^(k*l)*scal;
        od;
      od;
    od;
    mat:=DirectSumMat(List([1..p^(n-1-i)],j->mat)*Z(q)^0);
    #  if scal=1, then determinant is (-2)^(d/2).
    #  note -2 is a square iff q = 1 or 3 mod 8 (but 3 does not occur here) .
    if unitary then
      #  make determinant one while preserving form.
      det:=DeterminantMat(mat);
      rt:=RootFFE(det^-1,r*(rq-1));
      isp:=rt<>fail;
      Assert(1,isp or r=4);
      if isp then
        mat:=mat*rt^(rq-1);
      fi;
      slm:=mat;
    else
      slm:=MakeDeterminantOne@(mat);
    fi;
    if DeterminantMat(slm)<>w^0 then
      if r<>4 then
        Error("Bug C");
      fi;
      if not got then
        got:=true;
        slmk2:=slm;
        if general then
          Add(esn,slm);
        fi;
      else
        Add(esn,slmk2^-1*slm);
      fi;
    else
      Add(esn,slm);
    fi;
  od;
  #  Finally some permutation matrices that normalise it.
  R:=Group(dp);
  for i in [2..n] do
    phi:=GroupHomomorphismByImages(R,R,
      GeneratorsOfGroup(R),Concatenation([R.1*R.i],List([2..n],j->R.j)));
    mat:=PermutationMat(PermInducingAut@(R,phi),GF(q));
    if r=4 and not unitary then
      slm:=MakeDeterminantOne@(mat);
    else
      slm:=mat;
    fi;
    if DeterminantMat(slm)<>w^0 then
      if r<>4 then
        Error("Bug D");
      fi;
      Add(esn,slmk^-1*slm);
    else
      Add(esn,slm);
    fi;
  od;
  G:=Group(Concatenation(esg,esn),One(gl));
  if unitary then
    # =v= MULTIASSIGN =v=
    form:=UnitaryForm@(G);
    isit:=form.val1;
    form:=form.val2;
    # =^= MULTIASSIGN =^=
    cmat:=TransformForm@(form,"unitary");
  fi;
  #  Better adjoin a generating scalar!
  if unitary and not normaliser then
    zz:=z^(rq-1);
    if general then
      Add(esn,zz*IdentityMat(r,GF(q)));
    else
      Add(esn,zz^(QuoInt((rq+1),Gcd(rq+1,r)))*IdentityMat(r,GF(q)));
    fi;
  else
    if general then
      Add(esn,z*IdentityMat(r,GF(q)));
    else
      Add(esn,z^(QuoInt((q-1),Gcd(q-1,r)))*IdentityMat(r,GF(q)));
    fi;
  fi;
  G:=Group(Concatenation(esg,esn),One(gl));
  if unitary then
    G:=G^cmat;
  fi;
  return G;
end);

InstallGlobalFunction(NormaliserOfExtraSpecialGroupMinus@,
function(r,q)
local 
   G,M,MakeSymplectic,R,a,b,bool,d,dp,esg,esn,exp,fac,form,gl,i,
   insl,isit,iss,j,k,l,mat,mat1,mat2,n,nsmat,p,perm,phi,rno,slm,slmk,slmn,w,
   z,symplectic,general,normaliser;
  symplectic:=ValueOption("symplectic");
  if symplectic=fail then
    symplectic:=false;
  fi;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  #   Construct complete normaliser of minus-type extraspecial group as
  #  subgroup
  #  * of GL(r,q), where r = 2^n.
  #  *
  #  * If general is false then intersection with SL(r,q) is returned
  #  * normaliser should only be set when symplectic is true, and means
  #  * return full normaliser fixing symplectic form mod scalars
  #  *
  
  fac:=Collected(Factors(r));
  if Length(fac)<>1 or fac[1][1]<>2 or q mod 2<>1 then
    Error("First argument must be a power of 2 in NormaliserOfExtraSpecialGroupMinus");
  fi;
  if normaliser then
    general:=true;
  fi;
  n:=fac[1][2];

  MakeSymplectic:=function(mat,form)
  local K,c,d,formt,r;
    d:=Length(mat);
    K:=DefaultFieldOfMatrix(mat);
    formt:=mat*form*TransposedMat(mat);
    c:=formt[1][2];
    r:=RootFFE(c,2);
    if r<>fail then
      r:=RootFFE(c,2);
      return rec(val1:=true,
        val2:=mat*r^-1);
    else
      return rec(val1:=false,
        val2:=mat);
    fi;
    
  end;
  ;
  if symplectic then
    form:=DirectSumMat(List([1..QuoInt(r,2)],i->Matrix(GF(q),2,2,[0,1,-1,0])))
     ;
    #  the symplectic form preserved by derived subgroup of group
  fi;
  insl:=true;
  gl:=GL(r,q);
  w:=-Z(q)^0;
  #   first make generators of extraspecial group
  #   need two squares summing to -1.
  a:=0;
  for i in [1..q-1] do
    b:=RootFFE((-1-i^2)*Z(q)^0,2);
    bool:=b<>fail;
    if bool then
      a:=i*One(GF(q));
      break;
    fi;
  od;
  esg:=[];
  mat:=[[a,b],[b,-a]];
  #  Det(mat) = 1
  Add(esg,DirectSumMat(List([1..2^(n-1)],j->mat)));
  #  diagonal generators (n >= 1):
  for i in [1..n-1] do
    d:=[];
    for j in [1..2^(n-1-i)] do
      for k in [0..1] do
        for l in [1..2^i] do
          Add(d,w^k);
        od;
      od;
    od;
    Add(esg,DiagonalMat(d));
  od;
  #  permutation matrix generators
  M:=function(r,p) if r mod p=0 then return p; else return r mod p;fi;end;
  dp:=[];
  #   we will collect the permutations for use later.
  for i in [0..n-1] do
    perm:=[];
    for j in [1..2^(n-1-i)] do
      for l in [1..2^(i+1)] do
        perm[(j-1)*2^(i+1)+l]:=(j-1)*2^(i+1)+M(l+2^i,2^(i+1));
      od;
    od;
    perm:=PermList(perm);
    Add(dp,perm);
    if i=0 then
      Add(esg,PermutationMat(perm,GF(q))*DiagonalMat(Concatenation(List([1..2^(n-1)],i->[1,-1]*Z(q)^0))));
      #  determinant = 1
    else
      Add(esg,PermutationMat(perm,GF(q)));
    fi;
  od;
  #  esg now generates extraspecial group of order p^(2n+1).
  #  Now normaliser gens.
  iss:=true;
  esn:=[];
  #  first those for first component.
  mat1:=[[1,1],[-1,1]]*Z(q)^0;
  #  Det(mat1) = 2
  slm:=MakeDeterminantOne@(DirectSumMat(List([1..2^(n-1)],j->mat1)));
  if DeterminantMat(slm)<>w^0 then
    if r > 4 then
      Error("Bug A");
    fi;
    insl:=false;
    slmk:=slm;
  fi;
  if symplectic then
    # =v= MULTIASSIGN =v=
    slm:=MakeSymplectic(slm,form);
    isit:=slm.val1;
    slm:=slm.val2;
    # =^= MULTIASSIGN =^=
    if isit or normaliser then
      Add(esn,slm);
    else
      iss:=false;
      nsmat:=slm;
      #  could have Det(nsmat) = -1
    fi;
  else
    if DeterminantMat(slm)=w^0 or general then
      Add(esn,slm);
    fi;
  fi;
  mat2:=[[1+a+b,1-a+b],[-1-a+b,1-a-b]];
  #  Det(mat2) = 4
  slm:=MakeDeterminantOne@(DirectSumMat(List([1..2^(n-1)],j->mat2)));
  if DeterminantMat(slm)<>w^0 then
    Error("Bug B");
  fi;
  if symplectic then
    # =v= MULTIASSIGN =v=
    slm:=MakeSymplectic(slm,form);
    isit:=slm.val1;
    slm:=slm.val2;
    # =^= MULTIASSIGN =^=
    Assert(1,isit);
    Add(esn,slm);
  else
    Add(esn,slm);
  fi;
  for i in [1..n-1] do
    mat:=NullMat(2^(i+1),2^(i+1),GF(q));
    rno:=0;
    for k in [0..1] do
      for j in [1..2^i] do
        rno:=rno+1;
        for l in [0..1] do
          mat[rno][j+l*2^i]:=w^(k*l);
        od;
      od;
    od;
    #   determinant mat = 4 when i=1
    slm:=MakeDeterminantOne@(DirectSumMat(List([1..2^(n-1-i)],j->mat)));
    if DeterminantMat(slm)<>w^0 then
      slm:=slmk^-1*slm;
    fi;
    if symplectic then
      # =v= MULTIASSIGN =v=
      slm:=MakeSymplectic(slm,form);
      isit:=slm.val1;
      slm:=slm.val2;
      # =^= MULTIASSIGN =^=
      if isit or normaliser then
        Add(esn,slm);
      else
        if iss then
          iss:=false;
          nsmat:=slm;
        else
          #  this only happens when Determinant(nsmat) = 1
          # =v= MULTIASSIGN =v=
          slmn:=MakeSymplectic(nsmat^-1*slm,form);
          isit:=slmn.val1;
          slmn:=slmn.val2;
          # =^= MULTIASSIGN =^=
          Assert(1,isit);
          Add(esn,slmn);
        fi;
      fi;
    else
      Add(esn,slm);
    fi;
  od;
  if n > 1 then
    #  One to mix up the first and second Q8 and D8
    mat:=[[1,0,1,0],[0,1,0,1],[0,1,0,-1],[-1,0,1,0]]*Z(q);
    #  Det(mat)=4
    slm:=MakeDeterminantOne@(DirectSumMat(List([1..2^(n-2)],j->mat)));
    if DeterminantMat(slm)<>w^0 then
      slm:=slmk^-1*slm;
    fi;
    if symplectic then
      # =v= MULTIASSIGN =v=
      slm:=MakeSymplectic(slm,form);
      isit:=slm.val1;
      slm:=slm.val2;
      # =^= MULTIASSIGN =^=
      if isit or normaliser then
        Add(esn,slm);
      else
        if iss then
          iss:=false;
          nsmat:=slm;
        else
          #  this only happens when Determinant(nsmat) = 1
          # =v= MULTIASSIGN =v=
          slmn:=MakeSymplectic(nsmat^-1*slm,form);
          isit:=slmn.val1;
          slmn:=slmn.val2;
          # =^= MULTIASSIGN =^=
          Assert(1,isit);
          Add(esn,slmn);
        fi;
      fi;
    else
      Add(esn,slm);
    fi;
    #  Finally some permutation matrices that normalise it.
    R:=Group(dp,());
    for i in [3..n] do
      phi:=GroupHomomorphismByImages(R,R,
        GeneratorsOfGroup(R),Concatenation([R.1,R.2*R.i],List([3..n],j->R.j)
       ));
      slm:=MakeDeterminantOne@(PermutationMat(PermInducingAut@(R,phi),GF(q)));
      if DeterminantMat(slm)<>w^0 then
        Error("Bug C");
      fi;
      if symplectic then
        # =v= MULTIASSIGN =v=
        slm:=MakeSymplectic(slm,form);
        isit:=slm.val1;
        slm:=slm.val2;
        # =^= MULTIASSIGN =^=
        if isit then
          Add(esn,slm);
        else
          if iss then
            iss:=false;
            nsmat:=slm;
          else
            #  this only happens when Determinant(nsmat) = 1
            # =v= MULTIASSIGN =v=
            slmn:=MakeSymplectic(nsmat^-1*slm,form);
            isit:=slmn.val1;
            slmn:=slmn.val2;
            # =^= MULTIASSIGN =^=
            Assert(1,isit);
            Add(esn,slmn);
          fi;
        fi;
      else
        Add(esn,slm);
      fi;
    od;
  fi;
  #  Better adjoin a generating scalar in SL!
  if normaliser or not symplectic then
    z:=PrimitiveElement(GF(q));
    if general then
      Add(esn,z*IdentityMat(r,GF(q)));
    else
      Add(esn,z^(QuoInt((q-1),Gcd(q-1,r)))*IdentityMat(r,GF(q)));
    fi;
  fi;
  G:=Group(Concatenation(esg,esn),One(gl));
  if symplectic then
    #  isit, form := SymplecticForm@(G : Scalars:=true);
    G:=G^TransformForm@(form,"symplectic");
  fi;
  return G;
  
end);

