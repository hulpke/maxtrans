#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.39, 1/28/16 by AH

#  Global Variables used: Append, DiagonalJoin, DiagonalMatrix, GF, GL,
#  IdentityMat, IsEven, IsotropicStabSp, Matrix, PointStabSp,
#  PrimitiveElement, Sp, Submatrix, SymplecticStab, Transpose

#  Defines: IsotropicStabSp, PointStabSp, ReduciblesSp, SymplecticStab

DeclareGlobalFunction("IsotropicStabSp@");

DeclareGlobalFunction("PointStabSp@");

DeclareGlobalFunction("ReduciblesSp@");

DeclareGlobalFunction("SymplecticStab@");

#  23/04/04 testing, tidying up code + changing p to q to emphasise
#  that works for prime powers.
#  
#  * We use the generators for Sp and GL as described by Don. maximal
#  * subgroups are: the point stabiliser (don't forget Sp is
#  * transitive), the k-dim isotropic subspace stabiliser (2 \leq k \leq
#  * d/2), the k-dim symplectic subspace stabiliser (k even, 2 \leq k <
#  * d/2). Note the "<" at the top of second bound, this is because it is
#  * contained in an imprimitive group.

#  
#  * The point stabiliser has structure (p^d-1):((p-1) \times Sp(d-2,
#  * p)). We stabilise <[1, 0, \ldots, 0]>.

InstallGlobalFunction(PointStabSp@,
function(d,q)
local diag,diag1,diag2,half,normaliser,symp1,symp2,trans1,trans2,z;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,IsEvenInt(d) and d > 2);
  z:=PrimitiveElement(GF(q));
  half:=QuoInt(d,2);
  diag:=List([1..d],i->[i,i,1]);
  diag1:=DiagonalMat(Concatenation([z],List([2..d-1],i->z^0),[z^-1]));
  #  Sp(d-2, q) on <e2, e3, \ldots, f3, f2>.
  symp1:=DirectSumMat([IdentityMat(1,GF(q)),Sp(d-2,q).1,IdentityMat(1,GF(q))]);
  symp2:=DirectSumMat([IdentityMat(1,GF(q)),Sp(d-2,q).2,IdentityMat(1,GF(q))]);
  #  The transvections around the edge, the "p-gunk".
  trans1:=MatrixByEntries(GF(q),d,d,Concatenation([[d,1,1]],diag));
  trans2:=MatrixByEntries(GF(q),d,d,Concatenation([[1,1,1],[d,d,1],[d-1,1,1]
   ,[d-1,2,1],[d,1,1],[d,2,-1]],List([2..d-1],i->[i,i,-1])));
  if normaliser then
    diag2:=NormSpMinusSp@(d,q);
    return SubgroupContaining(GL(d,q),diag1,diag2,symp1,symp2,trans1,trans2);
  fi;
  return SubgroupContaining(GL(d,q),diag1,symp1,symp2,trans1,trans2);
  
end);

#  
#  * Here we stabilise <e_1, \ldots, e_k>, k \leq d/2;

#  require 2 gens for GL(k, q).
#  require 2 gens for Sp(d - 2k, q)
#  require 2 transvecs.
InstallGlobalFunction(IsotropicStabSp@,
function(d,q,k)
local diag,diag2,form,gl1,gl2,half,normaliser,sp1,sp2,trans1,trans2,z;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,IsEvenInt(d) and d > 2 and k > 1);
  #  use PointStabSp for k=1
  Assert(1,k < (d/2+1));
  z:=PrimitiveElement(GF(q));
  half:=QuoInt(d,2);
  form:=MatrixByEntries(GF(q),k,k,List([1..k],i->[i,k-i+1,1]));
  diag:=List([1..d],i->[i,i,z^0]);
  if k < half then
    #  GL(k, q) on <e_1..e_k>, balanced on <f_k..f_1>.
    gl1:=DirectSumMat([GL(k,q).1,IdentityMat(d-2*k,GF(q))
     ,form*TransposedMat(GL(k,q).1^-1)*form]);
    gl2:=DirectSumMat([GL(k,q).2,IdentityMat(d-2*k,GF(q))
     ,form*TransposedMat(GL(k,q).2^-1)*form]);
    #  the symplectic group acting on a (d-2k) space.
    sp1:=DirectSumMat([IdentityMat(k,GF(q)),Sp(d-2*k,q).1,IdentityMat(k,GF(q))]);
    sp2:=DirectSumMat([IdentityMat(k,GF(q)),Sp(d-2*k,q).2,IdentityMat(k,GF(q))]);
  else
    #   k = half.
    gl1:=DirectSumMat([GL(k,q).1,form*TransposedMat(GL(k,q).1^-1)*form]);
    gl2:=DirectSumMat([GL(k,q).2,form*TransposedMat(GL(k,q).2^-1)*form]);
  fi;
  trans1:=MatrixByEntries(GF(q),d,d,Concatenation([[d,1,1]],diag));
  if k < half then
    trans2:=MatrixByEntries(GF(q),d,d,Concatenation([[d,d-k,1],[k+1,1,-1]]
     ,diag));
  fi;
  if k < half then
    if normaliser then
      diag2:=NormSpMinusSp@(d,q);
      return SubgroupContaining(GL(d,q),gl1,gl2,sp1,sp2,trans1,trans2,diag2);
    fi;
    return SubgroupContaining(GL(d,q),gl1,gl2,sp1,sp2,trans1,trans2);
  else
    if normaliser then
      diag2:=NormSpMinusSp@(d,q);
      return SubgroupContaining(GL(d,q),gl1,gl2,trans1,diag2);
    fi;
    return SubgroupContaining(GL(d,q),gl1,gl2,trans1);
  fi;
  
end);

#  
#  * Here we need to make a direct product of Sp(k, q) and Sp(d-k, q),
#  * but have to be careful to preserve the correct form.
#  * We assume d is at least 6 or this type of group is nonmaximal.

InstallGlobalFunction(SymplecticStab@,
function(d,q,k)
local diag2,finalmat,gen,half,i,j,mat1,mat2,normaliser;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,IsEvenInt(k) and k < QuoInt(d,2));
  Assert(1,d > 4);
  half:=QuoInt(k,2);
  mat1:=DirectSumMat([IdentityMat(half,GF(q)),Sp(d-k,q).1,IdentityMat(half,GF(q))]);
  mat2:=DirectSumMat([IdentityMat(half,GF(q)),Sp(d-k,q).2,IdentityMat(half,GF(q))]);
  gen:=[];
  for i in [1,2] do
    j:=(i-1)*4;
    gen[1+j]:=Submatrix(Sp(k,q).i,1,1,half,half);
    gen[2+j]:=Submatrix(Sp(k,q).i,1,half+1,half,half);
    gen[3+j]:=Submatrix(Sp(k,q).i,half+1,1,half,half);
    gen[4+j]:=Submatrix(Sp(k,q).i,half+1,half+1,half,half);
  od;
  finalmat:=[];
  for i in [0,1] do
    finalmat[i+1]:=SquareBlockMatrix@([gen[1+4*i],
      NullMat(half,d-k,GF(q)),gen[2+4*i],
      NullMat(d-k,half,GF(q)),IdentityMat(d-k,GF(q)),
      NullMat(d-k,half,GF(q)),gen[3+4*i],
      NullMat(half,d-k,GF(q)),gen[4+4*i]],q);
  od;
  if normaliser then
    diag2:=NormSpMinusSp@(d,q);
    return SubgroupContaining(GL(d,q),mat1,mat2,finalmat[1],finalmat[2],diag2);
  fi;
  return SubgroupContaining(GL(d,q),mat1,mat2,finalmat[1],finalmat[2]);
  
end);

InstallGlobalFunction(ReduciblesSp@,
function(d,q)
local All,half,i,list;
  All:=ValueOption("All");
  if All=fail then
    All:=true;
  fi;
  Assert(1,d > 2 and IsEvenInt(d));
  if d=4 and q mod 2=0 and not All then
    return [PointStabSp@(d,q)];
  fi;
  list:=[];
  Add(list,PointStabSp@(d,q));
  half:=QuoInt(d,2);
  for i in [2..half] do
    Add(list,IsotropicStabSp@(d,q,i));
  od;
  for i in [2..half-1] do
    if IsEvenInt(i) then
      Add(list,SymplecticStab@(d,q,i));
    fi;
  od;
  return list;
  
end);

