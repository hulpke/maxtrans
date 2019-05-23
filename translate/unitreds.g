#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, Ceiling, ChangeMat, DiagonalJoin,
#  DiagonalMatrix, Eltseq, EvenBlocks, Floor, GF, GL, GetA, IdentityMatrix,
#  IsEven, IsIrreducible, IsOdd, IsotropKStab, ListMatToQ, Log, Matrix,
#  MaximalSubgroups, NonisotropKStab, OddBlocks, PSU, PrimitiveElement, SL, SU,
#  ScalarMatrix, Submatrix, Transpose

#  Defines: ChangeMat, EvenBlocks, GetA, IsotropKStab, ListMatToQ,
#  NonisotropKStab, OddBlocks, ReduciblesUnit

DeclareGlobalFunction("IsotropKStab@");

DeclareGlobalFunction("NonisotropKStab@");

#  23/04/03 testing, and some significant tidying up, in particular to
#  use the generators for the unitary groups as given in magma rather
#  than re-writing them down.
#  
#  * The maximal reducible subgroups of the unitary groups consist of
#  * the following:
#  * stabilisers of isotropic k-spaces 1 \leq k \leq Floor(d/2)
#  * stabilisers of unitary k-spaces 1 \leq k < Ceiling(d/2)
#  * we can't have a unitary k-space of dimension d/2 as this is a
#  * subgroup of an imprimitive group.

#  in all of the following, p is *not* neccesarily prime - it is simply
#  the square root of q.
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
ChangeMat@:=function(mat,k,p)
local form,mat;
  form:=MatrixByEntries(GF(p^2),k,k,List([1..k],i->[i,k-i+1,1])) #CAST GL(k,p^2)
   
    ;
  mat:=Eltseq(mat^-1);
  mat:=ListMatToQ@(mat,p);
  mat:=MatrixByEntries(GF(p^2),k,k,mat);
  return form*TransposedMat(mat)*form;
end;
;
GetA@:=function(p)
local a;
  for a in GF(p^2) do
    if a+a^p=1 then
      return a;
    fi;
  od;
  Info(InfoWarning,1,"error: couldn't find element of norm 1");
  return 0;
end;
;
OddBlocks@:=function(k,p)
local block,i,k2;
  k2:=Floor(k/2);
  block:=# [*-list:
  [];
  for i in [1,2] do
    block[1+9*(i-1)]:=Submatrix(SU(k,p).i,1,1,k2,k2);
    block[2+9*(i-1)]:=Submatrix(SU(k,p).i,1,1+k2,k2,1);
    block[3+9*(i-1)]:=Submatrix(SU(k,p).i,1,2+k2,k2,k2);
    block[4+9*(i-1)]:=Submatrix(SU(k,p).i,1+k2,1,1,k2);
    block[5+9*(i-1)]:=Submatrix(SU(k,p).i,1+k2,1+k2,1,1);
    block[6+9*(i-1)]:=Submatrix(SU(k,p).i,1+k2,2+k2,1,k2);
    block[7+9*(i-1)]:=Submatrix(SU(k,p).i,2+k2,1,k2,k2);
    block[8+9*(i-1)]:=Submatrix(SU(k,p).i,2+k2,1+k2,k2,1);
    block[9+9*(i-1)]:=Submatrix(SU(k,p).i,2+k2,2+k2,k2,k2);
  od;
  return block;
end;
;
EvenBlocks@:=function(k,p)
local block,i,k2;
  k2:=QuoInt(k,2);
  block:=[];
  for i in [1,2] do
    block[1+4*(i-1)]:=Submatrix(SU(k,p).i,1,1,k2,k2);
    block[2+4*(i-1)]:=Submatrix(SU(k,p).i,1,1+k2,k2,k2);
    block[3+4*(i-1)]:=Submatrix(SU(k,p).i,1+k2,1,k2,k2);
    block[4+4*(i-1)]:=Submatrix(SU(k,p).i,1+k2,1+k2,k2,k2);
  od;
  return block;
end;
;
InstallGlobalFunction(IsotropKStab@,
function(d,p,k)
local D,K,beta,diag,general,gens,half,lm2,normaliser,nu,temp,temp2,x,z;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  if normaliser then
    general:=true;
  fi;
  if d=3 then
    #  dfh
    Assert(1,k=1);
    K:=GF(p^2);
    z:=PrimitiveElement(K);
    D:=DiagonalMat([z^(-p),z^(p-1),z]);
    beta:=-(1+z^(p-1))^(-1);
    Assert(1,(beta+beta^p)=(-1) #CAST GF(p)
      );
    if p=2 then
      gens:=[D,MatrixByEntries(K,3,3,[1,0,0,1,1,0,beta,1,1])
       ,MatrixByEntries(K,3,3,[1,0,0,beta^2,1,0,beta,beta,1])];
    else
      gens:=[D,MatrixByEntries(K,3,3,[1,0,0,-1,1,0,beta,1,1])];
    fi;
    if general then
      Add(gens,GUMinusSU@(d,p));
    fi;
    if normaliser then
      Add(gens,ScalarMat(d,z));
    fi;
    return SubStructure(GL(d,p^2),gens);
  fi;
  z:=PrimitiveElement(GF(p^2));
  half:=Ceiling(d/2);
  if IsEvenInt(p) then
    nu:=1 #CAST GF(p)
      ;
  else
    nu:=z^(QuoInt((p+1),2));
  fi;
  Assert(1,(nu+nu^p)=0 #CAST GF(p)
    );
  #   Brooksbank asserts that there is an O(log p) algorithm for
  #   solving beta + beta^p eq -1 in GF(p^2) for prime p. need to find
  #   it.
  beta:=-(1+z^(p-1))^(-1);
  Assert(1,(beta+beta^p)=(-1) #CAST GF(p)
    );
  gens:=[];
  #  
  #  * First we get the generators for GL(k, p^2) acting on the isotropic
  #  * {e_1, \ldots, e_k} and make requisite adjustments for {f_k,
  #  * \ldots, f_1}.
  #  * If the space that we are stabilising is half the dimension then we
  #  * don't get the whole of GL(k, p^2) - We have all matrices whose
  #  * determinant lies in GF(p), in each block.
  
  #   first we deal with GL.1
  if not (2*k=d or 2*k=(d-1)) then
    diag:=DiagonalMat(Concatenation([z],List([2..k],i->1),[z^-1]
     ,List([k+2..d-k-1],i->1),[z^p],List([d-k+1..d-1],i->1),[z^(-p)]));
    Add(gens,diag);
  elif (2*k=d-1) then
    diag:=DiagonalMat(Concatenation([z],List([2..half-1],i->1),[z^(p-1)]
     ,List([half+1..d-1],i->1),[z^-p]));
    Add(gens,diag);
  else
    #  k eq half then
    Add(gens,DiagonalMat(Concatenation([z,z^-1],List([3..d-2],i->1),[z^p,z^(-p)]
     )));
    Add(gens,DiagonalMat(Concatenation([z^(p+1)],List([2..d-1],i->1),[z^(-(p+1))
     ])));
  fi;
  if k > 1 then
    temp:=SL(k,p^2).2;
    temp2:=ChangeMat@(temp,k,p);
    if k < d/2 then
      Add(gens,DirectSumMat([temp,IdentityMatrix(GF(p^2),d-2*k),temp2]));
    else
      Add(gens,DirectSumMat([temp,temp2]));
    fi;
  fi;
  #  
  #  * Now we need SU(d-2k, p), acting on {e_k+1.. e_{half}, ?w?
  #  * (depending on odd or even d), f_{d/2}..f_{k+1}}.
  
  if (d-2*k) > 1 then
    Add(gens,DirectSumMat([IdentityMatrix(GF(p^2),k),SU(d-2*k,p)
     .1,IdentityMatrix(GF(p^2),k)]));
    Add(gens,DirectSumMat([IdentityMatrix(GF(p^2),k),SU(d-2*k,p)
     .2,IdentityMatrix(GF(p^2),k)]));
  fi;
  #  
  #  * Finally we need the transvections. We take three: one mapping f_1
  #  * to f_1 + nu.e_1 and fixing the rest, one mapping f_1 to f_1 +
  #  * f_k+1, e_k+1 to -e_1+e_k+1 and fixing the rest
  #  * Because of the irreducibility of the actions of SU(d-2k, p)
  #  * and GL(k, p^2) this should generate the whole collection of
  #  * transvections.
  
  Add(gens,MatrixByEntries(GF(p^2),d,d,Concatenation(List([1..d],i->[i,i,1])
   ,[[d,1,nu]])));
  if d=(2*k+1) and IsOddInt(p) then
    #  x:= Root((GF(p^2)!-2), p+1); - too slow
    lm2:=Log(z,-2 #CAST GF(p^2)
      );
    x:=z^(QuoInt(lm2,(p+1)));
    Add(gens,MatrixByEntries(GF(p^2),d,d,Concatenation(List([1..d],i->[i,i,1])
     ,[[d,1,1],[half,1,-(x^p)],[d,half,x]])));
  elif d=(2*k+1) and IsEvenInt(p) then
    Add(gens,MatrixByEntries(GF(p^2),d,d,Concatenation(List([1..d],i->[i,i,1])
     ,[[d,1,z],[half,1,1],[d,half,1]])));
  else
    Add(gens,MatrixByEntries(GF(p^2),d,d,Concatenation(List([1..d],i->[i,i,1])
     ,[[d,d-k,1],[k+1,1,-1]])));
  fi;
  if general then
    Add(gens,GUMinusSU@(d,p));
  fi;
  if normaliser then
    Add(gens,ScalarMat(d,z));
  fi;
  return SubStructure(GL(d,p^2),gens);
end);

#  ***************************************************************
#  ***************************************************************
#  ***************************************************************
#  
#  * The second function that is required is the stabilisers of
#  * nonisotropic subspaces.
#  * These groups have the structure: SU(x, q) \times SU(d-x, q).(q+1),
#  * which I imagine means that we can have any determinant in \gf(q) on
#  * each part, as long as is balanced by the other part.
#  * So, we need two sets of generators for the SUs, plus one for the
#  * .(q+1) on the outside of determinants.
#  * We treat SU(4, 2) as a special case.

InstallGlobalFunction(NonisotropKStab@,
function(d,p,k)
local 
   a,b,block,d2,diag,g1,g2,g3,general,gens,i,i1,i2,id,k2,m1,m2,m3,m4,m5,m6,m7,
   m9,mat,normaliser,nu,r,submatrix,z;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,d > 2);
  #  if d lt 5 then assert p gt 2; end if;
  #  
  #  * We require k < d/2 as otherwise we have a subgroup of an
  #  * imprimitive group.
  
  Assert(1,k < d/2);
  if normaliser then
    general:=true;
  fi;
  z:=PrimitiveElement(GF(p^2));
  if p=2 then
    nu:=1;
  else
    nu:=z^(QuoInt((p+1),2));
  fi;
  gens:=[];
  #  
  #  * The structure of the
  #  * matrices depends on whether k is odd or even, and whether d is odd
  #  * or even.
  #  * SU(k, p) is blocks around the edges with the identity in the
  #  * middle, unless k is odd in which case we have to mess around with
  #  * either w (if d is odd) or e_d and f_d (d even). SU(d-k, p) is then
  #  * in the middle, unless d is even and k is odd in which case, once
  #  * again, the middle two rows and columns are messed up.
  
  k2:=Floor(k/2);
  d2:=Floor(d/2);
  r:=Floor((d-k)/2);
  if IsEvenInt(k) then
    #   SU(k, p)
    block:=EvenBlocks@(k,p);
    for i in [1,2] do
      Add(gens,SquareBlockMatrix@([block[1+(i-1)*4],0,block[2+(i-1)*4]
       ,0,IdentityMatrix(GF(p^2),d-k),0,block[3+(i-1)*4],0,block[4+(i-1)*4]]
       ,p^2));
    od;
    #  SU(d-k, p)
    for i in [1,2] do
      Add(gens,DirectSumMat([IdentityMatrix(GF(p^2),k2),SU(d-k,p)
       .i,IdentityMatrix(GF(p^2),k2)]));
    od;
    #  extra diagonal matrix
    diag:=DiagonalMat(Concatenation([z],List([1..k2-1],i->1),[z^-1]
     ,List([k2+2..d-k2-1],i->1),[z^p],List([1..k2-1],i->1),[z^-p]));
    #  "diag =", diag;
    Add(gens,diag);
    if general then
      Add(gens,GUMinusSU@(d,p));
    fi;
    if normaliser then
      Add(gens,ScalarMat(d,z));
    fi;
    return SubStructure(GL(d,p^2),gens);
  elif IsOddInt(d) and IsOddInt(k) then
    if k > 1 then
      #  We take SU(k, p) as semi^2 blocks in the corners, plus small
      #  blocks at the obvious junctions in the middle row and middle
      #  column.
      block:=OddBlocks@(k,p);
      i1:=IdentityMatrix(GF(p^2),QuoInt((d-k),2));
      for i in [0,9] do
        Add(gens,SquareBlockMatrix@([block[1+i],0,block[2+i],0,block[3+i]
         ,0,i1,0,0,0,block[4+i],0,block[5+i],0,block[6+i],0,0,0,i1,0,block[7+i]
         ,0,block[8+i],0,block[9+i]],p^2));
      od;
    else
      #  k eq 1
      Add(gens,SU(d,p).1);
    fi;
    #  SU(d-k, p)
    block:=EvenBlocks@(d-k,p);
    for i in [0,1] do
      submatrix:=SquareBlockMatrix@([block[1+i*4],0,block[2+i*4]
       ,0,IdentityMatrix(GF(p^2),1),0,block[3+i*4],0,block[4+i*4]],p^2);
      if k > 1 then
        submatrix:=DirectSumMat([IdentityMatrix(GF(p^2),k2)
         ,submatrix,IdentityMatrix(GF(p^2),k2)]);
      fi;
      Add(gens,submatrix);
    od;
    #  extra diagonal matrix
    if d > 3 then
      if k2 > 0 then
        Add(gens,DiagonalMat(GF(p^2),Concatenation(List([1..k2-1],i->1),[z]
         ,List([1..(QuoInt((d-k),2)-1)],i->1),[z^-1,1,z^p]
         ,List([1..(QuoInt((d-k),2)-1)],i->1),[z^-p],List([1..k2-1],i->1))));
      fi;
    fi;
    if general then
      Add(gens,GUMinusSU@(d,p));
    fi;
    if normaliser then
      Add(gens,ScalarMat(d,z));
    fi;
    return SubStructure(GL(d,p^2),gens);
  fi;
  #   d even k odd. Here we have to construct two orthonormal
  #  * vectors to lie in the k-space and the (d-k)-space respectively.
  
  #  SU(k, p)
  k2:=QuoInt((k-1),2);
  r:=QuoInt((d-k),2);
  id:=IdentityMatrix(GF(p^2),r);
  a:=GetA@(p);
  #  b:= Root(GF(p^2)!(-1), p+1);  -  too slow!
  # rewritten select statement
  if IsEvenInt(p) then
    b:=z^(p-1);
  else
    b:=z^(QuoInt((p-1),2));
  fi;
  if (k > 3) or (p > 2 and k=3) then
    #  SU(k, p).1
    g1:=DiagonalMat(Concatenation(List([1..k2-1],i->1),[z],List([k2+1..(d2-1)]
     ,i->1)));
    g2:=MatrixByEntries(GF(p^2),2,2,[z^(p-1)*a+a^p,z^(p-1)-1,(z^(p-1)-1)*a^(p+1)
     ,z^(p-1)*a^p+a]);
    g3:=DiagonalMat(Concatenation(List([1..(d2-k2-1)],i->1),[z^(-p)]
     ,List([(d2-k2+2)..d2],i->1)));
    mat:=DirectSumMat([g1,g2,g3]);
    #  mat;
    Add(gens,mat);
    #  SU(k, p).2
    m1:=Submatrix(SU(k,p).2,1,1,k2,k2);
    m2:=MatrixByEntries(GF(p^2),k2,2,[[k2,1,-a],[k2,2,-1]]);
    m3:=Submatrix(SU(k,p).2,1,k2+2,k2,k2);
    m4:=MatrixByEntries(GF(p^2),2,k2,[[1,1,-1],[2,1,-a^p]]);
    m5:=MatrixByEntries(GF(p^2),2,2,[(a^p-a),-2,-2*a^(p+1),a-a^p]);
    m6:=Submatrix(SU(k,p).2,k2+2,1,k2,k2);
    m7:=Submatrix(SU(k,p).2,k2+2,k2+2,k2,k2);
    Add(gens,SquareBlockMatrix@([m1,0,m2,0,m3,0,id,0,0,0,m4,0,m5,0,0,0,0,0,id,0,
     m6,0,0,0,m7],p^2));
  elif k=3 and p=2 then
    i1:=IdentityMatrix(GF(p^2),1);
    m1:=MatrixByEntries(GF(p^2),1,2,[z^2,z]);
    m2:=MatrixByEntries(GF(p^2),1,1,[z]);
    m3:=MatrixByEntries(GF(p^2),2,2,[1,0,0,1]);
    m4:=MatrixByEntries(GF(p^2),2,1,[z^2,z]);
    Add(gens,SquareBlockMatrix@([i1,0,m1,0,m2,0,id,0,0,0,0,0,m3,0,m4,0,0,0,id,0,
     0,0,0,0,i1],p^2));
    i2:=IdentityMatrix(GF(p^2),2);
    m5:=MatrixByEntries(GF(p^2),2,1,[1,z^2]);
    m6:=MatrixByEntries(GF(p^2),1,2,[z,1]);
    Add(gens,SquareBlockMatrix@([m2,0,m6,0,i1,0,id,0,0,0,m5,0,i2,0,0,0,0,0,id,0,
     i1,0,0,0,0],p^2));
  elif k=1 then
    Add(gens,DirectSumMat([IdentityMatrix(GF(p^2),r),MatrixByEntries(GF(p^2)
     ,2,2,[z^(p-1)*a+z^(1-p)*a^p,z^(p-1)-z^(1-p),a^(p+1)*(z^(p-1)-z^(1-p))
     ,z^(p-1)*a^p+a*z^(1-p)]),IdentityMatrix(GF(p^2),r)]));
  fi;
  #  SU(d-k, q). We may assume wlog that either (d-k) > 3 or (q \neq 2)
  #  as (d-k=3, q=2 => k = 1 and SU(4, 2) \cong Sp(4, 3) is a special
  #  case.
  #  assert ((d-k gt 3) or (d-k eq 3 and p gt 2));
  r:=QuoInt((d-k),2);
  g1:=DiagonalMat(Concatenation(List([1..d2-2],i->1),[z]));
  g2:=MatrixByEntries(GF(p^2),2,2,[a+a^p*z^(p-1),1-z^(p-1),a^(p+1)-(a^(p+1)
   *z^(p-1)),(a^p+a*z^(p-1))]);
  g3:=DiagonalMat(Concatenation([z^(-p)],List([1..d2-2],i->1)));
  Add(gens,DirectSumMat([g1,g2,g3]));
  id:=IdentityMatrix(GF(p^2),k2);
  m1:=Submatrix(SU(d-k,p).2,1,1,r,r);
  m2:=MatrixByEntries(GF(p^2),r,2,[[r,1,a^p*b],[r,2,-b]]);
  m3:=Submatrix(SU(d-k,p).2,1,r+2,r,r);
  m4:=MatrixByEntries(GF(p^2),2,r,[[1,1,b^-1],[2,1,-a*b^(-1)]]);
  m5:=MatrixByEntries(GF(p^2),2,2,[a-a^p,2,2*a^(p+1),(a^p-a)]);
  m7:=Submatrix(SU(d-k,p).2,r+2,1,r,r);
  m9:=Submatrix(SU(d-k,p).2,r+2,r+2,r,r);
  mat:=SquareBlockMatrix@([m1,m2,m3,m4,m5,0,m7,0,m9],p^2);
  if k2 > 0 then
    mat:=DirectSumMat([id,mat,id]);
  fi;
  Add(gens,mat);
  #  diagonal matrix: this seems to be misbehaving
  if k > 1 or IsOddInt(d) then
    diag:=DiagonalMat(Concatenation([z],List([1..k2-1],i->1),[z^-1]
     ,List([k2+2..d-k2-1],i->1),[z^p],List([1..k2-1],i->1),[z^-p]));
    Add(gens,diag);
  fi;
  if general then
    Add(gens,GUMinusSU@(d,p));
  fi;
  if normaliser then
    Add(gens,ScalarMat(d,z));
  fi;
  return SubStructure(GL(d,p^2),gens);
end);

ReduciblesUnit@:=function(d,q)
local i,list,max,phi,psu;
  Assert(1,d > 2);
  if d < 5 and q=2 then
    psu:=PSU(d,q);
    phi:=GroupHomomorphismByImages(SU(d,q),psu,
      GeneratorsOfGroup(SU(d,q)),[psu.1,psu.2]);
    max:=List(MaximalSubgroups(psu),m->m.subgroup@@phi);
    return Filtered(max,m->not IsIrreducible(m));
  fi;
  list:=[];
  for i in [1..QuoInt(d,2)] do
    Add(list,IsotropKStab@(d,q,i));
  od;
  for i in [1..QuoInt((d-1),2)] do
    Add(list,NonisotropKStab@(d,q,i));
  od;
  return list;
end;
;

