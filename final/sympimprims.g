#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.38, 1/12/16 by AH

#  Global Variables used: Append, CorrectForm, DiagonalJoin, DiagonalMatrix,
#  Divisors, GF, GL, GetStabOfHalf, GetWreathProd, IsEven, Matrix,
#  PrimitiveElement, Sp, Sym, SymplecticForm, WreathProduct

#  Defines: GetStabOfHalf, GetSympImprims, GetSympImprimsD4, GetWreathProd

DeclareGlobalFunction("GetStabOfHalf@");

DeclareGlobalFunction("GetSympImprimsD4@");

DeclareGlobalFunction("GetWreathProd@");

#  
#  * There is always a group which acts as GL on a maximal totally
#  * isotropic subspace, and then is balanced on the other one.
#  *
#  * This code requires d > 4 as Sp(2, q) is a special case.
#  *

InstallGlobalFunction(GetStabOfHalf@,
function(d,q)
local f,mat1,mat2,normaliser,swapmat,z;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,IsEvenInt(d));
  #  assert not q eq 2;
  f:=QuoInt(d,2);
  Assert(1,f > 2);
  z:=PrimitiveElement(GF(q));
  mat1:=DiagonalMat(Concatenation(Concatenation([z],List([2..d-1],i->1))
   ,[z^-1]));
  mat2:=MatrixByEntries(GF(q)
   ,d,d,Concatenation(Concatenation(Concatenation([[1,1,-1],[1,f,1]]
   ,List([2..f],i->[i,i-1,-1])),[[d-1,f+1,-1],[d,f+1,1]]),List([f+1..d-1]
   ,i->[i,i+1,-1])));
  swapmat:=MatrixByEntries(GF(q),d,d,Concatenation(List([1..f],i->[i,f+i,1])
   ,List([f+1..d],i->[i,i-f,-1])));
  if normaliser then
    return SubgroupContaining(GL(d,q),mat1,mat2,swapmat,NormSpMinusSp@(d,q));
  fi;
  return SubgroupContaining(GL(d,q),mat1,mat2,swapmat);
end);

#  
#  * The other function is a wreath product of Sp(d/n, q) and S_n. There
#  * seem to be two ways to go here: the easy way is to make the wreath
#  * product and conjugate it, as then conjugate it:
#  * making wreath: O(d^2). gives 4 gens.
#  * conjugating: O(d^3). So O(d^3). But then O(d) groups gives
#  * O(d^4)...
#  *
#  * assumes d gt 4, and that if n eq 2 then q is not 2.

InstallGlobalFunction(GetWreathProd@,
function(d,q,n)
local bool,elt,f,form,g,mat,normaliser,s;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,d > 4);
  #  if n gt 2 then assert q gt 2; end if; why? orthogonal?
  s:=QuoInt(d,n);
  f:=QuoInt(d,2);
  Assert(1,IsEvenInt(s));
  g:=MatWreathProduct(Sp(s,q),SymmetricGroup(n));
  # =v= MULTIASSIGN =v=
  form:=SymplecticForm@(g);
  bool:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  if normaliser then
    elt:=DirectSumMat(List([1..n],i->NormSpMinusSp@(s,q)));
    g:=SubgroupContaining(GL(d,q),g,elt);
  fi;
  mat:=CorrectForm@(form,d,q,"symplectic");
  return g^mat;
end);

#  
#  * The following function ties it all together.
#  * Take GL on maximal isotropic for odd q.
#  * Take wreath product of Sp(d/n, SymmetricGroup(n)) where q > 2 unless n eq 2.

InstallGlobalFunction(GetSympImprimsD4@,
function(q)
local bool,elt,form,g,imprim1,imprim2,newmat1,newmat2,newmat3,normaliser,x,z;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  z:=PrimitiveElement(GF(q));
  g:=MatWreathProduct(Sp(2,q),SymmetricGroup(2));
  # =v= MULTIASSIGN =v=
  form:=SymplecticForm@(g);
  bool:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  if normaliser then
    elt:=DirectSumMat(List([1..2],i->NormSpMinusSp@(2,q)));
    g:=SubgroupContaining(GL(4,q),g, elt);
  fi;
  x:=CorrectForm@(form,4,q,"symplectic");
  imprim1:=g^x;
  if IsEvenInt(q) then
    return imprim1;
  fi;
  newmat1:=DiagonalMat([z,1,1,z^-1]);
  newmat2:=MatrixByEntries(GF(q),4,4,[-1,1,0,0,-1,0,0,0,0,0,-1,-1,0,0,1,0]);
  newmat3:=MatrixByEntries(GF(q),4,4,[0,0,-1,0,0,0,0,-1,1,0,0,0,0,1,0,0]);
  if normaliser then
    imprim2:=SubgroupContaining(GL(4,q),newmat1, newmat2,newmat3,NormSpMinusSp@(4,q));
  else 
    imprim2:=SubgroupContaining(GL(4,q) ,newmat1, newmat2,newmat3);
  fi;
  return rec(val1:=imprim1,
    val2:=imprim2);
  
end);

GetSympImprims@:=function(d,q)
local divs,groups,n;
  Assert(1,d > 4);
  divs:=Filtered(DivisorsInt(d),x->x > 1 and IsEvenInt(QuoInt(d,x)));
  groups:=[];
  for n in divs do
    #  
    #  if q eq 2 and d div n eq 2 then //otherwise orthogonal (KL)
    #  continue;
    #  end if;
    
    Add(groups,GetWreathProd@(d,q,n));
  od;
  #    if IsOdd(q) then //Colva and KL have this - o.w. group is orthogonal
  Add(groups,GetStabOfHalf@(d,q));
  #    end if;
  return groups;
  
end;
