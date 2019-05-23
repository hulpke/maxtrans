#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, DiagonalJoin, DiagonalMatrix, DirectProduct,
#  GF, GL, Iden, Identity, IsEven, Matrix, Max, Min, PrimitiveElement, SL,
#  SLPointMeetHyperplane, SLStabOfNSpace, SLStabOfNSpaceMeetDual,
#  SLStabOfNSpaceMissDual, Torus

#  Defines: GLStabOfNSpace, Iden, ReduciblesSL, SLPointMeetHyperplane,
#  SLPointStab, SLPointUnmeetHyperplane, SLStabOfHalfDim, SLStabOfNSpace,
#  SLStabOfNSpaceMeetDual, SLStabOfNSpaceMissDual, Torus

DeclareGlobalFunction("GLStabOfNSpace@");

DeclareGlobalFunction("ReduciblesSL@");

DeclareGlobalFunction("SLPointMeetHyperplane@");

DeclareGlobalFunction("SLPointStab@");

DeclareGlobalFunction("SLPointUnmeetHyperplane@");

DeclareGlobalFunction("SLStabOfHalfDim@");

DeclareGlobalFunction("SLStabOfNSpace@");

DeclareGlobalFunction("SLStabOfNSpaceMeetDual@");

DeclareGlobalFunction("SLStabOfNSpaceMissDual@");

Torus@:=function(d,p)
local torus,z;
  z:=PrimitiveElement(GF(p));
  torus:=DiagonalMat(Concatenation([z,z^-1],List([3..d],i->1)));
  return torus;
end;
;
Iden@:=function(d,p)
return Identity(GL(d,p));
end;
;
#  
#  * Throughout this file we make use of the fact that GL(d, p)
#  * is as described in Don's paper.
#  
#  /*
#  * Point meet hyperplane can be taken to be <(0, 0, \ldots, 1)> and
#  * hyperplane is (0, a_1, \ldots, a_d-1).
#  * that is matrices with (a)i1 = 0 for i > 1, (a)di = 0 for i < d.
#  *

InstallGlobalFunction(SLPointMeetHyperplane@,
function(d,p)
local diag,diag1,diag2,sl1,sl2,transvec1,transvec2,z;
  diag:=List([1..d],i->[i,i,1]);
  z:=PrimitiveElement(GF(p));
  diag1:=DiagonalMat(Concatenation([z,z^-1],List([3..d],i->1)));
  diag2:=DiagonalMat(Concatenation(List([1..d-2],i->1),[z,z^-1]));
  if d > 3 then
    sl1:=DirectSumMat([Iden@(1,p),SL(d-2,p).1,Iden@(1,p)]);
    sl2:=DirectSumMat([Iden@(1,p),SL(d-2,p).2,Iden@(1,p)]);
  else
    sl1:=Iden@(d,p);
    sl2:=Iden@(d,p);
  fi;
  transvec1:=MatrixByEntries(GF(p),d,d,Concatenation([[1,2,1]],diag)) #CAST 
   GL(d,p)
    ;
  transvec2:=MatrixByEntries(GF(p),d,d,Concatenation([[d-1,d,1]],diag)) #CAST 
   GL(d,p)
    ;
  return SubStructure(SL(d,p),diag1,#TODO CLOSURE
    diag2,sl1,sl2,transvec1,transvec2);
end);

#  
#  * Point unmeet hyperplane can be taken to be <(1, 0, \ldots, 0)>
#  * and <(0, a_1, \ldots, a_d-1)>; first row is zero after 1st entry,
#  * first column is zero after 1st entry.

InstallGlobalFunction(SLPointUnmeetHyperplane@,
function(d,p)
local diag1,sl1,sl2;
  diag1:=Torus@(d,p);
  sl1:=DirectSumMat(Iden@(1,p),SL(d-1,p).1);
  sl2:=DirectSumMat(Iden@(1,p),SL(d-1,p).2);
  return SubStructure(SL(d,p),diag1,#TODO CLOSURE
    sl1,sl2);
end);

#  
#  * point is (0, 0, \ldots, 1)

InstallGlobalFunction(SLPointStab@,
function(d,p)
local diag,grp,transvec,z;
  z:=PrimitiveElement(GF(p));
  diag:=List([1..d],i->[i,i,1]);
  grp:=SLPointMeetHyperplane@(d,p);
  transvec:=MatrixByEntries(GF(p),d,d,Concatenation(diag,[[2,1,1]])) #CAST 
   GL(d,p)
    ;
  return SubStructure(SL(d,p),grp,#TODO CLOSURE
    transvec);
end);

#  
#  *

InstallGlobalFunction(SLStabOfHalfDim@,
function(d,p)
#  /out:this seems to be identical to SLStabOfNSpace(d,p,d/2)
local diag,diag1,dir_prod,half,transvec,z;
  Assert(1,IsEvenInt(d));
  half:=QuoInt(d,2);
  diag:=List([1..d],i->[i,i,1]);
  z:=PrimitiveElement(GF(p));
  diag1:=DiagonalMat(Concatenation([z],List([2..d-1],i->1),[z^-1]));
  dir_prod:=DirectProduct(SL(half,p),SL(half,p));
  transvec:=MatrixByEntries(GF(p),d,d,Concatenation(diag,[[1,half+1,1]])) #CAST 
   GL(d,p)
    ;
  return SubStructure(SL(d,p),diag1,#TODO CLOSURE
    dir_prod,transvec);
end);

#  
#  * We take the n-space to be (0, \ldots, 0, a_1, \ldots, a_n) and
#  * the (d-n)-space to be (a_1, \ldots, a_d-n, 0, \ldots, 0)

InstallGlobalFunction(SLStabOfNSpaceMissDual@,
function(d,p,n)
local diag1,diag2,dir_prod,general,z;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  z:=PrimitiveElement(GF(p));
  diag1:=DiagonalMat(Concatenation([z],List([2..d-1],i->1),[z^-1]));
  diag2:=DiagonalMat(Concatenation([z],List([2..d],i->1)));
  dir_prod:=DirectProduct(SL(d-n,p),SL(n,p));
  if general then
    return SubStructure(GL(d,p),diag1,#TODO CLOSURE
      diag2,dir_prod);
  fi;
  return SubStructure(SL(d,p),diag1,#TODO CLOSURE
    dir_prod);
end);

#  
#  * We take the n-space to be (0, \ldots, 0, a_1, \ldots, a_n)

InstallGlobalFunction(SLStabOfNSpace@,
function(d,p,n)
local diag,grp,transvec;
  diag:=List([1..d],i->[i,i,1]);
  grp:=SLStabOfNSpaceMissDual@(d,p,n);
  transvec:=MatrixByEntries(GF(p),d,d,Concatenation([[1,d-n+1,1]],diag)) #CAST 
   GL(d,p)
    ;
  return SubStructure(SL(d,p),grp,#TODO CLOSURE
    transvec);
end);

InstallGlobalFunction(GLStabOfNSpace@,
function(d,p,n)
local diag,grp1,transvec;
  diag:=List([1..d],i->[i,i,1]);
  grp1:=DirectProduct(GL((d-n),p),GL(n,p));
  transvec:=MatrixByEntries(GF(p),d,d,Concatenation([[1,d-n+1,1]],diag)) #CAST 
   GL(d,p)
    ;
  return SubStructure(GL(d,p),grp1,#TODO CLOSURE
    transvec);
end);

#  
#  * We take the n-space to be (0, \ldots, 0, a_1, \ldots, a_n)
#  * and the (d-n)-space to be (0, \ldots, 0, b_1, \ldots, b_(d-n))
#  *

InstallGlobalFunction(SLStabOfNSpaceMeetDual@,
function(d,p,n)
local 
   diag,diag1,diag2,diag3,dir_prod,general,lower,prod1,trans1,trans2,trans3,
   upper,z;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  lower:=Min(Set([n,d-n]));
  upper:=Max(Set([n,d-n]));
  Assert(1,not (lower=upper));
  diag:=List([1..d],i->[i,i,1]);
  z:=PrimitiveElement(GF(p));
  diag1:=MatrixByEntries(GF(p),d,d,Concatenation([[1,1,z],[lower+1,lower+1,z^-1]
   ],List(Concatenation([2..lower],[lower+2..d]),i->[i,i,1]))) #CAST GL(d,p)
    ;
  diag2:=MatrixByEntries(GF(p),d,d,Concatenation([[1,1,z],[d,d,z^-1]]
   ,List([2..d-1],i->[i,i,1]))) #CAST GL(d,p)
    ;
  diag3:=MatrixByEntries(GF(p),d,d,Concatenation([[1,1,z]],List([2..d]
   ,i->[i,i,1]))) #CAST GL(d,p)
    ;
  prod1:=DirectProduct(SL(lower,p),SL(upper-lower,p));
  dir_prod:=DirectProduct(prod1,SL(d-upper,p));
  trans1:=MatrixByEntries(GF(p),d,d,Concatenation(diag,[[1,lower+1,1]])) #CAST 
   GL(d,p)
    ;
  trans2:=MatrixByEntries(GF(p),d,d,Concatenation(diag,[[1,upper+1,1]])) #CAST 
   GL(d,p)
    ;
  trans3:=MatrixByEntries(GF(p),d,d,Concatenation(diag,[[lower+1,upper+1,1]])) 
   #CAST GL(d,p)
    ;
  if general then
    return SubStructure(GL(d,p),diag1,#TODO CLOSURE
      diag2,diag3,dir_prod,trans1,trans2,trans3);
  fi;
  return SubStructure(SL(d,p),diag1,#TODO CLOSURE
    diag2,dir_prod,trans1,trans2,trans3);
end);

InstallGlobalFunction(ReduciblesSL@,
function(d,q)
local All,Novelties,i,lim,list;
  Novelties:=ValueOption("Novelties");
  if Novelties=fail then
    Novelties:=false;
  fi;
  All:=ValueOption("All");
  if All=fail then
    All:=true;
  fi;
  Assert(1,d > 1);
  list:=[];
  if Novelties then
    for i in [1..QuoInt((d-1),2)] do
      Add(list,SLStabOfNSpaceMeetDual@(d,q,i));
      Add(list,SLStabOfNSpaceMissDual@(d,q,i));
    od;
  else
    # rewritten select statement
    if All then
      lim:=d-1;
    else
      lim:=QuoInt(d,2);
    fi;
    for i in [1..lim] do
      Add(list,SLStabOfNSpace@(d,q,i));
    od;
  fi;
  return list;
end);


