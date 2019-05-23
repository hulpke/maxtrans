
#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.35, 12/15/15 by AH

#  Global Variables used: Append, DiagonalJoin, DiagonalMatrix,
#  DirectProduct, GF, GL, Iden, Identity, IsEven, Matrix, Max, Min,
#  PrimitiveElement, SL, SLPointMeetHyperplane, SLStabOfNSpace,
#  SLStabOfNSpaceMeetDual, SLStabOfNSpaceMissDual, Torus

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
  torus:=DiagonalMat(Concatenation([z,z^-1],List([3..d],i->z^0)));
  return torus;
  
end;

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
  diag:=IdentityMat(d,GF(p));
  z:=PrimitiveElement(GF(p));
  diag1:=DiagonalMat(Concatenation([z,z^-1],List([3..d],i->z^0)));
  diag2:=DiagonalMat(Concatenation(List([1..d-2],i->1),[z,z^-1]));
  if d > 3 then
    sl1:=DirectSumMat(IdentityMat(1,GF(p)),SL(d-2,p).1,IdentityMat(1,GF(p)));
    sl2:=DirectSumMat(IdentityMat(1,GF(p)),SL(d-2,p).2,IdentityMat(1,GF(p)));
  else
    sl1:=IdentityMat(d,GF(p));
    sl2:=IdentityMat(d,GF(p));
  fi;
  transvec1:=ShallowCopy(diag);
  transvec1[1][2]:=Z(p)^0;
  transvec2:=ShallowCopy(diag);
  transvec2[d-1][d]:=Z(p)^0;
  return SubgroupNC(SL(d,p),[diag1,diag2,sl1,sl2,transvec1,transvec2]);
end);

#  
#  * Point unmeet hyperplane can be taken to be <(1, 0, \ldots, 0)>
#  * and <(0, a_1, \ldots, a_d-1)>; first row is zero after 1st entry,
#  * first column is zero after 1st entry.

InstallGlobalFunction(SLPointUnmeetHyperplane@,
function(d,p)
local diag1,sl1,sl2;
  diag1:=Torus@(d,p);
  sl1:=DirectSumMat(IdentityMat(1,GF(p)),SL(d-1,p).1);
  sl2:=DirectSumMat(IdentityMat(1,GF(p)),SL(d-1,p).2);
  return SubgroupNC(SL(d,p),[diag1,sl1,sl2]);
end);
#  
#  * point is (0, 0, \ldots, 1)

InstallGlobalFunction(SLPointStab@,
function(d,p)
local diag,grp,transvec;
  grp:=SLPointMeetHyperplane@(d,p);
  transvec:=IdentityMat(d,GF(p));
  transvec[2][1]:=Z(p)^0;
  return SubgroupNC(SL(d,p),Concatenation(GeneratorsOfGroup(grp),
	  [ transvec ] ));
  
end);

InstallGlobalFunction(SLStabOfHalfDim@,
function(d,p)
local diag,diag1,dir_prod,half,transvec,z;
  #  this seems to be identical to SLStabOfNSpace(d,p,d/2)
  Assert(1,IsEvenInt(d));
  half:=QuoInt(d,2);
  z:=PrimitiveElement(GF(p));
  diag1:=DiagonalMat(Concatenation(Concatenation([z],List([2..d-1],i->z^0))
   ,[z^-1]));
  dir_prod:=DirectProduct(SL(half,p),SL(half,p));
  transvec:=IdentityMat(d,GF(p));
  transvec[1][half+1]:=Z(p)^0;
  return SubgroupNC(SL(d,p),[diag1,dir_prod,transvec]);
end);

#  
#  * We take the n-space to be (0, \ldots, 0, a_1, \ldots, a_n) and
#  * the (d-n)-space to be (a_1, \ldots, a_d-n, 0, \ldots, 0)

InstallGlobalFunction(SLStabOfNSpaceMissDual@,
function(d,p,n)
local diag1,diag2,dir_prod,z,general;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  z:=PrimitiveElement(GF(p));
  diag1:=DiagonalMat(Concatenation(Concatenation([z],List([2..d-1],i->1))
   ,[z^-1]));
  diag2:=DiagonalMat(Concatenation([z],List([2..d],i->1)));

  dir_prod:=MatDirectProduct(SL(d-n,p),SL(n,p));
  if general then
    return Group(Concatenation([diag1,diag2],GeneratorsOfGroup(dir_prod)));
  fi;
  return Group(Concatenation([diag1],GeneratorsOfGroup(dir_prod)));
  
end);

#  
#  * We take the n-space to be (0, \ldots, 0, a_1, \ldots, a_n)

InstallGlobalFunction(SLStabOfNSpace@,
function(d,p,n)
local diag,grp,transvec;
  diag:=List([1..d],i->[i,i,1]);
  grp:=SLStabOfNSpaceMissDual@(d,p,n);
  transvec:=MatrixByEntries(GF(p),d,d,Concatenation([[1,d-n+1,1]],diag));
  return Group(Concatenation(GeneratorsOfGroup(grp),[transvec]));
  
end);

InstallGlobalFunction(GLStabOfNSpace@,
function(d,p,n)
local diag,grp1,transvec;
  diag:=List([1..d],i->[i,i,1]);
  grp1:=MatDirectProduct(GL((d-n),p),GL(n,p));
  transvec:=MatrixByEntries(GF(p),d,d,Concatenation([[1,d-n+1,1]],diag));
  return Group(Concatenation(GeneratorsOfGroup(grp1),[transvec]));
end);

#  
#  * We take the n-space to be (0, \ldots, 0, a_1, \ldots, a_n)
#  * and the (d-n)-space to be (0, \ldots, 0, b_1, \ldots, b_(d-n))
#  *

InstallGlobalFunction(SLStabOfNSpaceMeetDual@,
function(d,p,n)
local 
   diag,diag1,diag2,diag3,dir_prod,lower,prod1,trans1,trans2,trans3,upper,z,
   general;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  lower:=Minimum(n,d-n);
  upper:=Maximum(n,d-n);
  Assert(1,not lower=upper);
  diag:=List([1..d],i->[i,i,1]);
  z:=PrimitiveElement(GF(p));
  diag1:=MatrixByEntries(GF(p),d,d,Concatenation([[1,1,z],
    [lower+1,lower+1,z^-1]],List(Concatenation([2..lower],[lower+2..d])
   ,i->[i,i,1])));
  diag2:=MatrixByEntries(GF(p),d,d,Concatenation([[1,1,z],[d,d,z^-1]],
    List([2..d-1],i->[i,i,1])));
  diag3:=MatrixByEntries(GF(p),d,d,Concatenation([[1,1,z]],
    List([2..d],i->[i,i,1])));
  prod1:=MatDirectProduct(SL(lower,p),SL(upper-lower,p));
  dir_prod:=MatDirectProduct(prod1,SL(d-upper,p));
  trans1:=MatrixByEntries(GF(p),d,d,Concatenation(diag,[[1,lower+1,1]]));
  trans2:=MatrixByEntries(GF(p),d,d,Concatenation(diag,[[1,upper+1,1]]));
  trans3:=MatrixByEntries(GF(p),d,d,Concatenation(diag,[[lower+1,upper+1,1]]));
  if general then
    return Group(Concatenation(GeneratorsOfGroup(dir_prod),
      [diag1,diag2,diag3,trans1,trans2,trans3]));
  fi;
  return Group(Concatenation(GeneratorsOfGroup(dir_prod),
    [diag1,diag2,trans1,trans2,trans3]));
end);

InstallGlobalFunction(ReduciblesSL@,
function(d,q)
local i,lim,list,Novelties,All;
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
    if All then lim:=d-1; else lim:=QuoInt(d,2);fi;
    for i in [1..lim] do
      Add(list,SLStabOfNSpace@(d,q,i));
    od;
  fi;
  return list;
end);

