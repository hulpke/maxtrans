#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.35, 12/15/15 by AH

#  Global Variables used: CorrectForm, DiagonalMatrix, GF, GL, IsEven,
#  Matrix, PrimitiveElement, SOMinus, SOPlus, ScalarMatrix, Sym,
#  SymplecticForm, WreathProduct

#  Defines: NoveltyImprims, NoveltyReduct, NoveltySemilin

DeclareGlobalFunction("NoveltyImprims@");

DeclareGlobalFunction("NoveltyReduct@");

DeclareGlobalFunction("NoveltySemilin@");

#  we stabilise <(1, 0, 0, 0)> and <(1, 0, 0, 0), (0, 1, 0, 0)>. This is
#  essentially unique, as must stabilise point and isotropic 2-space,
#  and since stabilising <(1, 0, 0, 0)> also does stuff to <(0, 0, 0, 1)>
#  we might as well have point inside 2-space.
InstallGlobalFunction(NoveltyReduct@,
function(q)
local d,diag1,diag2,g,normaliser,scal,trans1,trans2,trans3,trans4,z;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,IsEvenInt(q));
  z:=PrimitiveElement(GF(q));
  d:=List([1..4],i->[i,i,1]);
  diag1:=DiagonalMat([z,1,1,z^-1]*z^0);
  diag2:=DiagonalMat([1,z,z^-1,1]*z^0);
  trans1:=MatrixByEntries(GF(q),4,4,Concatenation([[4,1,1]],d));
  trans2:=MatrixByEntries(GF(q),4,4,Concatenation(d,[[2,1,1],[4,3,1]]));
  trans3:=MatrixByEntries(GF(q),4,4,Concatenation(d,[[3,1,1],[4,2,1]]));
  trans4:=MatrixByEntries(GF(q),4,4,Concatenation(d,[[3,2,1]]));
  scal:=z*IdentityMat(4,GF(q));

  if normaliser then
    g:=Group(diag1, diag2,trans1,trans2,trans3,trans4,scal);
  else 
    g:=Group(diag1, diag2,trans1,trans2,trans3,trans4);
  fi;
  return g;
  
end);

#  **************************************************************
InstallGlobalFunction(NoveltySemilin@,
function(q)
local bool,form,frob,gammal1,grp,mat,normaliser,scal,singer,z;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,IsEvenInt(q));
  gammal1:=GammaL1@(4,q);
  singer:=gammal1.1;
  frob:=gammal1.2;
  grp:=Group(singer^(q^2-1),frob);
  # =v= MULTIASSIGN =v=
  form:=SymplecticForm@(grp);
  bool:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,bool);
  if normaliser then
    z:=PrimitiveElement(GF(q));
    scal:=z*IdentityMat(4,GF(q));
    grp:=Group(Concatenation(GeneratorsOfGroup(grp),[scal]));
  fi;
  mat:=CorrectForm@(form,4,q,"symplectic");
  return grp^mat;
  
end);

#  **************************************************************
InstallGlobalFunction(NoveltyImprims@,
function(q)
local bool,form,grp1,grp2,mat1,mat2,normaliser,scal,z;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,IsEvenInt(q));
  grp1:=MatWreathProduct(SOPlus(2,q),SymmetricGroup(2));
  if q=2 then
    form:=MatrixByEntries(GF(2),4,4,[0,1,0,0,1,0,0,0,0,0,0,1,0,0,1,0]);
  else
    # =v= MULTIASSIGN =v=
    form:=SymplecticForm@(grp1);
    bool:=form.val1;
    form:=form.val2;
    # =^= MULTIASSIGN =^=
    Assert(1,bool);
  fi;
  mat1:=CorrectForm@(form,4,q,"symplectic");
  grp2:=MatWreathProduct(SOMinus(2,q),SymmetricGroup(2));
  # =v= MULTIASSIGN =v=
  form:=SymplecticForm@(grp2);
  bool:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,bool);
  mat2:=CorrectForm@(form,4,q,"symplectic");
  if normaliser then
    z:=PrimitiveElement(GF(q));
    scal:=z*IdentityMat(4,GF(q));
    grp1:=Group(Concatenation(GeneratorsOfGroup(grp1),[scal]));
    grp2:=Group(Concatenation(GeneratorsOfGroup(grp2),[scal]));
  fi;
  return rec(val1:=grp1^mat1,
    val2:=grp2^mat2);
  
end);

