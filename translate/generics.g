#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: ActionGroup, Constituents, Determinant,
#  DiagonalMatrix, Dimension, Dual, Factorisation, GCD, GF, GL, GModule, GU,
#  IsEven, IsIrreducible, IsOdd, IsOverSmallerField, IsPower, Order,
#  PermutationMatrix, PrimitiveElement, SL, SU, ScalarMatrix, Sp, Sym,
#  SymmetricBilinearForm, SymplecticForm, TensorPower, TensorProduct,
#  TransformForm, Transpose, Valuation

#  Defines: OrthogSL2, SymplecticSL2, l2q2dim9, l2q3dim8, l3q2dim9l, l3q2dim9u,
#  l3qdim10, l3qdim6, l3qdim8, l4qdim10, l5qdim10, sp4qdim10, u3qdim10,
#  u3qdim6, u3qdim8, u4qdim10, u5qdim10

DeclareGlobalFunction("OrthogSL2@");

DeclareGlobalFunction("SymplecticSL2@");

DeclareGlobalFunction("l2q2dim9@");

DeclareGlobalFunction("l2q3dim8@");

DeclareGlobalFunction("l3q2dim9l@");

DeclareGlobalFunction("l3q2dim9u@");

DeclareGlobalFunction("l3qdim10@");

DeclareGlobalFunction("l3qdim6@");

DeclareGlobalFunction("l3qdim8@");

DeclareGlobalFunction("l4qdim10@");

DeclareGlobalFunction("l5qdim10@");

DeclareGlobalFunction("sp4qdim10@");

DeclareGlobalFunction("u3qdim10@");

DeclareGlobalFunction("u3qdim6@");

DeclareGlobalFunction("u3qdim8@");

DeclareGlobalFunction("u4qdim10@");

DeclareGlobalFunction("u5qdim10@");

InstallGlobalFunction(OrthogSL2@,
function(d,q)
#  /out: construct SL(2,q) in O(d,q) for d odd 
local A,G,M,MM,S,T,general,i,normaliser,special,w;
  special:=ValueOption("special");
  if special=fail then
    special:=false;
  fi;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,IsOddInt(d));
  Assert(1,IsOddInt(q));
  #   construct GL(2,q) as SL(2,q) with extra generator 
  w:=PrimitiveElement(GF(q));
  G:=SubStructure(GL(2,q),SL(2,q),#TODO CLOSURE
    DiagonalMat(GF(q),[w,1]));
  M:=GModule(G);
  MM:=M;
  for i in [3..d] do
    T:=TensorProduct(M,MM);
    MM:=Filtered(Constituents(T),c->DimensionOfMatrixGroup(c)=i)[1];
  od;
  A:=ActionGroup(MM);
  S:=ScalarMat(d,w^(QuoInt((d-1),2)));
  A:=SubStructure(GL(d,q),A.1,#TODO CLOSURE
    A.2,A.3*S^-1);
  Assert(1,DeterminantMat(A.3)=1 #CAST GF(q)
    );
  Assert(1,SymmetricBilinearForm(A));
  A:=A^TransformForm(A);
  if normaliser then
    return SubStructure(GL(d,q),A.1,#TODO CLOSURE
      A.2,A.3,ScalarMat(d,w));
  elif general then
    return SubStructure(GL(d,q),A.1,#TODO CLOSURE
      A.2,A.3,ScalarMat(d,-1));
  elif special or InOmega@(A.3,d,q,0) then
    #  InOmega(A.3,d,q,0) seems to happen for d = 1 or 7 mod 8.
    return A;
  else
    return SubStructure(GL(d,q),A.1,#TODO CLOSURE
      A.2);
  fi;
end);

InstallGlobalFunction(SymplecticSL2@,
function(d,q)
#  /out: construct SL(2,q) in Sp(d,q) for d even 
local A,DA,G,M,MM,S,T,form,i,isit,normaliser,tmat,w;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,IsEvenInt(d));
  Assert(1,IsOddInt(q));
  #   construct GL(2,q) as SL(2,q) with extra generator 
  w:=PrimitiveElement(GF(q));
  G:=SubStructure(GL(2,q),SL(2,q),#TODO CLOSURE
    DiagonalMat(GF(q),[w,1]));
  M:=GModule(G);
  MM:=M;
  for i in [3..d] do
    T:=TensorProduct(M,MM);
    MM:=Filtered(Constituents(T),c->DimensionOfMatrixGroup(c)=i)[1];
  od;
  A:=ActionGroup(MM);
  S:=ScalarMat(d,w^(QuoInt((d-2),2)));
  A:=SubStructure(GL(d,q),A.1,#TODO CLOSURE
    A.2,A.3*S^-1);
  DA:=SubStructure(A,A.1,#TODO CLOSURE
    A.2);
  # =v= MULTIASSIGN =v=
  form:=SymplecticForm@(DA);
  isit:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,isit);
  tmat:=TransformForm(form,"symplectic");
  A:=A^tmat;
  if normaliser then
    return A;
  else
    return SubStructure(A,A.1,#TODO CLOSURE
      A.2);
  fi;
end);

InstallGlobalFunction(l3qdim6@,
function(q)
local A,G,M,MM,S,T,general,w;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  Assert(1,IsOddInt(q));
  w:=PrimitiveElement(GF(q));
  # rewritten select statement
  if general then
    G:=GL(3,q);
  else
    G:=SL(3,q);
  fi;
  M:=GModule(G);
  T:=TensorProduct(M,M);
  MM:=Filtered(Constituents(T),c->DimensionOfMatrixGroup(c)=6)[1];
  A:=ActionGroup(MM);
  if not general then
    S:=ScalarMat(6,w^(QuoInt((q-1),Gcd(6,q-1))));
    return SubStructure(GL(6,q),A,#TODO CLOSURE
      S);
  fi;
  return SubStructure(GL(6,q),A,#TODO CLOSURE
    ScalarMat(6,w));
end);

InstallGlobalFunction(u3qdim6@,
function(q)
local A,G,M,MM,S,T,general,normaliser,w;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,IsOddInt(q));
  if normaliser then
    general:=true;
  fi;
  w:=PrimitiveElement(GF(q^2));
  # rewritten select statement
  if general then
    G:=GU(3,q);
  else
    G:=SU(3,q);
  fi;
  M:=GModule(G);
  T:=TensorProduct(M,M);
  MM:=Filtered(Constituents(T),c->DimensionOfMatrixGroup(c)=6)[1];
  A:=ActionGroup(MM);
  A:=A^TransformForm(A);
  if not general then
    S:=ScalarMat(6,(w^(q-1))^(QuoInt((q+1),Gcd(6,q+1))));
    return SubStructure(GL(6,q^2),A,#TODO CLOSURE
      S);
  fi;
  if not normaliser then
    return SubStructure(GL(6,q^2),A,#TODO CLOSURE
      ScalarMat(6,w^(q-1)));
  fi;
  return SubStructure(GL(6,q^2),A,#TODO CLOSURE
    ScalarMat(6,w));
end);

InstallGlobalFunction(l2q3dim8@,
function(q)
#  /out:SL(2,q^3).3 <= Sp(8,q);
local G,M,M1,M2,T,varX,iso,normaliser,u,w;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  w:=PrimitiveElement(GF(q^3));
  G:=SubStructure(GL(2,q^3),SL(2,q^3),#TODO CLOSURE
    DiagonalMat(GF(q^3),[w,1]));
  M:=GModule(G);
  M1:=ModToQ@(M,q);
  M2:=ModToQ@(M1,q);
  T:=TensorProduct(M,TensorProduct(M1,M2));
  Assert(1,IsIrreducible(T));
  u:=PermutationMatrix@(GF(q^3),(2,3,5)(4,7,6) #CAST SymmetricGroup(8)
    ) #CAST GL(8,q^3)
    ;
  #  induces field automorphism
  varX:=SubStructure(GL(8,q^3),ActionGroup(T),#TODO CLOSURE
    u);
  # =v= MULTIASSIGN =v=
  G:=IsOverSmallerField(varX);
  iso:=G.val1;
  G:=G.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,iso);
  G:=G^TransformForm(SubStructure(G,G.1,#TODO CLOSURE
    G.2));
  if normaliser then
    return G;
  fi;
  return (SubStructure(G,G.1,#TODO CLOSURE
    G.2,G.4));
end);

InstallGlobalFunction(l3qdim8@,
function(q)
#  /out:SL(3,q)(.3) <= O+(8,q), q mod 3 = 1 or O-(8,q), q mod 3 = 2
local C,G,G8,M,M8,T,general,normaliser,special,w;
  special:=ValueOption("special");
  if special=fail then
    special:=false;
  fi;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  w:=PrimitiveElement(GF(q));
  G:=GL2@(3,q);
  M:=GModule(G);
  T:=TensorProduct(M,M);
  C:=Constituents(T);
  M8:=Filtered(C,c->DimensionOfMatrixGroup(c)=8)[1];
  G8:=ActionGroup(M8);
  G8:=G8^TransformForm(G8);
  if normaliser then
    return SubStructure(GL(8,q),G8,#TODO CLOSURE
      ScalarMat(8,w));
  elif general and IsOddInt(q) then
    return SubStructure(GL(8,q),G8,#TODO CLOSURE
      ScalarMat(8,-1));
  elif (special or general) and IsEvenInt(q) then
    return SubStructure(GL(8,q),G8);
  elif special or q mod 3=1 then
    return SubStructure(GL(8,q),G8.1,#TODO CLOSURE
      G8.2,ScalarMat(8,-1));
  else
    return SubStructure(GL(8,q),G8.1,#TODO CLOSURE
      G8.2);
  fi;
end);

InstallGlobalFunction(u3qdim8@,
function(q)
#  /out:SU(3,q)(.3) <= O+(8,q), q mod 3 = 2 or O-(8,q), q mod 3 = 1
local C,G,G8,G8q,M,M8,T,general,isit,normaliser,special,w;
  special:=ValueOption("special");
  if special=fail then
    special:=false;
  fi;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  w:=PrimitiveElement(GF(q));
  G:=GU2@(3,q);
  M:=GModule(G);
  T:=TensorProduct(M,M);
  C:=Constituents(T);
  M8:=Filtered(C,c->DimensionOfMatrixGroup(c)=8)[1];
  G8:=ActionGroup(M8);
  # =v= MULTIASSIGN =v=
  G8q:=IsOverSmallerField(G8);
  isit:=G8q.val1;
  G8q:=G8q.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,isit);
  G8q:=G8q^TransformForm(G8q);
  if normaliser then
    return SubStructure(GL(8,q),G8q,#TODO CLOSURE
      ScalarMat(8,w));
  elif general and IsOddInt(q) then
    return SubStructure(GL(8,q),G8q,#TODO CLOSURE
      ScalarMat(8,-1));
  elif (special or general) and IsEvenInt(q) then
    return SubStructure(GL(8,q),G8q);
  elif special or q mod 3=2 then
    return SubStructure(GL(8,q),G8q.1,#TODO CLOSURE
      G8q.2,ScalarMat(8,-1));
  else
    return SubStructure(GL(8,q),G8q.1,#TODO CLOSURE
      G8q.2);
  fi;
end);

InstallGlobalFunction(l2q2dim9@,
function(q)
#  /out:L(2,q^2).2 <= O(9,q);
local 
   C,G,M,M1,T,varX,form,g3,g4,general,gg,isit,iso,normaliser,rt,scal,special,
   tform,u,w,z;
  special:=ValueOption("special");
  if special=fail then
    special:=false;
  fi;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  w:=PrimitiveElement(GF(q^2));
  z:=w^(q+1);
  G:=SubStructure(GL(2,q^2),SL(2,q^2),#TODO CLOSURE
    DiagonalMat(GF(q^2),[w,1]));
  M:=GModule(G);
  M1:=ModToQ@(M,q);
  T:=TensorProduct(M,M1);
  Assert(1,IsIrreducible(T));
  u:=PermutationMatrix@(GF(q^2),Tuple([2,3]) #CAST SymmetricGroup(4)
    ) #CAST GL(4,q^2)
    ;
  #  induces field automorphism
  varX:=SubStructure(GL(4,q^2),ActionGroup(T),#TODO CLOSURE
    u);
  # =v= MULTIASSIGN =v=
  G:=IsOverSmallerField(varX);
  iso:=G.val1;
  G:=G.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,iso);
  M:=GModule(G);
  T:=TensorProduct(M,M);
  C:=Filtered(Constituents(T),c->DimensionOfMatrixGroup(c)=9)[1];
  G:=ActionGroup(C);
  G:=G^TransformForm(SubStructure(G,G.1,#TODO CLOSURE
    G.2));
  #  adjust G.3 to fix form and G.4 to have determinant 1
  # =v= MULTIASSIGN =v=
  form:=SymmetricBilinearForm(SubStructure(G,G.1,#TODO CLOSURE
    G.2));
  isit:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,isit);
  tform:=G.3*form*TransposedMat(G.3);
  scal:=form[1][9]/tform[1][9];
  # =v= MULTIASSIGN =v=
  rt:=IsPower(scal,2);
  isit:=rt.val1;
  rt:=rt.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,isit);
  g3:=G.3*ScalarMat(9,rt);
  # rewritten select statement
  if DeterminantMat(g3)=1 then
    g3:=g3;
  else
    g3:=-g3;
  fi;
  # rewritten select statement
  if DeterminantMat(G.4)=1 then
    g4:=G.4;
  else
    g4:=-G.4;
  fi;
  G:=SubStructure(GL(9,q),G.1,#TODO CLOSURE
    G.2,g3,g4);
  if normaliser then
    return SubStructure(GL(9,q),G,#TODO CLOSURE
      ScalarMat(9,z));
  elif general then
    return SubStructure(GL(9,q),G,#TODO CLOSURE
      ScalarMat(9,-1));
  elif special then
    return G;
  else
    # rewritten select statement
    if InOmega@(g3,9,q,0) then
      gg:=g3;
    else
      # rewritten select statement
      if InOmega@(g4,9,q,0) then
        gg:=g4;
      else
        gg:=g3*g4;
      fi;
    fi;
    return (SubStructure(G,G.1,#TODO CLOSURE
      G.2,gg));
  fi;
end);

InstallGlobalFunction(l3q2dim9l@,
function(q)
#  /out:(3.)L(3,q^2)(.3).2 <= L(9,q)
local G,M,M1,T,varX,g4,general,iso,u,w,z;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  w:=PrimitiveElement(GF(q^2));
  z:=w^(q+1);
  G:=SubStructure(GL(3,q^2),SL(3,q^2),#TODO CLOSURE
    DiagonalMat(GF(q^2),[w,1,1]));
  M:=GModule(G);
  M1:=ModToQ@(M,q);
  T:=TensorProduct(M,M1);
  Assert(1,IsIrreducible(T));
  u:=PermutationMatrix@(GF(q^2),(2,4)(3,7)(6,8) #CAST SymmetricGroup(9)
    ) #CAST GL(9,q^2)
    ;
  #  induces field automorphism
  varX:=SubStructure(GL(9,q^2),ActionGroup(T),#TODO CLOSURE
    u);
  # =v= MULTIASSIGN =v=
  G:=IsOverSmallerField(varX);
  iso:=G.val1;
  G:=G.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,iso);
  #  adjust G.4 to have determinant 1
  # rewritten select statement
  if DeterminantMat(G.4)=1 then
    g4:=G.4;
  else
    g4:=-G.4;
  fi;
  G:=SubStructure(GL(9,q),G.1,#TODO CLOSURE
    G.2,G.3,g4);
  if general then
    return SubStructure(GL(9,q),G,#TODO CLOSURE
      ScalarMat(9,z));
  else
    #  get power of G.3 with determinant 1
    return (SubStructure(G,G.1,#TODO CLOSURE
      G.2,G.3^Order(DeterminantMat(G.3)),G.4));
  fi;
end);

InstallGlobalFunction(l3q2dim9u@,
function(q)
#  /out:(3.)L(3,q^2)(.3).2 <= L(9,q)
local G,M,M1,T,g4,general,normaliser,u,w,z;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  w:=PrimitiveElement(GF(q^2));
  z:=w^(q-1);
  G:=SubStructure(GL(3,q^2),SL(3,q^2),#TODO CLOSURE
    DiagonalMat(GF(q^2),[w,1,1]));
  M:=GModule(G);
  M1:=ModToQ@(M,q);
  T:=TensorProduct(Dual(M),M1);
  Assert(1,IsIrreducible(T));
  u:=PermutationMatrix@(GF(q^2),(2,4)(3,7)(6,8) #CAST SymmetricGroup(9)
    ) #CAST GL(9,q^2)
    ;
  #  induces field automorphism
  G:=SubStructure(GL(9,q^2),ActionGroup(T),#TODO CLOSURE
    u);
  G:=G^TransformForm(SubStructure(G,G.1,#TODO CLOSURE
    G.2));
  #  adjust G.4 to have determinant 1
  # rewritten select statement
  if DeterminantMat(G.4)=1 then
    g4:=G.4;
  else
    g4:=-G.4;
  fi;
  G:=SubStructure(GL(9,q^2),G.1,#TODO CLOSURE
    G.2,G.3,g4);
  if normaliser then
    return SubStructure(GL(9,q^2),G,#TODO CLOSURE
      ScalarMat(9,w));
  elif general then
    return SubStructure(GL(9,q^2),G,#TODO CLOSURE
      ScalarMat(9,z));
    #  get power of G.3 with determinant 1
  else
    return (SubStructure(G,G.1,#TODO CLOSURE
      G.2,G.3^Order(DeterminantMat(G.3)),G.4));
  fi;
end);

InstallGlobalFunction(l3qdim10@,
function(q)
local A,G,M,MM,S,T,g3,general,isit,o,rt,tp,w;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  Assert(1,CollectedFactors(q)[1][1] >= 5);
  w:=PrimitiveElement(GF(q));
  G:=SubStructure(GL(3,q),SL(3,q),#TODO CLOSURE
    DiagonalMat(GF(q),[w,1,1]));
  M:=GModule(G);
  T:=TensorPower(M,3);
  MM:=Filtered(Constituents(T),c->DimensionOfMatrixGroup(c)=10)[1];
  G:=ActionGroup(MM);
  if general then
    return SubStructure(GL(10,q),G,#TODO CLOSURE
      ScalarMat(10,w));
  fi;
  #  get intersection with SL
  o:=Order(DeterminantMat(G.3));
  tp:=3^Valuation(o,3);
  g3:=G.3^(QuoInt(o,tp));
  # =v= MULTIASSIGN =v=
  rt:=IsPower(DeterminantMat(g3),10);
  isit:=rt.val1;
  rt:=rt.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,isit);
  g3:=g3*ScalarMat(10,rt^-1);
  S:=ScalarMat(10,w^(QuoInt((q-1),Gcd(10,q-1))));
  return SubStructure(GL(10,q),G.1,#TODO CLOSURE
    G.2,g3,S);
end);

InstallGlobalFunction(u3qdim10@,
function(q)
local A,G,M,MM,S,T,g3,general,isit,normaliser,o,rt,tp,w;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,CollectedFactors(q)[1][1] >= 5);
  if normaliser then
    general:=true;
  fi;
  w:=PrimitiveElement(GF(q^2));
  G:=SubStructure(GL(3,q^2),SU(3,q),#TODO CLOSURE
    GU(3,q).1);
  M:=GModule(G);
  T:=TensorPower(M,3);
  MM:=Filtered(Constituents(T),c->DimensionOfMatrixGroup(c)=10)[1];
  A:=ActionGroup(MM);
  G:=A^TransformForm(A);
  if normaliser then
    return SubStructure(GL(10,q^2),G,#TODO CLOSURE
      ScalarMat(10,w));
  fi;
  if general then
    return SubStructure(GL(10,q^2),G,#TODO CLOSURE
      ScalarMat(10,w^(q-1)));
  fi;
  #  get intersection with SU
  o:=Order(DeterminantMat(G.3));
  tp:=3^Valuation(o,3);
  g3:=G.3^(QuoInt(o,tp));
  # =v= MULTIASSIGN =v=
  rt:=IsPower(DeterminantMat(g3),10*(q-1));
  isit:=rt.val1;
  rt:=rt.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,isit);
  g3:=g3*ScalarMat(10,rt^-(q-1));
  S:=ScalarMat(10,(w^(q-1))^(QuoInt((q+1),Gcd(10,q+1))));
  return SubStructure(GL(10,q^2),G.1,#TODO CLOSURE
    G.2,g3,S);
end);

InstallGlobalFunction(l4qdim10@,
function(q)
local A,G,M,MM,S,T,g3,general,isit,o,rt,tp,w;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  Assert(1,CollectedFactors(q)[1][1] >= 3);
  w:=PrimitiveElement(GF(q));
  G:=SubStructure(GL(4,q),SL(4,q),#TODO CLOSURE
    DiagonalMat(GF(q),[w,1,1,1]));
  M:=GModule(G);
  T:=TensorPower(M,2);
  MM:=Filtered(Constituents(T),c->DimensionOfMatrixGroup(c)=10)[1];
  G:=ActionGroup(MM);
  if general then
    return SubStructure(GL(10,q),G,#TODO CLOSURE
      ScalarMat(10,w));
  fi;
  #  get intersection with SL
  o:=Order(DeterminantMat(G.3));
  tp:=2^Valuation(o,2);
  g3:=G.3^(QuoInt(2*o,tp));
  # =v= MULTIASSIGN =v=
  rt:=IsPower(DeterminantMat(g3),10);
  isit:=rt.val1;
  rt:=rt.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,isit);
  g3:=g3*ScalarMat(10,rt^-1);
  S:=ScalarMat(10,w^(QuoInt((q-1),Gcd(10,q-1))));
  return SubStructure(GL(10,q),G.1,#TODO CLOSURE
    G.2,g3,S);
end);

InstallGlobalFunction(u4qdim10@,
function(q)
local A,G,M,MM,S,T,g3,general,isit,normaliser,o,rt,tp,w;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,CollectedFactors(q)[1][1] >= 3);
  if normaliser then
    general:=true;
  fi;
  w:=PrimitiveElement(GF(q^2));
  G:=SubStructure(GL(4,q^2),SU(4,q),#TODO CLOSURE
    GU(4,q).1);
  M:=GModule(G);
  T:=TensorPower(M,2);
  MM:=Filtered(Constituents(T),c->DimensionOfMatrixGroup(c)=10)[1];
  A:=ActionGroup(MM);
  G:=A^TransformForm(A);
  if normaliser then
    return SubStructure(GL(10,q^2),G,#TODO CLOSURE
      ScalarMat(10,w));
  fi;
  if general then
    return SubStructure(GL(10,q^2),G,#TODO CLOSURE
      ScalarMat(10,w^(q-1)));
  fi;
  #  get intersection with SU
  o:=Order(DeterminantMat(G.3));
  tp:=2^Valuation(o,2);
  g3:=G.3^(QuoInt(2*o,tp));
  # =v= MULTIASSIGN =v=
  rt:=IsPower(DeterminantMat(g3),10*(q-1));
  isit:=rt.val1;
  rt:=rt.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,isit);
  g3:=g3*ScalarMat(10,rt^-(q-1));
  S:=ScalarMat(10,(w^(q-1))^(QuoInt((q+1),Gcd(10,q+1))));
  return SubStructure(GL(10,q^2),G.1,#TODO CLOSURE
    G.2,g3,S);
end);

InstallGlobalFunction(l5qdim10@,
function(q)
local A,G,M,MM,S,T,general,w;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  w:=PrimitiveElement(GF(q));
  # rewritten select statement
  if general then
    G:=GL(5,q);
  else
    G:=SL(5,q);
  fi;
  M:=GModule(G);
  T:=TensorProduct(M,M);
  MM:=Filtered(Constituents(T),c->DimensionOfMatrixGroup(c)=10)[1];
  A:=ActionGroup(MM);
  if not general then
    S:=ScalarMat(10,w^(QuoInt((q-1),Gcd(10,q-1))));
    return SubStructure(GL(10,q),A,#TODO CLOSURE
      S);
  fi;
  return SubStructure(GL(10,q),A,#TODO CLOSURE
    ScalarMat(10,w));
end);

InstallGlobalFunction(u5qdim10@,
function(q)
local A,G,M,MM,S,T,general,normaliser,w;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  if normaliser then
    general:=true;
  fi;
  w:=PrimitiveElement(GF(q^2));
  # rewritten select statement
  if general then
    G:=GU(5,q);
  else
    G:=SU(5,q);
  fi;
  M:=GModule(G);
  T:=TensorProduct(M,M);
  MM:=Filtered(Constituents(T),c->DimensionOfMatrixGroup(c)=10)[1];
  A:=ActionGroup(MM);
  A:=A^TransformForm(A);
  if not general then
    S:=ScalarMat(10,(w^(q-1))^(QuoInt((q+1),Gcd(10,q+1))));
    return SubStructure(GL(10,q^2),A,#TODO CLOSURE
      S);
  fi;
  if not normaliser then
    return SubStructure(GL(10,q^2),A,#TODO CLOSURE
      ScalarMat(10,w^(q-1)));
  fi;
  return SubStructure(GL(10,q^2),A,#TODO CLOSURE
    ScalarMat(10,w));
end);

InstallGlobalFunction(sp4qdim10@,
function(q)
#  /out:Sp4q <= O^+(10,q) (q=1 mod 4) or O^-(10,q) (q=3 mod 4)
local C,G,M,M10,form,g3,general,isit,normaliser,rt,scal,sign,special,tform,w;
  special:=ValueOption("special");
  if special=fail then
    special:=false;
  fi;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,IsOddInt(q));
  w:=PrimitiveElement(GF(q));
  G:=SubStructure(GL(4,q),SP(4,q),#TODO CLOSURE
    NormSpMinusSp@(4,q));
  M:=GModule(G);
  C:=Constituents(TensorProduct(M,M));
  M10:=Filtered(C,c->DimensionOfMatrixGroup(c)=10)[1];
  G:=ActionGroup(M10);
  G:=G^TransformForm(SubStructure(G,G.1,#TODO CLOSURE
    G.2));
  # =v= MULTIASSIGN =v=
  form:=SymmetricBilinearForm(SubStructure(G,G.1,#TODO CLOSURE
    G.2));
  isit:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,isit);
  tform:=G.3*form*TransposedMat(G.3);
  scal:=form[1][10]/tform[1][10];
  # =v= MULTIASSIGN =v=
  rt:=IsPower(scal,2);
  isit:=rt.val1;
  rt:=rt.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,isit);
  g3:=G.3*ScalarMat(10,rt);
  G:=SubStructure(GL(10,q),G.1,#TODO CLOSURE
    G.2,g3);
  # rewritten select statement
  if q mod 4=1 then
    sign:=1;
  else
    sign:=-1;
  fi;
  Assert(1,DeterminantMat(g3)=1 and not InOmega@(g3,10,q,sign));
  if normaliser then
    return SubStructure(GL(10,q),G,#TODO CLOSURE
      ScalarMat(10,w));
  elif special or general then
    return SubStructure(GL(10,q),G,#TODO CLOSURE
      ScalarMat(10,-1));
  else
    return SubStructure(GL(10,q),G.1,#TODO CLOSURE
      G.2,ScalarMat(10,-1));
  fi;
end);


