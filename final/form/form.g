#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.36, 12/19/15 by AH

#  Global Variables used: ActionGenerator, Append, ApproximateDerivedGroup,
#  BaseRing, Characteristic, ClassicalForms, ClassicalForms_QuadraticForm2,
#  ClassicalForms_Signum, ClassicalForms_Signum2, Coefficients,
#  CompositionSeries, Degree, Determinant, DiagonalMatrix, Dimension,
#  DollarDollar, Dual, Eltseq, Factorisation, GL, GModule, Generators, Group,
#  Id, Identity, InnerProduct, Integers, IsAbsolutelyIrreducible,
#  IsConsistent, IsEven, IsIrreducible, IsIsomorphic, IsOdd, IsPower, IsZero,
#  Log, MatToQ, Matrix, MatrixAlgebra, MatrixRing, Max, ModToQ, Ncols, Ngens,
#  Nrows, NumberOfRows, Parent, PolynomialRing, QuadraticForm, RMatrixSpace,
#  Random, RandomProcess, SetToSequence, SymmetricBilinearForm,
#  SymplecticForm, Transpose, Type, UnitaryForm, VectorSpace, Zero

#  Defines: ApproximateDerivedGroup, ClassicalForms,
#  ClassicalForms_QuadraticForm2, ClassicalForms_Signum,
#  ClassicalForms_Signum2, FormType, InternalGetOrthogonalForm,
#  InternalOrthTestQuadForm, ListMatToQ, MatToQ, ModToQ, OrthogonalForm,
#  QuadraticForm, QuadraticFormType, SymmetricBilinearForm,
#  SymmetricBilinearFormType, SymplecticForm, UnitaryForm

DeclareGlobalFunction("MatToQ@");

ApproximateDerivedGroup@:=function(G)
local F,H,P,ct,d,done,l,oldl,mo;
  #   G must act absolutely irreducibly. This functions attempts to compute
  #  * a subgroup of [G,G] that acts absolutely irreducibly.
  #  * If it succeeds, it returns true and the subgroup.
  #  * If it fails (perhaps because [G,G] is not absolutely irreducible),
  #  * then it reurns false.
  
  F:=DefaultFieldOfMatrixGroup(G);
  mo:=GModuleByMats(GeneratorsOfGroup(G),F);
  if not MTX.IsAbsolutelyIrreducible(mo) then
    Error("Group is not acting absolutely irreducibly");
  fi;
  d:=DimensionOfMatrixGroup(G);
  P:=Group(GeneratorsOfGroup(G)); # for separate randomization
  #   following command has added Check:=false
  H:=Group(Comm(Random(P),Random(P)),
    Comm(Random(P),Random(P)),Comm(Random(P),Random(P)));
  oldl:=d;
  done:=false;
  ct:=0;
  repeat
    mo:=GModuleByMats(GeneratorsOfGroup(H),F);
    l:=Length(MTX.BasesCompositionSeries(mo))-1; # -1 as GAP counts trivial
    if l < oldl then
      #  making progress!
      oldl:=l;
      ct:=0;
    fi;
    if l=1 then
      if MTX.IsAbsolutelyIrreducible(mo) then
        done:=true;
      else
        H:=Group(Concatenation(GeneratorsOfGroup(H),Comm(Random(P),Random(P))));
        ct:=ct+1;
      fi;
    else
      H:=Group(Concatenation(GeneratorsOfGroup(H),Comm(Random(P),Random(P))));
      ct:=ct+1;
    fi;
    
  until done or ct=Maximum(20,Length(GeneratorsOfGroup(G)));
  if done then
    return rec(val1:=true,
      val2:=H);
  fi;
  return rec(val1:=false,
    val2:=fail);
  
end;

#  ******************************************************************
#  * functions for symplectic groups                                  *
#  ******************************************************************
SymplecticForm@:=function(G)
#  -> ,BoolElt ,AlgMatElt ,MonStgElt  Assuming that G acts absolutely
#  irreducibly , try to find a symplectic form which is G - invariant (
#  modulo scalars if Scalars is true ) or prove that no such form exists .
local F,D,M,Scalars,bool,d,g,i,j,mat,s,scals,tmat,z;
  Scalars:=ValueOption("Scalars");
  if Scalars=fail then
    Scalars:=false;
  fi;
  #  G should be matrix group acting (absolutely?) irreducibly.
  #  Decide whether G preserves symplectic form.
  F:=DefaultFieldOfMatrixGroup(G);
  M:=GModuleByMats(GeneratorsOfGroup(G),F);
  if not MTX.IsIrreducible(M) then
    Error("SymplecticForm: G must be irreducible");
  fi;
  D:=MTX.DualModule(M);
  d:=DimensionOfMatrixGroup(G);
  mat:=MTX.IsomorphismModules(M,D);
  bool:=mat<>fail;
  if bool then
    if mat=-TransposedMat(mat) then
      #   To get a unique result, we make the first nonzero entry
      #  * in mat 1 
      for i in [1..d] do
        if mat[1][i]<>0 then
          mat:=mat*mat[1][i]^-1;
          break;
        fi;
      od;
      if Scalars then
        return rec(val1:=bool,
          val2:=mat,
          val3:=List([1..Length(GeneratorsOfGroup(G))],i->mat[1][1]^0));
      else
        return rec(val1:=bool,
          val2:=mat);
      fi;
    fi;
    #  if mat eq -Transpose(mat)
    if not Scalars then
      if MTX.IsAbsolutelyIrreducible(M) then
        return rec(val1:=false,
          val2:=fail);
      else
        Error("SymplecticForm failed - group is not absolutely irreducible");
        #  return "unknown", fail;
      fi;
    fi;
  fi;
  #  if bool
  if not Scalars then
    return rec(val1:=false,
      val2:=fail);
  fi;
  # =v= MULTIASSIGN =v=
  D:=ApproximateDerivedGroup@(G);
  bool:=D.val1;
  D:=D.val2;
  # =^= MULTIASSIGN =^=
  if not bool then
    Error("SymplecticForm failed - derived group may not be absolutely irreducible");
    #  return "unknown",fail,fail;
  fi;
  # =v= MULTIASSIGN =v=
  mat:=SymplecticForm@(D);
  bool:=mat.val1;
  mat:=mat.val2;
  # =^= MULTIASSIGN =^=
  if bool then
    scals:=[];
    z:=0*mat[1][1];
    for g in GeneratorsOfGroup(G) do
      tmat:=g*mat*TransposedMat(g);
      s:=z;
      for i in [1..d] do
        for j in [1..d] do
          if tmat[i][j]<>z then
            if mat[i][j]=z then
              return rec(val1:=false,
                val2:=fail,
                val3:=fail);
            fi;
            if s=z then
              s:=tmat[i][j]*mat[i][j]^-1;
            elif s<>tmat[i][j]*mat[i][j]^-1 then
              return rec(val1:=false,
                val2:=fail,
                val3:=fail);
            fi;
          elif mat[i][j]<>z then
            return rec(val1:=false,
              val2:=fail,
              val3:=fail);
          fi;
        od;
      od;
      Add(scals,s);
    od;
    return rec(val1:=true,
      val2:=mat,
      val3:=scals);
  fi;
  return rec(val1:=false,
    val2:=fail,
    val3:=fail);
  
end;

#  *******************************************************************
#  * functions for orthogonal groups.                                  *
#  *******************************************************************
#  ******************************************************
#  * This function computes the quadratic form preserved by
#  * an orthogonal group in characteristic 2.

ClassicalForms_QuadraticForm2@:=function(field,form,gens,scalars)
local H,R,V,b,e,flag,h,i,j,l,r,x,y;
  #   raise an error if char is not two
  if Characteristic(field)<>2 then
    Error("ERROR: characteristic must be two");
  fi;
  #   construct the upper half of the form
  #R:=MatrixRing(field,Length(form));
  H:=Zero(form);
  for i in [1..Length(form)] do
    for j in [i+1..Length(form)] do
      H[i][j]:=form[i][j];
    od;
  od;
  #   store the linear equations in <e>
  e:=[];
  #   loop over all generators
  b:=[];
  for y in [1..Size(gens)] do
    #   remove scalars
    x:=gens[y]*scalars[y]^-1;
    #   first the right hand side
    r:=x*H*TransposedMat(x)+H;
    #   check <r>
    for i in [1..Length(form)] do
      for j in [1..Length(form)] do
        if r[i][j]+r[j][i]<>Zero(field) then
          return false;
        fi;
      od;
    od;
    #   and now the diagonals
    for i in [1..Length(form)] do
      l:=[];
      for j in [1..Length(form)] do
        l[j]:=x[i][j]^2;
      od;
      l[i]:=l[i]+1;
      Add(b,r[i][i]);
      Add(e,l);
    od;
  od;
  #   and return a solution
  V:=field^(Size(gens)*Length(form));
  #b:=b*FORCEOne(V);
  #  e := [e[i,j]:j in [1..NumberOfRows(form)],i in [1..#e]];
  e:=List([1..Length(e)],i->List([1..Length(form)],j->e[i][j]));
  #e:=IsConsistent(TransposedMat(e),b);
  e:=SolutionMat(TransposedMat(e),b);
  flag:=e<>fail;
  if flag then
    for i in [1..Length(form)] do
      H[i][i]:=e[i];
    od;
    return H;
  else
    return false;
  fi;
  
end;

#  *****************************************************************
#  * This one computes the type of an orthogonal form in Characteristic
#  * 2. It seems to do an awful lot of unneccesary stuff, I'm not really
#  * sure....

ClassicalForms_Signum2@:=function(field,form,quad)
local R,avoid,base,c,d,i,j,k,pol,sgn,x;
  #   compute a new basis, such that the symmetric form is standard
  base:=form^0;
  avoid:=[];
  for i in [1..Length(form)-1] do
    #   find first non zero entry
    d:=1;
    while d in avoid or form[i][d]=Zero(field) do
      d:=d+1;
    od;
    Add(avoid,d);
    #   clear all other entries in this row & column
    for j in [d+1..Length(form)] do
      c:=form[i][j]/form[i][d];
      if c<>Zero(field) then
        for k in [1..Length(form)] do
          form[k][j]:=form[k][j]-c*form[k][d];
        od;
        form[j]:=form[j]-c*form[d];
        base[j]:=base[j]-c*base[d];
      fi;
    od;
  od;
  #   reshuffle basis
  c:=[];
  j:=[];
  for i in [1..Length(form)] do
    if not i in j then
      k:=form[i][avoid[i]];
      Add(c,base[i]/k);
      Add(c,base[avoid[i]]);
      Add(j,avoid[i]);
    fi;
  od;
  base:=c;
  #   and try to fix the quadratic form (this not really necessary)
  x:=X(field,1);
  sgn:=1;
  for i in [1,1+2..Length(form)-1] do
    c:=(base[i]*quad)*base[i];
    if c=Zero(field) then
      c:=(base[i+1]*quad)*base[i+1];
      if c<>Zero(field) then
        base[i+1]:=base[i+1]-c*base[i];
      fi;
    else
      j:=(base[i+1]*quad)*base[i+1];
      if j=Zero(field) then
        base[i]:=base[i]-c*base[i+1];
      else
	Error("fix pol");
        #  pol := [y[1]:i in [1..y[2]],y in Factorisation(x^2+x/j + c/j)];
        pol:=pol;
        if Size(pol)=2 then
          pol:=List(pol,y->-CoefficientsOfUnivariatePolynomial(y)[1]);
          base[i]:=base[i]+pol[1]*base[i+1];
          base[i+1]:=(base[i]+pol[2]*base[i+1])/(pol[1]+pol[2]);
        else
          sgn:=-sgn;
        fi;
      fi;
    fi;
  od;
  #   and return
  return sgn;
  
end;

#  *******************************************************************
#  * This next one is actually a magma intrinsic. Works for odd
#  * characteristic.

ClassicalForms_Signum@:=function(field,form)
local det,sgn,sqr;
  #   if dimension is odd, the signum must be 0
  if Length(form) mod 2=1 then
    return 0;
    #   hard case: characteristic is 2
  elif Characteristic(field)=2 then
    Error("ERROR : characteristic must be odd");
  fi;
  #   easy case
  det:=DeterminantMat(form);
  sqr:=Log(det) mod 2=0; # what is this?
  if Int((Length(form)*(Characteristic(field)^Degree(field)-1)/4))
      mod 2=0 then
    if sqr then
      sgn:=1;
    else
      sgn:=-1;
    fi;
  else
    if sqr then
      sgn:=-1;
    else
      sgn:=1;
    fi;
  fi;
  #   and return
  return sgn;
  
end;

OrthogonalForm@:=function(G)
#  -> ,BoolElt ,MonStgElt ,AlgMatElt  Assuming that G acts absolutely
#  irreducibly , try to find a symmetric bilinear form which is G - invariant
#  , or a quadratic form in characteristic 2 .
local D,F,M,bool,d,gens,i,mat,q,quad,scals,sign;
  #   G should be a matrix group acting (absolutely?) irreducibly.
  #   Decide whether G preserves a symmetric bilinear form.
  F:=DefaultFieldOfMatrixGroup(G);
  M:=GModuleByMats(GeneratorsOfGroup(G),F);
  if not MTX.IsIrreducible(M) then
    Error("SymmetricBilinearForm: G must be irreducible");
  fi;
  d:=DimensionOfMatrixGroup(G);
  q:=Size(F);
  D:=MTX.DualModule(M);
  mat:=MTX.IsomorphismModules(M,D);
  bool:=mat<>fail;
  if bool then
    if mat=TransposedMat(mat) then
      #   To get a unique result, we make the first nonzero entry
      #  * in mat 1 
      for i in [1..d] do
        if mat[1][i]<>0 then
          mat:=mat*mat[1][i]^-1;
          break;
        fi;
      od;
      if IsOddInt(d) then
        return rec(val1:=true,
          val2:="orth",
          val3:=mat);
      fi;
      if IsOddInt(q) then
        sign:=ClassicalForms_Signum@(F,mat);
      else
        gens:=GeneratorsOfGroup(G);
        scals:=List([1..Length(gens)],i->One(G));
        quad:=ClassicalForms_QuadraticForm2@(F,mat,gens,scals);
        if quad=false then
          if MTX.IsAbsolutelyIrreducible(M) then
            return rec(val1:=false,
              val2:=fail,
              val3:=fail);
          else
            Error("OrthogonalForm failed - group is not absolutely irreducible");
            #  return "unknown", fail, fail;
          fi;
        fi;
        sign:=ClassicalForms_Signum2@(F,mat,quad);
      fi;
      if sign=1 then
        return rec(val1:=true,
          val2:="orth+",
          val3:=mat);
      elif sign=-1 then
        return rec(val1:=true,
          val2:="orth-",
          val3:=mat);
      else
        Info(InfoWarning,1,"Signum failed");
        return rec(val1:=false,
          val2:=fail,
          val3:=fail);
      fi;
    fi;
    #  if mat eq Transpose(mat)
    if MTX.IsAbsolutelyIrreducible(M) then
      return rec(val1:=false,
        val2:=fail,
        val3:=fail);
    else
      Error("OrthogonalForm failed - group is not absolutely irreducible");
      #  return "unknown", fail, fail;
    fi;
  fi;
  #  if bool
  return rec(val1:=false,
    val2:=fail,
    val3:=fail);
  
end;

#   Plus a couple of others to replace existing Magma functions 
SymmetricBilinearForm@:=function(G)
#  -> ,BoolElt ,AlgMatElt ,MonStgElt  Assuming that G acts absolutely
#  irreducibly , try to find a symmetric bilinear form which is G - invariant
#  ( modulo scalars if Scalars is true ) or prove that no such form exists .
local D,F,M,Scalars,bool,d,g,gens,i,j,mat,q,quad,s,scals,sign,tmat,type,z;
  Scalars:=ValueOption("Scalars");
  if Scalars=fail then
    Scalars:=false;
  fi;
  F:=DefaultFieldOfMatrixGroup(G);
  q:=Size(F);
  M:=GModuleByMats(G,F);
  if not MTX.IsIrreducible(M) then
    Error("SymmetricBilinearForm: G must be irreducible");
  fi;
  d:=DimensionOfMatrixGroup(G);
  D:=MTX.DualModule(M);
  mat:=MTX.IsomorphismModules(M,D);
  bool:=mat<>fail;
  if bool then
    if mat=TransposedMat(mat) then
      for i in [1..d] do
        if mat[1][i]<>0 then
          mat:=mat*mat[1][i]^-1;
          break;
        fi;
      od;
      if IsOddInt(q) then
	if IsEvenInt(d) then
	  sign:=ClassicalForms_Signum@(F,mat);
	else
	  sign:=0;
	fi;
         ;
      else
        gens:=GeneratorsOfGroup(G);
        scals:=List([1..Size(gens)],i->One(G));
        quad:=ClassicalForms_QuadraticForm2@(F,mat,gens,scals);
        if quad=false then
          #  should only happen in characteristic 2
          if Scalars then
            return rec(val1:=bool,
              val2:=mat,
              val3:="symplectic",
              val4:=List([1..Length(GeneratorsOfGroup(G))],i->mat[1][1]^0));
          else
            return rec(val1:=bool,
              val2:=mat,
              val3:="symplectic");
          fi;
        fi;
        sign:=ClassicalForms_Signum2@(F,mat,quad);
      fi;
      if sign=1 then type:="orthogonalplus";
      elif sign=-1 then type:="orthogonalminus";
      else type:="orthogonalcircle";fi;
      if Scalars then
        return rec(val1:=bool,
          val2:=mat,
          val3:=type,
          val4:=List([1..Length(GeneratorsOfGroup(G))],i->mat[1][1]^0));
      else
        return rec(val1:=bool,
          val2:=mat,
          val3:=type);
      fi;
    fi;
    #  if mat eq Transpose(mat)
    if not Scalars then
      if MTX.IsAbsolutelyIrrelucible(M) then
        return rec(val1:=false,
          val2:=fail,
          val3:=fail);
      else
        Error("SymmetricBilinearForm failed - group is not absolutely irreducible");
        #  return "unknown", fail, fail;
      fi;
    fi;
  fi;
  #  if bool
  if not Scalars then
    return rec(val1:=false,
      val2:=fail,
      val3:=fail);
  fi;
  # =v= MULTIASSIGN =v=
  D:=ApproximateDerivedGroup@(G);
  bool:=D.val1;
  D:=D.val2;
  # =^= MULTIASSIGN =^=
  if not bool then
    Error("SymmetricBilinearForm failed - derived group may not be absolutely irreducible");
    #  return "unknown",fail,fail,fail;
  fi;
  # =v= MULTIASSIGN =v=
  type:=SymmetricBilinearForm@(D);
  bool:=type.val1;
  mat:=type.val2;
  type:=type.val3;
  # =^= MULTIASSIGN =^=
  if bool then
    scals:=[];
    z:=0*mat[1][1];
    d:=DimensionOfMatrixGroup(G);
    for g in GeneratorsOfGroup(G) do
      tmat:=g*mat*TransposedMat(g);
      s:=z;
      for i in [1..d] do
        for j in [1..d] do
          if tmat[i][j]<>z then
            if mat[i][j]=z then
              return rec(val1:=false,
                val2:=fail,
                val3:=fail,
                val4:=fail);
            fi;
            if s=z then
              s:=tmat[i][j]*mat[i][j]^-1;
            elif s<>tmat[i][j]*mat[i][j]^-1 then
              return rec(val1:=false,
                val2:=fail,
                val3:=fail,
                val4:=fail);
            fi;
          elif mat[i][j]<>z then
            return rec(val1:=false,
              val2:=fail,
              val3:=fail,
              val4:=fail);
          fi;
        od;
      od;
      Add(scals,s);
    od;
    return rec(val1:=true,
      val2:=mat,
      val3:=type,
      val4:=scals);
  fi;
  return rec(val1:=false,
    val2:=fail,
    val3:=fail,
    val4:=fail);
  
end;

InstallGlobalFunction(QuadraticForm@,
#  -> ,BoolElt ,AlgMatElt ,MonStgElt  Assuming that G acts absolutely
#  irreducibly , try to find a quadratic form which is G - invariant ( modulo
#  scalars if Scalars is true ) or prove that no such form exists .
function(G)
local D,F,M,Scalars,bool,d,g,gens,i,j,mat,q,quad,s,scals,sign,tmat,type,z;
  Scalars:=ValueOption("Scalars");
  if Scalars=fail then
    Scalars:=false;
  fi;
  #   G should be a matrix group acting (absolutely?) irreducibly.
  #   Decide whether G preserves a quadratic form
  d:=DimensionOfMatrixGroup(G);
  F:=DefaultFieldOfMatrixGroup(G);
  q:=Size(F);
  M:=GModuleByMats(G,F);
  if not MTX.IsIrreducible(M) then
    Error("QuadraticForm: G must be irreducible");
  fi;
  D:=MTX.DualModule(M);
  mat:=MTX.IsomorphismModules(M,D);
  bool:=mat<>fail;
  if bool then
    if mat=TransposedMat(mat) then
      for i in [1..d] do
        if mat[1][i]<>0 then
          mat:=mat*mat[1][i]^-1;
          break;
        fi;
      od;
      if IsOddInt(q) then
	if IsOddInt(q) then
	  sign:=ClassicalForms_Signum@(F,mat);
	else
	  sign:=0;
	fi;
        for i in [2..d] do
          for j in [1..i-1] do
            mat[i][j]:=0*mat[i][j];
          od;
        od;
        for i in [1..d] do
          mat[i][i]:=mat[i][i]/2;
        od;
	if sign=1 then
	  type:="orthogonalplus";
	elif sign=-1 then
	  type:="orthogonalminus";
	else
	  type:="orthogonalcircle";
	fi;
        if Scalars then
          return rec(val1:=bool,
            val2:=mat,
            val3:=type,
            val4:=List(GeneratorsOfGroup(G),i->mat[1][1]^0));
        else
          return rec(val1:=bool,
            val2:=mat,
            val3:=type);
        fi;
      fi;
      gens:=GeneratorsOfGroup(G);
      scals:=List([1..Length(gens)],i->One(G));
      quad:=ClassicalForms_QuadraticForm2@(F,mat,gens,scals);
      if quad<>false then
        sign:=ClassicalForms_Signum2@(F,mat,quad);
      elif Scalars then
        return rec(val1:=false,
          val2:=fail,
          val3:=fail,
          val4:=fail);
      else
        return rec(val1:=false,
          val2:=fail,
          val3:=fail);
      fi;
      if sign=1 then
	type:="orthogonalplus";
      elif sign=-1 then
	type:="orthogonalminus";
      else
	type:="orthogonalcircle";
      fi;
      if Scalars then
        return rec(val1:=bool,
          val2:=quad,
          val3:=type,
          val4:=List(GeneratorsOfGroup(G),i->mat[1][1]^0));
      else
        return rec(val1:=bool,
          val2:=quad,
          val3:=type);
      fi;
    fi;
    #  if mat eq Transpose(mat)
    if not Scalars then
      if MTX.IsAbsolutelyIrreducible(M) then
        return rec(val1:=false,
          val2:=fail,
          val3:=fail);
      else
        Error("QuadraticForm failed - group is not absolutely irreducible");
        #  return "unknown", fail, fail;
      fi;
    fi;
  fi;
  #  if bool
  if not Scalars then
    return rec(val1:=false,
      val2:=fail,
      val3:=fail);
  fi;
  # =v= MULTIASSIGN =v=
  D:=ApproximateDerivedGroup@(G);
  bool:=D.val1;
  D:=D.val2;
  # =^= MULTIASSIGN =^=
  if not bool then
    Info(InfoWarning,1,
      "QuadraticForm failed - derived group may not be absolutely irreducible");
    #  return "unknown",fail,fail,fail;
  fi;
  # =v= MULTIASSIGN =v=
  type:=QuadraticForm@(D);
  bool:=type.val1;
  mat:=type.val2;
  type:=type.val3;
  # =^= MULTIASSIGN =^=
  if bool then
    scals:=[];
    z:=0*mat[1][1];
    d:=Dimension(G);
    for g in GeneratorsOfGroup(G) do
      tmat:=g*mat*TransposedMat(g);
      for i in [2..d] do
        for j in [1..i-1] do
          tmat[j][i]:=tmat[j][i]+tmat[i][j];
          tmat[i][j]:=0*tmat[i][j];
        od;
      od;
      s:=z;
      for i in [1..d] do
        for j in [i..d] do
          if tmat[i][j]<>z then
            if mat[i][j]=z then
              return rec(val1:=false,
                val2:=fail,
                val3:=fail,
                val4:=fail);
            fi;
            if s=z then
              s:=tmat[i][j]*mat[i][j]^-1;
            elif s<>tmat[i][j]*mat[i][j]^-1 then
              return rec(val1:=false,
                val2:=fail,
                val3:=fail,
                val4:=fail);
            fi;
          elif mat[i][j]<>z then
            return rec(val1:=false,
              val2:=fail,
              val3:=fail,
              val4:=fail);
          fi;
        od;
      od;
      Add(scals,s);
    od;
    return rec(val1:=true,
      val2:=mat,
      val3:=type,
      val4:=scals);
  fi;
  return rec(val1:=false,
    val2:=fail,
    val3:=fail,
    val4:=fail);
end);

#  *******************************************************************
#  * functions for unitary groups                                      *
#  *******************************************************************
ListMatToQ@:=function(a,q)
local i,list;
  #   raise every element of matrix A to q-th power.
  return List(Flat(a),x->x^q);
end;

InstallGlobalFunction(MatToQ@,
function(A,q)
local B,i,j;
  #   raise every element of matrix A to q-th power
  B:=MutableCopyMat(A);
  for i in [1..Length(A)] do
    for j in [1..Length(A[1])] do
      B[i][j]:=(A[i][j])^q;
    od;
  od;
  return B;
end);

ModToQ@:=function(M,q)
local G;
  #   same for GModule M
  return GModuleByMats(List(M.generators,x->MatToQ@(x,q)),M.field);
end;

UnitaryForm@:=function(G)
#  -> ,BoolElt ,AlgMatElt  Assuming that G acts absolutely irreducibly , try
#  to find a unitary form which is G - invariant ( modulo scalars if Scalars
#  is true ) or prove that no such form exists .
local D,DD,F,M,Scalars,bool,c,d,f,g,i,isp,j,mat,q,q2,s,scal,scals,tmat,x,z;
  Scalars:=ValueOption("Scalars");
  if Scalars=fail then
    Scalars:=false;
  fi;
  #  G should be matrix group over GF(q^2) acting (absolutely?) irreducibly.
  #  Decide whether G preserves unitary form.
  d:=DimensionOfMatrixGroup(G);
  F:=DefaultFieldOfMatrixGroup(G);
  q2:=Size(F);
  f:=Collected(Factors(q2));
  if f[1][2] mod 2=1 then
    if Scalars then
      return rec(val1:=false,
        val2:=fail,
        val3:=fail);
    else
      return rec(val1:=false,
        val2:=fail);
    fi;
  fi;
  q:=f[1][1]^(QuoInt(f[1][2],2));
  M:=GModuleByMats(GeneratorsOfGroup(G),F);
  D:=MTX.DualModule(M);
  DD:=ModToQ@(D,q);
  mat:=MTX.IsomorphismModules(M,DD);
  bool:=mat<>fail;
  #   We now need to ensure that mat is actually the matrix of a/
  #  * unitary form, which can be achieved by multiplying it by a scalar
  
  if bool then
    if mat<>TransposedMat(MatToQ@(mat,q)) then
      #  c := Representative( { <i,j>: i in [1..d], j in [1..d] | mat[i][j]
      #  ne F!0 } );
      x:=First([1..Length(mat)],x->not IsZero(mat[x]));
      c:=[x,First([1..Length(mat[x])],y->not IsZero(mat[x][y]))];
      if not IsZero(mat[c[2]][c[1]]) then
        x:=mat[c[1]][c[2]]*mat[c[2]][c[1]]^-q;
        z:=RootFFE(x,q-1);
        isp:=z<>fail;
      fi;
      if IsZero(mat[c[2]][c[1]]) or not isp then
        if not MTX.IsAbsolutelyIrreducible(M) then
          Error("UnitaryForm failed - group is not absolutely irreducible");
          #  return "unknown", fail, fail;
        fi;
        Error("IsPower failed in UnitaryForm");
      fi;
      scal:=DiagonalMat(List([1..d],i->z));
      mat:=mat*scal;
    fi;
    for i in [1..d] do
      if mat[1][i]<>0 then
        x:=mat[1][i];
        if x=x^q then
          mat:=mat*x^-1;
        fi;
        break;
      fi;
    od;
    if mat<>TransposedMat(MatToQ@(mat,q)) and not MTX.IsAbsolutelyIrreducible(M) then
      Error("UnitaryForm failed - group is not absolutely irreducible");
    fi;
    Assert(1,mat=TransposedMat(MatToQ@(mat,q)));
    if Scalars then
      return rec(val1:=bool,
        val2:=mat,
        val3:=List([1..Length(GeneratorsOfGroup(G))],i->mat[1][1]^0));
    else
      return rec(val1:=bool,
        val2:=mat);
    fi;
  fi;
  if not Scalars then
    return rec(val1:=false,
      val2:=fail);
  fi;
  # =v= MULTIASSIGN =v=
  D:=ApproximateDerivedGroup@(G);
  bool:=D.val1;
  D:=D.val2;
  # =^= MULTIASSIGN =^=
  if not bool then
    Info(InfoWarning,1,
      "UnitaryForm failed - derived group may not be absolutely irreducible");
    #  return "unknown",fail,fail;
  fi;
  # =v= MULTIASSIGN =v=
  mat:=UnitaryForm@(D);
  bool:=mat.val1;
  mat:=mat.val2;
  # =^= MULTIASSIGN =^=
  if bool then
    scals:=[];
    z:=0*mat[1][1];
    d:=DimensionOfMatrixGroup(G);
    for g in GeneratorsOfGroup(G) do
      tmat:=g*mat*TransposedMat(MatToQ@(g,q));
      s:=z;
      for i in [1..d] do
        for j in [i..d] do
          if tmat[i][j]<>z then
            if mat[i][j]=z then
              return rec(val1:=false,
                val2:=fail,
                val3:=fail);
            fi;
            if s=z then
              s:=tmat[i][j]*mat[i][j]^-1;
            elif s<>tmat[i][j]*mat[i][j]^-1 then
              return rec(val1:=false,
                val2:=fail,
                val3:=fail);
            fi;
          elif mat[i][j]<>z then
            return rec(val1:=false,
              val2:=fail,
              val3:=fail);
          fi;
        od;
      od;
      Add(scals,s);
    od;
    return rec(val1:=true,
      val2:=mat,
      val3:=scals);
  fi;
  return rec(val1:=false,
    val2:=fail,
    val3:=fail);
  
end;

ClassicalForms@:=function(G)
#  -> ,Rec  Assuming that G acts absolutely irreducibly , try to find a
#  classical form which is G - invariant ( modulo scalars if Scalars is true
#  ) or prove that no such form exists .
local Scalars,ans,bool,form,scals,scalsq,signq,type,typeq,mo;
  Scalars:=ValueOption("Scalars");
  if Scalars=fail then
    Scalars:=false;
  fi;
  mo:=GModuleByMats(GeneratorsOfGroup(G),DefaultFieldOfMatrixGroup(G));
  if not MTX.IsIrreducible(mo) then
    Error("ClassicalForms: G must be irreducible");
  fi;
  ans:=rec();
  ans.formType:="linear";
  ans.bilinearForm:=false;
  ans.quadraticForm:=false;
  ans.sesquilinearForm:=false;
  ans.scalars:=false;
  if Scalars then
    # =v= MULTIASSIGN =v=
    scals:=SymmetricBilinearForm@(G:Scalars:=true);
    bool:=scals.val1;
    form:=scals.val2;
    type:=scals.val3;
    scals:=scals.val4;
    # =^= MULTIASSIGN =^=
    if bool="unknown" then
      ans.formType:="unknown";
    elif bool then
      ans.bilinearForm:=form;
      # =v= MULTIASSIGN =v=
      scalsq:=QuadraticForm@(G:Scalars:=true);
      bool:=scalsq.val1;
      form:=scalsq.val2;
      type:=scalsq.val3;
      scalsq:=scalsq.val4;
      # =^= MULTIASSIGN =^=
      if bool="unknown" or bool=false then
        #  should only happen in characteristic 2
        ans.formType:="symplectic";
        ans.scalars:=scals;
        return ans;
      else
        ans.formType:=type;
        if type="orthogonalplus" then
          signq:=1;
        elif type="orthogonalminus" then
          signq:=-1;
        elif type="orthogonalcircle" then
          signq:=0;
        fi;
        ans.quadraticForm:=form;
        ans.scalars:=scals;
        ans.sign:=signq;
        return ans;
      fi;
    fi;
    # =v= MULTIASSIGN =v=
    scals:=SymplecticForm@(G:Scalars:=true);
    bool:=scals.val1;
    form:=scals.val2;
    scals:=scals.val3;
    # =^= MULTIASSIGN =^=
    if bool="unknown" then
      ans.formType:="unknown";
    elif bool then
      ans.formType:="symplectic";
      ans.bilinearForm:=form;
      ans.scalars:=scals;
      return ans;
    fi;
    # =v= MULTIASSIGN =v=
    scals:=UnitaryForm@(G:Scalars:=true);
    bool:=scals.val1;
    form:=scals.val2;
    scals:=scals.val3;
    # =^= MULTIASSIGN =^=
    if bool="unknown" then
      ans.formType:="unknown";
    elif bool then
      ans.formType:="unitary";
      ans.sesquilinearForm:=form;
      ans.scalars:=scals;
      return ans;
    fi;
  else
    # =v= MULTIASSIGN =v=
    type:=SymmetricBilinearForm@(G);
    bool:=type.val1;
    form:=type.val2;
    type:=type.val3;
    # =^= MULTIASSIGN =^=
    if bool="unknown" then
      ans.formType:="unknown";
    elif bool then
      ans.bilinearForm:=form;
      # =v= MULTIASSIGN =v=
      typeq:=QuadraticForm@(G);
      bool:=typeq.val1;
      form:=typeq.val2;
      typeq:=typeq.val3;
      # =^= MULTIASSIGN =^=
      if bool="unknown" or bool=false then
        #  should only happen in characteristic 2
        ans.formType:="symplectic";
        ans.scalars:=List(GeneratorsOfGroup(G),i->One(G)[1][1]);
        return ans;
      else
        ans.formType:=type;
        if type="orthogonalplus" then
          signq:=1;
        elif type="orthogonalminus" then
          signq:=-1;
        elif type="orthogonalcircle" then
          signq:=0;
        fi;
        ans.quadraticForm:=form;
        ans.scalars:=List(GeneratorsOfGroup(G),i->One(G)[1][1]);
        ans.sign:=signq;
        return ans;
      fi;
    fi;
    # =v= MULTIASSIGN =v=
    form:=SymplecticForm@(G);
    bool:=form.val1;
    form:=form.val2;
    # =^= MULTIASSIGN =^=
    if bool="unknown" then
      ans.formType:="unknown";
    elif bool then
      ans.formType:="symplectic";
      ans.bilinearForm:=form;
      ans.scalars:=List(GeneratorsOfGroup(G),i->One(G)[1][1]);
      return ans;
    fi;
    # =v= MULTIASSIGN =v=
    form:=UnitaryForm@(G);
    bool:=form.val1;
    form:=form.val2;
    # =^= MULTIASSIGN =^=
    if bool="unknown" then
      ans.formType:="unknown";
    elif bool then
      ans.formType:="unitary";
      ans.sesquilinearForm:=form;
      ans.scalars:=List(GeneratorsOfGroup(G),i->One(G)[1][1]);
      return ans;
    fi;
  fi;
  return ans;
  
end;
;
FormType@:=function(G)
#  -> ,MonStgElt  Return the type of any classical form ( mod scalars if
#  Scalars is true ) fixed by G .
local Scalars,cf;
  Scalars:=ValueOption("Scalars");
  if Scalars=fail then
    Scalars:=false;
  fi;
  cf:=ClassicalForms@(G:Scalars:=Scalars);
  if IsBound(cf.formType) then
    return cf.formType;
  fi;
  return "unknown";
  
end;
;
SymmetricBilinearFormType@:=function(form)
#  -> ,MonStgElt  Return the type ( orthogonalplus or orthogonalminus ) of
#  symmetric bilinear form in odd characteristic
local field;
  field:=ValueOption("field");
  if field=fail then
    field:=0;
  fi;
  if field=0 then
    field:=DefaultFieldOfMatrixGroup(form);
  else
    Assert(1,IsSubset(field,DefaultFieldOfMatrixGroup(form)));
    form:=form;
  fi;
  if ClassicalForms_Signum@(field,form)=1 then
    return "orthogonalplus";
  else
    return "orthogonalminus";
  fi;
  
end;
;
QuadraticFormType@:=function(form)
#  -> ,MonStgElt  Return the type ( orthogonalplus or orthogonalminus ) of
#  quadratic form in even characteristic
local field;
  field:=ValueOption("field");
  if field=fail then
    field:=0;
  fi;
  if field=0 then
    field:=DefaultFieldOfMatrixGroup(form);
  else
    Assert(1,IsSubset(field,DefaultFieldOfMatrixGroup(form)));
    form:=form;
  fi;
  if ClassicalForms_Signum2@(field,form+TransposedMat(form),form)=1 then
    return "orthogonalplus";
  else
    return "orthogonalminus";
  fi;
  
end;
;
InternalGetOrthogonalForm@:=function(G)
#  -> ,AlgMatElt  Internal
local r;
  #   SH, Oct 07 
  #   this intrinsic just calls ClassicalForms and checks the result 
  #   used from within the C-code membership test                    
  #   it is only called with groups generated by one of GO*, SO*, Omega*,
  #  (CO*) intrinsics 
  #   if it wasnt for the CO*, which are not yet implemented, we could use
  #  OrthogonalForm intrinsic 
  #   next line has option :Scalars
  #  r := ClassicalForms(G:Scalars);
  r:=ClassicalForms@(G);
  Assert(1,not IsBool(r.bilinearForm));
  #  assert r`formType[1..4]) eq "orth";
  return MatrixByEntries(r.bilinearForm);
  
end;
;
InternalOrthTestQuadForm@:=function(x)
#  -> ,BoolElt  Internal
local G,Q,T,r;
  #   billu, Nov 08 
  G:=Parent(x);
  #   next line has option :Scalars
  #  r := ClassicalForms(G:Scalars);
  r:=ClassicalForms@(G);
  Assert(1,not IsBool(r.bilinearForm));
  #  assert r`formType[1..4] eq "orth";
  Q:=r.quadraticForm;
  Assert(1,not IsBool(Q));
  T:=x*Q*TransposedMat(x)-Q;
  return ForAll([1..DimensionOfMatrixGroup(G)],i->IsZero(T[i][i]));
  
end;
;


