#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.36, 12/19/15 by AH

#  Global Variables used: Append, BaseRing, ChangeMat, ClassicalForms,
#  ConvertTo1sAndPrims, CorrectDiag, CorrectForm, Degree, Determinant,
#  DiagonalMatrix, Eltseq, Factorisation, GL, GetConjMat, GetCoords,
#  GetRandomConj, GetSeed, Identity, IdentityMatrix, IsAntiDiagonal,
#  IsDiagonal, IsEven, IsFinite, IsOdd, IsSquare, IsZero, ListMatToQ, Matrix,
#  MatrixAlgebra, MatrixRing, Ncols, NormaliseForm, Nrows, NumberOfRows,
#  PrimitiveElement, QuadraticFormMinus, QuadraticFormPlus,
#  QuadraticFormType, Quotrem, Random, Root, SetSeed, StandardHermitianForm,
#  SwapRows, SymmetricBilinearForm, SymmetricBilinearFormMinus,
#  SymmetricBilinearFormPlus, SymmetricBilinearFormType, TransformForm,
#  Transpose, UT, symplectic_std

#  Defines: ChangeMat, ConvertTo1sAndPrims, CorrectDiag, CorrectForm,
#  GetConjMat, GetCoords, GetRandomConj, IsAntiDiagonal, ListMatToQ,
#  NormaliseForm, TransformForm, symplectic_std

IsAntiDiagonal@:=function(mat,d)
local i,j;
  for i in [1..d] do
    for j in [1..d] do
      if (not (i=(d-j+1))) and (not (mat[i][j]=0)) then
        return false;
      fi;
    od;
  od;
  return true;
  
end;

#  **********************************************************************
#  * This function takes a diagonal form matrix and finds a change of
#  * basis matrix which sends the form to a diagonal one consisting only
#  * of 1s and primitives.
#  *********************************************************************
ConvertTo1sAndPrims@:=function(form,d,q)
local D,F,a,b,i,list,nonsquares,z;
  F:=DefaultFieldOfMatrix(form);
  Assert(1,Size(F)=q);
  z:=PrimitiveElement(F);
  list:=[];
  nonsquares:=[];
  for i in [1..d] do
    b:=RootFFE(form[i][i],2);
    a:=b<>fail;
    if a then
      Add(list,(b^-1));
    else
      b:=RootFFE(form[i][i]*(z^-1),2);
      a:=b<>fail;
      Add(list,(b^-1));
      Add(nonsquares,i);
    fi;
  od;
  D:=DiagonalMat(list);
  #  return (d ne 0) select GL(d, F)!D else D;
  
end;

#  ***********************************************************************
#  * ChangeMat returns either Tranpose(Frobenius(mat)) or
#  * Transpose(mat), depending on whether we have a form s.t.
#  * g*form*Transpose(g) = form or g * form*(Transpose(Frobenius(g)))
#  * = form.

ChangeMat@:=function(mat,type,d,p)
local F;
  F:=DefaultFieldOfMatrix(mat);
  if type="unitary" then
    Assert(1,Size(F)=p^2);
    return TransposedMat(MatToQ@(mat,p));
  else
    return TransposedMat(mat);
  fi;
  
end;

#  **********************************************************************
#  *

NormaliseForm@:=function(form,mat,type,d,p)
local F,mat2,q;
  F:=DefaultFieldOfMatrix(form);
  if type="unitary" then
    Assert(1,Size(F)=p^2);
    q:=p^2;
  else
    Assert(1,Size(F)=p);
    q:=p;
  fi;
  form:=form;
  mat2:=ChangeMat@(mat,type,d,p);
  if d<>0 then
    return (mat*form*mat2);
  fi;
  return mat*form*mat2;
  
end;

#  *********************************************************************
#  * GetCoords returns the column number in which row i of the form must
#  * be nonzero for conjugation.

GetCoords@:=function(i,d,q,type)
if type="symplectic" then
    return d-i+1;
  else
    return i;
  fi;
  
end;

#  *********************************************************************
#  * CorrectDiag takes a (diagonal or antidiagonal) form matrix, and the
#  * type of form that it is supposed to represent, and finds a
#  * conjugating element such that the group will now preserve a
#  * form matrix consisting of all +1s and -1s.
#  * In the case of an orthogonal form of type "orth+" it turns
#  * everything into 1s and zs, where z is a primitive element of the
#  * field.
#  * In the case of "orth", if the form has an odd number of nonsquares
#  * then it converts the matrix to all +1s, if it has an odd number of
#  * squares then it converts the matrix to all primitives.
#  * q is a prime power.

CorrectDiag@:=function(form,d,q,type)
local F,Restore,a,b,bool,conj,final,i,list,mat2,mat3,mat4,newform,newlist,
   nonsquares,ns,p,quot,redefined,rem,s1,s2,temp,x,z;
  Restore:=ValueOption("Restore");
  if Restore=fail then
    Restore:=false;
  fi;
  F:=DefaultFieldOfMatrix(form);
  Assert(1,Size(F)=q);
  if type="unitary" then
    p:=RootFFE(q,2);
    bool:=p<>fail;
    if d<>0 then
      return DiagonalMat(List([1..d],i->RootFFE(form[i][i],p+1)^-1));
    fi;
    return DiagonalMat(List([1..d],i->RootFFE(form[i][i],p+1)^-1));
  elif type="symplectic" then
      # Int(d/2) was Quotrem
    list:=List([1..Int(d/2)],i->(form[i][d-i+1])^-1);
    if d<>0 then
      # Int(d/2) was Quotrem
      return DiagonalMat(Concatenation(list,List([1..Int(d/2)],i->1)));
    fi;
    return DiagonalMat(Concatenation(list,List([1..Int(d/2)],i->1)));
  fi;
  z:=PrimitiveElement(F);
  conj:=ConvertTo1sAndPrims@(form,d,q);
  #  "counting nonsquare entries.";
  nonsquares:=[];
  for i in [1..d] do
    b:=RootFFE(form[i][i],2);
    a:=b<>fail;
    if not a then
      Add(nonsquares,i);
    fi;
  od;
  ns:=Length(nonsquares);
  #  
  #  * if all entries are square then conjugation by conj will do.
  
  if ns=0 then
    return conj;
  fi;
  #   At this stage in case orth it is necessary to decide whether we
  #  * are converting nonsquares into squares or vice versa. We pick
  #  * whichever one has an even number of occurrences.
  
  redefined:=false;
  if type="orth" then
    if ns=d then
      return conj;
    fi;
    if IsOddInt(ns) then
      redefined:=true;
      temp:=nonsquares;
      nonsquares:=Filtered([1..d],x-> not x in temp);
      ns:=Size(nonsquares);
    fi;
  fi;
  #   collecting field element required to turn pairs of nonsquares
  #  * into squares, or in case orth maybe vice versa
  
  #   save random number state, then set to known value for reproducible
  #   results; Derek implied this was desirable for more than just
  #   debugging purposes.
  if Restore then
    Info(InfoWarning,1,"store random state");
    # # =v= MULTIASSIGN =v=
    # s2:=GetSeed();
    # s1:=s2.val1;
    # s2:=s2.val2;
    # # =^= MULTIASSIGN =^=
    # SetSeed(0);
  fi;
  x:=false;
  while not x do
    b:=Random(F);
    if not redefined then
      # =v= MULTIASSIGN =v=
      a:=RootFFE(z^-1-b^2,2);
      x:=a<>fail;
    else
      a:=RootFFE(z-b^2,2);
      x:=a<>fail;
    fi;
  od;
  #if Restore then
  #  #   restore the random state
  #  SetSeed(s1,s2);
  #fi;
  #  
  #  * we have to change squares into nonsquares in pairs.
  #  * First we sort out the coordinates that we will fix. These are
  #  * the "squares".
  
  rem:=QuotientRemainder(ns,2);
  quot:=rem[1];
  rem:=rem[2];
  list:=[];
  for i in [1..d] do
    if not i in nonsquares then
      Add(list,[i,i,One(F)]);
    fi;
  od;
  #   now we convert pairs of "nonsquares"
  
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
  mat2:=MatrixByEntries(F,d,d,list);
  conj:=mat2*conj;
  #  "moving final nonsquare entry (if exists) to (d, d) position";
  mat3:=IdentityMatrix(d,F);
  if rem=1 then
    if not final=d then
      newlist:=Concatenation(List(Filtered([1..d],i->not i=final and not i=d),i->[i,i,1]),[[final,d,1],[d,final,1]]);
      mat3:=MatrixByEntries(F,d,d,newlist);
    fi;
  fi;
  conj:=mat3*conj;
  newform:=NormaliseForm@(form,conj,type,d,q);
  #   So by this stage we should have the matrix being all squares or
  #  * all nonsquares, and the final entry being the unique one that is
  #  * different, if such exists. However, because we've been
  #  * converting it around, we should re-check that it's all 1s or
  #  * all primitives
  
  mat4:=ConvertTo1sAndPrims@(newform,d,q);
  return mat4*conj;
  
end;

#  **************************************************************
#  
#  * This function returns a matrix that is the identity on the
#  * first i rows and columns, and a random (invertible) matrix on
#  * the bottom d \times d block.
#  * in the symplectic case, or orthogonals over even fields,
#  * it's the first rows and final columns that are zero.
#  * note that there's a minor problem with ensuring that the matrix has
#  * nonzero determinant.

GetRandomConj@:=function(i,d,F,type)
local j,k,newelt,q,startelt;
  q:=Size(F);
  startelt:=PseudoRandom(GL(d-i,F));
  newelt:=DiagonalMat(List([1..d],j->One(F)));
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
  if not DeterminantMat(newelt)=0 then
    #  "conj_elt =", newelt;
    return newelt;
  else
    return GetRandomConj@(i,d,F,type);
  fi;
  
end;

#  **************************************************************
GetConjMat@:=function(form,col,d,q,type)
local F,conjmat,i,vec;
  F:=DefaultFieldOfMatrix(form);
  Assert(1,Size(F)=q);
  conjmat:=DiagonalMat(List([1..d],i->One(F)));
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
  return conjmat;
  
end;

symplectic_std@:=function(F)
local Fb,Fc,K,T,b,i,j,n,ok,a;
  #   this function is written by Markus Kirschmer (16/10/09)
  #  * The following should transform a skewsymmetric matrix over any field
  #  of
  #  * char \ne 2  to  the standard one. Is simply constructs pairwise
  #  * perpendicular 2-dimensional subspaces that yield the forms [[0,1],
  #  [0,-1]].
  #  * Finally it reorders the bases.
  
  K:=DefaultFieldOfMatrix(F);
  n:=Length(F);
  T:=MutableIdentityMat(n,K);
  for i in [1..QuoInt(n,2)] do
    b:=T[2*(i-1)+1];
    Fb:=F*b;
    ok:=ForAny([2*i..n],j->not IsZero(T[j]*Fb));
    Assert(1,(ok));
    #   otherwise F is singular
    #SwapRows(T,2*i,j);
    ok:=T[2*i];T[2*i]:=T[j];T[j]:=ok;
    ok:=T[2*i]*Fb;
    T[2*i]:=T[2*i]/(-ok[1]);

    Fc:=F*T[2*i];
    for j in [2*i+1..n] do
      ok:=T[j]*Fb;
      a:=T[j]*Fc;
      T[j]:=T[j]+T[2*i]*ok[1]-b*a[1];
    od;
  od;
  return (T{Concatenation([1,1+2..n],[n,n+-2..1])})^-1;
  
end;

#  *********************************************************************
#  
#  * finds a matrix that will conjugate a group preserving form1 of type
#  * type into a group preserving a standard form. For symplectic groups
#  * this is AntiDiag([1..1 -1..-1]), for the remaining
#  * groups I have (somewhat lazily) got it to take them to an orthonormal
#  * basis.
#  * For orthogonal groups in even characteristic a completely different
#  * function is used - note that this MUST have already been checked,
#  * and a quadratic form put into it.

CorrectForm@:=function(form,d,q,type)
#  -> ,GrpMatElt  form should be a classical form of type type fixed by a
#  subgroup G of GL ( d , q ) . Return a matrix mat such that G ^ mat fixes
#  our preferred standard form .
local F,Restore,bool,conj,conj_torus,conjmat,coords,i,mat,p,s1,s2,temp;
  Restore:=ValueOption("Restore");
  if Restore=fail then
    Restore:=false;
  fi;
  F:=DefaultFieldOfMatrix(form);
  Assert(1,Size(F)=q);
  if type="unitary" then
    p:=RootFFE(q,2);
    bool:=p<>fail;
  else
    p:=q;
  fi;
  if type="orthogonalplus" then
    type:="orth+";
  fi;
  if type="orthogonalminus" then
    type:="orth-";
  fi;
  #   this special version only called for q odd
  if (type="orth+" or type="orth-") and IsEvenInt(q) then
    # =v= MULTIASSIGN =v=
    mat:=CorrectQuadForm@(form,d,q,type);
    form:=mat.val1;
    mat:=mat.val2;
    # =^= MULTIASSIGN =^=
    return mat;
  fi;
  conj:=IdentityMatrix(F,d);
  #  
  #  * We go through row by row doing a type of row reduction. Once it's
  #  * been done d-1 times then the final row is guaranteed to be
  #  * nonzero in the right place.
  
  #   save random number state, then set to known value for reproducible
  #   results; Derek implied this was desirable for more than just
  #   debugging purposes.
  #  if Restore then
  # =v= MULTIASSIGN =v=
Info(InfoWarning,1,"store random state");
#  s2:=GetSeed();
#  s1:=s2.val1;
#  s2:=s2.val2;
#  # =^= MULTIASSIGN =^=
#  SetSeed(0);
#  #  end if;

  for i in [1..d-1] do
    #   First we have to deal with the problem that the relevant matrix
    #  * entry (entry [coords][i]) may be zero.
    #  * In the unitary case this is entry [i][i].
    #  * In the symplectic case it's entry [d-i+1][i].
    #  * In orth+ case it's also [d-i+1][i]. We also need [i][i] to be zero.
    
    temp:=form;
    mat:=IdentityMatrix(d,F);
    coords:=GetCoords@(i,d,q,type);
    while temp[coords][i]=0 do
      mat:=GetRandomConj@(i-1,d,F,type);
      temp:=NormaliseForm@(form,mat,type,d,p);
    od;
    form:=temp;
    conj:=mat*conj;
    conjmat:=GetConjMat@(form,i,d,q,type);
    form:=NormaliseForm@(form,conjmat,type,d,p);
    conj:=conjmat*conj;
  od;
  #   restore the random state
  #if Restore then
  #  SetSeed(s1,s2);
  #fi;
  #   By now the matrix should either be diagonal or antidiagonal.
  
  #  "checking that mat is Diagonal or antidiagonal";
  if type="symplectic" then
    Assert(1,IsAntiDiagonal@(form,d));
  else
    #IsDiagonal(form));
    Assert(1,ForAll([1..Length(form)],
         i->ForAll([1..Length(form[i])],j->j=i or IsZero(form[i][j]))));
  fi;
  #  "finding element to conjugate torus";
  conj_torus:=CorrectDiag@(form,d,q,type:Restore:=Restore);
  form:=NormaliseForm@(form,conj_torus,type,d,p);
  conj:=conj_torus*conj;
  conj:=conj^-1;
  if d<>0 then
    #  GL(0,F) doesn't exist
    conj:=conj;
  fi;
  return conj;
  
end;

CorrectForm@:=function(form,d,q,type)
#  -> ,GrpMatElt  form should be a classical form of type type fixed by a
#  subgroup G of GL ( d , q ) . Return a matrix mat such that G ^ mat fixes
#  our preferred standard form .
local Restore;
  Restore:=ValueOption("Restore");
  if Restore=fail then
    Restore:=false;
  fi;
  return CorrectForm@(MatrixByEntries(form),d,q,type:Restore:=Restore);
  
end;

TransformForm@:=function(form,type)
#  -> ,GrpMatElt  form should be a classical form of type type fixed by a
#  subgroup G of GL ( d , q ) . Return a matrix mat such that G ^ mat lies in
#  the classical group returned by the Magma function GU , Sp , GO ( Plus /
#  Minus ) .
local Restore,UT,cform,d,f,ffac,field,g,g2,i,j,mform,q,rq,rtype,nobrk;
  field:=ValueOption("field");
  if field=fail then
    field:=0;
  fi;
  Restore:=ValueOption("Restore");
  if Restore=fail then
    Restore:=false;
  fi;
  #   16/10/09 Put in Markus Kirschmer's code for sympectic case over
  #  * infinite field.
  
  #   form is assumed to be of type "type" and fixed by  group G <= GL(d,q) .
  #  * where field = GF(q), which defaults to BaseRing(form).
  #  * For the orthogonal types, form should be as returned by
  #  * SymmetricBilinearForm, except when q is even, when it should
  #  * be as returned by QuadraticForm.
  #  * return g in GL(d,q) such that G^g fixes the Magma form.
  #  * i.e. G^g <= Sp(d,q), GU(d,sqrt(q)) or GO(Plus/Minus)(d,q).
  #  *
  #  * type can be "symplectic", "unitary", "orth", "orthogonal",
  #  * "orthogonalcircle", "orth+", "orthogonalplus", "oplus",
  #  *  "orth-", "ominus", "orthogonalminus".
  
  if not IsFinite(DefaultFieldOfMatrix(form)) and type="symplectic" then
    return symplectic_std@(form);
  fi;
  UT:=function(mat)
  local K,i,j,n,nmat;
    n:=Length(mat);
    Assert(1,n=Length(mat[1]));
    K:=DefaultFieldOfMatrix(mat);
    nmat:=List(mat,ShallowCopy);
    for i in [2..n] do
      for j in [1..i-1] do
        nmat[j][i]:=nmat[j][i]+nmat[i][j];
        nmat[i][j]:=Zero(K);
      od;
    od;
    return nmat;
    
  end;

  d:=Length(form);
  if field=0 then
    field:=DefaultFieldOfMatrix(form);
  else
    Assert(1,IsSubset(field,DefaultFieldOfMatrix(form)));
    #form:=form*FORCEOne(MatrixAlgebra(field,d));
  fi;
  q:=Size(field);
  if type in ["orth","orthogonal","orthogonalcircle"] then
    type:="orth";
  elif type in ["orth+","orthogonalplus","oplus"] then
    type:="orth+";
  elif type in ["orth-","orthogonalminus","ominus"] then
    type:="orth-";
  elif type<>"symplectic" and type<>"unitary" then
    Error("illegal form type");
  fi;
  if type="orth+" or type="orth-" then
    #  check that the specified type is correct
    if type="orth+" then
      rtype:="orthogonalplus";
    else 
      rtype:="orthogonalminus";
    fi;

    if (IsOddInt(q) and rtype<>SymmetricBilinearFormType@(form:field:=field)) 
       or (IsEvenInt(q) and rtype<>QuadraticFormType@(form:field:=field) )
       then
      Error("Orthogonal form type specified is incorrect");
    fi;
  fi;
  g:=CorrectForm@(form,d,q,type:Restore:=Restore);
  if type="symplectic" then
    Assert(1,g^-1*form*TransposedMat(g^-1)
     =MatrixByEntries(field,d,d,Concatenation(List([1..QuoInt(d,2)]
     ,i->[i,d+1-i,1]),List([QuoInt(d,2)+1..d],i->[i,d+1-i,-1]))));
    return g;
  elif type="unitary" then
    f:=Collected(Factors(q));
    if f[1][2] mod 2=1 then
      Error("Field size must be a square for unitary type");
    fi;
    rq:=f[1][1]^(QuoInt(f[1][2],2));
    #mform:=StandardHermitianForm(d,field); # seems to return an
    # antidiagonal matrix.
    mform:=Reversed(IdentityMatrix(d,field));
    g2:=CorrectForm@(mform,d,q,type:Restore:=Restore);
    g:=g*g2^-1;
    Assert(1,g^-1*form*TransposedMat(MatToQ@(g^-1,rq))=mform);
    return g;
  elif type="orth" then
    if d >= 3 then
      mform:=SymmetricBilinearForm@(d,field);
    else
      #mform:=SELECT((d=1) then MatrixByEntries(1,1,[1/2]) else MatrixByEntries(0,0,[]));
      if d=1 then
	mform:=[[1/2]];
      else
	mform:=[];
      fi;
    fi;
    mform:=SymmetricBilinearForm@(d,field);
    g2:=CorrectForm@(mform,d,q,type:Restore:=Restore);
    g:=g*g2^-1;
    #  in this case, it is possible that form is transposed to a non-square
    #  scalar multiple
    cform:=g^-1*form*TransposedMat(g^-1);
    nobrk:=true;
    i:=1;
    while i<=d and nobrk do
      j:=1;
      while j<=d and nobrk do
        if cform[i][j]<>0 then
          ffac:=cform[i][j]/mform[i][j];
          #break i;
	  nobrk:=false;
        fi;
	j:=j+1;
      od;
      i:=i+1;
    od;
    Assert(1,d=0 or g^-1*form*TransposedMat(g^-1)=ffac*mform);
    return g;
  elif type="orth+" then
    if d=2 and q <= 3 then
      if IsEvenInt(q) then
	mform:=MatrixByEntries(field,2,2,[0,1,0,0]);
      else
	mform:=MatrixByEntries(field,2,2,[0,1,1,0]);
      fi;
    else
      if IsEvenInt(q) then
        mform:=QuadraticFormPlus@(d,field);
      else
        mform:=SymmetricBilinearFormPlus@(d,field);
      fi;
    fi;
    g2:=CorrectForm@(mform,d,q,type:Restore:=Restore);
    g:=g*g2^-1;
    if IsEvenInt(q) then
      Assert(1,UT(g^-1*form*TransposedMat(g^-1))=mform);
    else
      Assert(1,g^-1*form*TransposedMat(g^-1)=mform);
    fi;
    return g;
  elif type="orth-" then
    if IsEvenInt(q) then
      mform:=QuadraticFormMinus@(d,field);
    else
      mform:=SymmetricBilinearFormMinus@(d,field);
    fi;
    g2:=CorrectForm@(mform,d,q,type:Restore:=Restore);
    g:=g*g2^-1;
    if IsEvenInt(q) then
      Assert(1,UT(g^-1*form*TransposedMat(g^-1))=mform);
    else
      Assert(1,g^-1*form*TransposedMat(g^-1)=mform);
    fi;
    return g;
  fi;
  
end;

# the following seems to be not needed in GAP.
#TransformForm@:=function(form,type)
##  -> ,GrpMatElt  A version of TransformForm using GrpMatElt as argument type
##  for form
#local Restore,field,form2;
#  field:=ValueOption("field");
#  if field=fail then
#    field:=0;
#  fi;
#  Restore:=ValueOption("Restore");
#  if Restore=fail then
#    Restore:=false;
#  fi;
#  form2:=List(form,ShallowCopy);
#  return TransformForm@(form2,type:field:=field,Restore:=Restore);
#end;

# changed from TransformForm to avoid introducting an operation
TransformFormGroup@:=function(G)
#  -> ,GrpMatElt  If the input group G fixes a classical form , then return a
#  matrix mat such that G ^ mat lies in the classical group returned by the
#  Magma function GU , Sp , GO ( Plus / Minus ) . Otherwise return false .
local Restore,Scalars,d,form,q,r,type;
  Scalars:=ValueOption("Scalars");
  if Scalars=fail then
    Scalars:=false;
  fi;
  Restore:=ValueOption("Restore");
  if Restore=fail then
    Restore:=false;
  fi;
  r:=ClassicalForms@(G:Scalars:=Scalars);
  type:=r.formType;
  if type="linear" then
    Info(InfoWarning,1,"No fixed form");
    return false;
  fi;
  d:=Degree(G);
  q:=Size(DefaultFieldOfMatrix(G));
  if IsEvenInt(q) and type in Set(["orthogonalplus","orthogonalminus"]) 
     then
    form:=r.quadraticForm;
  elif type="unitary" then
    form:=r.sesquilinearForm;
  else
    form:=r.bilinearForm;
  fi;
  return TransformForm@(form,type:Restore:=Restore);
  
end;

