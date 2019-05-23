#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.35, 12/15/15 by AH

#  Global Variables used: BaseRing, Correct2dimQuadForm, DiagonalJoin,
#  DiagonalMatrix, GL, GOMinus, Id, Matrix, PolynomialRing, QuadraticForm,
#  RenormaliseForm, Root, Roots, Submatrix, Swapmat, Transpose

#  Defines: Correct2dimQuadForm, CorrectQuadForm, RenormaliseForm, Swapmat

DeclareGlobalFunction("CorrectQuadForm@");

#  
#  * This the implemention of  the algorithm described in Derek's
#  * email, combined with my own algorithm for the final (2 \times 2)
#  * block.
#  * The algorithm reduces a quadratic form to the standard one, over
#  * GF(2^m) for some m.

#  ***************************************************************
#  
#  * This takes a quadratic form $F$ and a conjugating matrix $C$ and
#  * returns the form that a group preserving $F$ would preserve
#  * after conjugation by $C$.

RenormaliseForm@:=function(form,conj,n,q)
local F,i,j,newform;
  F:=DefaultFieldOfMatrix(form);
  Assert(1,Size(F)=q);
  form:=conj^-1*form*TransposedMat(conj^-1);
  newform:=List([1..n^2],i->Zero(F));
  for i in [1..n] do
    for j in [i..n] do
      if not i=j then
        newform[(i-1)*n+j]:=form[i][j]+form[j][i];
      else
        newform[(i-1)*n+j]:=form[i][j];
      fi;
    od;
  od;
  return MatrixByEntries(F,n,n,newform);
  
end;

#  ****************************************************************
#  this returns a matrix which swaps a[i][i] and a[j][j]
Swapmat@:=function(i,j,F,n)
local diag,swapmat;
  diag:=List([1..n],i->[i,i,1]);
  swapmat:=MatrixByEntries(F,n,n,Concatenation(diag,[[i,i,0],[j,j,0]
   ,[i,j,1],[j,i,1]]));
  return swapmat;
end;

#  ****************************************************************
Correct2dimQuadForm@:=function(form,n,q,type)
local A,B,C,D,F,X,Y,Z,_,a,b,c,form_4,goal,mat,p,poly,root,roots,roots2,
  sqrt,x, z;
  #  
  #  * The orthogonal groups of minus type in 2 dimensions have
  #  * a different form than the central 2 \times 2 block of the form
  #  * for the orthgonals in > 2 dimensions.
  
  F:=DefaultFieldOfMatrix(form);
  Assert(1,Size(F)=q);
  if n > 2 and type="orth-" then
    # =v= MULTIASSIGN =v=
    form_4:=QuadraticForm@(GOMinus(4,F));
    #_:=form_4.val1;
    form_4:=form_4.val2;
    # =^= MULTIASSIGN =^=
    goal:=[[form_4[2][2],form_4[2][3]],[0,form_4[3][3]]];
  elif n=2 and type="orth-" then
    # =v= MULTIASSIGN =v=
    goal:=QuadraticForm@(GOMinus(2,F));
    #_:=goal.val1;
    goal:=goal.val2;
    # =^= MULTIASSIGN =^=
  fi;
  a:=form[1][1];
  b:=form[1][2];
  c:=form[2][2];
  x:=X(F,1);
  if type="orth+" then
    if a=0 and c=0 then
      sqrt:=RootFFE(b,2);
      return DiagonalMat([sqrt,sqrt]);
    elif c=0 then
      #   so a is not zero, and neither is b.
      mat:=[[0,a*b^-2],[b*a^-1,1]]*One(F);
      return mat^-1;
    elif b=0 then
      #   so c is not zero, and neither is b.
      mat:=[[b^-1,0],[b^-1*c,1]]*One(F);
      return mat^-1;
    else
      #  roots exist since form is of plus type.
      roots:=RootsOfUPol(form[1][1]*x^2+form[1][2]*x+form[2][2]);
      z:=roots[1];
      mat:=[[z,1],[b^-1+z*a*b^-2,a*b^-2]]*One(F);
      return mat^-1;
    fi;
  fi;
  #  
  #  * The remaining code is for orth-. Sadly, I don't know exactly what
  #  * the form will be, so I've done it for a general form..
  
  #  we have matrix [a, b, 0, c] and are aiming for [X, Y, 0,
  #  Z]. We will get there by multiplying by [A, B, C, D]. We know
  #  that b and Y are nonzero, and that ax^2+bx+c is irreducible.
  X:=goal[1][1];
  Y:=goal[1][2];
  Z:=goal[2][2];
  #p:=PolynomialRing(F); x:=p.1; #already def
  for A in F do
    poly:=a*A^2+x*A*b+x^2*c-X;
    roots:=RootsOfUPol(poly);
    #  roots;
    for root in Set(roots) do
      B:=root;
      if not (A=0 or B=0) then
        roots2:=RootsOfUPol(x^2*B^-2*X+x*B^-1*Y+a*b^-2*B^-2*Y^2+Z);
        if Length(roots2) > 0 then
          #  it seems that this is always the case
          #  but I can't quite see why.
          D:=roots2[1];
          C:=B^-1*(Y*b^-1+A*D);
          mat:=[[A,B],[C,D]];
          return mat^-1;
        fi;
      elif not B=0 then
        #  so A = 0.
        C:=Y*B^-1*b^-1;
        roots2:=RootsOfUPol(x^2*c+x*C*b+C^2*a+Z);
        if Length(roots2) > 0 then
          #  again, this is always the case.
          mat:=[[A,B],[C,roots2[1]]];
          return mat^-1;
        fi;
      elif not A=0 then
        #  so B eq 0.
        D:=Y*b^-1*A^-1;
        roots2:=RootsOfUPol(x^2*a+x*D*b+D^2*c+Z);
        if Length(roots2) > 0 then
          #  and so is this.
          mat:=[[A,B],[roots2[1][1],D]];
          return mat^-1;
        fi;
      fi;
    od;
  od;
  #  "error: form =", form, "goal =", goal;
  return false;
  
end;
;
#  *******************************************************************
#  this is the main function to standardise a quadratic form.
InstallGlobalFunction(CorrectQuadForm@,
function(form,n,q,type)
local F,centre,conj,diag,f,t,h,mat,ri,rj,s,u;
  F:=DefaultFieldOfMatrix(form);
  Assert(1,Size(F)=q);
  diag:=List([1..n],i->[i,i,1]);
  s:=1;
  f:=n;
  conj:=IdentityMat(n,F);
  while (f-s) > 1 do
    #  if there exists a diagonal entry which is zero
    t:=First([s..f],i->form[i][i]=0);
    if t<>fail then
      #   move it to row s
      mat:=Swapmat@(t,s,F,n);
      form:=RenormaliseForm@(form,mat,n,q);
      conj:=conj*mat;
      #  if there is an entry in row start which is nonzero
      t:=First([s..f-1],i->not IsZero(form[s][i]));
      if t<>fail then
        mat:=Swapmat@(t,f,F,n);
        form:=RenormaliseForm@(form,mat,n,q);
        conj:=conj*mat;
      fi;
      #  new x_f -> sum _{j=s,f} form_{s j} old x_j
      mat:=MatrixByEntries(F,n,n,Concatenation(diag,
        List([0..(f-s)],j->[s+j,f,form[s][s+j]])));
      form:=RenormaliseForm@(form,mat,n,q);
      conj:=conj*mat;
      #   new x_s = sum _{i=s,f} form_{i f} old x_i
      mat:=MatrixByEntries(F,n,n,Concatenation(diag,
        List([0..(f-s)],j->[s+j,s,form[s+j][f]])));
      form:=RenormaliseForm@(form,mat,n,q);
      conj:=conj*mat;
      s:=s+1;
      f:=f-1;
    elif ForAny([s..f],i->ForAny([i+1..f],j->form[i][j]=0)) then
      t:=First([s..f],i->ForAny([i+1..f],j->form[i][j]=0));
      u:=First([t+1..f],j->form[t][j]=0);
      ri:=RootFFE(form[t][t],2);
      rj:=RootFFE(form[u][u],2);
      mat:=MatrixByEntries(F,n,n,Concatenation(diag,[[t,t,ri],[u,t,rj]]));
      form:=RenormaliseForm@(form,mat,n,q);
      conj:=conj*mat;
    else
      mat:=MatrixByEntries(F,n,n,Concatenation(diag,[[s+1,s+1,form[s][s+1]],[s+2,s+1,form[s][s+2]]]));
      form:=RenormaliseForm@(form,mat,n,q);
      conj:=conj*mat;
    fi;
  od;
  #  the final 2 \times 2 block in the centre.
  h:=QuoInt(n,2);
  h:=[h,h+1];
  centre:=form{h}{h}; #Submatrix(form,h,h,2,2);
  mat:=Correct2dimQuadForm@(centre,n,q,type);
  if mat=false then
    Error("ERROR: 2-dimensional quadratic form seems to be wrong");
  fi;
  if n > 2 then
    mat:=DirectSumMat(IdentityMat(h-1,F),mat,IdentityMat(h-1,F));
  fi;
  form:=RenormaliseForm@(form,mat,n,q);
  return rec(val1:=form,
    val2:=conj*mat);
  
end);

#  
#  * Some tests.
#  
#  pairs:= [<2, 8>, <2, 16>, <2, 32>, <2, 64>, <2, 128>, <2,
#  256>,
#  <4, 2>, <4, 4>, <4, 8>, <4, 16>,
#  <6, 2>, <6, 4>, <6, 8>, <6, 16>,
#  <8, 2>, <8, 4>, <8, 8>,
#  <10, 2>, <10, 4>,
#  <12, 2>,
#  <14, 2>];
#  
#  for p in pairs do
#  p;
#  for y in [1..100] do
#  z:= Random(GL(p[1], p[2]));
#  qf:= QuadraticForm(GOMinus(p[1], p[2])^z);
#  a, b:= CorrectQuadForm(qf, p[1], p[2], "orth-");
#  QuadraticForm(GOMinus(p[1], p[2])^(z*b)) eq
#  QuadraticForm(GOMinus(p[1], p[2]));
#  qf:= QuadraticForm(GOPlus(p[1], p[2])^z);
#  a, b:= CorrectQuadForm(qf, p[1], p[2], "orth+");
#  QuadraticForm(GOPlus(p[1], p[2])^(z*b)) eq
#  QuadraticForm(GOPlus(p[1], p[2]));
#  end for;
#  end for;
#  
#  


