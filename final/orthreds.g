#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.39, 1/28/16 by AH

#  Global Variables used: Append, CorrectForm, Determinant, DiagonalJoin,
#  DiagonalMatrix, Eltseq, GF, GL, GO, GOMinus, GOPlus, Id, IdentityMat,
#  IsEven, IsOdd, IsSquare, IsotropicStabOmega, KroneckerProduct, Matrix,
#  MatrixAlgebra, NSPointStabOmega, Ngens, NonDegenStabOmega, Om, Omega,
#  OmegaMinus, OmegaPlus, OrthogonalForm, PolynomialRing, PrimitiveElement,
#  QF, QuadraticForm, Roots, ScalarMatrix, Solution, Sp,
#  SymmetricBilinearForm, TransformForm, Transpose, VectorSpace

#  Defines: IsotropicStabOmega, NSPointStabOmega, NonDegenStabOmega,
#  OrthogonalReducibles

DeclareGlobalFunction("IsotropicStabOmega@");

DeclareGlobalFunction("NSPointStabOmega@");

DeclareGlobalFunction("NonDegenStabOmega@");

InstallGlobalFunction(IsotropicStabOmega@,
function(d,q,k,sign)
local 
   Om,ce,diag,elt,form,gen,general,gens,go,hd,i,isf,magform,mr,normaliser,
   ourform,special,t,type,u,v,x,y,z,glkq;
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
  #  
  #  * Here we stabilise <e_1, \ldots, e_k>, k \leq d/2;
  
  Assert(1,d > 2);
  Assert(1,(IsOddInt(d) and sign=0) or (IsEvenInt(d) and sign in Set([-1,1])
   ));
  Assert(1,IsEvenInt(d) or IsOddInt(q));
  Assert(1,2*k <= d);
  Assert(1,sign<>-1 or 2*k<>d);
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  if IsOddInt(d) then
    Om:=Omega;
  elif sign=1 then
    Om:=OmegaPlus;
  else
    Om:=OmegaMinus;
  fi;
  if d-2*k > 1 then
    #  We need an element go in SO(d-2*k,q) - Omega.
    go:=SOMinusOmega@(d-2*k,q,sign);
  fi;
  if IsOddInt(d) then
    #  Magma's form is not scalar antidiagonal for some reason!
    mr:=QuoInt((d+1),2);
    ourform:=MatrixByEntries(GF(q),d,d,List([1..d],i->[i,d-i+1,1]));
    # =v= MULTIASSIGN =v=
    magform:=OrthogonalForm@(Om(d,q));
    isf:=magform.val1;
    type:=magform.val2;
    magform:=magform.val3;
    # =^= MULTIASSIGN =^=
    ce:=magform[1][d]/magform[mr][mr];
  fi;
  if sign=-1 then
    hd:=QuoInt(d,2);
    # =v= MULTIASSIGN =v=
    magform:=QuadraticForm@(Om(d,q));
    isf:=magform.val1;
    magform:=magform.val2;
    # =^= MULTIASSIGN =^=
    magform:=magform*magform[1][d]^-1;
    t:=magform[hd][hd];
    u:=magform[hd][hd+1];
    v:=magform[hd+1][hd+1];
  fi;
  z:=PrimitiveElement(GF(q));
  form:=MatrixByEntries(GF(q),k,k,List([1..k],i->[i,k-i+1,1])) #CAST GL(k,q)
   
    ;
  diag:=List([1..d],i->[i,i,1]);
  gens:=[];
  #  GL(k, q) on <e_1..e_k>, balanced on <f_k..f_1>.
  gens:=[];
  glkq:=GL(k,q);
  for i in [1..Length(GeneratorsOfGroup(glkq))] do
    gen:=glkq.(i);
    elt:=DirectSumMat([gen,IdentityMat(d-2*k,GF(q)),
	  form*TransposedMat(gen^-1)*form]);
    if IsEvenInt(q) or (IsOddInt(q) and
      # IsSquare test
      IsEvenInt(LogFFE(DeterminantMat(gen),Z(q))) or 
       InOmega@(elt,d,q,sign) or special) then
      Add(gens,elt);
      continue;
    fi;
    if d-2*k > 1 then
      elt:=DirectSumMat([gen,go,form*TransposedMat(gen^-1)*form]);
      Add(gens,elt);
    elif elt^2<>elt^0 then
      Add(gens,elt^2);
    elif i<>Length(GeneratorsOfGroup(glkq)) then
      #  only for case q=3, k>1
      gen:=(glkq.(i+1))^gen;
      elt:=DirectSumMat([gen,IdentityMat(d-2*k,GF(q)),
	      form*TransposedMat(gen^-1)*form]);
      Add(gens,elt);
    fi;
  od;
  if d-2*k > 1 then
    #  the orthogonal group acting on a (d-2k) space.
    gens:=Concatenation(gens,
	List(GeneratorsOfGroup(Om(d-2*k,q)),
	i->DirectSumMat([IdentityMat(k,GF(q)),i,
     IdentityMat(k,GF(q))])));
    if special then
      Add(gens,DirectSumMat([IdentityMat(k,GF(q))
       ,SOMinusOmega@(d-2*k,q,sign),IdentityMat(k,GF(q))]));
    fi;
    if general and IsOddInt(q) then
      Add(gens,DirectSumMat([IdentityMat(k,GF(q))
       ,GOMinusSO@(d-2*k,q,sign),IdentityMat(k,GF(q))]));
    fi;
  fi;
  if d-2*k=1 and general and IsOddInt(q) then
    Add(gens,DirectSumMat([IdentityMat(k,GF(q)),MatrixByEntries(GF(q)
     ,1,1,[-1]),IdentityMat(k,GF(q))]));
  fi;
  if k > 1 then
    Add(gens,MatrixByEntries(GF(q),d,d,Concatenation([[d-1,1,1],[d,2,-1]]
     ,diag)));
  fi;
  if (d > 2*k+2) or (d=2*k+2 and sign=1) then
    Add(gens,MatrixByEntries(GF(q),d,d,Concatenation([[k+1,1,1],[d,d-k,-1]]
     ,diag)));
    if d=2*k+2 and sign=1 then
      Add(gens,MatrixByEntries(GF(q),d,d,Concatenation([[k+2,1,1]
       ,[d,d-k-1,-1]],diag)));
    fi;
  elif d=2*k+1 then
    Add(gens,MatrixByEntries(GF(q),d,d,Concatenation([[k+1,1,1],[d,d-k,-ce]
     ,[d,1,-ce/2]],diag)));
  elif d=2*k+2 and sign=-1 then
    y:=2*v/(u^2-4*v*t);
    x:=-u/(u^2-4*v*t);
    Add(gens,MatrixByEntries(GF(q),d,d,Concatenation([[k+1,1,1],[d,k+1,y]
     ,[d,k+2,x],[d,1,-y^2*t-y*u*x-x^2*v]],diag)));
  fi;
  if normaliser then
    if IsOddInt(q) and IsEvenInt(d) and d<>2*k then
      Add(gens,DirectSumMat([z*IdentityMat(k,One(z)),NormGOMinusGO@(d-2*k,q,sign)
       ,IdentityMat(k,GF(q))]));
    elif IsOddInt(q) and d=2*k then
      Add(gens,NormGOMinusGO@(d,q,sign));
    elif q > 3 then
      Add(gens,z*IdentityMat(d,One(z)));
    fi;
  fi;
  return Group(gens);
  #  sign=1, k = d/2, c=2, so (q even), go-so ( q odd); o.w. c=1.
end);

InstallGlobalFunction(NSPointStabOmega@,
function(d,q,sign)
local 
   Omdq,P,QF,U,V,W,bf,c,cmat,eqns,gen,gens,i,ims,isf,mat,newgen,normaliser,
   qf,rts,sp,special,u,v,w,x,z;
  special:=ValueOption("special");
  if special=fail then
    special:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,IsEvenInt(d) and IsEvenInt(q) and d > 2 and sign in Set([-1,1]))
   ;
  QF:=function(v,qf)
	return (MatrixByEntries(v)*qf*TransposedMat(MatrixByEntries(v)))[1][1];
      end;
  if normaliser then
    special:=true;
  fi;
  if sign=1 then
    Omdq:=OmegaPlus(d,q);
  else 
    Omdq:=OmegaMinus(d,q);
  fi;
  # =v= MULTIASSIGN =v=
  qf:=QuadraticForm@(Omdq);
  isf:=qf.val1;
  qf:=qf.val2;
  # =^= MULTIASSIGN =^=
  # =v= MULTIASSIGN =v=
  bf:=SymmetricBilinearForm@(Omdq);
  isf:=bf.val1;
  bf:=bf.val2;
  # =^= MULTIASSIGN =^=
  #  normalize qf and bf
  qf:=qf[1][d]^-1*qf;
  bf:=bf[1][d]^-1*bf;
  V:=IdentityMat(d,GF(q));
  U:=IdentityMat(d-2,GF(q));
  W:=IdentityMat(d-1,GF(q));
  v:=Concatenation([1],List([1..d-2],i->0),[1]);
  Assert(1,QF(v,qf)=1);
  cmat:=MatrixByEntries(GF(q),d,d,Concatenation([[1,d,1],[d,1,1]]
   ,List([2..d-1],i->[i,i,1])));

  #  Element of group to be constructed that is outside of Omega
  gens:=[];
  sp:=Sp(d-2,q);
  #   Now we calculate embedding of sp into G.
  #  Unfortunately bf is not always just antidiagonal 1, so need to transform
  #  generators
  mat:=DiagonalMat(GF(q),Concatenation(List([2..QuoInt(d,2)],i->bf[i][d+1-i]
   ^-1),List([2..QuoInt(d,2)],i->1)));
    ;
  for gen in List(GeneratorsOfGroup(sp),i->i^mat) do
    ims:=[];
    for i in [1..d-2] do
      w:=(Concatenation([0],U[i]*gen,[0]));
        ;
      c:=(QF(V[i+1],qf)+QF(w,qf))^(QuoInt(q,2));
      #  ^(q div 2) = sqrt.
      w:=w+c*v;
      #  image of V[i+1] under generator
      Assert(1,QF(w,qf)=QF(V[i+1],qf));
      Add(ims,w);
    od;
    eqns:=TransposedMat(MatrixByEntries(Concatenation(ims,[v])));
    z:=SolutionMat(bf*eqns,W[d-1]);
    x:=X(GF(q),1);
    rts:=RootsOfUPol(GF(q),x^2+x+QF(z,qf));
    if rts=[] then
      Error("Cannot solve quadratic");
    fi;
    z:=z+rts[1][1]*v;
    newgen:=MatrixByEntries(Concatenation([z],ims,[z+v]));
    if not special and not InOmega@(newgen,d,q,sign) then
      newgen:=newgen*cmat;
    fi;
    Add(gens,newgen);
  od;
  if special then
    Add(gens,cmat);
  fi;
  if normaliser and q > 2 then
    Add(gens,PrimitiveElement(GF(q))*IdentityMat(d,GF(q)));
  fi;
  return Group(gens);
  #  c=1.
end);

InstallGlobalFunction(NonDegenStabOmega@,
function(d,q,sign,k,sign1)
local 
   Omdq,cmat1,cmat2,cmat3,cmat4,cmat5,cmat5s,ex,form,form1,form2,formt,gen,
   general,gens,ggl1,ggl2,gnl1,gnl2,gp1,gp2,gsl1,gsl2,ipelt,ipn,isf,newgen,
   normaliser,sign2,special,t,tmat,type,w;
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
  ipn:=ValueOption("ipn");
  if ipn=fail then
    ipn:=false;
  fi;
  #   Construct stabilizer of nondenerate space of dimension k,
  #  * of type Omega^sign1(k,q) + Omega^sign2(d-k,q) in Omega^sign(d,q),
  #  * where sign2 is to be calculated.
  
  Assert(1,d > 2);
  Assert(1,(IsEvenInt(d) and IsEvenInt(k)) or IsOddInt(q));
  Assert(1,(IsOddInt(d) and sign=0) or (IsEvenInt(d) and sign in [-1,1]));
  Assert(1,(IsOddInt(k) and sign1=0) or (IsEvenInt(k) and sign1 in [-1,1]))
   ;
  Assert(1,k < d);
  Assert(1,IsEvenInt(d) or sign1<>0);
  #  o.w. sign2 would be ambiguous
  Assert(1,sign1<>-1 or sign<>-1);
  #  instead use sign2 = 1, k = d-k
  Assert(1,k > 1);
  #  instead use k = d-1
  if ipn then
    normaliser:=true;
  fi;
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  #  ipn is used only to compute imprimitive normaliser when k=d/2 is odd,
  #  and components are non-isometric.
  # rewritten select statement
  if sign=0 then
    type:="orth";
  else
    # rewritten select statement
    if sign=1 then
      type:="orth+";
    else
      type:="orth-";
    fi;
  fi;
  # rewritten select statement
  if sign=1 then
    sign2:=sign1;
  else
    # rewritten select statement
    if sign=-1 and sign1=1 then
      sign2:=-1;
    else
      # rewritten select statement
      if sign=-1 and sign1=0 then
        sign2:=0;
      else
        sign2:=0;
      fi;
    fi;
  fi;
  #  sign eq 0
  #   legal values for (sign1,sign2,sign) are
  #  * (+,+,+), (-,-,+), (+,-,-), (0,0,+) (k>1), (0,0,-) (k>1), (+,0,0),
  #  (-,0,0).
  
  # rewritten select statement
  if sign1=0 then
    gp1:=GO(k,q);
  else
    # rewritten select statement
    if sign1=1 then
      gp1:=GOPlus(k,q);
    else
      gp1:=GOMinus(k,q);
    fi;
  fi;
  # rewritten select statement
  if d-k=1 then
    gp2:=SubgroupNC(GL(1,q),[[[-1*Z(q)^0]]]);
  else
    # rewritten select statement
    if sign2=0 then
      gp2:=GO(d-k,q);
    else
      # rewritten select statement
      if sign2=1 then
        gp2:=GOPlus(d-k,q);
      else
        gp2:=GOMinus(d-k,q);
      fi;
    fi;
  fi;
  #  Note that we use GO  (rather than SO, Omega) to calculate the forms
  #  to ensure absolute irreducibility of gp1, gp2 in dimension 2.
  if IsEvenInt(q) then
    if q=2 and k=2 and sign1=1 then
      form1:=MatrixByEntries(GF(q),2,2,[0,1,0,0]);
    else
      # =v= MULTIASSIGN =v=
      form1:=QuadraticForm@(gp1);
      isf:=form1.val1;
      form1:=form1.val2;
      # =^= MULTIASSIGN =^=
    fi;
    #  note d-k=1 cannot occur for even q.
    if q=2 and d-k=2 and sign2=1 then
      form2:=MatrixByEntries(GF(q),2,2,[0,1,0,0]);
    else
      # =v= MULTIASSIGN =v=
      form2:=QuadraticForm@(gp2);
      isf:=form2.val1;
      form2:=form2.val2;
      # =^= MULTIASSIGN =^=
    fi;
  else
    if q=3 and k=2 and sign1=1 then
      form1:=MatrixByEntries(GF(q),2,2,[0,1,1,0]);
    else
      # =v= MULTIASSIGN =v=
      form1:=SymmetricBilinearForm@(gp1);
      isf:=form1.val1;
      form1:=form1.val2;
      # =^= MULTIASSIGN =^=
    fi;
    if d-k > 1 then
      if q=3 and d-k=2 and sign2=1 then
        form2:=MatrixByEntries(GF(q),2,2,[0,1,1,0]);
      else
        # =v= MULTIASSIGN =v=
        form2:=SymmetricBilinearForm@(gp2);
        isf:=form2.val1;
        form2:=form2.val2;
        # =^= MULTIASSIGN =^=
      fi;
    else
      form2:=MatrixByEntries(GF(q),1,1,[1]);
    fi;
  fi;
  #  We need elements of ggl1/2, gsl1/2 in sl-omega (d-k>1) and gl-sl(p odd)
  gsl1:=SOMinusOmega@(k,q,sign1);
  if d-k > 1 then
    gsl2:=SOMinusOmega@(d-k,q,sign2);
  fi;
  if IsOddInt(q) then
    ggl1:=GOMinusSO@(k,q,sign1);
    ggl2:=GOMinusSO@(d-k,q,sign2);
  fi;
  #  now redefine gp1, gp2 to include generators of Omega + gsl, ggl
  # rewritten select statement
  if sign1=0 then
    gp1:=Omega(k,q);
  else
    # rewritten select statement
    if sign1=1 then
      gp1:=OmegaPlus(k,q);
    else
      gp1:=OmegaMinus(k,q);
    fi;
  fi;
  gp1:=SubgroupContaining(GL(k,q),gp1,gsl1);
  if IsOddInt(q) then
    # rewritten select statement
    if d-k > 1 then
      gp1:=SubgroupContaining(GL(k,q),gp1,ggl1);
    else
      gp1:=SubgroupContaining(GL(k,q),gp1,ggl1,ggl1*gsl1);
    fi;
    #  this difference is because we have fewer adjusting elements in gp2 when
    #  d-k=1.
  fi;
  if d-k > 1 then
    # rewritten select statement
    if sign2=0 then
      gp2:=Omega(d-k,q);
    else
      # rewritten select statement
      if sign2=1 then
        gp2:=OmegaPlus(d-k,q);
      else
        gp2:=OmegaMinus(d-k,q);
      fi;
    fi;
    gp2:=SubgroupContaining(GL(d-k,q),gp2, gsl2);
    #  we don't need to put ggl2 into gp2 - ggl2 is needed to "adjust"
    #  ggl1 only.
  fi;
  #  In case (o,o,+-) we need to make sure the forms are of correct type
  if sign1=0 then
    #  Plus-type form is identity except when d = 2 mod 4, q = 3 mod 4.
    w:=PrimitiveElement(GF(q));
    ex:=d mod 4=2 and q mod 4=3;
    # rewritten select statement
    if (sign=1 and not ex) or (sign=-1 and ex) then
      formt:=IdentityMat(k,GF(q));
    else
      formt:=DiagonalMat(Concatenation(List([1..k-1],i->Z(q)^0),[w]));
    fi;
    #  IdentityMatrix(GF(q),k)
    cmat1:=CorrectForm@(form1,k,q,"orth");
    cmat2:=CorrectForm@(formt,k,q,"orth");
    gp1:=gp1^(cmat1*cmat2^-1);
    form1:=formt;
    if d-k > 1 then
      #  form2 should always be of + type
      formt:=IdentityMat(d-k,GF(q));
      #  IdentityMatrix(GF(q),d-k);
      cmat3:=CorrectForm@(form2,d-k,q,"orth");
      cmat4:=CorrectForm@(formt,d-k,q,"orth");
      gp2:=gp2^(cmat3*cmat4^-1);
      form2:=formt;
      #  also transform elements gsl2, ggl2 used to adjust elements of gp1.
      gsl2:=gsl2^(cmat3*cmat4^-1);
      if IsOddInt(q) then
        ggl2:=ggl2^(cmat3*cmat4^-1);
      fi;
    fi;
    if ipn and k=QuoInt(d,2) and form1[k][k]=w then
      #  find element in normaliser interchanging the two spaces
      ipelt:=KroneckerProduct(MatrixByEntries(GF(q),2,2,[0,1,1,0]),One(GL(k,q)));
      cmat5:=cmat2*cmat4^-1;
      #  cmat5 * form1 * cmat5^T = t form2 - find t.
      t:=(cmat5*form1*TransposedMat(cmat5))[1][1]/form2[1][1];
      cmat5s:=t^-1*IdentityMat(k,GF(q))*cmat5;
      ipelt:=(DirectSumMat(cmat5s,cmat5^-1)*ipelt);
        ;
    fi;
  fi;
  #  We will need to transform our generators to fix Magma's quadratic form.
  tmat:=TransformForm@(DirectSumMat(form1,form2),type);
  #  Now we can start constructing the generators
  gens:=[];
  for gen in GeneratorsOfGroup(gp1) do
    if DeterminantMat(gen)<>1 then
      if general then
        newgen:=DirectSumMat(gen,One(gp2))^tmat;
        Add(gens,newgen);
      fi;
      #  use ggl2 to adjust it and make determinant 1
      newgen:=DirectSumMat(gen,ggl2)^tmat;
      if special or InOmega@(newgen,d,q,sign) then
        Add(gens,newgen);
      elif d-k > 1 then
        #  adjust again using gsl2.
        newgen:=DirectSumMat(gen,ggl2*gsl2)^tmat;
        Assert(1,InOmega@(newgen,d,q,sign));
        Add(gens,newgen);
      fi;
    else
      newgen:=DirectSumMat(gen,IdentityMat(d-k,GF(q)))^tmat;
      if special or InOmega@(newgen,d,q,sign) then
        Add(gens,newgen);
      elif d-k > 1 then
        #  adjust using gsl2.
        newgen:=DirectSumMat(gen,gsl2)^tmat;
        Assert(1,InOmega@(newgen,d,q,sign));
        Add(gens,newgen);
      fi;
    fi;
  od;
  if d-k > 1 then
    for gen in GeneratorsOfGroup(gp2) do
      newgen:=DirectSumMat(IdentityMat(k,GF(q)),gen)^tmat;
      if special or InOmega@(newgen,d,q,sign) then
        Add(gens,newgen);
      fi;
    od;
  fi;
  if normaliser then
    if IsOddInt(q) and IsEvenInt(d) and IsEvenInt(k) then
      gnl1:=NormGOMinusGO@(k,q,sign1);
      gnl2:=NormGOMinusGO@(d-k,q,sign2);
      newgen:=(DirectSumMat(gnl1,gnl2))^tmat;
      Add(gens,newgen);
    elif q > 3 then
      Add(gens,PrimitiveElement(GF(q))*IdentityMat(d,GF(q)));
    fi;
  fi;
  if ipn and k=QuoInt(d,2) and form1[k][k]=w then
    Add(gens,ipelt^tmat);
  fi;
  return Group(gens);
  #   q, k, d-k odd, c=2, normgo-go, o.w. c=1.
end);

OrthogonalReducibles@:=function(d,q,sign)
local half,i,list;
  Assert(1,d > 2);
  Assert(1,(IsOddInt(d) and sign=0) or (IsEvenInt(d) and sign in Set([-1,1])));
  list:=[];
  half:=QuoInt(d,2);
  for i in [1..half] do
    if sign<>-1 or i<>half then
      Add(list,IsotropicStabOmega@(d,q,i,sign));
    fi;
  od;
  if IsOddInt(d) then
    for i in [2,2+2..d-1] do
      Add(list,NonDegenStabOmega@(d,q,sign,i,1));
      Add(list,NonDegenStabOmega@(d,q,sign,i,-1));
    od;
  else
    #  d even
    for i in [1..half] do
      if IsEvenInt(i) then
        if sign=1 then
          Add(list,NonDegenStabOmega@(d,q,sign,i,1));
          Add(list,NonDegenStabOmega@(d,q,sign,i,-1));
        else
          #  sign = -1
          Add(list,NonDegenStabOmega@(d,q,sign,i,1));
          if i<>half then
            Add(list,NonDegenStabOmega@(d,q,sign,d-i,1));
          fi;
        fi;
      else
        #  i odd
        if IsOddInt(q) then
          Add(list,NonDegenStabOmega@(d,q,sign,d-i,0));
        fi;
      fi;
    od;
  fi;
  if IsEvenInt(d) and IsEvenInt(q) then
    Add(list,NSPointStabOmega@(d,q,sign));
  fi;
  return list;
end;

