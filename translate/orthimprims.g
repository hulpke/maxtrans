#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Alt, Append, DJ, Determinant, DiagonalJoin, Divisors,
#  Exclude, GF, GL, GO, GOMinus, GOPlus, IdentityMatrix, IsEven, IsOdd,
#  KroneckerProduct, Matrix, Ngens, Omega, OmegaMinus, OmegaPlus, OrthImprim,
#  OrthStabOfHalfND, OrthStabOfHalfTS, PermutationMatrix, PrimitiveElement,
#  QuadraticForm, SL, ScalarMatrix, Sym, SymmetricBilinearForm, TransformForm,
#  Transpose

#  Defines: OrthImprim, OrthStabOfHalfND, OrthStabOfHalfTS, OrthogonalImprims

DeclareGlobalFunction("OrthImprim@");

DeclareGlobalFunction("OrthStabOfHalfND@");

DeclareGlobalFunction("OrthStabOfHalfTS@");

InstallGlobalFunction(OrthImprim@,
function(d,q,sign,k,sign1)
#  /out: Construct imprimitive subgroup
#  * of type Omega^sign1(k,q) wreath d/k in Omega^sign(d,q),

local 
   Omdq,cmat1,cmat2,ex,form,form1,formt,gen,general,gens,ggl1,gnl1,gp1,gsl1,id,
   isf,newgen,normaliser,sg,special,t,tmat,type,w;
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
  Assert(1,d > 2);
  Assert(1,k < d and d mod k=0);
  Assert(1,(IsEvenInt(d) and IsEvenInt(k)) or IsOddInt(q));
  Assert(1,(IsOddInt(d) and sign=0) or (IsEvenInt(d) and sign in Set([-1,1])));
  Assert(1,(IsOddInt(k) and sign1=0) or (IsEvenInt(k) and sign1 in Set([-1,1])))
   ;
  t:=QuoInt(d,k);
  #  Check parameters are compatible.
  if sign in Set([-1,1]) then
    ex:=d mod 4=2 and q mod 4=3;
    #  i.e. D non-square
    if (sign1 in Set([-1,1]) and sign1^t<>sign) or (sign1=0 and ex and sign=1) 
       or (sign1=0 and not ex and sign=-1) then
      Error("Incompatible parameters");
    fi;
  fi;
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
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
  if k=1 then
    gp1:=SubStructure(GL(k,q),[-1]);
  else
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
  fi;
  #  Note that we use GO  (rather than SO, Omega) to calculate the forms
  #  to ensure absolute irreducibility of gp1, gp2 in dimension 2.
  if IsEvenInt(q) then
    if q=2 and k=2 and sign1=1 then
      form1:=MatrixByEntries(GF(q),2,2,[0,1,0,0]);
    else
      # =v= MULTIASSIGN =v=
      form1:=QuadraticForm(gp1);
      isf:=form1.val1;
      form1:=form1.val2;
      # =^= MULTIASSIGN =^=
    fi;
  else
    if q=3 and k=2 and sign1=1 then
      form1:=MatrixByEntries(GF(q),2,2,[0,1,1,0]);
    else
      # =v= MULTIASSIGN =v=
      form1:=SymmetricBilinearForm(gp1);
      isf:=form1.val1;
      form1:=form1.val2;
      # =^= MULTIASSIGN =^=
    fi;
  fi;
  #  We need elements of in sl-omega (k>1) and gl-sl(p odd)
  if k > 1 then
    gsl1:=SOMinusOmega@(k,q,sign1);
  fi;
  if IsOddInt(q) then
    ggl1:=GOMinusSO@(k,q,sign1);
  fi;
  #  now redefine gp1 to include generators of Omega + gsl, ggl
  if k > 1 then
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
    gp1:=SubStructure(GL(k,q),gp1,#TODO CLOSURE
      gsl1);
    if IsOddInt(q) then
      gp1:=SubStructure(GL(k,q),gp1,#TODO CLOSURE
        ggl1);
    fi;
  fi;
  #  We will need to transform our generators to fix Magma's quadratic form.
  tmat:=TransformForm(DirectSumMat(List([1..t],i->form1)),type);
  id:=IdentityMatrix(GF(q),k) #CAST GL(k,q)
    ;
  #  Now we can start constructing the generators
  gens:=[];
  for gen in List([1..Ngens(gp1)],i->gp1.i) do
    if DeterminantMat(gen)<>1 then
      #  use ggl1 to adjust it and make determinant 1
      if general then
        newgen:=DirectSumMat(Concatenation([gen],List([1..t-1],i->id))) #CAST 
         GL(d,q)
          ^tmat;
        Add(gens,newgen);
      fi;
      newgen:=DirectSumMat(Concatenation([gen,ggl1],List([1..t-2],i->id))) 
       #CAST GL(d,q)
        ^tmat;
      if special or InOmega@(newgen,d,q,sign) then
        Add(gens,newgen);
      elif k > 1 then
        #  adjust again using gsl1.
        newgen:=DirectSumMat(Concatenation([gen,ggl1*gsl1],List([1..t-2],i->id))
         ) #CAST GL(d,q)
          ^tmat;
        Assert(1,InOmega@(newgen,d,q,sign));
        Add(gens,newgen);
      fi;
    else
      newgen:=DirectSumMat(Concatenation([gen],List([1..t-1],i->id))) #CAST 
       GL(d,q)
        ^tmat;
      if special or InOmega@(newgen,d,q,sign) then
        Add(gens,newgen);
      elif k > 1 then
        #  adjust using gsl1.
        newgen:=DirectSumMat(Concatenation([gen,gsl1],List([1..t-2],i->id))) 
         #CAST GL(d,q)
          ^tmat;
        Assert(1,InOmega@(newgen,d,q,sign));
        Add(gens,newgen);
      fi;
    fi;
  od;
  #  Now generators of S_n
  for gen in List([1..Ngens(AlternatingGroup(t))],i->AlternatingGroup(t).i) do
    newgen:=KroneckerProduct(PermutationMatrix@(GF(q),gen),id) #CAST GL(d,q)
      ^tmat;
    Assert(1,InOmega@(newgen,d,q,sign));
    Add(gens,newgen);
  od;
  newgen:=KroneckerProduct(PermutationMatrix@(GF(q),Tuple([1,2]) #CAST 
   SymmetricGroup(t)
    ),id) #CAST GL(d,q)
    ^tmat;
  if DeterminantMat(newgen)<>1 then
    newgen:=newgen*DirectSumMat(Concatenation([ggl1],List([1..t-1],i->id))) 
     #CAST GL(d,q)
      ^tmat;
  fi;
  if special or InOmega@(newgen,d,q,sign) then
    Add(gens,newgen);
  elif k > 1 then
    newgen:=newgen*DirectSumMat(Concatenation([gsl1],List([1..t-1],i->id))) 
     #CAST GL(d,q)
      ^tmat;
    Assert(1,InOmega@(newgen,d,q,sign));
    Add(gens,newgen);
  fi;
  if normaliser then
    if IsOddInt(q) and IsEvenInt(k) then
      gnl1:=NormGOMinusGO@(k,q,sign1);
      newgen:=DirectSumMat(List([1..t],i->gnl1)) #CAST GL(d,q)
        ^tmat;
      Add(gens,newgen);
    elif q > 3 then
      Add(gens,ScalarMat(d,PrimitiveElement(GF(q))));
    fi;
  fi;
  return SubStructure(GL(d,q),gens);
  #  k=1: t even,q=1,7 mod 8, c=4(so + ngo-go); t even q=3,5 mod 8, c=2
  #  (ngo-go);
  #  k=1: t odd,  q=1,7 mod 8, c=2 (so); t odd q=3,5 mod 8, c=1.
  #  k>1: k odd, t even, c=2 (ngo-go); else c=1.
end);

InstallGlobalFunction(OrthStabOfHalfTS@,
function(d,q)
#  /out:Construct GL_{d/2}(q).2 <= OmegaPlus(d,q)
local DJ,f,general,gens,mat1,mat2,normaliser,special,swapmat,z;
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
  Assert(1,IsEvenInt(d));
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  f:=QuoInt(d,2);
  z:=PrimitiveElement(GF(q));
  DJ:=function(mat,f,q)
  local cb;
    cb:=MatrixByEntries(GF(q),f,f,List([1..f],i->[i,f+1-i,1])) #CAST GL(f,q)
      ;
    return DirectSumMat(mat,TransposedMat(cb*mat^-1*cb));
  end;
  if special then
    mat1:=DJ(GL(f,q).1,f,q);
    mat2:=DJ((GL(f,q).2),f,q);
  else
    #  want matrices to generate GL(d,q) for q even or GL(d,q)/2
    #  for q odd.
    # rewritten select statement
    if q=3 then
      mat1:=DJ(SL(f,q).1,f,q);
    else
      # rewritten select statement
      if IsEvenInt(q) then
        mat1:=DJ(GL(f,q).1,f,q);
      else
        mat1:=DJ((GL(f,q).1)^2,f,q);
      fi;
    fi;
    # rewritten select statement
    if q=3 then
      mat2:=DJ(SL(f,q).2,f,q);
    else
      mat2:=DJ((GL(f,q).2),f,q);
    fi;
  fi;
  if not general and (not special or IsOddInt(q)) and IsOddInt(f) then
    #  swapping matrix not in Omega/SO
    return SubStructure(GL(d,q),mat1,#TODO CLOSURE
      mat2);
  fi;
  swapmat:=MatrixByEntries(GF(q),d,d,List([1..d],i->[i,d+1-i,1])) #CAST GL(d,q)
    ;
  gens:=[mat1,mat2,swapmat];
  if normaliser then
    Add(gens,NormGOMinusGO@(d,q,1));
  fi;
  return SubStructure(GL(d,q),gens);
  #  d/2 even, c=2, so (q even), go-so (q odd); o.w. c=1.
end);

InstallGlobalFunction(OrthStabOfHalfND@,
function(d,q)
#  /out:Construct O_{d/2}(q)^2, d even, d/2 odd/out:This is actually reducible,
#  so we construct it thus./out:It is classified as imprimitive because the two
#  subspaces fixed are/out:interchanged by an element fixing the orthogonal
#  form mod scalars.
local general,normaliser,sign,special;
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
  Assert(1,IsOddInt(q) and IsEvenInt(d) and IsOddInt(QuoInt(d,2)));
  # rewritten select statement
  if q mod 4=1 then
    sign:=-1;
  else
    sign:=1;
  fi;
  return NonDegenStabOmega@(d,q,sign,QuoInt(d,2)
   ,0:special:=special,general:=general,ipn:=normaliser);
  #  c=1
end);

OrthogonalImprims@:=function(d,q,sign)
local divs,ex,k,list,sign1,t;
  Assert(1,d > 2);
  Assert(1,(IsOddInt(d) and sign=0) or (IsEvenInt(d) and sign in Set([-1,1])));
  list:=[];
  divs:=DivisorsInt(d);
  RemoveSet(divs,1);
  for t in divs do
    k:=QuoInt(d,t);
    if IsEvenInt(k) then
      sign1:=1;
      if sign=sign1^t then
        Add(asmax,OrthImprim@(d,q,sign,k,sign1));
      fi;
      sign1:=-1;
      if sign=sign1^t then
        Add(asmax,OrthImprim@(d,q,sign,k,sign1));
      fi;
    else
      #  k odd
      if IsEvenInt(q) then
        continue;
      fi;
      if IsEvenInt(t) then
        ex:=d mod 4=2 and q mod 4=3;
        #  D non-square
        if (ex and sign=-1) or (not ex and sign=1) then
          Add(list,OrthImprim@(d,q,sign,k,0));
        fi;
      else
        #  k, t odd
        Add(list,OrthImprim@(d,q,sign,k,0));
      fi;
    fi;
  od;
  if IsEvenInt(d) then
    if sign=1 then
      Add(list,OrthStabOfHalfTS@(d,q));
    fi;
    if IsOddInt(q) and d mod 4=2 then
      if (q mod 4=1 and sign=-1) or (q mod 4=3 and sign=1) then
        Add(list,OrthStabOfHalfND@(d,q));
      fi;
    fi;
  fi;
  return list;
end;
;

