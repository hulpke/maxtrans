#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, CorrectForm, Determinant, DiagonalMatrix,
#  Eltseq, GCD, GF, GL, GO, GOMinus, GOPlus, GU, Gcd, GetAandB, Integers,
#  IsConsistent, IsEven, IsOdd, IsPrime, IsSquare, Lcm, Matrix, Ngens, Omega,
#  OmegaMinus, OmegaPlus, OrthogonalForm, PrimitiveElement, RSpace, Root, SL,
#  SO, SOMinus, SOPlus, SU, ScalarMatrix, Sp, TransformForm, UnitaryForm

#  Defines: GetAandB, OrthsInSU, SpInSU, SubfieldOdimEven, SubfieldOdimOdd,
#  SubfieldSL, SubfieldSU, SubfieldSp, getextSU

DeclareGlobalFunction("OrthsInSU@");

DeclareGlobalFunction("SpInSU@");

DeclareGlobalFunction("SubfieldOdimEven@");

DeclareGlobalFunction("SubfieldOdimOdd@");

DeclareGlobalFunction("SubfieldSL@");

DeclareGlobalFunction("SubfieldSU@");

DeclareGlobalFunction("SubfieldSp@");

InstallGlobalFunction(SubfieldSL@,
function(d,p,e,f)
local c,divisor,general,isc,mat,new_gen,new_scal,newgens,prim_scal,sol,vec,z;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  Assert(1,IsPrimeInt(p));
  Assert(1,e mod f=0);
  Assert(1,IsPrimeInt(QuoInt(e,f)));
  #  first we make the basic group.
  # rewritten select statement
  if general then
    newgens:=List([1,2],i->GL(d,p^f).i #CAST GL(d,p^e)
      );
  else
    newgens:=List([1,2],i->SL(d,p^f).i #CAST GL(d,p^e)
      );
  fi;
  z:=PrimitiveElement(GF(p^e));
  if general then
    return SubStructure(GL(d,p^e),newgens,#TODO CLOSURE
      ScalarMat(d,z));
  fi;
  divisor:=Gcd(p^e-1,d);
  c:=QuoInt((divisor*Lcm(p^f-1,QuoInt((p^e-1),divisor))),(p^e-1));
  prim_scal:=ScalarMat(d,z^(QuoInt((p^e-1),divisor)));
  if c mod Gcd(p^f-1,d)=0 then
    return SubStructure(SL(d,p^e),newgens,#TODO CLOSURE
      prim_scal);
  fi;
  mat:=MatrixByEntries(Integers(),2,1,[d,p^e-1]);
  vec:=[QuoInt(c*(p^e-1),(p^f-1))] #CAST RSpace(Integers(),1)
    ;
  # =v= MULTIASSIGN =v=
  sol:=SolutionMat(mat,vec);
  isc:=sol.val1;
  sol:=sol.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,isc);
  #  
  #  assert exists(t){x: x in [1..(p^e-1)div divisor] | ((d div divisor)*x
  #  - ((p^e-1) div ((Gcd(p^f-1, (p^e-1) div divisor) * divisor)))) mod ((p^e
  #  - 1) div divisor) eq 0};
  #  new_scal:= ScalarMatrix(d, z^-t);
  
  new_scal:=ScalarMat(d,z^-sol[1]);
  new_gen:=new_scal*DiagonalMat(Concatenation([z^(QuoInt((p^e-1),(p^f-1)))]
   ,List([2..d],i->1)))^c;
  Assert(1,DeterminantMat(new_gen)=1);
  return SubStructure(GL(d,p^e),newgens,#TODO CLOSURE
    prim_scal,new_gen);
end);

#  ******************************************************************
InstallGlobalFunction(SubfieldSp@,
function(d,p,e,f)
local delta,newgens,norm,normaliser,norms,power,scal_power,z;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,IsPrimeInt(p));
  Assert(1,e mod f=0);
  newgens:=List([1,2],i->SP(d,p^f).i #CAST GL(d,p^e)
    );
  z:=PrimitiveElement(GF(p^e));
  norms:=NormSpMinusSp@(d,p^f) #CAST GL(d,p^e)
    ;
  if normaliser then
    return SubStructure(GL(d,p^e),newgens,#TODO CLOSURE
      norms,ScalarMat(d,z));
  fi;
  if IsEvenInt(p) or IsOddInt(QuoInt(e,f)) then
    return SubStructure(GL(d,p^e),newgens);
  fi;
  power:=QuoInt((p^e-1),(p^f-1));
  Assert(1,IsEvenInt(power));
  norm:=NormSpMinusSp@(d,p^e);
  delta:=norm^power;
  scal_power:=QuoInt(power,2);
  Add(newgens,delta*ScalarMat(d,z^-scal_power) #CAST GL(d,p^e)
    );
  return SubStructure(GL(d,p^e),newgens);
end);

#  *******************************************************************
getextSU@:=function(d,p,e,f)
return QuoInt(((p^e+1)*Gcd(p^f+1,d)),(Lcm(p^f+1,QuoInt((p^e+1),Gcd(p^e+1,d)))
   *Gcd(p^e+1,d)));
end;
;
#  *******************************************************************
InstallGlobalFunction(SubfieldSU@,
function(d,p,e,f)
local 
   c,divisor,general,isc,mat,new_gen,new_scal,newgens,normaliser,prim_scal,sol,
   vec,z;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,IsPrimeInt(p));
  Assert(1,e mod f=0);
  Assert(1,IsPrimeInt(QuoInt(e,f)));
  Assert(1,not IsEvenInt(QuoInt(e,f)));
  #  otherwise not a subgroup!
  if normaliser then
    general:=true;
  fi;
  #  first we make the basic group.
  # rewritten select statement
  if general then
    newgens:=List([1,2],i->GU(d,p^f).i #CAST GL(d,p^(2*e))
      );
  else
    newgens:=List([1,2],i->SU(d,p^f).i #CAST SL(d,p^(2*e))
      );
  fi;
  z:=PrimitiveElement(GF(p^(2*e)));
  if normaliser then
    return SubStructure(GL(d,p^(2*e)),newgens,#TODO CLOSURE
      ScalarMat(d,z));
  elif general then
    return SubStructure(GL(d,p^(2*e)),newgens,#TODO CLOSURE
      ScalarMat(d,z^(p^e-1)));
  fi;
  divisor:=Gcd(p^e+1,d);
  c:=QuoInt((divisor*Lcm(p^f+1,QuoInt((p^e+1),divisor))),(p^e+1));
  #  "c mod (p^f+1, d) = ", c mod Gcd(p^f+1, d);
  prim_scal:=ScalarMat(d,z^(QuoInt((p^(2*e)-1),divisor)));
  Add(newgens,prim_scal);
  if c mod Gcd(p^f+1,d)<>0 then
    mat:=MatrixByEntries(Integers(),2,1,[d,p^e+1]);
    vec:=[QuoInt(c*(p^e+1),(p^f+1))] #CAST RSpace(Integers(),1)
      ;
    # =v= MULTIASSIGN =v=
    sol:=SolutionMat(mat,vec);
    isc:=sol.val1;
    sol:=sol.val2;
    # =^= MULTIASSIGN =^=
    Assert(1,isc);
    #  
    #  assert exists(t){x: x in [1..(p^e+1) div divisor] | (d div divisor)*x
    #  - ((p^e+1) div (Gcd(p^f+1, (p^e+1) div divisor) * divisor)) mod ((p^e
    #  + 1) div divisor) eq 0};
    #  new_scal:= ScalarMatrix(d, z^(t*(p^e-1)));
    #  new_diag := GL(d, p^(2*e))!(GU(d, p^f).1)^c;
    
    new_scal:=ScalarMat(d,z^(sol[1]*(p^e-1)));
    new_gen:=new_scal*(GU(d,p^f).1) #CAST GL(d,p^(2*e))
      ^c;
    Assert(1,DeterminantMat(new_gen)=1);
    Add(newgens,new_gen);
  fi;
  return SubStructure(SL(d,p^(2*e)),newgens);
end);

#  ******************************************************************
InstallGlobalFunction(SpInSU@,
function(d,q)
local 
   bool,cmat,f1,f2,general,grp,mat1,mat2,newgens,norm_elt,normaliser,pow,power,
   z;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,IsEvenInt(d));
  #  DFH: corrected bug in defn of norm_elt, 25/10/12
  if normaliser then
    general:=true;
  fi;
  z:=PrimitiveElement(GF(q^2));
  newgens:=[Eltseq(SP(d,q).1) #CAST GL(d,q^2)
    ,Eltseq(SP(d,q).2) #CAST GL(d,q^2)
    ];
  #   if IsOdd(q) and (general or (Gcd(q+1, d div 2) eq Gcd(q+1, d)) ) then
  #  pow :=  (q+1) div 2;
  #  norm_elt:= Gcd(q+1, d div 2) eq Gcd(q+1, d) select
  #  GL(d, q^2)!DiagonalMatrix([z^pow: i in [1..d div 2]]
  #  cat [-z^-pow: i in [1..d div 2]]) else
  #  GL(d, q^2)!DiagonalMatrix([z: i in [1..d div 2]]
  #  cat [z^-q: i in [1..d div 2]]);
  #  Append(~newgens, norm_elt);
  #  end if; 
  pow:=QuoInt((q+1),Gcd(q+1,QuoInt(d,2)));
  # rewritten select statement
  if general then
    norm_elt:=DiagonalMat(Concatenation(List([1..QuoInt(d,2)],i->z)
     ,List([1..QuoInt(d,2)],i->z^-q))) #CAST GL(d,q^2)
      ;
  else
    norm_elt:=DiagonalMat(Concatenation(List([1..QuoInt(d,2)],i->z^pow)
     ,List([1..QuoInt(d,2)],i->z^(-q*pow)))) #CAST GL(d,q^2)
      ;
  fi;
  Add(newgens,norm_elt);
  if general then
    grp:=SubStructure(GL(d,q^2),newgens);
    cmat:=TransformForm(grp);
    if normaliser then
      Add(newgens,ScalarMat(d,z));
      grp:=SubStructure(GL(d,q^2),newgens);
    fi;
    return grp^cmat;
  fi;
  #   don't need this if we always include norm_elt
  #  if Gcd(q+1, d) gt 2 then
  #  m:= Gcd(q+1, d);
  #  Append(~newgens, ScalarMatrix(d, z^((q^2-1) div m)));
  #  end if;
  
  grp:=SubStructure(GL(d,q^2),newgens);
  if IsEvenInt(q) then
    return grp;
  fi;
  #   in the following, f1 is the matrix of the unitary form preserved
  #   by Sp, should be able to prove this directly from K+L.
  #   f2 is the unitary form preserved by standard SU in magma.
  power:=QuoInt((q+1),2);
  # =v= MULTIASSIGN =v=
  f1:=UnitaryForm(grp);
  bool:=f1.val1;
  f1:=f1.val2;
  # =^= MULTIASSIGN =^=
  f2:=MatrixByEntries(GF(q^2),d,d,List([1..d],i->[i,d-i+1,1]));
  mat1:=CorrectForm(f1,d,q^2,"unitary");
  mat2:=CorrectForm(f2,d,q^2,"unitary");
  return grp^(mat1*(mat2^-1));
end);

#  *******************************************************************
#  This function makes matrix entries that are needed for the
#  normaliser of GO^{+/-}(d, q).
GetAandB@:=function(q)
local a,b,bool,z;
  z:=PrimitiveElement(GF(q));
  for a in GF(q) do
    # =v= MULTIASSIGN =v=
    b:=IsSquare(z-a^2);
    bool:=b.val1;
    b:=b.val2;
    # =^= MULTIASSIGN =^=
    if bool then
      return rec(val1:=a,
        val2:=b);
    fi;
  od;
end;
;
InstallGlobalFunction(OrthsInSU@,
function(d,q)
#  /out:KL have q odd? o.w. normalises symplectic type group
local 
   a,b,bool,delta_minus,delta_plus,disc_minus,f,f2,final_minus,final_plus,form,
   form1,form2,form_minus,general,gominus,grp1,grp2,isit,m1,m2,mat1,mat2,
   mat_minus,newgens,newgens1,newgens2,newgrp,normaliser,prim_scal,prim_scal_gu,
   prim_scal_su,type,y_minus,y_plus,z;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  Assert(1,IsOddInt(q) or IsEvenInt(d));
  #  o.w. orthogonal group reducible
  if normaliser then
    general:=true;
  fi;
  z:=PrimitiveElement(GF(q^2));
  prim_scal_su:=ScalarMat(d,z^(QuoInt((q^2-1),Gcd(q+1,d)))) #CAST GL(d,q^2)
    ;
  prim_scal_gu:=ScalarMat(d,z^(q-1)) #CAST GL(d,q^2)
    ;
  prim_scal:=ScalarMat(d,z) #CAST GL(d,q^2)
    ;
  if IsOddInt(d) then
    newgens:=[Eltseq(SO(d,q).1) #CAST GL(d,q^2)
      ,Eltseq(SO(d,q).2) #CAST GL(d,q^2)
      ];
    newgrp:=SubStructure(GL(d,q^2),newgens);
    # =v= MULTIASSIGN =v=
    form1:=UnitaryForm(newgrp);
    isit:=form1.val1;
    form1:=form1.val2;
    # =^= MULTIASSIGN =^=
    Assert(1,isit);
    if normaliser then
      newgrp:=SubStructure(GL(d,q^2),newgens,#TODO CLOSURE
        prim_scal);
    elif general then
      newgrp:=SubStructure(GL(d,q^2),newgens,#TODO CLOSURE
        prim_scal_gu);
    else
      newgrp:=SubStructure(GL(d,q^2),newgens,#TODO CLOSURE
        prim_scal_su);
    fi;
    form2:=MatrixByEntries(GF(q^2),d,d,List([1..d],i->[i,d-i+1,1]));
    mat1:=CorrectForm(form1,d,q^2,"unitary");
    mat2:=CorrectForm(form2,d,q^2,"unitary");
    return newgrp^(mat1*mat2^-1);
  fi;
  # rewritten select statement
  if general then
    newgens1:=List([1..Ngens(GOPlus(d,q))],i->Eltseq(GOPlus(d,q).i) #CAST 
     GL(d,q^2)
      );
  else
    newgens1:=List([1..Ngens(SOPlus(d,q))],i->Eltseq(SOPlus(d,q).i) #CAST 
     GL(d,q^2)
      );
  fi;
  # rewritten select statement
  if general then
    newgens2:=List([1..Ngens(GOMinus(d,q))],i->Eltseq(GOMinus(d,q).i) #CAST 
     GL(d,q^2)
      );
  else
    newgens2:=List([1..Ngens(SOMinus(d,q))],i->Eltseq(SOMinus(d,q).i) #CAST 
     GL(d,q^2)
      );
  fi;
  if IsEvenInt(q) then
    return rec(val1:=SubStructure(SL(d,q^2),newgens1),
      val2:=SubStructure(SL(d,q^2),newgens2));
  fi;
  # =v= MULTIASSIGN =v=
  form_minus:=OrthogonalForm(GOMinus(d,q));
  isit:=form_minus.val1;
  type:=form_minus.val2;
  form_minus:=form_minus.val3;
  # =^= MULTIASSIGN =^=
  Assert(1,isit and type="orth-");
  #  this will conjugate the group so that it is in the form
  #  assumed by Kleidman and Liebeck.
  mat_minus:=CorrectForm(form_minus,d,q,"orth-");
  gominus:=GOMinus(d,q)^mat_minus;
  # =v= MULTIASSIGN =v=
  form:=OrthogonalForm(gominus);
  isit:=form.val1;
  type:=form.val2;
  form:=form.val3;
  # =^= MULTIASSIGN =^=
  Assert(1,isit and type="orth-");
  mat_minus:=mat_minus #CAST GL(d,q^2)
    ;
  newgens2:=List(newgens2,g->g^mat_minus);
  #  we need the discriminant to compute the element \delta for minus
  #  type groups.
  form:=form[1][1]^-1*form;
  if form[d][d]=1 then
    disc_minus:="square";
    Assert(1,not IsEvenInt(QuoInt((q-1)*d,4)));
  else
    disc_minus:="nonsquare";
    Assert(1,IsEvenInt(QuoInt((q-1)*d,4)));
  fi;
  delta_plus:=(DiagonalMat(Concatenation(List([1..QuoInt(d,2)],i->z^(q+1))
   ,List([1..QuoInt(d,2)],i->1))) #CAST GL(d,q)
    );
  delta_plus:=delta_plus #CAST GL(d,q^2)
    ;
  # =v= MULTIASSIGN =v=
  b:=GetAandB@(q);
  a:=b.val1;
  b:=b.val2;
  # =^= MULTIASSIGN =^=
  if disc_minus="square" then
    delta_minus:=MatrixByEntries(GF(q^2)
     ,d,d,Concatenation(List([0..((QuoInt(d,2))-1)],i->[[2*i+1,2*i+1,a]
     ,[2*i+1,2*i+2,b],[2*i+2,2*i+1,b],[2*i+2,2*i+2,-a]]))) #CAST GL(d,q^2)
      ;
  else
    delta_minus:=MatrixByEntries(GF(q^2)
     ,d,d,Concatenation(Concatenation(List([0..((QuoInt(d,2))-2)]
     ,i->[[2*i+1,2*i+1,a],[2*i+1,2*i+2,b],[2*i+2,2*i+1,b],[2*i+2,2*i+2,-a]])
     ,[[d-1,d,1],[d,d-1,z^(q+1)]]))) #CAST GL(d,q^2)
      ;
  fi;
  y_plus:=delta_plus*prim_scal^-1;
  Assert(1,UnitaryForm(SubStructure(GL(d,q^2),newgens1,#TODO CLOSURE
    y_plus)));
  y_minus:=delta_minus*prim_scal^-1;
  Assert(1,UnitaryForm(SubStructure(GL(d,q^2),newgens2,#TODO CLOSURE
    y_minus)));
  if general then
    Add(newgens1,y_plus);
  else
    power_for_y_plus:=First([1..q+1],i->DeterminantMat(y_plus)
     =DeterminantMat(prim_scal^(i*(q-1))));
    if power_for_y_plus<>fail then
      final_plus:=y_plus*prim_scal^(-power_for_y_plus*(q-1));
      Add(newgens1,final_plus);
    else
      power_for_y_plus:=First([1..q^2-1],i->DeterminantMat(y_plus*GOPlus(d,q).4 
       #CAST GL(d,q^2)
        )=DeterminantMat(prim_scal^(i*(q-1))));
      if power_for_y_plus<>fail then
        final_plus:=y_plus*GOPlus(d,q).4 #CAST GL(d,q^2)
          *prim_scal^(-(q-1)*power_for_y_plus);
        Add(newgens1,final_plus);
      else
        Assert(1,power_for_y_plus:=ForAny([1..q+1]
         ,i->DeterminantMat(prim_scal^(i*(q-1)))=DeterminantMat(GOPlus(4,q).4) 
         #CAST GF(q^2)
          ));
        final_plus:=GOPlus(d,q).4 #CAST GL(d,q^2)
          *prim_scal^(-(q-1)*power_for_y_plus);
        Add(newgens1,final_plus);
      fi;
    fi;
  fi;
  if general then
    Add(newgens2,y_minus);
  else
    power_for_y_minus:=First([1..q+1],i->DeterminantMat(y_minus)
     =DeterminantMat(prim_scal^(i*(q-1))));
    if power_for_y_minus<>fail then
      final_minus:=y_minus*prim_scal^(-power_for_y_minus*(q-1));
      Add(newgens2,final_minus);
    else
      power_for_y_minus:=First([1..q^2-1],i->DeterminantMat(y_minus*gominus.4 
       #CAST GL(d,q^2)
        )=DeterminantMat(prim_scal^(i*(q-1))));
      if power_for_y_minus<>fail then
        final_minus:=y_minus*gominus.4 #CAST GL(d,q^2)
          *prim_scal^(-(q-1)*power_for_y_minus);
        Add(newgens2,final_minus);
      else
        Assert(1,power_for_y_minus:=ForAny([1..q+1]
         ,i->DeterminantMat(prim_scal^(i*(q-1)))=DeterminantMat(gominus.4) 
         #CAST GF(q^2)
          ));
        final_minus:=gominus.4 #CAST GL(d,q^2)
          *prim_scal^(-(q-1)*power_for_y_minus);
        Add(newgens2,final_minus);
      fi;
    fi;
  fi;
  grp2:=SubStructure(GL(d,q^2),newgens2);
  # =v= MULTIASSIGN =v=
  f:=UnitaryForm(grp2);
  bool:=f.val1;
  f:=f.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,bool);
  # =v= MULTIASSIGN =v=
  f2:=UnitaryForm(GU(d,q));
  bool:=f2.val1;
  f2:=f2.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,bool);
  m1:=CorrectForm(f,d,q^2,"unitary") #CAST GL(d,q^2)
    ;
  m2:=CorrectForm(f2,d,q^2,"unitary") #CAST GL(d,q^2)
    ;
  if normaliser then
    grp1:=SubStructure(GL(d,q^2),newgens1,#TODO CLOSURE
      prim_scal);
    grp2:=SubStructure(GL(d,q^2),newgens2,#TODO CLOSURE
      prim_scal);
  elif general then
    grp1:=SubStructure(GL(d,q^2),newgens1,#TODO CLOSURE
      prim_scal_gu);
    grp2:=SubStructure(GL(d,q^2),newgens2,#TODO CLOSURE
      prim_scal_gu);
  else
    grp1:=SubStructure(GL(d,q^2),newgens1,#TODO CLOSURE
      prim_scal_su);
    grp2:=SubStructure(GL(d,q^2),newgens2,#TODO CLOSURE
      prim_scal_su);
  fi;
  grp2:=grp2^(m1*m2^-1);
  return rec(val1:=grp1,
    val2:=grp2);
end);

InstallGlobalFunction(SubfieldOdimOdd@,
function(d,p,e,f)
local general,gens,normaliser,special,x;
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
  Assert(1,IsPrimeInt(p));
  Assert(1,e mod f=0);
  Assert(1,IsPrimeInt(QuoInt(e,f)));
  Assert(1,IsOddInt(d) and IsOddInt(p));
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  # rewritten select statement
  if general then
    x:=GO(d,p^f);
  else
    # rewritten select statement
    if (special or QuoInt(e,f)=2) then
      x:=SO(d,p^f);
    else
      x:=Omega(d,p^f);
    fi;
  fi;
  gens:=List([1..Ngens(x)],i->x.i #CAST GL(d,p^e)
    );
  if normaliser then
    Add(gens,ScalarMat(d,PrimitiveElement(GF(p^e))));
  fi;
  return SubStructure(GL(d,p^e),gens);
  #  if e/f = 2, c=2, so; o.w. c=1
end);

InstallGlobalFunction(SubfieldOdimEven@,
function(d,p,e,f,sign1)
local general,ggl,gol,grp,grp1,mat,normaliser,q,r,special,w,z;
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
  Assert(1,IsPrimeInt(p));
  Assert(1,e mod f=0);
  Assert(1,IsPrimeInt(QuoInt(e,f)));
  Assert(1,sign1 in Set([-1,1]));
  Assert(1,IsEvenInt(d));
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  r:=QuoInt(e,f);
  z:=PrimitiveElement(GF(p^e));
  if IsOddInt(r) or p=2 then
    if general then
      # rewritten select statement
      if sign1=1 then
        grp:=GOPlus(d,p^f);
      else
        grp:=GOMinus(d,p^f);
      fi;
    elif special then
      # rewritten select statement
      if sign1=1 then
        grp:=SOPlus(d,p^f);
      else
        grp:=SOMinus(d,p^f);
      fi;
    else
      # rewritten select statement
      if sign1=1 then
        grp:=OmegaPlus(d,p^f);
      else
        grp:=OmegaMinus(d,p^f);
      fi;
    fi;
    grp1:=SubStructure(GL(d,p^e),List([1..Ngens(grp)],i->grp.i #CAST GL(d,p^e)
      ));
    mat:=TransformForm(grp1);
    if normaliser then
      if IsOddInt(p) then
        grp1:=SubStructure(GL(d,p^e),grp1,#TODO CLOSURE
          NormGOMinusGO@(d,p^f,sign1) #CAST GL(d,p^e)
          );
      fi;
      grp1:=SubStructure(GL(d,p^e),grp1,#TODO CLOSURE
        ScalarMat(d,z));
    fi;
    return grp1^mat;
  fi;
  q:=p^f;
  if general then
    # rewritten select statement
    if sign1=1 then
      grp:=GOPlus(d,q);
    else
      grp:=GOMinus(d,q);
    fi;
  else
    # rewritten select statement
    if sign1=1 then
      grp:=SOPlus(d,q);
    else
      grp:=SOMinus(d,q);
    fi;
  fi;
  grp1:=SubStructure(GL(d,p^e),List([1..Ngens(grp)],i->grp.i #CAST GL(d,p^e)
    ));
  mat:=TransformForm(grp1);
  grp1:=grp1^mat;
  if not special and ((d mod 4=0 and sign1=-1) or (d mod 4=2 and ((q mod 4=1 
     and sign1=1) or (q mod 4=3 and sign1=-1)))) then
    return grp1;
  fi;
  #  otherwise adjoin element from NGO-GO
  ggl:=(GOMinusSO@(d,q,sign1) #CAST GL(d,p^e)
    )^mat;
  gol:=(NormGOMinusGO@(d,q,sign1) #CAST GL(d,p^e)
    )^mat;
  #  multiply by scalars to fix form
  w:=PrimitiveElement(GF(q)) #CAST GF(p^e)
    ;
  gol:=gol*ScalarMat(GF(p^e),d,Root(w,2)^-1) #CAST GL(d,p^e)
    ;
  if DeterminantMat(gol)<>1 then
    gol:=gol*ggl;
  fi;
  Assert(1,special or InOmega@(gol,d,p^e,1));
  if normaliser then
    return SubStructure(GL(d,p^e),grp1,#TODO CLOSURE
      gol,ScalarMat(d,z));
  fi;
  return SubStructure(GL(d,p^e),grp1,#TODO CLOSURE
    gol);
  #  if e/f odd or p=2,  c=1
  #  o.w. 4|d, sign1 = -1 or d=2 mod 4 and
  #            (q mod 4 = 1, sign1=1 or q mod 4 = 3, sign1 = -1) c=2, ngo-go,
  #  o.w. c=4, so + ngo-go
end);


