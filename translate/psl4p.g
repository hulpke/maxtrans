#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: A7, AandB, Append, ClassicalForms, CoprimeMaximals,
#  CorrectForm, DerivedSubgroup, Determinant, DiagonalMatrix, FPGroupStrong,
#  FreeGroup, GF, GL, GOMinus, Getsl27d4, Image, Integers,
#  IsAbsolutelyIrreducible, IsPrime, IsPrimitive, IsSemiLinear, IsSquare,
#  IsTensor, Ngens, NonCoprimeMaximals, NormOfOMinus, NormOfOPlus,
#  OrthogonalForm, PrimitiveElement, SL, SOMinus, SOPlus, Sp, SquareRoot, U4_2

#  Defines: A7, AandB, CoprimeMaximals, Getsl27d4, L4pIdentify,
#  NonCoprimeMaximals, NormOfOMinus, NormOfOPlus, U4_2

DeclareGlobalFunction("L4pIdentify@");

#   function names in this file:
#  Getsl27d4
#  A7(p)
#  U4_2(p)
#  AandB(p)
#  NormOfOMinus(p)
#  NormOfOPlus(p)
#  CoprimeMaximals(p, factor, type,Print)
#  NonCoprimeMaximals(group, p, factor, type, psl, soc,Print)
#  L4pIdentify(group, p)

Getsl27d4@:=function(p)
local L,_LR,c9;
  _LR:=rec(F:=FreeGroup(2));
  _LR.AI:=[[a^-1,b^-1]];
  #  POSTPONED `where'
  b:=(_LR.F).2;
  #  POSTPONED `where'
  a:=(_LR.F).1;
  #  two constituents interchanged by _LR`AI[1][1]
  _LR.G:=SubStructure(GL(8,Integers()),[[0,1,0,0,0,0,0,0],[-1,0,0,0,0,0,0,0]
   ,[0,0,0,1,0,0,0,0],[0,0,-1,0,0,0,0,0],[0,0,0,0,0,0,1,0],[0,0,0,0,0,0,0,1]
   ,[0,0,0,0,-1,0,0,0],[0,0,0,0,0,-1,0,0]]
,#TODO CLOSURE
    [[1,0,0,0,0,0,0,0],[0,0,1,0,0,0,0,0],[0,0,0,0,1,0,0,0],[0,0,0,0,0,1,0,0]
   ,[0,1,0,0,0,0,0,0],[0,0,0,0,0,0,0,-1],[0,0,0,0,0,0,1,0],[0,0,0,-1,0,0,0,0]]
);
  L:=ReduceOverFiniteField@(_LR,p);
  c9:=L[1];
  #  just testing this for now, delete later.
  Assert(1,IsAbsolutelyIrreducible(c9) and (not IsSemiLinear(c9)) and 
   IsPrimitive(c9) and (not IsTensor(c9)) and ClassicalForms(c9)
   .formType="linear");
  return c9;
end;
;
#  ******************************************************************
#  * 2.Alt(7) is a maximal C_9 group of SL(4, p) for p gt 7 and       *
#  * b7 in GF(p). has been tested on all primes p s.t. 8 lt p lt 1000 *
#  ******************************************************************
A7@:=function(p)
local C,D,G,b7,i7,sl,x,y;
  Assert(1,IsPrimeInt(p) and p > 7);
  sl:=SL(4,p);
  i7:=SquareRoot((-7) #CAST GF(p)
    );
  b7:=((-1+i7)/2) #CAST GF(p)
    ;
  x:=((i7+3)/4) #CAST GF(p)
    ;
  y:=(b7/2) #CAST GF(p)
    ;
  C:=[0,0,1,0,0,0,0,1,-1,0,-1,0,0,-1,0,-1] #CAST sl
    ;
  D:=[0,-x,x,-y,-y,y,-y,0,-y,0,(-i7-1)/2,-x,0,-y,y,y] #CAST sl
    ;
  G:=SubStructure(sl,C,#TODO CLOSURE
    D);
  return G;
end;
;
#  
#  * We find a maximal C_9 subgroup isomorphic to U_(4, 2) = Sp(4, 3)
#  * whenever the field has order divisible by 3. This actually
#  * creates 2.Sp(4, 3) \leq SL(4, p), hence derived subgroup at the end.

U4_2@:=function(p)
local a,b,c,f1,f2,g1,g2,grp,omega,omegab,z;
  Assert(1,(p-1) mod 3=0);
  z:=PrimitiveElement(GF(p));
  omega:=z^(QuoInt((p-1),3));
  omegab:=omega^2;
  g1:=((2+omega)/3) #CAST GF(p)
    ;
  g2:=((1-omega)/3) #CAST GF(p)
    ;
  f1:=((1+2*omegab)/3) #CAST GF(p)
    ;
  f2:=((1-omegab)/3) #CAST GF(p)
    ;
  a:=DiagonalMat([1,1,omega,1]) #CAST GL(4,p)
    ;
  b:=[1,0,0,0,0,f1,f2,f2,0,f2,f1,f2,0,f2,f2,f1] #CAST GL(4,p)
    ;
  c:=[g1,0,-g2,g2,0,1,0,0,-g2,0,g1,g2,g2,0,g2,g1] #CAST GL(4,p)
    ;
  grp:=SubStructure(GL(4,p),a,#TODO CLOSURE
    b,c);
  return DerivedSubgroup(grp);
end;
;
#  
#  * The elements a and b of GF(p) are needed to make the
#  * normaliser in SL of O^-(4, p). They satisfy a^2+b^2 = z.
#  * See Kleidman + Liebeck, p39 for details.

AandB@:=function(p)
local a,b,bool,z;
  z:=PrimitiveElement(GF(p));
  for b in [1..p-1] do
    # =v= MULTIASSIGN =v=
    a:=IsSquare(z-b #CAST GF(p)
      ^2);
    bool:=a.val1;
    a:=a.val2;
    # =^= MULTIASSIGN =^=
    if bool then
      return rec(val1:=a,
        val2:=b);
    fi;
  od;
  Print("couldn't find a and b in GF(",p,")");
  return rec(val1:=false,
    val2:=_);
end;
;
#  *****************************************************************
#  Makes the normaliser of SOMinus(4, p) in SL(4,p): only designed for
#  p=3 mod 4,
NormOfOMinus@:=function(p)
local a,b,bool,form,g1,group,mat2,norm_mat,type,z;
  g1:=SOMinus(4,p);
  # =v= MULTIASSIGN =v=
  form:=OrthogonalForm(g1);
  bool:=form.val1;
  type:=form.val2;
  form:=form.val3;
  # =^= MULTIASSIGN =^=
  mat2:=CorrectForm(form,4,p,"orth-") #CAST GL(4,p)
    ;
  # =v= MULTIASSIGN =v=
  b:=AandB@(p);
  a:=b.val1;
  b:=b.val2;
  # =^= MULTIASSIGN =^=
  z:=PrimitiveElement(GF(p));
  norm_mat:=[a,b,0,0,b,-a,0,0,0,0,0,1,0,0,z,0] #CAST GL(4,p)
    ;
  if p mod 4=3 then
    norm_mat:=(norm_mat^(QuoInt((p-1),2)))^(mat2^-1);
  else
    norm_mat:=((norm_mat^(QuoInt((p-1),4)))^(mat2^-1))*GOMinus(4,p).4;
  fi;
  Assert(1,not norm_mat in g1);
  Assert(1,DeterminantMat(norm_mat)=1);
  group:=SubStructure(SL(4,p),g1,#TODO CLOSURE
    norm_mat);
  return group;
end;
;
#  *************************************************************
#  Makes the normaliser in SL(4, p) of SOPlus(4, p): only
#  designed for p=1 mod 4.
NormOfOPlus@:=function(p)
local bool,form,g1,group,mat1,norm1,norm2,type,z;
  g1:=SOPlus(4,p);
  # =v= MULTIASSIGN =v=
  form:=OrthogonalForm(g1);
  bool:=form.val1;
  type:=form.val2;
  form:=form.val3;
  # =^= MULTIASSIGN =^=
  mat1:=CorrectForm(form,4,p,"orth+");
  norm1:=DiagonalMat([-1,1,1,1]) #CAST GL(4,p)
    ;
  norm1:=norm1^(mat1^-1);
  z:=PrimitiveElement(GF(p));
  norm2:=DiagonalMat([1,1,z,z]) #CAST GL(4,p)
    ;
  norm2:=norm2^(QuoInt((p-1),4));
  group:=SubStructure(SL(4,p),g1,#TODO CLOSURE
    norm1*norm2);
  return group;
end;
;
#  ******************************************************************
#  This makes those maximal subgroups which behave differently when p=3
#  mod 4 from the general case.
CoprimeMaximals@:=function(p,factor,type,Print)
local alt7,c9,diag,maximals,ominus,u4_2;
  maximals:=[];
  diag:=(GL(4,p).1)@factor;
  ominus:=NormOfOMinus@(p);
  Add(maximals,ominus@factor);
  #  C_9s.
  if Print > 1 then
    Print("getting C_9's");
  fi;
  if type in Set(["psl","psl.2_2"]) then
    if not (p mod 7)=0 and IsSquare(p #CAST GF(7)
      ) then
      alt7:=A7@(p)@factor;
      maximals:=Concatenation(maximals,ImageCopies@(alt7,2,diag));
    fi;
    if p mod 6=1 then
      u4_2:=U4_2@(p)@factor;
      maximals:=Concatenation(maximals,ImageCopies@(u4_2,2,diag));
    fi;
  fi;
  if not (p mod 7)=0 and IsSquare(p #CAST GF(7)
    ) then
    if (((p mod 8)=7) and type="psl.2_2") or (((p mod 8)=3) and type="psl.2_3") 
       then
      c9:=Getsl27d4@(p)@factor;
      maximals:=Concatenation(maximals,ImageCopies@(c9,2,diag));
    fi;
  fi;
  return maximals;
end;
;
#  ******************************************************************
#  Those maximal subgroups which behave differently when p=1 mod 4.
NonCoprimeMaximals@:=function(p,factor,type,soc,psl,invol,Print)
local alt7,diag,ext,ext1,extraspec,l27,maximals,ominus,u4_2;
  maximals:=[];
  #  
  #  * Extraspecials: We have 4 conjugate classes of 2^4:Sym_6 if p=1
  #  * \mod 8 and type = "psl", Two of these extend in "psl.2_2",
  #  * otherwise they fuse (pairwise or in 4s..).
  #  * if p = 5 mod 8 we have 2 conjugate 2^4:\Alt_6 which extend in
  #  * psl.2_1, psl.2_2 and psl.12, but fuse elsewhere.
  
  diag:=(GL(4,p).1)@factor;
  if type in Set(["psl","psl.2_1","psl.2_2","psl.12"]) then
    if (p mod 8=1) and type in Set(["psl","psl.2_2"]) then
      extraspec:=NormaliserOfSymplecticGroup@(4,p);
      if type="psl" then
        if Print > 1 then
          Print("getting extraspecials");
        fi;
        maximals:=Concatenation(maximals,ImageCopies@(extraspec@factor,4,diag))
         ;
      elif type="psl.2_2" then
        if Print > 1 then
          Print("getting extraspecials");
        fi;
        extraspec:=SelectGroupGeneral@(psl,extraspec@factor,diag,invol);
        Add(maximals,extraspec);
        Add(maximals,extraspec^(diag^2));
      fi;
    elif p mod 8=5 then
      if Print > 1 then
        Print("getting extraspecials");
      fi;
      ext:=NormaliserOfSymplecticGroup@(4,p);
      ext1:=SubStructure(ext,List(Filtered([1..Ngens(ext)]
       ,i->DeterminantMat(ext.i)=1),i->ext.i));
      maximals:=Concatenation(maximals,ImageCopies@(ext1@factor,2,diag));
    fi;
  fi;
  if type in Set(["psl","psl.2_1","psl.2_3","psl.13"]) then
    if Print > 1 then
      Print("getting OMinus(4,p)");
    fi;
    ominus:=NormOfOMinus@(p)@factor;
    maximals:=Concatenation(maximals,ImageCopies@(ominus,2,diag));
  fi;
  #  C_9s
  if Print > 1 then
    Print("getting C_9's");
  fi;
  if type="psl" or type="psl.2_2" then
    if not (p=7) and (IsSquare(p #CAST GF(7)
      )) then
      alt7:=A7@(p)@factor;
      if type="psl" then
        maximals:=Concatenation(maximals,ImageCopies@(alt7,4,diag));
      elif type="psl.2_2" then
        alt7:=SelectGroupGeneral@(psl,alt7,diag,invol);
        Add(maximals,alt7);
        Add(maximals,alt7^(diag^2));
      fi;
    fi;
    if p mod 6=1 then
      u4_2:=U4_2@(p)@factor;
      if type="psl" then
        maximals:=Concatenation(maximals,ImageCopies@(u4_2,4,diag));
      else
        u4_2:=SelectGroupGeneral@(psl,u4_2,diag,invol);
        Add(maximals,u4_2);
        Add(maximals,u4_2^(diag^2));
      fi;
    fi;
  fi;
  #  novelty L_2(7)s
  if ((not (p=7)) and (IsSquare(p #CAST GF(7)
    )) and type in Set(["psl.2_2","psl.2_3"])) then
    if (((p mod 8)=1) and type="psl.2_2") or (((p mod 8)=5) and type="psl.2_3") 
       then
      l27:=Getsl27d4@(p)@factor;
      l27:=SelectGroupGeneral@(psl,l27,diag,invol);
      Add(maximals,l27);
      Add(maximals,l27^(diag^2));
    fi;
  fi;
  return maximals;
end;
;
#  ****************************************************************
#  
#  The main function. This works out the type of group and whether
#  or not we're coprime (i.e. whether or not p=3 mod 4). It then
#  computes the maximal subgroups which don't depend so much
#  on whether or not we're in the coprime case, before calling
#  and NonCoprimeMaximals to get the rest.

InstallGlobalFunction(L4pIdentify@,
function(group,p)
local 
   F,Print,apsl,coprime,diag,factor,gl,group,homom,i,image,invol,max,maximals,
   newgens,oplus,phi,psl,sl,soc,symp,type;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  Assert(1,IsPrimeInt(p));
  Assert(1,p > 3);
  #  PSL(4, 2) and PSL(4, 3) are special cases.
  if p mod 4=3 then
    coprime:=true;
  else
    coprime:=false;
  fi;
  if Print > 1 then
    Print("Making standard group");
  fi;
  gl:=GL(4,p);
  sl:=SL(4,p);
  apsl:=PGammaL2@(4,p);
  factor:=GroupHomomorphismByImages(gl,apsl,
    apsl.1,apsl.2);
  psl:=sl@factor;
  diag:=GL(4,p).1@factor;
  if Print > 1 then
    Print("Setting up isomorphism");
  fi;
  # =v= MULTIASSIGN =v=
  group:=MakeHomomGeneral@(group,4,p,1,psl,apsl,factor:Print:=0);
  homom:=group.val1;
  soc:=group.val2;
  group:=group.val3;
  # =^= MULTIASSIGN =^=
  if Print > 1 then
    Print("Calling FPGroupStrong");
  fi;
  # =v= MULTIASSIGN =v=
  phi:=FPGroupStrong(SubStructure(psl,List([1..Ngens(soc)],i->soc.i@homom)));
  F:=phi.val1;
  phi:=phi.val2;
  # =^= MULTIASSIGN =^=
  if Print > 1 then
    Print("Identifying group");
  fi;
  #   Also get the generators of apsl correct
  newgens:=List([1..Ngens(group)],i->group.i@homom);
  image:=Image(homom);
  invol:=apsl.3;
  if image=psl then
    type:="psl";
    apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.1,apsl.3]));
  elif image=apsl then
    type:="aut_psl";
    apsl:=SubStructure(apsl,newgens);
  elif coprime then
    #  when coprime the outer automorphism group is 2^2
    if image=SubStructure(apsl,apsl.1,#TODO CLOSURE
      apsl.2) then
      type:="pgl";
      apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.3]));
    elif image=SubStructure(apsl,apsl.1^2,#TODO CLOSURE
      apsl.2,apsl.3) then
      type:="psl.2_2";
      apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.1]));
    else
      Assert(1,image=SubStructure(apsl,apsl.1^2,#TODO CLOSURE
        apsl.2,apsl.1*apsl.3));
      type:="psl.2_3";
      apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.3]));
    fi;
    #  now the outer aut group is D_{2 x 4}
  elif image=SubStructure(apsl,apsl.1,#TODO CLOSURE
    apsl.2) then
    type:="pgl";
    apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.3]));
  elif image=SubStructure(apsl,apsl.1^2,#TODO CLOSURE
    apsl.2,apsl.3) then
    type:="psl.12";
    #  outer aut of order 4: diag^2, duality, product.
    apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.1]));
  elif image=SubStructure(apsl,apsl.1^2,#TODO CLOSURE
    apsl.2,apsl.1*apsl.3) then
    type:="psl.13";
    #  outer aut of order 4: diag^2, duality*diag, product.
    apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.3]));
  elif image=SubStructure(apsl,apsl.1^2,#TODO CLOSURE
    apsl.2) then
    type:="psl.2_1";
    #  outer aut of order 2, diag^2 (central)
    apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.1,apsl.3]));
  elif image=SubStructure(apsl,apsl.1^4,#TODO CLOSURE
    apsl.2,apsl.3) or image=SubStructure(apsl,apsl.1^4,#TODO CLOSURE
    apsl.2,apsl.1^2*apsl.3) then
    type:="psl.2_2";
    #  outer aut of order 2, either duality or duality*diag^2 (these are
    #  conjugate in Out(PSL))
    apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.1]));
    invol:=group.(Ngens(group))@homom;
  else
    Assert(1,image=SubStructure(apsl,apsl.1^4,#TODO CLOSURE
      apsl.2,apsl.1*apsl.3) or image=SubStructure(apsl,apsl.1^4,#TODO CLOSURE
      apsl.2,apsl.1^3*apsl.3));
    type:="psl.2_3";
    #  outer aut of order 2, either duality*diag or duality*diag^2
    #  (these are conjugate in Out(PSL))
    apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.1]));
    invol:=group.(Ngens(group))@homom;
  fi;
  if Print > 1 then
    Print("Type = ",type);
  fi;
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=apsl,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  if Print > 1 then
    Print("getting reducibles");
  fi;
  if type in Set(["psl","psl.2_1","pgl"]) then
    Add(maximals,SLPointStab@(4,p)@factor);
    Add(maximals,SLStabOfNSpace@(4,p,3)@factor);
  else
    Add(maximals,SLStabOfNSpaceMeetDual@(4,p,1)@factor);
    Add(maximals,SLStabOfNSpaceMissDual@(4,p,1)@factor);
  fi;
  Add(maximals,SLStabOfHalfDim@(4,p)@factor);
  if Print > 1 then
    Print("getting imprimitives");
  fi;
  if p > 5 or type in Set(["pgl","psl.13","psl.2_3"]) then
    Add(maximals,ImprimsMeetSL@(4,p,4)@factor);
  fi;
  Add(maximals,ImprimsMeetSL@(4,p,2)@factor);
  if Print > 1 then
    Print("getting semilinears");
  fi;
  Add(maximals,GammaLMeetSL@(4,p,2)@factor);
  #  Sp(4, p): 2 copies if exists: coprime PSL. PSL.2_2.
  i:=DiagonalMat([1,1,-1,-1]) #CAST SL(4,p)
    ;
  if type in Set(["psl","psl.2_1","psl.2_2","psl.12"]) then
    if Print > 1 then
      Print("getting Sp(4,p)");
    fi;
    symp:=SubStructure(SL(4,p),SP(4,p),#TODO CLOSURE
      i)@factor;
    maximals:=Concatenation(maximals,ImageCopies@(symp,2,diag));
  fi;
  if coprime then
    if Print > 1 then
      Print("getting SOPlus(4,p)");
    fi;
    oplus:=SubStructure(SL(4,p),SOPlus(4,p),#TODO CLOSURE
      i);
    Add(maximals,oplus@factor);
  elif type in Set(["psl","psl.2_1","psl.2_2","psl.12"]) then
    if Print > 1 then
      Print("getting OPlus(4,p)");
    fi;
    oplus:=NormOfOPlus@(p)@factor;
    maximals:=Concatenation(maximals,ImageCopies@(oplus,2,diag));
  fi;
  if coprime then
    maximals:=Concatenation(maximals,CoprimeMaximals@(p,factor,type,Print));
  else
    maximals:=Concatenation(maximals,NonCoprimeMaximals@(p,factor,type,soc,psl,
     invol,Print));
  fi;
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);


