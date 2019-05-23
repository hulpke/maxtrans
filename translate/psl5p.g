#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, DerivedSubgroup, Determinant, DiagonalMatrix,
#  FPGroupStrong, GF, GL, Image, IsPrime, IsSquare, M11, Matrix, Ngens, Order,
#  PSL2_11, PrimitiveElement, SL, SO, Transpose, U4_2

#  Defines: L5pIdentify, M11, PSL2_11, U4_2

DeclareGlobalFunction("L5pIdentify@");

#  
#  This file contains functions called:
#  PSL2_11(p)
#  U4_2(p)
#  M11()
#  L5pIdentify(group, p)

#  **************************************************************
#   makes a C_9 group whenever (-11) is square mod p.
PSL2_11@:=function(p)
local A,B,b11,bool,i11,psl2_11;
  # =v= MULTIASSIGN =v=
  i11:=IsSquare((-11) #CAST GF(p)
    );
  bool:=i11.val1;
  i11:=i11.val2;
  # =^= MULTIASSIGN =^=
  if not bool then
    Print("error: -11 not square in GF(",p,")");
    return false;
  fi;
  b11:=(-1+i11)/2;
  A:=MatrixByEntries(GF(p)
   ,5,5,[1,0,0,0,0,1,-1,b11,0,0,0,0,1,0,0,-1,0,-1,-1,b11,0,0,0,0,1]);
  B:=MatrixByEntries(GF(p)
   ,5,5,[b11,-b11,-1,b11+1,2,0,-1,-1,0,0,0,1,0,0,0,1,0,0,0,0,1,-b11-1,0,2,-b11])
   ;
  psl2_11:=SubStructure(SL(5,p),A,#TODO CLOSURE
    B);
  return psl2_11;
end;
;
#  **************************************************************
#  makes C_9 group U(4, 2) whenever cube root of unity exists.
U4_2@:=function(p)
local a,b,c,d1,d2,d3,d4,d5,g,w,z;
  Assert(1,p mod 6=1);
  z:=PrimitiveElement(GF(p));
  w:=z^(QuoInt((p-1),3));
  a:=[1,-w^2,0,-w^2,1,-w,1,0,-1,w,0,0,2,0,0,-w,-1,0,1,w,1,w^2,0,w^2,1] #CAST 
   GL(5,p)
    ;
  b:=[1,0,1,-w,-w,0,2,0,0,0,1,0,1,w,w,-w^2,0,w^2,1,-1,-w^2,0,w^2,-1,1] #CAST 
   GL(5,p)
    ;
  c:=[2,0,0,0,0,0,1,-w,-w,-1,0,-w^2,1,-1,-w^2,0,-w^2,-1,1,-w^2,0,-1,-w,-w,1] 
   #CAST GL(5,p)
    ;
  d1:=DiagonalMat([-1,1,1,1,1]) #CAST GL(5,p)
    ;
  d2:=DiagonalMat([1,-1,1,1,1]) #CAST GL(5,p)
    ;
  d3:=DiagonalMat([1,1,-1,1,1]) #CAST GL(5,p)
    ;
  d4:=DiagonalMat([1,1,1,-1,1]) #CAST GL(5,p)
    ;
  d5:=DiagonalMat([1,1,1,1,-1]) #CAST GL(5,p)
    ;
  g:=SubStructure(GL(5,p),a,#TODO CLOSURE
    b,c,d1,d2,d3,d4,d5);
  return DerivedSubgroup(g);
end;
;
#  *********************************************************
#  Makes M_11 \leq SL(5, 3).
M11@:=function()
local a,b;
  a:=[0,2,1,0,0,2,1,1,2,2,0,1,1,2,2,1,0,2,2,1,1,2,2,2,0] #CAST GL(5,3)
    ;
  b:=[0,0,2,0,2,1,1,2,2,0,2,2,2,2,2,1,2,1,1,0,2,2,0,2,1] #CAST GL(5,3)
    ;
  return SubStructure(SL(5,3),a,#TODO CLOSURE
    b);
end;
;
#  **************************************************************
#  *
#  * Now the main function; I haven't bothered splitting it into
#  * Coprime and Noncoprime as the behaviour of the subgroups is
#  * not enormously complicated in any case.

InstallGlobalFunction(L5pIdentify@,
function(group,p)
local 
   F,Print,apsl,coprime,diag,ext,ext1,factor,gl,group,homom,i,image,invol,l2_11,
   m11,max,maximals,newgens,o,phi,psl,sl,so5,soc,type,u42;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  Assert(1,IsPrimeInt(p));
  if p mod 5=1 then
    coprime:=false;
  else
    coprime:=true;
  fi;
  o:=Order(group);
  if Print > 1 then
    Print("Making standard group");
  fi;
  gl:=GL(5,p);
  sl:=SL(5,p);
  apsl:=PGammaL2@(5,p);
  factor:=GroupHomomorphismByImages(gl,apsl,
    apsl.1,apsl.2);
  psl:=sl@factor;
  diag:=GL(5,p).1@factor;
  if Print > 1 then
    Print("Setting up isomorphism");
  fi;
  # =v= MULTIASSIGN =v=
  group:=MakeHomomGeneral@(group,5,p,1,psl,apsl,factor:Print:=0);
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
  if coprime then
    if image=psl then
      type:="psl";
      apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.3]));
    else
      Assert(1,image=apsl);
      type:="psl.2";
      apsl:=SubStructure(apsl,newgens);
    fi;
  elif image=psl then
    type:="psl";
    apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.1,apsl.3]));
  elif Size(image)=2*Size(psl) then
    type:="psl.2";
    apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.1]));
    invol:=group.(Ngens(group))@homom;
  elif Size(image)=5*Size(psl) then
    type:="psl.5";
    apsl:=SubStructure(apsl,Concatenation(newgens,[apsl.3]));
  else
    Assert(1,image=apsl);
    type:="aut_psl";
    apsl:=SubStructure(apsl,newgens);
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
  #  
  #  * Reducible - if we have psl or psl.5 then we get 4
  #  * classes of point stabiliser, conjugate in pairs under
  #  * inverse transpose. Otherwise, we get 4 novelties.
  
  if Print > 1 then
    Print("getting reducibles");
  fi;
  if type in Set(["psl","psl.5"]) then
    Add(maximals,SLPointStab@(5,p)@factor);
    for i in [2,3,4] do
      Add(maximals,SLStabOfNSpace@(5,p,i)@factor);
    od;
  else
    for i in [1,2] do
      Add(maximals,SLStabOfNSpaceMeetDual@(5,p,i)@factor);
      Add(maximals,SLStabOfNSpaceMissDual@(5,p,i)@factor);
    od;
  fi;
  if p > 3 then
    if Print > 1 then
      Print("getting imprimitives");
    fi;
    Add(maximals,ImprimsMeetSL@(5,p,5)@factor);
  fi;
  if Print > 1 then
    Print("getting semilinears");
  fi;
  Add(maximals,GammaLMeetSL@(5,p,5)@factor);
  if not coprime then
    ext:=NormaliserOfExtraSpecialGroup@(5,p);
    ext1:=SubStructure(ext,List(Filtered([1..Ngens(ext)]
     ,i->DeterminantMat(ext.i)=1),i->ext.i));
    #  ext1:= NormaliserOfExtraSpecialGroupSL(5, p);
    if type="psl" then
      if Print > 1 then
        Print("getting extraspecials");
      fi;
      maximals:=Concatenation(maximals,ImageCopies@(ext1@factor,5,diag));
    elif type="psl.2" then
      if Print > 1 then
        Print("getting extraspecials");
      fi;
      ext1:=SelectGroupGeneral@(psl,ext1@factor,diag,invol);
      Add(maximals,ext1);
    fi;
  fi;
  if p > 2 then
    so5:=SO(5,p)@factor;
    if coprime then
      if Print > 1 then
        Print("getting orthogonals");
      fi;
      Add(maximals,so5);
    elif type="psl" then
      if Print > 1 then
        Print("getting orthogonals");
      fi;
      maximals:=Concatenation(maximals,ImageCopies@(so5,5,diag));
    elif type="psl.2" then
      if Print > 1 then
        Print("getting orthogonals");
      fi;
      so5:=SelectGroupGeneral@(psl,so5,diag,invol);
      Add(maximals,so5);
    fi;
  fi;
  if Print > 1 then
    Print("getting C_9s");
  fi;
  if p > 3 and not p=11 and IsSquare(p #CAST GF(11)
    ) then
    l2_11:=PSL2_11@(p)@factor;
    if coprime then
      Add(maximals,l2_11);
    elif type="psl" then
      maximals:=Concatenation(maximals,ImageCopies@(l2_11,5,diag));
    elif type="psl.2" then
      l2_11:=SelectGroupGeneral@(psl,l2_11,diag,invol);
      Add(maximals,l2_11);
    fi;
  fi;
  if p > 2 and p mod 6=1 then
    u42:=U4_2@(p)@factor;
    if coprime then
      Add(maximals,u42);
    elif type="psl" then
      maximals:=Concatenation(maximals,ImageCopies@(u42,5,diag));
    elif type="psl.2" then
      u42:=SelectGroupGeneral@(psl,u42,diag,invol);
      Add(maximals,u42);
    fi;
  fi;
  if p=3 and type="psl" then
    m11:=M11@();
    Add(maximals,m11@factor);
    Add(maximals,SubStructure(SL(5,p),TransposedMat(m11.-1),#TODO CLOSURE
      TransposedMat(m11.-2))@factor);
  fi;
  if p=3 and type="psl.2" then
    #  NOVELTY!!!
    if Print > 1 then
      Print("getting novelty");
    fi;
    Add(maximals,PSL2_11@(3)@factor);
  fi;
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);


