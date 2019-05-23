#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: ActionGenerators, Append, Centraliser,
#  ChevalleyGroup, Classes, CorrectForm, DiagonalMatrix, Dimension,
#  FPGroupStrong, Factorisation, GF, GL, GModule, Gcd, Generators, GetImprims,
#  GetL2q, GtoSp, Id, IndecomposableSummands, Index, IsConjugate, IsCyclic,
#  IsEven, IsOdd, MakeSp4EvenHomomGeneral, Ngens, NormalSubgroups, PSigmaSp,
#  PSp, PrimitiveElement, Random, RandomSchreier, RecogniseSp4Even, SL,
#  SOMinus, SOPlus, Socle, Sp, Sp4qMaximals, SylowSubgroup, Sym,
#  SymplecticForm, TensorPower, WhichGroup, WreathProduct

#  Defines: GetImprims, GetL2q, MakeSp4EvenHomomGeneral, PSp4qIdentify,
#  Sp4qMaximals, WhichGroup

DeclareGlobalFunction("PSp4qIdentify@");

DeclareGlobalFunction("MakeSp4EvenHomomGeneral@");

#  
#  * This file contains the functions to do the following:
#  * Input: Almost simple group $G$ with Soc(G) = PSp(4,q), and the
#  * prime power p^e. We assume e > 1, as PSp(4, p) was done as
#  * a special case.
#  * Output: Set of maximal subgroups of $G$, intersected with
#  * Soc(G). Trivialities are not returned.
#  *

#  function names:
#  WhichGroup(group, d, q)
#  GetImprims(q)
#  GetL2q(q)
#  SubfieldSp(d, p, e, f)
#  S4qMaximals(group, q)
WhichGroup@:=function(group,d,q)
local 
   biggrp,cls_g,cls_sigma,e,f,fac,info_g,info_sigma,ns,psp,s2,s2sigma,socquot;
  if d=1 then
    return rec(val1:=Socle(group),
      val2:=1);
  fi;
  fac:=CollectedFactors(q);
  e:=fac[1][2];
  Assert(1,d=2);
  psp:=Socle(group);
  Assert(1,Size(psp)=Size(PSp(4,q)));
  # =v= MULTIASSIGN =v=
  f:=Subquo(group,[psp]);
  socquot:=f.val1;
  f:=f.val2;
  # =^= MULTIASSIGN =^=
  if IsOddInt(Size(socquot)) then
    return rec(val1:=psp,
      val2:=2);
  fi;
  if not IsCyclic(socquot) then
    return rec(val1:=psp,
      val2:=0);
  fi;
  s2:=SylowSubgroup(group,2);
  biggrp:=PSigmaSp(4,q);
  ns:=NormalSubgroups(biggrp:IndexLimit:=QuoInt(e,(Size(socquot))));
  Assert(1,(QuoInt(Size(biggrp),ns[1].order))=(QuoInt(e,Size(socquot))));
  s2sigma:=SylowSubgroup(ns[1].subgroup,2);
  cls_g:=Classes(s2);
  cls_sigma:=Classes(s2sigma);
  info_g:=List([1..Size(cls_g)],i->[cls_g[i][1],cls_g[i][2]]);
  info_sigma:=List([1..Size(cls_sigma)],i->[cls_sigma[i][1],cls_sigma[i][2]]);
  if info_g=info_sigma then
    return rec(val1:=psp,
      val2:=2);
  else
    return rec(val1:=psp,
      val2:=0);
  fi;
end;
;
#  ********************************************************************
#  
#  * To make the 2nd group we use act as gens of gl on (e1, e2)
#  * and compensate on f1, f2, or swap the subspaces over.

GetImprims@:=function(q)
local bool,form,g,imprim1,imprim2,newmat1,newmat2,newmat3,x,z;
  z:=PrimitiveElement(GF(q));
  g:=WreathProduct(SP(2,q),SymmetricGroup(2));
  # =v= MULTIASSIGN =v=
  form:=SymplecticForm@(g);
  bool:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  #  "form_g =", form;
  x:=CorrectForm(form,4,q,"symplectic") #CAST GL(4,q)
    ;
  imprim1:=g^x;
  newmat1:=DiagonalMat([z,1,1,z^-1]) #CAST GL(4,q)
    ;
  newmat2:=[-1,1,0,0,-1,0,0,0,0,0,-1,-1,0,0,1,0] #CAST GL(4,q)
    ;
  newmat3:=[0,0,-1,0,0,0,0,-1,1,0,0,0,0,1,0,0] #CAST GL(4,q)
    ;
  imprim2:=SubStructure(GL(4,q),newmat1,#TODO CLOSURE
    newmat2,newmat3);
  return rec(val1:=imprim1,
    val2:=imprim2);
end;
;
#  ****************************************************************
GetL2q@:=function(q)
local bool,form1,g,group,indecs,module,newgroup,power,x;
  g:=SL(2,q);
  module:=GModule(g);
  power:=TensorPower(module,3);
  indecs:=IndecomposableSummands(power);
  Assert(1,newmod:=ForAny(indecs,x->DimensionOfMatrixGroup(x)=4));
  group:=SubStructure(GL(4,q),ActionGenerators(newmod));
  # =v= MULTIASSIGN =v=
  form1:=SymplecticForm@(group);
  bool:=form1.val1;
  form1:=form1.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,bool);
  x:=CorrectForm(form1,4,q,"symplectic") #CAST GL(4,q)
    ;
  newgroup:=group^x;
  return newgroup;
end;
;
#  ***************************************************************
#   this seems to be in subfield.m
#  function SubfieldSp(d, p, e, f)
#  assert IsPrime(p);
#  assert e mod f eq 0;
#  
#  newgens:= [GL(d, p^e)!Sp(d, p^f).i : i in [1, 2]];
#  
#  if IsEven(p) or IsOdd(e div f) then
#  return sub<GL(d, p^e)|newgens>;
#  end if;
#  
#  z:= PrimitiveElement(GF(p^e));
#  l:= d div 2;
#  
#  power:= (p^e-1) div (p^f-1);
#  delta:= GL(d, p^e)!DiagonalMatrix([z^power:i in [1..l]]cat[1:i in [1..l]]);
#  assert IsEven(power);
#  scal_power:= power div 2;
#  Append(~newgens, delta*GL(d, p^e)!ScalarMatrix(d, z^-scal_power));
#  return sub<GL(d, p^e)|newgens>;
#  end function;

#  ******************************************************************
#  *                   The main function                              *
#  *******************************************************************
#  Forward declaration of MakeSp4EvenHomomGeneral
Sp4qMaximals@:=function(group,q)
#  /out:out eq  GCD(q-1,2):e;
local 
   F,Print,a,apsp,b,bool,d,e,e2part,e_fac,fac,factor,form,g,group,grp,gsp,homom,
   mat,max,max1,max2,maximals,newgens,novelties,out_invol,p,phi,psp,si,si2part,
   soc,sominus,sp,subapsp,subgrp_copies,suz,x,z;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  fac:=CollectedFactors(q);
  p:=fac[1][1];
  e:=fac[1][2];
  Assert(1,Size(fac)=1);
  Assert(1,e > 1);
  d:=Gcd(Gcd(q-1,2),e);
  # =v= MULTIASSIGN =v=
  subgrp_copies:=WhichGroup@(group,d,q);
  soc:=subgrp_copies.val1;
  subgrp_copies:=subgrp_copies.val2;
  # =^= MULTIASSIGN =^=
  si:=Index(group,soc);
  # rewritten select statement
  if e mod 2=0 then
    e2part:=CollectedFactors(e)[1][2];
  else
    e2part:=0;
  fi;
  # rewritten select statement
  if si mod 2=0 then
    si2part:=CollectedFactors(si)[1][2];
  else
    si2part:=0;
  fi;
  novelties:=p mod 2=0 and e2part+1=si2part;
  #  that is when the graph automorphism of PSp(4,2^e) is present
  #  and we get novelties.
  if Print > 1 then
    Print("Novelties =",novelties);
  fi;
  if Print > 1 then
    Print("subgrp_copies =",subgrp_copies);
  fi;
  if Print > 1 then
    Print("making standard group");
  fi;
  sp:=SP(4,q);
  gsp:=GSp@(4,q);
  z:=PrimitiveElement(GF(q));
  out_invol:=DiagonalMat([z,z,1,1]) #CAST GL(4,q)
    ;
  # rewritten select statement
  if q mod 2=0 then
    apsp:=AutPSp4@(q);
  else
    apsp:=PGammaSp@(4,q);
  fi;
  factor:=GroupHomomorphismByImages(gsp,apsp,
    GeneratorsOfGroup(gsp),List([1..Ngens(gsp)],i->apsp.i));
  psp:=sp@factor;
  if Print > 1 then
    Info(InfoWarning,1,"Setting up homomorphism");
  fi;
  if p mod 2=1 then
    # =v= MULTIASSIGN =v=
    group:=MakeSpHomomGeneral@(group,4,p,e,psp,apsp,factor:Print:=0);
    homom:=group.val1;
    soc:=group.val2;
    group:=group.val3;
    # =^= MULTIASSIGN =^=
  else
    # =v= MULTIASSIGN =v=
    group:=MakeSp4EvenHomomGeneral@(group,e,psp,apsp,factor:Print:=0);
    homom:=group.val1;
    soc:=group.val2;
    group:=group.val3;
    # =^= MULTIASSIGN =^=
  fi;
  if Print > 1 then
    Print("Calling FPGroupStrong");
  fi;
  # =v= MULTIASSIGN =v=
  phi:=FPGroupStrong(SubStructure(psp,List([1..Ngens(soc)],i->soc.i@homom)));
  F:=phi.val1;
  phi:=phi.val2;
  # =^= MULTIASSIGN =^=
  #  get apsp right
  newgens:=List([1..Ngens(group)],i->group.i@homom);
  subapsp:=SubStructure(apsp,newgens);
  for g in Generators(apsp) do
    if not g in subapsp then
      Add(newgens,g);
      subapsp:=SubStructure(apsp,newgens);
    fi;
  od;
  apsp:=subapsp;
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=apsp,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  if Print > 1 then
    Info(InfoWarning,1,"getting reducibles");
  fi;
  if novelties then
    Add(maximals,NoveltyReduct@(q)@factor);
  else
    #  Append(~maximals, Stabiliser(psp, 1));
    Add(maximals,PointStabSp@(4,q)@factor);
    Add(maximals,IsotropicStabSp@(4,q,2)@factor);
  fi;
  if Print > 1 then
    Info(InfoWarning,1,"getting imprimitives");
  fi;
  if novelties then
    # =v= MULTIASSIGN =v=
    max2:=NoveltyImprims@(q);
    max1:=max2.val1;
    max2:=max2.val2;
    # =^= MULTIASSIGN =^=
    if q > 4 then
      Add(maximals,max1@factor);
    fi;
    Add(maximals,max2@factor);
  else
    # =v= MULTIASSIGN =v=
    b:=GetImprims@(q);
    a:=b.val1;
    b:=b.val2;
    # =^= MULTIASSIGN =^=
    Add(maximals,a@factor);
    if IsOddInt(q) then
      Add(maximals,b@factor);
    fi;
  fi;
  if Print > 1 then
    Info(InfoWarning,1,"getting semilinears");
  fi;
  if novelties then
    Add(maximals,NoveltySemilin@(q)@factor);
  else
    Add(maximals,GammaSp@(4,q,2)@factor);
    if IsOddInt(q) then
      Add(maximals,GammaUMeetSp@(4,q)@factor);
    fi;
  fi;
  e_fac:=CollectedFactors(e);
  if Print > 1 then
    Info(InfoWarning,1,"getting subfields");
  fi;
  for x in e_fac do
    b:=x[1];
    if b=2 and subgrp_copies > 0 then
      grp:=SubfieldSp@(4,p,e,QuoInt(e,b));
      Add(maximals,grp@factor);
      if subgrp_copies > 1 then
        Add(maximals,(grp^out_invol)@factor);
      fi;
    elif b > 2 then
      Add(maximals,SubfieldSp@(4,p,e,QuoInt(e,b))@factor);
    fi;
  od;
  if IsEvenInt(q) then
    if not novelties then
      if Print > 1 then
        Info(InfoWarning,1,"getting orthogonals");
      fi;
      Add(maximals,SOPlus(4,q)@factor);
      sominus:=SOMinus(4,q);
      # =v= MULTIASSIGN =v=
      form:=SymplecticForm@(sominus);
      bool:=form.val1;
      form:=form.val2;
      # =^= MULTIASSIGN =^=
      Assert(1,bool);
      mat:=CorrectForm(form,4,q,"symplectic");
      Add(maximals,(sominus^mat)@factor);
    fi;
    if IsOddInt(e) then
      if Print > 1 then
        Info(InfoWarning,1,"getting suzuki");
      fi;
      suz:=ChevalleyGroup("2B",2,q);
      Add(maximals,suz@factor);
    fi;
  fi;
  #  There is a maximal C_9 subgroup isomorphic to PSL(2, q) whenever
  #  p \geq 5
  if p > 4 then
    if Print > 1 then
      Info(InfoWarning,1,"getting L(2, q)");
    fi;
    a:=GetL2q@(q);
    Add(maximals,a@factor);
  fi;
  return rec(val1:=homom,
    val2:=apsp,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end;
;
InstallGlobalFunction(PSp4qIdentify@,
function(group,q)
local Print,max;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  return Sp4qMaximals@(group,q:max:=max,Print:=Print);
end);

InstallGlobalFunction(MakeSp4EvenHomomGeneral@,
function(group,e,psp,apsp,factor)
local 
   CG,GtoSp,Print,SptoG,ce,d,g,group,h,homom,i,imgens,ims,isc,j,mat,newgens,p,
   pspgens,soc,socle,subgp,subsoc,works;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  soc:=Socle(group);
  #   Reduce number of generators of soc, and
  #  * rearrange generators of group to get those of soc coming first
  
  d:=4;
  p:=2;
  repeat
    newgens:=[Random(soc),Random(soc)];
    subsoc:=SubStructure(soc,newgens);
    RandomSchreier(subsoc);
    
  until subsoc=soc;
  #  
  #  while subsoc ne soc do
  #  x:=Random(soc);
  #  while x in subsoc do x:=Random(soc); end while;
  #  Append(~newgens,x); subsoc := sub<soc|newgens>; RandomSchreier(subsoc);
  #  end while;
  
  soc:=subsoc;
  subgp:=subsoc;
  for g in Generators(group) do
    if not g in subgp then
      Add(newgens,g);
      subgp:=SubStructure(group,newgens);
      RandomSchreier(subgp);
    fi;
  od;
  group:=subgp;
  works:=false;
  while not works do
    # =v= MULTIASSIGN =v=
    SptoG:=RecogniseSp4Even(soc,p^e);
    works:=SptoG.val1;
    GtoSp:=SptoG.val2;
    SptoG:=SptoG.val3;
    # =^= MULTIASSIGN =^=
  od;
  pspgens:=[];
  for i in [1..Ngens(soc)] do
    mat:=GtoSp(soc.i);
    Add(pspgens,mat@factor);
  od;
  #  Now identify images of all generators of group in apsp.
  ims:=pspgens;
  for i in [Ngens(soc)+1..Ngens(group)] do
    g:=group.i;
    CG:=apsp;
    ce:=One(apsp);
    for j in [1..Size(pspgens)] do
      mat:=GtoSp(soc.j^g);
      # =v= MULTIASSIGN =v=
      h:=IsConjugate(CG,pspgens[j]^ce,mat@factor);
      isc:=h.val1;
      h:=h.val2;
      # =^= MULTIASSIGN =^=
      if not isc then
        Error("Conjugation error in Aut(PSp(d,q))");
      fi;
      CG:=Centraliser(CG,mat@factor);
      ce:=ce*h;
    od;
    Add(ims,ce);
  od;
  return rec(val1:=GroupHomomorphismByImages(group,apsp,
    GeneratorsOfGroup(group),ims),
    val2:=soc,
    val3:=group);
end);


