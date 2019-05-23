#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, Centraliser, Classes, DiagonalMatrix,
#  Divisors, Eltseq, FPGroupStrong, Factorisation, GF, GL, Generators,
#  GetImprim, GetSemilin, GetSubfield, GtoSL, Id, IsConjugate, IsCyclic,
#  IsEven, IsOdd, IsPrime, IsProbablyPerfect, MakeHomomGeneral, Ngens, Order,
#  PGammaL, PSL, PrimitiveElement, Quotrem, Random, RandomProcess,
#  RandomSchreier, RecogniseSL, SL, SetToSequence, Socle, Stabiliser,
#  SylowSubgroup, WhichGroup

#  Defines: GetImprim, GetSemilin, GetSubfield, L2qIdentify, MakeHomomGeneral,
#  WhichGroup

DeclareGlobalFunction("L2qIdentify@");

DeclareGlobalFunction("MakeHomomGeneral@");

DeclareGlobalFunction("MakeHomomGeneral@");

#  **********************************************************************
#  here we have some almost simple group with socle PSL(2, q), where q
#  = p^e. Full aut grp is (C_2 \times C_e) if q is odd, and C_e
#  if q is even.
WhichGroup@:=function(group,p,e)
local central_invols,cls,f,o,order_psl,psl,quot,s,subfield_copies;
  Assert(1,IsPrimeInt(p));
  Assert(1,e > 3);
  #  we have done PSL(2, p), PSL(2, p^2) and
  #  PSL(2, p^3) as special cases.
  #   If e is even and q is odd then there are 2 copies of PSL(2,
  #   p^{e/2}).2 that fuse in PGL; therefore we need more details about
  #   which group in PGammaL we have.
  if IsEvenInt(e) and IsOddInt(p) then
    subfield_copies:=2;
  else
    subfield_copies:=1;
  fi;
  #  "computing group order";
  o:=Size(group);
  order_psl:=Size(PSL(2,p^e));
  if o=order_psl then
    return rec(val1:=subfield_copies,
      val2:=group);
  fi;
  #  "computing socle subgroup";
  psl:=Socle(group);
  if subfield_copies=1 then
    return rec(val1:=1,
      val2:=psl);
  fi;
  # =v= MULTIASSIGN =v=
  f:=Subquo(group,[psl]);
  quot:=f.val1;
  f:=f.val2;
  # =^= MULTIASSIGN =^=
  if IsOddInt(Size(quot)) then
    return rec(val1:=2,
      val2:=psl);
  fi;
  if not IsCyclic(quot) then
    #  must contain diagonal automorphism.
    return rec(val1:=0,
      val2:=psl);
  fi;
  #  we now know that we have a copy of PSL which has two maximal
  #  PSL(2, q_0)s in it, extended by a group of even order. The only
  #  question is whether all of the automorphism group corresponds to
  #  field automorphisms (in which case there will be two copies of the
  #  subfield group) or not. We distinguish between the case where all
  #  automorphisms are field automorphisms from the others by looking
  #  to see if the Sylow 2-subgroup contains multiple classes of
  #  involutions that are conjugate only to themselves.
  #  "computing syl2";
  s:=SylowSubgroup(group,2);
  #  "computing classes";
  cls:=Classes(s);
  central_invols:=Filtered(cls,x->x[1]=2 and x[2]=1);
  if Size(central_invols)=3 then
    return rec(val1:=2,
      val2:=psl);
  elif Size(central_invols)=1 then
    return rec(val1:=0,
      val2:=psl);
  else
    Info(InfoWarning,1,"error in which group");
    return rec(val1:=0,
      val2:=_);
  fi;
end;
;
#  ***********************************************************
GetImprim@:=function(q)
local m1,m2,z;
  z:=PrimitiveElement(GF(q));
  m1:=[z,0,0,z^-1] #CAST SL(2,q)
    ;
  m2:=[0,1,-1,0] #CAST SL(2,q)
    ;
  return SubStructure(SL(2,q),m1,#TODO CLOSURE
    m2);
end;
;
#  ************************************************************
#  trying a randomised version to make the semilinear
#  dihedral group, as this actually proved faster before
#  than the deterministic approach.
GetSemilin@:=function(group,q)
local d,goal_order,got_seed_invol,invol,made_semilin,o,proc,r,x,y;
  proc:=RandomProcess(group);
  got_seed_invol:=false;
  while not got_seed_invol do
    x:=Random(proc);
    o:=Order(x);
    # =v= MULTIASSIGN =v=
    r:=QuotientRemainder(o,2);
    d:=r.val1;
    r:=r.val2;
    # =^= MULTIASSIGN =^=
    if r=0 then
      invol:=x^d;
      Assert(1,Order(invol)=2);
      got_seed_invol:=true;
    fi;
  od;
  if IsEvenInt(q) then
    goal_order:=q+1;
  else
    goal_order:=QuoInt((q+1),2);
  fi;
  made_semilin:=false;
  while not made_semilin do
    y:=invol^Random(proc);
    if Order(invol*y)=goal_order then
      made_semilin:=true;
    fi;
  od;
  return SubStructure(group,invol,#TODO CLOSURE
    y);
end;
;
#  *************************************************************
#  we make SL(2, p^f) (possibly extended by an involution) inside
#  SL(2, p^e).
GetSubfield@:=function(p,e,f)
local fac,gens,i,newgens,power,sl,two_power,z;
  sl:=SL(2,p^e);
  gens:=SetToSequence(Generators(SL(2,p^f)));
  newgens:=[];
  for i in [1..Size(gens)] do
    Add(newgens,Eltseq(gens[i]) #CAST sl
      );
  od;
  #  We now extend by an involution if p is odd and e/f is even.
  if IsEvenInt(QuoInt(e,f)) and IsOddInt(p) then
    z:=PrimitiveElement(GF(p^e));
    if p^f mod 4=1 then
      fac:=CollectedFactors(p^e-1);
      two_power:=2^fac[1][2];
      power:=(QuoInt((p^e-1),two_power));
      Add(newgens,DiagonalMat([z^power,z^(-power)]) #CAST sl
        );
    else
      i:=z^(QuoInt((p^e-1),4));
      Add(newgens,DiagonalMat([-i,i]) #CAST sl
        );
    fi;
  fi;
  return SubStructure(sl,newgens);
end;
;
#  *********************************************************************
#  The main function. q is a prime power, where the power is greater
#  than 3. group satisfies PSL(2, q) \leq group \leq PGammaL(2,
#  q). function returns a list of the maximal subgroups of group.
#  no other restrictions on q.
#  Forward declaration of MakeHomomGeneral
InstallGlobalFunction(L2qIdentify@,
function(group,q)
local 
   F,Print,apsl,dh,divs,e,fac,factor,g,gl,group,grp,grp2,homom,max,maximals,
   newgens,outer_invol,p,phi,power,psl,sl,soc,subfield_copies,x,z;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  fac:=CollectedFactors(q);
  Assert(1,Size(fac)=1);
  p:=fac[1][1];
  e:=fac[1][2];
  #  "making standard copy";
  gl:=GL(2,q);
  sl:=SL(2,q);
  apsl:=PGammaL(2,q);
  factor:=GroupHomomorphismByImages(gl,apsl,
    apsl.1,apsl.2);
  psl:=sl@factor;
  if Print > 1 then
    Print("Setting up isomorphism");
  fi;
  # =v= MULTIASSIGN =v=
  soc:=WhichGroup@(group,p,e);
  subfield_copies:=soc.val1;
  soc:=soc.val2;
  # =^= MULTIASSIGN =^=
  #   Reduce number of generators of soc, and
  #  * rearrange generators of group to get those of soc coming first
  
  newgens:=[Random(soc),Random(soc)];
  while SubStructure(soc,newgens)<>soc do
    x:=Random(soc);
    while x in SubStructure(soc,newgens) do
      x:=Random(soc);
    od;
    Add(newgens,x);
  od;
  soc:=SubStructure(soc,newgens);
  for g in Generators(group) do
    if not g in SubStructure(group,newgens) then
      Add(newgens,g);
    fi;
  od;
  group:=SubStructure(group,newgens);
  # =v= MULTIASSIGN =v=
  dh:=MakeHomomGeneral@(group,2,p,e,psl,apsl,factor:Print:=0);
  homom:=dh.val1;
  soc:=dh.val2;
  dh:=dh.val3;
  # =^= MULTIASSIGN =^=
  #  dh := Domain(homom);
  #  ngs := 2;
  #  while dh.(ngs+1) in Socle(dh) do ngs+:=1; end while;
  if Print > 1 then
    Print("Calling FPGroupStrong");
  fi;
  # =v= MULTIASSIGN =v=
  phi:=FPGroupStrong(SubStructure(psl,List([1..Ngens(soc)],i->dh.i@homom)));
  F:=phi.val1;
  phi:=phi.val2;
  # =^= MULTIASSIGN =^=
  newgens:=List([1..Ngens(dh)],i->dh.i@homom);
  for g in Generators(apsl) do
    if not g in SubStructure(apsl,newgens) then
      Add(newgens,g);
    fi;
  od;
  apsl:=SubStructure(apsl,newgens);
  z:=PrimitiveElement(GF(q));
  if subfield_copies=2 then
    outer_invol:=[z,0,0,1] #CAST GL(2,q)
      ;
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
    Print("Getting reducible");
  fi;
  Add(maximals,Stabiliser(psl,1));
  if Print > 1 then
    Print("Getting imprimitive");
  fi;
  Add(maximals,GetImprim@(q)@factor);
  if Print > 1 then
    Print("Getting semilinear");
  fi;
  Add(maximals,GetSemilin@(psl,q));
  if Print > 1 then
    Print("Getting subfield");
  fi;
  divs:=Filtered(DivisorsInt(e),x->IsPrimeInt(x));
  for x in divs do
    power:=QuoInt(e,x);
    if (not x=2) or (subfield_copies=1) then
      if not p^power=2 then
        Add(maximals,GetSubfield@(p,e,power)@factor);
      fi;
    elif subfield_copies=2 then
      grp:=GetSubfield@(p,e,power);
      grp2:=grp^outer_invol;
      Add(maximals,grp@factor);
      Add(maximals,grp2@factor);
    fi;
  od;
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);

#   The following function uses the black-box SL recognition code to set up an
#  * isomorphism between an unknown group isomorphic to PSL(d,p^e) and
#  * the standard copy.
#  * Input parameters:
#  * group is the almost simple group, where it is  known that
#  * Socle(group) ~= PSL(d,p^e).
#  * psl < apsl where apsl is the standard copy of Aut(PSL(d,p^e)).
#  * factor is a homomorphism from the standard copy of GL(d,p^e) to apsl.
#  * homom (group->apsl), socle and group are returned, where group is the same
#  * group but with generators redefined to make those of socle come first.

#   the Black-Box constructive recognition code.
InstallGlobalFunction(MakeHomomGeneral@,
function(group,d,p,e,psl,apsl,factor)
local 
   CG,GtoSL,Print,SLtoG,ce,g,group,h,homom,i,imgens,ims,isc,j,mat,newgens,
   pslgens,soc,socle,subgp,subsoc,works,x;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  if not IsProbablyPerfect(group) then
    soc:=Socle(group);
  else
    soc:=group;
  fi;
  #   Reduce number of generators of soc, and
  #  * rearrange generators of group to get those of soc coming first
  
  if Ngens(soc) > 2 then
    newgens:=[Random(soc),Random(soc)];
    subsoc:=SubStructure(soc,newgens);
    RandomSchreier(subsoc);
    while subsoc<>soc do
      x:=Random(soc);
      while x in subsoc do
        x:=Random(soc);
      od;
      Add(newgens,x);
      subsoc:=SubStructure(soc,newgens);
      RandomSchreier(subsoc);
    od;
    soc:=subsoc;
  fi;
  subgp:=soc;
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
    SLtoG:=RecogniseSL(soc,d,p^e);
    works:=SLtoG.val1;
    GtoSL:=SLtoG.val2;
    SLtoG:=SLtoG.val3;
    # =^= MULTIASSIGN =^=
  od;
  pslgens:=[];
  for i in [1..Ngens(soc)] do
    mat:=GtoSL(soc.i);
    Add(pslgens,mat@factor);
  od;
  #  Now identify images of all generators of group in apsl.
  ims:=pslgens;
  for i in [Ngens(soc)+1..Ngens(group)] do
    g:=group.i;
    CG:=apsl;
    ce:=One(apsl);
    for j in [1..Size(pslgens)] do
      mat:=GtoSL(soc.j^g);
      # =v= MULTIASSIGN =v=
      h:=IsConjugate(CG,pslgens[j]^ce,mat@factor);
      isc:=h.val1;
      h:=h.val2;
      # =^= MULTIASSIGN =^=
      if not isc then
        Error("Conjugation error in Aut(PSL(d,q))");
      fi;
      CG:=Centraliser(CG,mat@factor);
      ce:=ce*h;
    od;
    Add(ims,ce);
  od;
  return rec(val1:=GroupHomomorphismByImages(group,apsl,
    GeneratorsOfGroup(group),ims),
    val2:=soc,
    val3:=group);
end);


