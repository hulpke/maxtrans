#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, AssertAttribute, BSGS, Centraliser,
#  ChangeBase, Cputime, DerivedGroup, Domain, Eltseq, FPGroupStrong,
#  Factorisation, FindGeneratingPElement, Fix, GF, GL, GenG, Generators,
#  GetL2p3Semilin, GetSubfield, Index, Integers, InverseWordMap, IsConjugate,
#  IsPrime, LHS, MakeHomom, Ngens, Order, PSL, Parent, PrimitiveElement,
#  Quotrem, RHS, Random, RandomProcess, ReduceGenerators, Relations, SL,
#  SetToSequence, Stabiliser, homom

#  Defines: FindGeneratingPElement, GetL2p3Semilin, GetSubfield, L2p3Identify,
#  MakeHomom

DeclareGlobalFunction("L2p3Identify@");

#  
#  Constructively recognise and find maximal subgroups  of L(2,p^3).?
#  Recognition by Derek Holt.
#  Maximals by Colva Roney-Dougal

#   This function produces the semilinear group, by
#  * looking for a random pair of involutions that
#  * generate a dihedral group of the correct order, p+1.
#  * input is a group isomorphic to PSL and the prime p. In practice
#  * this is currently used with the *standard* copy of PSL, as this
#  * is likely to have smaller degree than the "black box" PSL generated
#  * by the user.

GetL2p3Semilin@:=function(group,p)
local got_seed_invol,invol,made_semilin,o,proc,q,r,x,y;
  proc:=RandomProcess(group);
  got_seed_invol:=false;
  while not got_seed_invol do
    x:=Random(proc);
    o:=Order(x);
    # =v= MULTIASSIGN =v=
    r:=QuotientRemainder(o,2);
    q:=r.val1;
    r:=r.val2;
    # =^= MULTIASSIGN =^=
    if r=0 then
      invol:=x^q;
      got_seed_invol:=true;
      #  "invol = ", invol;
    fi;
  od;
  made_semilin:=false;
  while not made_semilin do
    y:=invol^Random(proc);
    #  "Order of product =", Order(invol*y);
    if Order(invol*y)=((p^3+1)/2) #CAST Integers()
       then
      made_semilin:=true;
    fi;
  od;
  return SubStructure(group,invol,#TODO CLOSURE
    y);
end;
;
#  ******************************************************
#  
#  * This function produces the subfield group SL(2, p) < SL(2, p^3). This is
#  * maximal.

GetSubfield@:=function(sl,p)
local gens,i,newgens;
  gens:=SetToSequence(Generators(SL(2,p)));
  newgens:=[];
  for i in [1..Size(gens)] do
    Add(newgens,Eltseq(gens[i]) #CAST sl
      );
  od;
  return SubStructure(sl,newgens);
end;
;
FindGeneratingPElement@:=function(G,g,p)
#  /out: g should be element returned by FindInvolution(G).
#  * Find a p-element y such that <g,y> = G.

local GenG,proc,y,z;
  GenG:=function(g,y)
  local i,procb,z;
    #  To test whether G=<g,y>, we do a quick probabilistic test using orders
    procb:=RandomProcess(SubStructure(G,g,#TODO CLOSURE
      y));
    for i in [1..50] do
      z:=Random(procb);
      if (p^3*(p^3-1)*15) mod Order(z)<>0 then
        return true;
      fi;
    od;
    return false;
  end;
  ;
  proc:=RandomProcess(G);
  y:=Random(proc);
  #  while  y eq Id(G) or (p^3 - 1) mod Order(y) ne 0 do
  while Order(y) <= 2 or (p^3-1) mod Order(y)<>0 do
    y:=Random(proc);
  od;
  z:=Tuple([y,y^Random(proc)]);
  while (Order(z)<>p) or (not GenG(g,z)) do
    z:=Tuple([y,y^Random(proc)]);
  od;
  return z;
end;
;
#   In the following function, psl, apsl are standard copies of PSL(2,p^3) and
#  * Aut(PSL(2,p^3)) = PGammaL(2,p^3).
#  * group is our unknown almost simple group with socle dgroup isomorphic
#  * to PSL(2,p^3).
#  * We start by defining isomorphism dgroup -> psl and then extend to
#  * monomorphism group -> apsl.

MakeHomom@:=function(dgroup,group,p,psl,apsl,conj_invol,field_auto)
#  /out: for generators, we choose an involution (unique class) and
#  another/out: random generating p-element.
local 
   F,Fgens,FtoG,Print,a,a1,ac,ad,b,b1,bc,bd,c,c1,d,d1,dgs,g,gotisom,homom,ind,
   isc,iwm,o1,o2,o3,phi,procdg,procg,procp,psls,r,t,wg,wgtoG,x;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  a1:=FindInvolution@(psl);
  b1:=FindGeneratingPElement@(psl,a1,p);
  #   try getting b1 to fix 1 - may help FPGroupStrong!
  for x in Fix(b1) do
    # =v= MULTIASSIGN =v=
    g:=IsConjugate(psl,x,1);
    isc:=g.val1;
    g:=g.val2;
    # =^= MULTIASSIGN =^=
    if isc then
      a1:=a1^g;
      b1:=b1^g;
      break;
    fi;
  od;
  #   set up word group for isomorphism test
  psls:=SubStructure(psl,a1,#TODO CLOSURE
    b1);
  AssertAttribute(psls,"Order",Size(psl));
  ChangeBase(psls,[1]);
  BSGS(psls);
  ReduceGenerators(psls);
  t:=Cputime();
  # =v= MULTIASSIGN =v=
  phi:=FPGroupStrong(psls);
  F:=phi.val1;
  phi:=phi.val2;
  # =^= MULTIASSIGN =^=
  if Print > 0 then
    Print("Time for FPGroupStrong:",Cputime(t));
  fi;
  iwm:=InverseWordMap(psls);
  Fgens:=List([1..Ngens(F)],i->F.i@phi@iwm);
  wg:=Parent(Fgens[1]);
  #   now look for required element in group
  a:=FindInvolution@(dgroup);
  b:=FindGeneratingPElement@(dgroup,a,p);
  procdg:=RandomProcess(dgroup);
  gotisom:=false;
  o1:=Order(a1*b1);
  o2:=Order(a1*b1^-1);
  o3:=Order(Tuple([a1,b1]));
  while not gotisom do
    #  print "looping";
    if Order(a*b)<>o1 or Order(a*b^-1)<>o2 or Order(Tuple([a,b]))<>o3 then
      b:=b^Random(procdg);
      continue;
    fi;
    wgtoG:=GroupHomomorphismByImages(wg,dgroup,
      GeneratorsOfGroup(wg),[a,b]);
    FtoG:=GroupHomomorphismByImages(F,dgroup,
      GeneratorsOfGroup(F),List(Fgens,g->g@wgtoG));
    gotisom:=true;
    for r in Relations(F) do
      if not LHS(r)@FtoG=RHS(r)@FtoG then
        gotisom:=false;
        break;
      fi;
    od;
    if not gotisom then
      b:=b^Random(procdg);
    fi;
  od;
  dgs:=SubStructure(dgroup,a,#TODO CLOSURE
    b);
  AssertAttribute(dgs,"Order",Size(psl));
  homom:=GroupHomomorphismByImages(dgs,apsl,
    GeneratorsOfGroup(dgs),[a1,b1]);
  ind:=Index(group,dgroup);
  if ind=1 then
    return rec(val1:=homom,
      val2:=F,
      val3:=phi);
  fi;
  procg:=RandomProcess(group);
  procp:=RandomProcess(psl);
  if ind=2 or ind=6 then
    #   get 2-element in outer automorphism group
    c:=Random(procg);
    while c^3 in dgroup do
      c:=Random(procg);
    od;
    if not c^2 in dgroup then
      c:=c^3;
    fi;
    ac:=(a^c)@homom;
    bc:=(b^c)@homom;
    c1:=conj_invol;
    g:=DihedralTrick@(a1^c1,ac,procp);
    c1:=c1*g;
    # =v= MULTIASSIGN =v=
    g:=IsConjugate(Centraliser(psl,ac),b1^c1,bc);
    isc:=g.val1;
    g:=g.val2;
    # =^= MULTIASSIGN =^=
    if not isc then
      Error("pgl error");
    fi;
    c1:=c1*g;
    dgs:=SubStructure(group,a,#TODO CLOSURE
      b,c);
    AssertAttribute(dgs,"Order",Size(psl)*2);
    if ind=2 then
      return rec(val1:=GroupHomomorphismByImages(dgs,apsl,
        GeneratorsOfGroup(dgs),[a1,b1,c1]),
        val2:=F,
        val3:=phi);
    fi;
  fi;
  #   get 3-element in outer automorphism group
  d:=Random(procg);
  while d^2 in dgroup do
    d:=Random(procg);
  od;
  if not d^3 in dgroup then
    d:=d^2;
  fi;
  ad:=(a^d)@homom;
  bd:=(b^d)@homom;
  d1:=field_auto;
  g:=DihedralTrick@(a1^d1,ad,procp);
  d1:=d1*g;
  # =v= MULTIASSIGN =v=
  g:=IsConjugate(Centraliser(psl,ad),b1^d1,bd);
  isc:=g.val1;
  g:=g.val2;
  # =^= MULTIASSIGN =^=
  if not isc then
    #  d1^2 should do the trick
    d1:=d1^2;
    g:=DihedralTrick@(a1^d1,ad,procp);
    d1:=d1*g;
    # =v= MULTIASSIGN =v=
    g:=IsConjugate(Centraliser(psl,ad),b1^d1,bd);
    isc:=g.val1;
    g:=g.val2;
    # =^= MULTIASSIGN =^=
    if not isc then
      Error("psigmal error");
    fi;
  fi;
  d1:=d1*g;
  if ind=3 then
    dgs:=SubStructure(group,a,#TODO CLOSURE
      b,d);
    AssertAttribute(dgs,"Order",Size(psl)*3);
    return rec(val1:=GroupHomomorphismByImages(dgs,apsl,
      GeneratorsOfGroup(dgs),[a1,b1,d1]),
      val2:=F,
      val3:=phi);
  fi;
  dgs:=SubStructure(group,a,#TODO CLOSURE
    b,c,d);
  AssertAttribute(dgs,"Order",Size(psl)*6);
  return rec(val1:=GroupHomomorphismByImages(dgs,apsl,
    GeneratorsOfGroup(dgs),[a1,b1,c1,d1]),
    val2:=F,
    val3:=phi);
end;
;
#  ******************************************************************
#  *                   The main function                              *
#  * The intersections of _any_ almost simple group with socle        *
#  * PSL(2, p^3) are the point stabiliser; D_{p^3 - 1}, the           *
#  * imprimitive group; D_{p^3 + 1}, the superfield group;            *
#  * and PSL(2, p). We get one copy of each.                          *
#  *******************************************************************
InstallGlobalFunction(L2p3Identify@,
function(group,q)
local 
   F,Print,apsl,conj_invol,dgroup,dh,fac,factor,field_auto,gl,homom,max,
   maximals,p,phi,psl,sl,z;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  fac:=CollectedFactors(q);
  Assert(1,Size(fac)=1 and fac[1][2]=3);
  p:=fac[1][1];
  Assert(1,IsPrimeInt(p));
  Assert(1,p > 2);
  if Print > 1 then
    Info(InfoWarning,1,"Making standard pgl");
  fi;
  gl:=GL(2,q);
  sl:=SL(2,q);
  apsl:=PGammaLD2@(q);
  factor:=GroupHomomorphismByImages(gl,apsl,
    GeneratorsOfGroup(gl),[apsl.1,apsl.2]);
  psl:=sl@factor;
  AssertAttribute(psl,"Order",Size(PSL(2,q)));
  if Print > 1 then
    Info(InfoWarning,1,"Making outer involution in PGL");
  fi;
  z:=PrimitiveElement(GF(q));
  conj_invol:=([z,0,0,1] #CAST gl
    )@factor;
  field_auto:=apsl.3;
  dgroup:=DerivedGroup(group);
  if Print > 1 then
    Print("Setting up homomorphisms");
  fi;
  # =v= MULTIASSIGN =v=
  phi:=MakeHomom@(dgroup,group,p,psl,apsl,conj_invol,field_auto:Print:=Print);
  homom:=phi.val1;
  F:=phi.val2;
  phi:=phi.val3;
  # =^= MULTIASSIGN =^=
  dh:=Domain(homom);
  apsl:=SubStructure(apsl,homom(dh.1),#TODO CLOSURE
    homom(dh.2),conj_invol,field_auto);
  AssertAttribute(apsl,"Order",Size(psl)*6);
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=apsl,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  if Print > 1 then
    Info(InfoWarning,1,"Making reducible");
  fi;
  Add(maximals,Stabiliser(psl,1));
  if Print > 1 then
    Info(InfoWarning,1,"Making imprimitive");
  fi;
  Add(maximals,Stabiliser(psl,Set([1,2])));
  if Print > 1 then
    Info(InfoWarning,1,"Making semilinear");
  fi;
  Add(maximals,GetL2p3Semilin@(psl,p));
  if Print > 1 then
    Info(InfoWarning,1,"Getting subfield");
  fi;
  Add(maximals,(GetSubfield@(sl,p)@factor));
  if Print > 1 then
    Print("Found maximals in standard copy");
  fi;
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);


