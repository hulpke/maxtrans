#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, AssertAttribute, BSGS, Centraliser,
#  ChangeBase, Classes, Cputime, DerivedSubgroup, DiagonalMatrix, Domain,
#  Eltseq, FPGroupStrong, Factorisation, FindGeneratingPElement, Fix, GF, GL,
#  GenG, Generators, GetAlt5, GetSemilin, GetSubfield, Integers,
#  InverseWordMap, IsConjugate, IsSquare, LHS, MakeHomom, Ngens, Order,
#  OtherMaximals, PSL, Parent, PolynomialRing, PrimitiveElement,
#  PslOrPsigmalMaximals, Quotrem, RHS, Random, RandomProcess, ReduceGenerators,
#  Relations, Root, Roots, SL, SetToSequence, Stabiliser, Sylow, WhichGroup,
#  homom

#  Defines: FindGeneratingPElement, GetAlt5, GetSemilin, GetSubfield,
#  L2p2Identify, MakeHomom, OtherMaximals, PslOrPsigmalMaximals, WhichGroup

DeclareGlobalFunction("L2p2Identify@");

#  
#  Constructively recognise and find maximal subgroups  of L(2,p^2).?
#  Recognition by Derek Holt.
#  Maximals by Colva Roney-Dougal

#  *******************************************************
#  * This makes group D_(q+1) = D_(p^2+1) = PGamL(1, p^4)  *
#  * meet PSL(2, p^2).  Tested on all p^2 in range p       *
#  * = [5..500]                                            *
#  *******************************************************
GetSemilin@:=function(group,q)
local d,got_seed_invol,invol,made_semilin,o,proc,r,x,y;
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
  made_semilin:=false;
  while not made_semilin do
    y:=invol^Random(proc);
    if Order(invol*y)=QuotientRemainder(q+1,2) then
      made_semilin:=true;
    fi;
  od;
  return SubStructure(group,invol,#TODO CLOSURE
    y);
end;
;
#  ********************************************************
#  *   This function produces Alt(5), as a group generated
#  *   by two mats [0, 1, -1, 0] and [a, b, c, d] where
#  *   this latter matrix has trace -1 and the product
#  *   has trace (1-sqrt(5)/2)
#  *
#  *
#  * Will be maximal in PSL(2, p^2) whenever Alt(5) is
#  * *not* a subgroup of PSL(2, p). Since Alt(5) is in
#  * PSL(2, p) whenever p^2 eq 1 mod 5, we will find it as
#  * maximal subgroup of PSL(2, p^2) whenever
#  * p^2 eq -1 mod 5.
#  *
#  * Tested on all p^2s congruent to -1 mod 5 in range
#  * [6..10000].
#  *
#  *********************************************************
GetAlt5@:=function(q)
local P,a,b,c,d,f,found,grp,roots,sigma;
  Assert(1,Size(CollectedFactors(q))=1 and IsSquare(q));
  sigma:=((1-Root(5 #CAST GF(q)
    ,2))/2) #CAST GF(q)
    ;
  a:=0 #CAST GF(q)
    ;
  P:=PolynomialRing(GF(q));
  # Implicit generator Assg from previous line.
  b:=P.1;
  found:=false;
  while not found do
    a:=a+1;
    d:=-1-a;
    #  matrix order 3 has trace -1
    f:=a*d-b*(b-sigma)-1;
    roots:=RootsOfUPol(f);
    if Size(roots) > 0 then
      found:=true;
      b:=roots[1][1];
      c:=b-sigma;
    fi;
  od;
  grp:=SubStructure(SL(2,q),[0,1,-1,0] #CAST SL(2,q)
    ,#TODO CLOSURE
    [a,b,c,d] #CAST SL(2,q)
    );
  if not Size(grp)=120 then
    Info(InfoWarning,1,"failed to make Alt(5)");
  fi;
  return grp;
end;
;
#  
#  * The following function returns SL(2, p).2 as a subgroup
#  * of SL(2, p^2). tested on p in [4..100] (p^2 in [16..1000]).

GetSubfield@:=function(sl,p)
local fac,gens,i,newgens,power,two_power,z;
  gens:=SetToSequence(Generators(SL(2,p)));
  newgens:=[];
  #  
  #  * This bit makes SL(2, p).
  
  for i in [1..Size(gens)] do
    Add(newgens,Eltseq(gens[i]) #CAST sl
      );
  od;
  #  
  #  * We now have to extend by an involution.
  
  z:=PrimitiveElement(GF(p^2));
  if p mod 4=1 then
    fac:=CollectedFactors(p^2-1);
    two_power:=2^fac[1][2];
    power:=((p^2-1)/two_power) #CAST Integers()
      ;
    return SubStructure(sl,newgens,#TODO CLOSURE
      DiagonalMat([z^power,z^(-power)]));
  else
    i:=z^((p^2-1)/4) #CAST Integers()
      ;
    return SubStructure(sl,newgens,#TODO CLOSURE
      DiagonalMat([-i,i]));
  fi;
end;
;
#  *********************************************************
#  * There are a total of 5 almost simple groups with socle  *
#  * L_2(p^2). We denote these by "psl", "pgl", "psigmal",   *
#  * "psl.2"  and "pgammal". (this is ATLAS ordering L,      *
#  * L.2_1, L.2_2, L.2_3 and L.2^2, with the exception of    *
#  * L_2(9)=Alt(6) where the ATLAS swaps .2_1 and .2_2)      *
#  *                                                         *
#  * "psl" can be identified by its order                    *
#  * "pgammal" can be identified by its order                *
#  * "pgl" contains elements of order p2 \pm1 that do not    *
#  * lie in psl                                              *
#  * "psigmal" contains elements of order 2p that do not lie *
#  * in psl.                                                 *
#  * "psl.2" contains elements of order 2(p-1) and 2(p+1)    *
#  * that do not lie in psl. depending on the congruence of  *
#  * p mod 4 one or the other of these element orders        *
#  * distinguishes psl.2                                     *
#  *                                                         *
#  * most of the time is taken up with computing the         *
#  * derived subgroup, we return this as well, since it      *
#  * will be useful in other parts of the code.              *
#  *                                                         *
#  * tested for psl, pgl, psigmal, psl.2, pgammal in the     *
#  * range p in [3..1000]                                    *
#  *********************************************************
WhichGroup@:=function(group,q)
local S,fac,ninv,o,order_psl,p,psl;
  fac:=CollectedFactors(q);
  Assert(1,Size(fac)=1);
  Assert(1,fac[1][2]=2);
  #  
  #  * we make p the characteristic of the group (so p eq sqrt(q))
  
  p:=fac[1][1];
  o:=Size(group);
  order_psl:=Size(PSL(2,q));
  if o=order_psl then
    return rec(val1:="psl",
      val2:=group);
  else
    #  "computing derived subgroup";
    psl:=DerivedSubgroup(group);
    if o=order_psl*4 then
      return rec(val1:="pgammal",
        val2:=psl);
    fi;
  fi;
  #   we now have one of the .2s, just have to work out which. 
  #   following does not work
  #  found_initial:= false;
  #  while not found_initial do
  #  x:= Random(group);
  #  if not x in psl then
  #  found_initial:= true;
  #  end if;
  #  end while;
  #  
  #  z:= q mod 4;
  #  two_p_minus_1:= false;
  #  two_p_plus_one:= false;
  #  decided:= false;
  #  while not decided do
  #  o:= Order(x);
  #  if (o eq (q + 1)) or (o eq (q - 1)) then
  #  return "pgl", psl;
  #  elif (o eq 2*p) then
  #  return "psigmal", psl;
  #  elif ((o eq 2*(p+1)) and (z eq 1)) or ((o eq 2*(p-1)) and (z eq
  #  3)) then
  #  return "psl.2", psl;
  #  end if;
  #  x:= x*Random(psl);
  #  end while;
  
  S:=Sylow(group,2);
  ninv:=Size(Filtered(Classes(S),c->c[1]=2));
  if ninv=3 then
    return rec(val1:="pgl",
      val2:=psl);
  elif ninv=7 then
    return rec(val1:="psigmal",
      val2:=psl);
  elif ninv=2 then
    return rec(val1:="psl.2",
      val2:=psl);
  else
    Error("wrong number of involution classes");
  fi;
end;
;
#   MakeHomom functions - DFH
#  * For generators of PSL(2,p), we choose an involution and a p-element.

FindGeneratingPElement@:=function(G,g,p)
#  /out: g should be element returned by FindInvolution(G).
#  * Find a p-element y such that <g,y> = G.

local GenG,proc,y;
  GenG:=function(g,y)
  local i,procb,z;
    #  To test whether G=<g,y>, we do a quick probabilistic test using orders
    procb:=RandomProcess(SubStructure(G,g,#TODO CLOSURE
      y));
    for i in [1..50] do
      z:=Random(procb);
      if (QuoInt(p^2*(p^2-1),2)) mod Order(z)<>0 then
        return true;
      fi;
    od;
    return false;
  end;
  ;
  proc:=RandomProcess(G);
  y:=Tuple([g^Random(proc),Random(proc)]);
  while (Order(y)<>p) or (not GenG(g,y)) do
    y:=Tuple([g^Random(proc),Random(proc)]);
  od;
  return y;
end;
;
#   In the following function, psl, apsl are standard copies of PSL(2,p^2) and
#  * Aut(PSL(2,p^2)) = PGammaL(2,p^2).
#  * group is our unknown almost simple group with socle dgroup isomorphic
#  * to PSL(2,p^2).
#  * We start by defining isomorphism dgroup -> psl and then extend to
#  * monomorphism group -> apsl.

MakeHomom@:=function(dgroup,group,p,psl,apsl,type,conj_invol,field_auto)
#  /out: for generators, we choose an involution (unique class) and
#  another/out: random generating p-element.
local 
   F,Fgens,FtoG,Print,a,a1,ac,ad,b,b1,bc,bd,c,c1,d,d1,dgs,g,gotisom,homom,isc,
   iwm,o1,o2,o3,phi,procdg,procg,procp,psls,r,s,seeking,t,wg,wgtoG,x;
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
  if Print > 1 then
    Print("Got psl gens");
  fi;
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
  if Print > 1 then
    Print("Got word group");
  fi;
  #   now look for required element in group
  a:=FindInvolution@(dgroup);
  b:=FindGeneratingPElement@(dgroup,a,p);
  if Print > 1 then
    Print("Got group gens");
  fi;
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
  if Print > 1 then
    Print("Identified psl");
  fi;
  dgs:=SubStructure(dgroup,a,#TODO CLOSURE
    b);
  AssertAttribute(dgs,"Order",Size(psl));
  homom:=GroupHomomorphismByImages(dgs,apsl,
    GeneratorsOfGroup(dgs),[a1,b1]);
  if type="psl" then
    return rec(val1:=homom,
      val2:=F,
      val3:=phi);
  fi;
  procg:=RandomProcess(group);
  procp:=RandomProcess(psl);
  if type="pgl" or type="pgammal" then
    #   get 2-element in outer automorphism group
    c:=Random(procg);
    while c in dgroup do
      c:=Random(procg);
    od;
    seeking:=type="pgammal";
    while seeking do
      s:=SubStructure(group,dgroup,#TODO CLOSURE
        c);
      AssertAttribute(s,"Order",2*Size(psl));
      if WhichGroup@(s,p^2)="pgl" then
        seeking:=false;
      else
        c:=Random(procg);
        while c in dgroup do
          c:=Random(procg);
        od;
      fi;
    od;
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
    if Print > 1 then
      Print("Identified pgl");
    fi;
    dgs:=SubStructure(group,a,#TODO CLOSURE
      b,c);
    AssertAttribute(dgs,"Order",Size(psl)*2);
    if type="pgl" then
      return rec(val1:=GroupHomomorphismByImages(dgs,apsl,
        GeneratorsOfGroup(dgs),[a1,b1,c1]),
        val2:=F,
        val3:=phi);
    fi;
  fi;
  if type="psigmal" or type="pgammal" then
    #   get 2-element in outer automorphism group
    d:=Random(procg);
    while d in dgroup do
      d:=Random(procg);
    od;
    seeking:=type="pgammal";
    while seeking do
      s:=SubStructure(group,dgroup,#TODO CLOSURE
        d);
      AssertAttribute(s,"Order",2*Size(psl));
      if WhichGroup@(s,p^2)="psigmal" then
        seeking:=false;
      else
        d:=Random(procg);
        while d in dgroup do
          d:=Random(procg);
        od;
      fi;
    od;
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
      Error("psigmal error");
    fi;
    d1:=d1*g;
    if Print > 1 then
      Print("Identified psigmal");
    fi;
    if type="psigmal" then
      dgs:=SubStructure(group,a,#TODO CLOSURE
        b,d);
      AssertAttribute(dgs,"Order",Size(psl)*2);
      return rec(val1:=GroupHomomorphismByImages(dgs,apsl,
        GeneratorsOfGroup(dgs),[a1,b1,d1]),
        val2:=F,
        val3:=phi);
    else
      dgs:=SubStructure(group,a,#TODO CLOSURE
        b,c,d);
      AssertAttribute(dgs,"Order",Size(psl)*4);
      return rec(val1:=GroupHomomorphismByImages(dgs,apsl,
        GeneratorsOfGroup(dgs),[a1,b1,c1,d1]),
        val2:=F,
        val3:=phi);
    fi;
  fi;
  #  remaining case is psl.2
  d:=Random(procg);
  while d in dgroup do
    d:=Random(procg);
  od;
  ad:=(a^d)@homom;
  bd:=(b^d)@homom;
  d1:=conj_invol*field_auto;
  g:=DihedralTrick@(a1^d1,ad,procp);
  d1:=d1*g;
  # =v= MULTIASSIGN =v=
  g:=IsConjugate(Centraliser(psl,ad),b1^d1,bd);
  isc:=g.val1;
  g:=g.val2;
  # =^= MULTIASSIGN =^=
  if not isc then
    Error("psl.2 error");
  fi;
  d1:=d1*g;
  if Print > 1 then
    Print("Identified psl.2");
  fi;
  dgs:=SubStructure(group,a,#TODO CLOSURE
    b,d);
  AssertAttribute(dgs,"Order",Size(psl)*2);
  return rec(val1:=GroupHomomorphismByImages(dgs,apsl,
    GeneratorsOfGroup(dgs),[a1,b1,d1]),
    val2:=F,
    val3:=phi);
end;
;
#  
#  * This function is for the cases PSL(2, p^2) and PSigmaL(p^2).
#  * The input group is always isomorphic to psl(2, p^2), as we find
#  * this when we find the type. q = p^2.

PslOrPsigmalMaximals@:=function(group,q,type,dgroup)
local 
   F,Print,alt5_1,alt5_2,apsl,conj_invol,dh,fac,factor,field_auto,gl,homom,max,
   maximals,p,phi,psl,sl,sub1,sub2,z;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  fac:=CollectedFactors(q);
  Assert(1,Size(fac)=1 and fac[1][2]=2);
  p:=fac[1][1];
  if Print > 1 then
    Info(InfoWarning,1,"Making standard pgl");
  fi;
  gl:=GL(2,p^2);
  apsl:=PGammaLD2@(p^2);
  factor:=GroupHomomorphismByImages(gl,apsl,
    GeneratorsOfGroup(gl),[apsl.1,apsl.2]);
  sl:=SL(2,p^2);
  psl:=sl@factor;
  AssertAttribute(psl,"Order",Size(PSL(2,p^2)));
  if Print > 1 then
    Info(InfoWarning,1,"Making outer involution in PGL");
  fi;
  z:=PrimitiveElement(GF(q));
  conj_invol:=([z,0,0,1] #CAST gl
    )@factor;
  field_auto:=apsl.3;
  if Print > 1 then
    Print("Setting up homomorphisms");
  fi;
  # =v= MULTIASSIGN =v=
  phi:=MakeHomom@(dgroup,group,p,psl,apsl,type,conj_invol,
   field_auto:Print:=Print);
  homom:=phi.val1;
  F:=phi.val2;
  phi:=phi.val3;
  # =^= MULTIASSIGN =^=
  dh:=Domain(homom);
  apsl:=SubStructure(apsl,homom(dh.1),#TODO CLOSURE
    homom(dh.2),conj_invol,field_auto);
  AssertAttribute(apsl,"Order",Size(psl)*4);
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
  Add(maximals,GetSemilin@(psl,q));
  if Print > 1 then
    Info(InfoWarning,1,"Making subfield");
  fi;
  sub1:=GetSubfield@(sl,p)@factor;
  sub2:=sub1^conj_invol;
  Add(maximals,sub1);
  Add(maximals,sub2);
  #   Alt(5). These are C_9 subgroups of PSL(2, q), fusing under PGL(2, q)
  
  if q mod 5=4 then
    if Print > 1 then
      Info(InfoWarning,1,"Making Alt5");
    fi;
    alt5_1:=(GetAlt5@(q)@factor);
    alt5_2:=alt5_1^conj_invol;
    Add(maximals,alt5_1);
    Add(maximals,alt5_2);
  fi;
  if Print > 1 then
    Print("Found maximals in standard copy");
  fi;
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end;
;
#  
#  * The following function returns the maximals of pgl, pgl.2 and
#  * pgammal, intersected with psl. They are the same in each case.
#  * does not include trivialities.

OtherMaximals@:=function(group,q,type,dgroup)
local 
   F,Print,apsl,conj_invol,dh,fac,factor,field_auto,gl,homom,max,maximals,p,phi,
   psl,sl,z;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  fac:=CollectedFactors(q);
  Assert(1,Size(fac)=1 and fac[1][2]=2);
  p:=fac[1][1];
  if Print > 1 then
    Info(InfoWarning,1,"Making standard pgl");
  fi;
  gl:=GL(2,p^2);
  apsl:=PGammaLD2@(p^2);
  factor:=GroupHomomorphismByImages(gl,apsl,
    GeneratorsOfGroup(gl),[apsl.1,apsl.2]);
  if Print > 1 then
    Info(InfoWarning,1,"Making standard psl");
  fi;
  sl:=SL(2,p^2);
  psl:=sl@factor;
  AssertAttribute(psl,"Order",Size(PSL(2,p^2)));
  if Print > 1 then
    Info(InfoWarning,1,"Making outer involution in PGL");
  fi;
  z:=PrimitiveElement(GF(q));
  conj_invol:=([z,0,0,1] #CAST gl
    )@factor;
  field_auto:=apsl.3;
  if Print > 1 then
    Print("Setting up homomorphisms");
  fi;
  # =v= MULTIASSIGN =v=
  phi:=MakeHomom@(dgroup,group,p,psl,apsl,type,conj_invol,
   field_auto:Print:=Print);
  homom:=phi.val1;
  F:=phi.val2;
  phi:=phi.val3;
  # =^= MULTIASSIGN =^=
  dh:=Domain(homom);
  apsl:=SubStructure(apsl,homom(dh.1),#TODO CLOSURE
    homom(dh.2),conj_invol,field_auto);
  AssertAttribute(apsl,"Order",Size(psl)*4);
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
  Add(maximals,GetSemilin@(psl,p^2));
  if Print > 1 then
    Print("Found maximals in standard copy");
  fi;
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end;
;
#  *******************************************************************
#  * The following is the main function. It takes a permutation
#  * group lying between psl(2, p^2) and pgammal(2, p^2),
#  * calls WhichGrp to identify which of the 5 possible groups it is,
#  * and then calls the appropriate maximal subgroups algorithm.

InstallGlobalFunction(L2p2Identify@,
function(group,q)
local Print,derived,fac,max,type;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  fac:=CollectedFactors(q);
  Assert(1,Size(fac)=1 and fac[1][2]=2);
  # =v= MULTIASSIGN =v=
  derived:=WhichGroup@(group,q);
  type:=derived.val1;
  derived:=derived.val2;
  # =^= MULTIASSIGN =^=
  if type="psl" or type="psigmal" then
    return PslOrPsigmalMaximals@(group,q,type,derived:max:=max,Print:=Print);
  else
    return OtherMaximals@(group,q,type,derived:max:=max,Print:=Print);
  fi;
end);


