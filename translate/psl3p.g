#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, AssertAttribute, BSGS, Centraliser,
#  ChangeBase, Coefficients, CoprimeMaximals, Cputime, DefiningPolynomial,
#  DerivedGroup, DerivedSubgroup, Determinant, DiagonalMatrix, Domain, Eltseq,
#  FPGroupStrong, Factorisation, FindCentralPElement, FindGeneratingPElement,
#  Fix, GF, GL, GenG, Generators, GetAlt6, GetExtraspec, GetImprims,
#  GetLineStab, GetPSL2_7, GetPointMeetLine, GetPointStab, GetPointUnmeetLine,
#  GetSLTorus, GetSemilin, Index, Integers, InverseWordMap, IsConjugate,
#  IsSquare, L3_8Maximals, L3_9Maximals, LHS, MakeHomom, MakeHomoml39, Ngens,
#  NonCoprimeMaximals, Order, PSL, Parent, PrimitiveElement, RHS, Random,
#  RandomProcess, ReduceGenerators, Relations, RootOfUnity, SL, SO,
#  SelectGroup, SetToSequence, SquareRoot, WhichGroupl38, WhichGroupl39, homom

#  Defines: CoprimeMaximals, FindCentralPElement, FindGeneratingPElement,
#  GetAlt6, GetExtraspec, GetImprims, GetLineStab, GetPSL2_7, GetPointMeetLine,
#  GetPointStab, GetPointUnmeetLine, GetSLTorus, GetSemilin, L3_8Maximals,
#  L3_9Maximals, L3pIdentify, MakeHomom, MakeHomoml39, NonCoprimeMaximals,
#  SelectGroup, WhichGroupl38, WhichGroupl39

DeclareGlobalFunction("L3pIdentify@");

#  
#  Constructively recognise and find maximal subgroups  of L(3,p).?
#  Recognition by Derek Holt.
#  Maximals by Colva Roney-Dougal.

#  This function returns the maximal C_9 group 3.Alt(6), which occurs whenever
#  *5 is a square in the field GF(p^e), and GF(p^e) contains a cube root
#  *of unity. tested on primes p in range [1..10000].

GetAlt6@:=function(q)
local b5,group,h,half,hbar,omega,r5;
  Assert(1,Size(CollectedFactors(q))=1);
  Assert(1,IsSquare(5 #CAST GF(q)
    ));
  r5:=SquareRoot(5 #CAST GF(q)
    );
  b5:=((-1+r5)/2) #CAST GF(q)
    ;
  omega:=RootOfUnity(3,GF(q));
  h:=omega-b5;
  hbar:=omega^2-b5;
  #  b5 real, omegabar = omega^2
  half:=(2^-1) #CAST GF(q)
    ;
  Assert(1,omega in GF(q));
  group:=SubStructure(GL(3,q),[-1,0,0,0,-1,0,0,0,1],#TODO CLOSURE
    [0,1,0,0,0,1,1,0,0],[-1,0,0,0,0,-1,0,-1,0]
   ,[half,-half,-h*half,-half,half,-h*half,hbar*half,hbar*half,0]);
  return group;
end;
;
GetExtraspec@:=function(p)
local a,b,c,d,grp,newgrp,ninth,omega,z;
  z:=PrimitiveElement(GF(p));
  omega:=z^((p-1)/3) #CAST Integers()
    ;
  if p mod 9=1 then
    ninth:=z^((p-1)/9) #CAST Integers()
      ;
  fi;
  a:=DiagonalMat([1,omega,omega^2]) #CAST GL(3,p)
    ;
  b:=[0,1,0,0,0,1,1,0,0] #CAST GL(3,p)
    ;
  if p mod 9=1 then
    c:=DiagonalMat([ninth^2,ninth^5,ninth^2]) #CAST GL(3,p)
      ;
  else
    c:=DiagonalMat([1,omega,1]) #CAST GL(3,p)
      ;
  fi;
  d:=[1,1,1,1,omega,omega^2,1,omega^2,omega] #CAST GL(3,p)
    ;
  grp:=SubStructure(GL(3,p),a,#TODO CLOSURE
    b,c,d);
  newgrp:=Intersection(grp,SL(3,p));
  return newgrp;
end;
;
#  tested on prime p in the range 1..1000.
GetImprims@:=function(p)
local grp,m1,m2,m3,z;
  z:=PrimitiveElement(GF(p));
  m1:=DiagonalMat([z,1,z^-1]) #CAST SL(3,p)
    ;
  m2:=[0,1,0,0,0,1,1,0,0] #CAST SL(3,p)
    ;
  m3:=[-1,0,0,0,0,-1,0,-1,0] #CAST SL(3,p)
    ;
  grp:=SubStructure(SL(3,p),m1,#TODO CLOSURE
    m2,m3);
  #  assert #grp eq (p-1)^2*6;
  return grp;
end;
;
#  This function produces the C_9 group PSL(2, 7), which occurs
#  *whenever Root(-7) lies in the field. The matrices come from the
#  *Atlas "Reflection" construction. Tested on primes p in range 7..10000.

GetPSL2_7@:=function(q)
local group,half,quarter,sqrt,z;
  Assert(1,q > 3 and not q=7);
  Assert(1,Size(CollectedFactors(q))=1);
  z:=(-7) #CAST GF(q)
    ;
  Assert(1,IsSquare(z));
  sqrt:=SquareRoot(z);
  half:=(2^-1) #CAST GF(q)
    ;
  quarter:=(4^-1) #CAST GF(q)
    ;
  group:=SubStructure(SL(3,q),DiagonalMat([1,-1,-1]) #CAST SL(3,q)
    ,#TODO CLOSURE
    [-1,0,0,0,0,-1,0,-1,0] #CAST SL(3,q)
    ,[0,-1,0,-1,0,0,0,0,-1] #CAST SL(3,q)
    ,[-half,half,(-1+sqrt)*quarter,half,-half,(-1+sqrt)*quarter,(-1-sqrt)
   *quarter,(-1-sqrt)*quarter,0] #CAST SL(3,q)
    );
  Assert(1,Size(group)=168);
  return group;
end;
;
GetSLTorus@:=function(p,sl)
local a,b,z;
  z:=PrimitiveElement(GF(p));
  a:=DiagonalMat([z,1,z^-1]) #CAST sl
    ;
  b:=DiagonalMat([z,z^-1,1]) #CAST sl
    ;
  return SubStructure(sl,a,#TODO CLOSURE
    b);
end;
;
#  
#  * Point_meet_line is all matrices of shape
#  *          [*, *, *
#  *           0, *, *,
#  *           0, 0, *];
#  * where the point is <(0, 0, 1)> and the line is {(0, a, b)}.
#  * Tested for having correct order on all primes in range [1..100].

GetPointMeetLine@:=function(p,sl)
local a,b,c,group,torus;
  torus:=GetSLTorus@(p,sl);
  a:=[1,1,0,0,1,0,0,0,1] #CAST sl
    ;
  b:=[1,0,1,0,1,0,0,0,1] #CAST sl
    ;
  c:=[1,0,0,0,1,1,0,0,1] #CAST sl
    ;
  group:=SubStructure(sl,torus,#TODO CLOSURE
    a,b,c);
  return group;
end;
;
#  
#  * Point_unmeet_line is all matrices of shape
#  *        [*, 0, 0,
#  *         0, *, *,
#  *         0, *, *];
#  * where the point is <(1, 0, 0)> and the line is {(0, a, b)}.
#  * We generate it by taking the generators for GL(2, p) and
#  * correcting the determinant using hte [1][1] position.
#  * Tested for correct order on all primes in range [1..100].

GetPointUnmeetLine@:=function(p,sl)
local d,gens,i,list,newgens;
  gens:=SetToSequence(Generators(GL(2,p)));
  newgens:=[];
  for i in [1..Size(gens)] do
    d:=DeterminantMat(gens[i]);
    list:=Eltseq(gens[i]);
    Add(newgens,[d^-1,0,0,0,list[1],list[2],0,list[3],list[4]] #CAST sl
      );
  od;
  return SubStructure(sl,newgens);
end;
;
#  
#  * The basic reducibles are just the point stabiliser and the line
#  * stabiliser. point stabiliser is the stabiliser of <(1, 0, 0)>,
#  * line stabiliser is the stabiliser of <(0, a, b)>. Tested for being
#  * correct order on all primes in the range [1..100].

GetLineStab@:=function(p,sl)
local group;
  group:=SubStructure(sl,GetPointUnmeetLine@(p,sl),#TODO CLOSURE
    [1,1,0,0,1,0,0,0,1],[1,0,1,0,1,0,0,0,1]);
  return group;
end;
;
GetPointStab@:=function(p,sl)
local group;
  group:=SubStructure(sl,GetPointUnmeetLine@(p,sl),#TODO CLOSURE
    [1,0,0,1,1,0,0,0,1],[1,0,0,0,1,0,1,0,1]);
  return group;
end;
;
GetSemilin@:=function(p,sl,gl)
#  /out:"making Singer Cycle";
local coeffs,cxp,cxp2,det,field_auto,grp,mat,newelt,o,pol,x;
  pol:=DefiningPolynomial(GF(p^3));
  x:=Parent(pol).1;
  coeffs:=Coefficients(pol);
  mat:=[0,1,0,0,0,1,-coeffs[1],-coeffs[2],-coeffs[3]] #CAST gl
    ;
  #  "putting cycle into sl";
  det:=DeterminantMat(mat);
  o:=Order(det);
  newelt:=Eltseq(mat^o) #CAST sl
    ;
  #  find field automorphism - the reason that x^3 has been added to the
  #  argument below is to ensured that cxp[2] and cxp2[2] are always defined!
  cxp:=Coefficients(x^3+x^p mod pol);
  cxp2:=Coefficients(x^3+(x^2)^p mod pol);
  field_auto:=[1,0,0,cxp[1],cxp[2],cxp[3],cxp2[1],cxp2[2],cxp2[3]] #CAST sl
    ;
  grp:=SubStructure(sl,newelt,#TODO CLOSURE
    field_auto);
  return grp;
end;
;
#  ****************************************************
#  * The following function is used in the noncoprime   *
#  * case - we start by making 3 copies of a group,     *
#  * which are conjugate under the outer 3-cycle.       *
#  * a unique one of these will commute with our        *
#  * given involution, so in the case psl.2 we require  *
#  * this to be appended to the list of maximals        *
#  ****************************************************
SelectGroup@:=function(psl,initial,three_cyc,invol)
local group,i,looking;
  looking:=true;
  for i in [0..2] do
    group:=initial^(three_cyc^i);
    if IsConjugate(psl,group,group^invol) then
      looking:=false;
      break;
    fi;
  od;
  if looking then
    Info(InfoWarning,1,"Error normalising subgroup in PSL.2");
  fi;
  return group;
end;
;
#   MakeHomom functions - DFH
#  * For generators of PSL(3,p), we choose an involution and a non-central
#  * p-element. These are in unique p-classes.

FindCentralPElement@:=function(G,p)
local foundelt,o,proc,x;
  proc:=RandomProcess(G);
  foundelt:=false;
  while not foundelt do
    x:=Random(proc);
    o:=Order(x);
    if o > p and o mod p=0 then
      x:=x^(QuoInt(o,p));
      foundelt:=true;
    fi;
  od;
  return x;
end;
;
FindGeneratingPElement@:=function(G,g,x,p)
#  /out: g should be element returned by FindInvolution(G), and
#  * x as returned by FindCentralPElement(G,p).
#  * Find a p-element y such that <g,y> = G.

local GenG,proc,y;
  GenG:=function(g,y)
  local i,procb,z;
    #  To test whether G=<g,y>, we do a quick probabilistic test using orders
    procb:=RandomProcess(SubStructure(G,g,#TODO CLOSURE
      y));
    for i in [1..50] do
      z:=Random(procb);
      if (p^2*(p^2-1)*(p^2-p)) mod Order(z)<>0 then
        return true;
      fi;
    od;
    return false;
  end;
  ;
  proc:=RandomProcess(G);
  y:=Tuple([x,Random(proc)]);
  while (Order(y)<>p) or (not GenG(g,y)) do
    y:=Tuple([x^Random(proc),Random(proc)]);
  od;
  return y;
end;
;
#   In the following function, psl, apsl are standard copies of PSL(3,p) and
#  * Aut(PSL(3,p)).
#  * group is our unknown almost simple group with socle dgroup isomorphic
#  * to PSL(3,p).
#  * we start by defining isomorphism dgroup -> psl and then extend to
#  * monomorphism group -> apsl.

MakeHomom@:=function(dgroup,group,p,psl,apsl)
#  /out: for generators, we choose an involution (unique class) and
#  another/out: random generating element.
local 
   F,Fgens,FtoG,Print,a,a1,ac,ad,b,b1,bc,bd,c,c1,d,d1,dgs,g,gotisom,homom,isc,
   iwm,o1,o2,o3,phi,procap,procdg,procg,procp,psi,psls,r,t,wg,wgtoG,x;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  if p=8 then
    # =v= MULTIASSIGN =v=
    b1:=FindGoodGens@(psl,21);
    a1:=b1.val1;
    b1:=b1.val2;
    # =^= MULTIASSIGN =^=
    psls:=SubStructure(psl,a1,#TODO CLOSURE
      b1);
    AssertAttribute(psls,"Order",Size(psl));
    # =v= MULTIASSIGN =v=
    phi:=FPGroupStrong(psls);
    F:=phi.val1;
    phi:=phi.val2;
    # =^= MULTIASSIGN =^=
    # =v= MULTIASSIGN =v=
    b:=FindGoodGens@(dgroup,21);
    a:=b.val1;
    b:=b.val2;
    # =^= MULTIASSIGN =^=
  else
    a1:=FindInvolution@(psl);
    x:=FindCentralPElement@(psl,p);
    b1:=FindGeneratingPElement@(psl,a1,x,p);
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
    x:=FindCentralPElement@(dgroup,p);
    b:=FindGeneratingPElement@(dgroup,a,x,p);
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
  fi;
  if Print > 1 then
    Info(InfoWarning,1,"Identified psl");
  fi;
  dgs:=SubStructure(dgroup,a,#TODO CLOSURE
    b);
  AssertAttribute(dgs,"Order",Size(psl));
  homom:=GroupHomomorphismByImages(dgs,apsl,
    GeneratorsOfGroup(dgs),[a1,b1]);
  if dgroup=group then
    return rec(val1:=homom,
      val2:=F,
      val3:=phi);
  fi;
  procg:=RandomProcess(group);
  procap:=RandomProcess(apsl);
  procp:=RandomProcess(psl);
  if Index(group,dgroup) mod 3=0 then
    #   first deal with 3-element in outer automorphism group
    c:=Random(procg);
    while c^2 in dgroup or not c^3 in dgroup do
      c:=Random(procg);
    od;
    ac:=(a^c)@homom;
    bc:=(b^c)@homom;
    c1:=Random(procap);
    while c1^2 in psl or not c1^3 in psl do
      c1:=Random(procap);
    od;
    g:=DihedralTrick@(a1^c1,ac,procp);
    c1:=c1*g;
    # =v= MULTIASSIGN =v=
    g:=IsConjugate(Centraliser(psl,ac),b1^c1,bc);
    isc:=g.val1;
    g:=g.val2;
    # =^= MULTIASSIGN =^=
    if not isc then
      #  c1^2 should do the trick
      c1:=c1^2;
      g:=DihedralTrick@(a1^c1,ac,procp);
      c1:=c1*g;
      # =v= MULTIASSIGN =v=
      g:=IsConjugate(Centraliser(psl,ac),b1^c1,bc);
      isc:=g.val1;
      g:=g.val2;
      # =^= MULTIASSIGN =^=
    fi;
    c1:=c1*g;
    if Print > 1 then
      Print("Identified psl.3");
    fi;
    dgs:=SubStructure(group,a,#TODO CLOSURE
      b,c);
    AssertAttribute(dgs,"Order",Size(psl)*3);
    if Index(group,dgroup)=3 then
      return rec(val1:=GroupHomomorphismByImages(dgs,apsl,
        GeneratorsOfGroup(dgs),[a1,b1,c1]),
        val2:=F,
        val3:=phi);
    fi;
    #    now with 2-element in outer automorphism group
    d:=Random(procg);
    while d^3 in dgroup or not d^2 in dgroup do
      d:=Random(procg);
    od;
    ad:=(a^d)@homom;
    bd:=(b^d)@homom;
    d1:=Random(procap);
    while d1^3 in psl or not d1^2 in psl do
      d1:=Random(procap);
    od;
    g:=DihedralTrick@(a1^d1,ad,procp);
    d1:=d1*g;
    # =v= MULTIASSIGN =v=
    g:=IsConjugate(Centraliser(psl,ad),b1^d1,bd);
    isc:=g.val1;
    g:=g.val2;
    # =^= MULTIASSIGN =^=
    if not isc then
      #   need to try d1^c1 and d1^(c1^2)
      d1:=d1^c1;
      g:=DihedralTrick@(a1^d1,ad,procp);
      d1:=d1*g;
      # =v= MULTIASSIGN =v=
      g:=IsConjugate(Centraliser(psl,ad),b1^d1,bd);
      isc:=g.val1;
      g:=g.val2;
      # =^= MULTIASSIGN =^=
      if not isc then
        #   need to try d1^c1 and d1^(c1^2)
        d1:=d1^c1;
        g:=DihedralTrick@(a1^d1,ad,procp);
        d1:=d1*g;
        # =v= MULTIASSIGN =v=
        g:=IsConjugate(Centraliser(psl,ad),b1^d1,bd);
        isc:=g.val1;
        g:=g.val2;
        # =^= MULTIASSIGN =^=
      fi;
    fi;
    d1:=d1*g;
    if Print > 1 then
      Print("Identified psl.6");
    fi;
    dgs:=SubStructure(group,a,#TODO CLOSURE
      b,c,d);
    AssertAttribute(dgs,"Order",Size(psl)*6);
    return rec(val1:=GroupHomomorphismByImages(dgs,apsl,
      GeneratorsOfGroup(dgs),[a1,b1,c1,d1]),
      val2:=F,
      val3:=phi);
  fi;
  #  Finally the psl.2 case
  d:=Random(procg);
  while d^3 in dgroup do
    d:=Random(procg);
  od;
  ad:=(a^d)@homom;
  bd:=(b^d)@homom;
  dgs:=SubStructure(group,a,#TODO CLOSURE
    b,d);
  AssertAttribute(dgs,"Order",Size(psl)*2);
  d1:=Random(procap);
  while d1^3 in psl or not d1^2 in psl do
    d1:=Random(procap);
  od;
  g:=DihedralTrick@(a1^d1,ad,procp);
  d1:=d1*g;
  # =v= MULTIASSIGN =v=
  g:=IsConjugate(Centraliser(psl,ad),b1^d1,bd);
  isc:=g.val1;
  g:=g.val2;
  # =^= MULTIASSIGN =^=
  if isc then
    d1:=d1*g;
    return rec(val1:=GroupHomomorphismByImages(dgs,apsl,
      GeneratorsOfGroup(dgs),[a1,b1,d1]),
      val2:=F,
      val3:=phi);
  fi;
  #  The awkward case when we have the wrong isomorphism onto psl
  #  Find outer 3-element in apsl.
  c1:=Random(procap);
  while c1^2 in psl do
    c1:=Random(procap);
  od;
  a1:=a1^c1;
  b1:=b1^c1;
  homom:=GroupHomomorphismByImages(SubStructure(group,a,#TODO CLOSURE
    b),apsl,
    GeneratorsOfGroup(SubStructure(group,a,#TODO CLOSURE
      b)),[a1,b1]);
  ad:=(a^d)@homom;
  bd:=(b^d)@homom;
  g:=DihedralTrick@(a1^d1,ad,procp);
  d1:=d1*g;
  # =v= MULTIASSIGN =v=
  g:=IsConjugate(Centraliser(psl,ad),b1^d1,bd);
  isc:=g.val1;
  g:=g.val2;
  # =^= MULTIASSIGN =^=
  if isc then
    d1:=d1*g;
    psi:=GroupHomomorphismByImages(psls,SubStructure(apsl,a1,#TODO CLOSURE
      b1),
      GeneratorsOfGroup(psls),[a1,b1]);
    return rec(val1:=GroupHomomorphismByImages(dgs,apsl,
      GeneratorsOfGroup(dgs),[a1,b1,d1]),
      val2:=F,
      val3:=phi*psi);
  fi;
  #  Try again - must work this time!
  a1:=a1^c1;
  b1:=b1^c1;
  homom:=GroupHomomorphismByImages(SubStructure(group,a,#TODO CLOSURE
    b),apsl,
    GeneratorsOfGroup(SubStructure(group,a,#TODO CLOSURE
      b)),[a1,b1]);
  ad:=(a^d)@homom;
  bd:=(b^d)@homom;
  g:=DihedralTrick@(a1^d1,ad,procp);
  d1:=d1*g;
  # =v= MULTIASSIGN =v=
  g:=IsConjugate(Centraliser(psl,ad),b1^d1,bd);
  isc:=g.val1;
  g:=g.val2;
  # =^= MULTIASSIGN =^=
  if isc then
    d1:=d1*g;
    psi:=GroupHomomorphismByImages(psls,SubStructure(apsl,a1,#TODO CLOSURE
      b1),
      GeneratorsOfGroup(psls),[a1,b1]);
    return rec(val1:=GroupHomomorphismByImages(dgs,apsl,
      GeneratorsOfGroup(dgs),[a1,b1,d1]),
      val2:=F,
      val3:=phi*psi);
  fi;
  Error("Failed to find map onto PSL.2");
end;
;
#  ****************************************************
#  * First we do the case where 3 does not divide       *
#  * p-1, as this has much simpler behavour - Out = 2   *
#  * which is handy for a start.....                    *
#  *****************************************************
CoprimeMaximals@:=function(group,p)
local F,IsPSL,Print,apsl,dgroup,dh,factor,gl,homom,max,maximals,o,phi,psl,sl;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  if Print > 1 then
    Print("Making standard group");
  fi;
  gl:=GL(3,p);
  sl:=SL(3,p);
  apsl:=PGL2@(3,p);
  factor:=GroupHomomorphismByImages(gl,apsl,
    GeneratorsOfGroup(gl),[apsl.1,apsl.2]);
  psl:=sl@factor;
  o:=Order(group);
  IsPSL:=o=Size(psl);
  dgroup:=DerivedSubgroup(group);
  #  
  #  * Note that since 3 does not divide (p-1) we have pgl = psl. We may
  #  * still have an outer element of order 2, but since the two copies of
  #  * the reducible groups are computed directly, as are the novelty
  #  * intersections, we don't need it ever.
  
  if Print > 1 then
    Print("Setting up homomorphisms");
  fi;
  # =v= MULTIASSIGN =v=
  phi:=MakeHomom@(dgroup,group,p,psl,apsl:Print:=Print);
  homom:=phi.val1;
  F:=phi.val2;
  phi:=phi.val3;
  # =^= MULTIASSIGN =^=
  dh:=Domain(homom);
  Assert(1,not apsl.3 in psl);
  apsl:=SubStructure(apsl,homom(dh.1),#TODO CLOSURE
    homom(dh.2),apsl.3);
  AssertAttribute(apsl,"Order",Size(psl)*2);
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=apsl,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  #  
  #  * Reducible - if we have psl then we get 2 classes, conjugate under
  #  * inverse transpose. Otherwise, we get two novelties, intersections
  #  * are point with line containing it and point with line not
  #  * containing it. In both cases the two groups are returned as matrix
  #  * groups, so we factor by the centre before applying homom.
  
  if Print > 1 then
    Print("Getting reducibles");
  fi;
  if IsPSL then
    Add(maximals,GetPointStab@(p,sl)@factor);
    Add(maximals,GetLineStab@(p,sl)@factor);
  else
    Add(maximals,GetPointMeetLine@(p,sl)@factor);
    Add(maximals,GetPointUnmeetLine@(p,sl)@factor);
  fi;
  #  
  #  * The maximal imprimitive is unique, and extends. The function
  #  * returns a matrix group, so we factor by the centre before applying
  #  * homom.
  
  if Print > 1 then
    Print("Getting imprimitives");
  fi;
  Add(maximals,GetImprims@(p)@factor);
  #  
  #  * The maximal semilinear is unique, and extends. It is returned as a
  #  * permutation group.
  
  if Print > 1 then
    Print("Getting semilinears");
  fi;
  Add(maximals,GetSemilin@(p,sl,gl)@factor);
  #  
  #  * There is a classical subgroup PSO(3, p) - we take SO(3, p) and
  #  * apply factor to it. It appears to always extend.
  
  if Print > 1 then
    Print("Getting classicals");
  fi;
  Add(maximals,SO(3,p)@factor);
  #  
  #  * Finally, there is PSL(2, 7), which is a maximal C_9 group whenever
  #  * -7 is a square in GF(p). For reasons that are not entirely clear to
  #  * me at present, it appears to extend. Is returned as a matrix
  #  * subgroup so apply factor to it.
  
  if p > 7 and IsSquare((-7) #CAST GF(p)
    ) then
    if Print > 1 then
      Print("Getting PSL(2, 7)");
    fi;
    Add(maximals,GetPSL2_7@(p)@factor);
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
#  ***************************************************
#  * Now we do the case where 3 does divide p-1. This  *
#  * means that we get additional conjugacy classes    *
#  * of some groups, we get extraspecial groups, and   *
#  * we get alt_6 as a C_9 group whenever 5 is a       *
#  * square in GF(p)                                   *
#  ****************************************************
NonCoprimeMaximals@:=function(group,p)
#  /out:
#  * first we make our standard copies of pgl, psl etc. we need
#  * pgl to give us the element of order 3 which will later provide us
#  * with multiple copies of O_3(p) and alt_6.

local 
   F,Print,apsl,dgroup,dh,factor,gl,homom,initial,invol,max,maximals,o,orderpsl,
   phi,psl,sl,three_cyc,type,z;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  if Print > 1 then
    Print("Making standard group");
  fi;
  gl:=GL(3,p);
  sl:=SL(3,p);
  apsl:=PGL2@(3,p);
  factor:=GroupHomomorphismByImages(gl,apsl,
    GeneratorsOfGroup(gl),[apsl.1,apsl.2]);
  psl:=sl@factor;
  dgroup:=DerivedSubgroup(group);
  o:=Order(group);
  orderpsl:=Size(PSL(3,p));
  if o=orderpsl then
    type:="psl";
  elif o=2*orderpsl then
    type:="psl.2";
  elif o=3*orderpsl then
    type:="psl.3";
  else
    Assert(1,o=6*orderpsl);
    type:="psl.sym3";
    dgroup:=DerivedSubgroup(dgroup);
  fi;
  #  Note - dgroup is actually the socle, not always the derived group!
  #  
  #  * Now we must make the element of order 3 which will be used to get
  #  * multiple copies of some groups.
  
  z:=PrimitiveElement(GF(p));
  three_cyc:=(DiagonalMat([z,1,1]) #CAST gl
    )@factor;
  if Print > 1 then
    Print("Setting up homomorphisms");
  fi;
  # =v= MULTIASSIGN =v=
  phi:=MakeHomom@(dgroup,group,p,psl,apsl:Print:=Print);
  homom:=phi.val1;
  F:=phi.val2;
  phi:=phi.val3;
  # =^= MULTIASSIGN =^=
  dh:=Domain(homom);
  Assert(1,not apsl.3 in psl);
  if type="psl.2" then
    invol:=homom(dh.3);
    #  necessary to get normalisers of subgroups correct.
  else
    invol:=apsl.3;
  fi;
  apsl:=SubStructure(apsl,homom(dh.1),#TODO CLOSURE
    homom(dh.2),three_cyc,invol);
  AssertAttribute(apsl,"Order",Size(psl)*6);
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=apsl,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  #  
  #  * first we must return the reducibles. in cases psl and psl.3 we have
  #  * two classes - the point and line stabiliser. these are returned as
  #  * matrix groups and so we must apply factor to them before applying
  #  * homom. in cases psl.2 and psl.sym_3 the classes fuse, but there are
  #  * novelty subgroups coming from the normalisers of the stabiliser of
  #  * point and a line containing it, and the stabiliser of a point and a
  #  * line not containing it.
  
  if Print > 1 then
    Print("Getting reducibles");
  fi;
  if type="psl" or type="psl.3" then
    Add(maximals,GetPointStab@(p,sl)@factor);
    Add(maximals,GetLineStab@(p,sl)@factor);
  else
    Add(maximals,GetPointMeetLine@(p,sl)@factor);
    Add(maximals,GetPointUnmeetLine@(p,sl)@factor);
  fi;
  #  
  #  * Next we get the imprimitive. This is unique, and extends in all
  #  * cases.
  
  if Print > 1 then
    Print("Getting imprimitives");
  fi;
  Add(maximals,GetImprims@(p)@factor);
  #  
  #  * Next we get the semilinear group. This is unique, and extends in
  #  * all cases.
  
  if Print > 1 then
    Print("Getting semilinear");
  fi;
  Add(maximals,GetSemilin@(p,sl,gl)@factor);
  #  
  #  * Next we get the extraspecial group.
  
  if Print > 1 then
    Print("Getting extraspecials");
  fi;
  if p mod 9=1 then
    #   three classes in pgl
    if type="psl" then
      initial:=GetExtraspec@(p)@factor;
      Add(maximals,initial);
      Add(maximals,initial^three_cyc);
      Add(maximals,initial^(three_cyc^2));
    elif type="psl.2" then
      initial:=GetExtraspec@(p)@factor;
      Add(maximals,SelectGroup@(psl,initial,three_cyc,invol));
    fi;
  else
    Add(maximals,GetExtraspec@(p)@factor);
  fi;
  #  
  #  * Next we do the classical group. What seems to happen here is
  #  * that in PSL there are 3 classes, in PSL.2 two of them fuse, and one
  #  * remains which commutes with the outer involution, and in PSL.3 and
  #  * PSL.sym_3 all three of them fuse.
  
  if Print > 1 then
    Print("Getting classicals");
  fi;
  if type="psl" then
    initial:=SO(3,p)@factor;
    Add(maximals,initial);
    Add(maximals,initial^three_cyc);
    Add(maximals,initial^(three_cyc^2));
  elif type="psl.2" then
    initial:=SO(3,p)@factor;
    Add(maximals,SelectGroup@(psl,initial,three_cyc,invol));
  fi;
  #  
  #  * Now we have only the C_9s left to do. Start with Alt(6). Same
  #  * fusion/splitting pattern as for O(3, p).
  
  if IsSquare(5 #CAST GF(p)
    ) then
    if Print > 1 then
      Print("Getting alt6");
    fi;
    if type="psl" then
      initial:=GetAlt6@(p)@factor;
      Add(maximals,initial);
      Add(maximals,initial^three_cyc);
      Add(maximals,initial^(three_cyc^2));
    elif type="psl.2" then
      initial:=GetAlt6@(p)@factor;
      Add(maximals,SelectGroup@(psl,initial,three_cyc,invol));
    fi;
  fi;
  #  
  #  * And finally we do PSL(2, 7). Again, same fusion/splitting pattern
  #  * as for O(3, p).
  
  if p > 3 and not p=7 and IsSquare((-7) #CAST GF(p)
    ) then
    if Print > 1 then
      Print("Getting PSL(2, 7)");
    fi;
    if type="psl" then
      initial:=GetPSL2_7@(p)@factor;
      Add(maximals,initial);
      Add(maximals,initial^three_cyc);
      Add(maximals,initial^(three_cyc^2));
    elif type="psl.2" then
      initial:=GetPSL2_7@(p)@factor;
      Add(maximals,SelectGroup@(psl,initial,three_cyc,invol));
    fi;
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
WhichGroupl38@:=function(group)
local o,order_psl,type;
  o:=Order(group);
  order_psl:=16482816;
  if o=order_psl then
    type:="psl";
  elif o=2*order_psl then
    type:="psl.2";
  elif o=3*order_psl then
    type:="psigmal";
  elif o=6*order_psl then
    type:="psl.6";
  fi;
  return type;
end;
;
L3_8Maximals@:=function(group)
#  /out:
#  * setting up groups. psl = pgl = sl. psigmal = pgammal = g.3.

local 
   F,Print,apsl,dgroup,dh,factor,gl,homom,imprim,line,max,maximals,phi,point,
   point_meet_line,point_unmeet_line,psl,psl3_2,semilin,sl,type,z;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  if Print > 1 then
    Print("Making standard group");
  fi;
  gl:=GL(3,8);
  sl:=SL(3,8);
  apsl:=PGammaL2@(3,8);
  factor:=GroupHomomorphismByImages(gl,apsl,
    apsl.1,apsl.2);
  psl:=sl@factor;
  #   note apsl.3 is field auto, apsl.4 is graph auto.
  dgroup:=DerivedSubgroup(group);
  #   setting up field.
  
  if Print > 1 then
    Print("Setting up homomorphism");
  fi;
  # =v= MULTIASSIGN =v=
  phi:=MakeHomom@(dgroup,group,8,psl,apsl:Print:=Print);
  homom:=phi.val1;
  F:=phi.val2;
  phi:=phi.val3;
  # =^= MULTIASSIGN =^=
  dh:=Domain(homom);
  apsl:=SubStructure(apsl,homom(dh.1),#TODO CLOSURE
    homom(dh.2),apsl.3,apsl.4);
  AssertAttribute(apsl,"Order",Size(psl)*6);
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=apsl,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  z:=PrimitiveElement(GF(8));
  #   type is one of "psl", "psl.2", "psigmal" or "psl.6".
  
  type:=WhichGroupl38@(group);
  #  
  #  * point_unmeet_line is all matrices of shape [* 0 0
  #  *                                             0 * *
  #  *                                             0 * *];
  #  * point_meet_line is all matrices of shape    [* * *
  #  *                                             0 * *
  #  *                                             0 0 *];
  #  * If the outer aut. part of the group has even order,
  #  * then we have point-line duality and hence there are novelty
  #  * subgroups. otherwise we have the point stabiliser and the line
  #  * stabiliser.
  
  if Print > 1 then
    Print("Getting reducibles");
  fi;
  point_unmeet_line:=SubStructure(sl,[z^-1,0,0,0,z,0,0,0,1],#TODO CLOSURE
    [1,0,0,0,1,1,0,1,0]);
  point_meet_line:=SubStructure(sl,DiagonalMat([z^-1,1,z]),#TODO CLOSURE
    DiagonalMat([z^-1,z,1]),[1,1,0,0,1,0,0,0,1],[1,0,1,0,1,0,0,0,1]
   ,[1,0,0,0,1,1,0,0,1]);
  if type="psl.2" or type="psl.6" then
    Add(maximals,point_meet_line@factor);
    Add(maximals,point_unmeet_line@factor);
  else
    point:=SubStructure(sl,point_unmeet_line,#TODO CLOSURE
      [1,0,0,1,1,0,0,0,1],[1,0,0,0,1,0,1,0,1]);
    Add(maximals,point@factor);
    line:=SubStructure(sl,point_unmeet_line,#TODO CLOSURE
      [1,1,0,0,1,0,0,0,1],[1,0,1,0,1,0,0,0,1]);
    Add(maximals,line@factor);
  fi;
  if Print > 1 then
    Print("Getting imprimitive");
  fi;
  imprim:=SubStructure(sl,DiagonalMat([z^-1,1,z]),#TODO CLOSURE
    DiagonalMat([z^-1,z,1]),[0,1,0,0,0,1,1,0,0],[1,0,0,0,0,1,0,1,0]);
  Add(maximals,imprim@factor);
  if Print > 1 then
    Print("Getting semilinear");
  fi;
  semilin:=SubStructure(sl,[0,1,0,0,0,1,-1,-z,0],#TODO CLOSURE
    [1,0,0,0,z^2,z,0,z^2,z^6]);
  Add(maximals,semilin@factor);
  if Print > 1 then
    Print("Getting subfield");
  fi;
  psl3_2:=SubStructure(sl,[1,1,0,0,1,0,0,0,1],#TODO CLOSURE
    [0,0,1,1,0,0,0,1,0]);
  Add(maximals,(psl3_2)@factor);
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
WhichGroupl39@:=function(group)
local Print,dgroup,g,o,order_psl,proc,type;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  o:=Order(group);
  order_psl:=42456960;
  if o=order_psl then
    type:="psl";
  elif o=4*order_psl then
    type:="psl.4";
  else
    Assert(1,o=2*order_psl);
    proc:=RandomProcess(group);
    dgroup:=DerivedGroup(group);
    while true do
      g:=Random(proc);
      o:=Order(g);
      if o=14 then
        type:="psl.fg";
        break;
      fi;
      if o=26 then
        type:="psl.f";
        break;
      fi;
      if o=20 and not g in dgroup then
        type:="psl.g";
        break;
      fi;
    od;
  fi;
  return type;
end;
;
MakeHomoml39@:=function(dgroup,group,p,psl,apsl,type,field_auto,graph_auto)
#  /out: for generators, we choose an involution (unique class) and
#  another/out: random generating element.
local 
   F,Print,a,a1,ac,ad,b,b1,bc,bd,c,c1,d,d1,dgs,g,homom,isc,phi,procdg,procg,
   procp,psls,s,seeking;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  procp:=RandomProcess(psl);
  a1:=FindInvolution@(psl);
  b1:=Random(procp);
  while Order(b1)<>3 or Order(a1*b1)<>24 do
    b1:=Random(procp);
  od;
  psls:=SubStructure(psl,a1,#TODO CLOSURE
    b1);
  AssertAttribute(psls,"Order",Size(psl));
  # =v= MULTIASSIGN =v=
  phi:=FPGroupStrong(psls);
  F:=phi.val1;
  phi:=phi.val2;
  # =^= MULTIASSIGN =^=
  procdg:=RandomProcess(dgroup);
  a:=FindInvolution@(dgroup);
  b:=Random(procdg);
  while Order(b)<>3 or Order(a*b)<>24 do
    b:=Random(procdg);
  od;
  if Print > 1 then
    Print("Got psl gens");
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
  if type="psl.f" or type="psl.4" then
    #   get 2-element in outer automorphism group
    c:=Random(procg);
    while c in dgroup do
      c:=Random(procg);
    od;
    seeking:=type="psl.4";
    while seeking do
      s:=SubStructure(group,dgroup,#TODO CLOSURE
        c);
      AssertAttribute(s,"Order",2*Size(psl));
      if WhichGroupl39@(s)="psl.f" then
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
    c1:=field_auto;
    g:=DihedralTrick@(a1^c1,ac,procp);
    c1:=c1*g;
    # =v= MULTIASSIGN =v=
    g:=IsConjugate(Centraliser(psl,ac),b1^c1,bc);
    isc:=g.val1;
    g:=g.val2;
    # =^= MULTIASSIGN =^=
    if not isc then
      Error("psl.f error");
    fi;
    c1:=c1*g;
    if Print > 1 then
      Print("Identified psl.f");
    fi;
    if type="psl.f" then
      dgs:=SubStructure(group,a,#TODO CLOSURE
        b,c);
      AssertAttribute(dgs,"Order",Size(psl)*2);
      return rec(val1:=GroupHomomorphismByImages(dgs,apsl,
        GeneratorsOfGroup(dgs),[a1,b1,c1]),
        val2:=F,
        val3:=phi);
    fi;
  fi;
  if type="psl.g" or type="psl.4" then
    #   get 2-element in outer automorphism group
    d:=Random(procg);
    while d in dgroup do
      d:=Random(procg);
    od;
    seeking:=type="psl.4";
    while seeking do
      s:=SubStructure(group,dgroup,#TODO CLOSURE
        d);
      AssertAttribute(s,"Order",2*Size(psl));
      if WhichGroupl39@(s)="psl.g" then
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
    d1:=graph_auto;
    g:=DihedralTrick@(a1^d1,ad,procp);
    d1:=d1*g;
    # =v= MULTIASSIGN =v=
    g:=IsConjugate(Centraliser(psl,ad),b1^d1,bd);
    isc:=g.val1;
    g:=g.val2;
    # =^= MULTIASSIGN =^=
    if not isc then
      Error("psl.g error");
    fi;
    d1:=d1*g;
    if Print > 1 then
      Print("Identified psl.g");
    fi;
    if type="psl.g" then
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
  #  remaining case is psl.fg
  d:=Random(procg);
  while d in dgroup do
    d:=Random(procg);
  od;
  ad:=(a^d)@homom;
  bd:=(b^d)@homom;
  d1:=field_auto*graph_auto;
  g:=DihedralTrick@(a1^d1,ad,procp);
  d1:=d1*g;
  # =v= MULTIASSIGN =v=
  g:=IsConjugate(Centraliser(psl,ad),b1^d1,bd);
  isc:=g.val1;
  g:=g.val2;
  # =^= MULTIASSIGN =^=
  if not isc then
    Error("psl.fg error");
  fi;
  d1:=d1*g;
  if Print > 1 then
    Print("Identified psl.fg");
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
L3_9Maximals@:=function(group)
local 
   F,Print,apsl,dgroup,dh,factor,field_auto,gl,graph_auto,homom,imprim,line,max,
   maximals,phi,point,point_meet_line,point_unmeet_line,psl,psl3_3,psu3_3,
   semilin,sl,type,z;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  if Print > 1 then
    Print("Making standard group");
  fi;
  gl:=GL(3,9);
  sl:=SL(3,9);
  apsl:=PGammaL2@(3,9);
  factor:=GroupHomomorphismByImages(gl,apsl,
    apsl.1,apsl.2);
  psl:=sl@factor;
  #   note apsl.3 is field auto, apsl.4 is graph auto.
  field_auto:=apsl.3;
  graph_auto:=apsl.4;
  dgroup:=DerivedSubgroup(group);
  #   setting up field.
  
  type:=WhichGroupl39@(group);
  if Print > 1 then
    Print("Setting up homomorphism");
  fi;
  # =v= MULTIASSIGN =v=
  phi:=MakeHomoml39@(dgroup,group,9,psl,apsl,type,field_auto,
   graph_auto:Print:=Print);
  homom:=phi.val1;
  F:=phi.val2;
  phi:=phi.val3;
  # =^= MULTIASSIGN =^=
  dh:=Domain(homom);
  apsl:=SubStructure(apsl,homom(dh.1),#TODO CLOSURE
    homom(dh.2),apsl.3,apsl.4);
  AssertAttribute(apsl,"Order",Size(psl)*4);
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=apsl,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  z:=PrimitiveElement(GF(9));
  #  
  #  * point_unmeet_line is all matrices of shape [* 0 0
  #  *                                             0 * *
  #  *                                             0 * *];
  #  * point_meet_line is all matrices of shape    [* * *
  #  *                                             0 * *
  #  *                                             0 0 *];
  #  * If the group is psl.g, psl.fg or psl.4,
  #  * then we have point-line duality and hence there are novelty
  #  * subgroups. otherwise we have the point stabiliser and the line
  #  * stabiliser.
  
  if Print > 1 then
    Print("Getting reducibles");
  fi;
  point_unmeet_line:=SubStructure(sl,[z^-1,0,0,0,z,0,0,0,1],#TODO CLOSURE
    [1,0,0,0,1,1,0,-1,0]);
  point_meet_line:=SubStructure(sl,DiagonalMat([z^-1,1,z]),#TODO CLOSURE
    DiagonalMat([z^-1,z,1]),[1,1,0,0,1,0,0,0,1],[1,0,1,0,1,0,0,0,1]
   ,[1,0,0,0,1,1,0,0,1]);
  if type="psl.g" or type="psl.fg" or type="psl.4" then
    Add(maximals,point_meet_line@factor);
    Add(maximals,point_unmeet_line@factor);
  else
    point:=SubStructure(sl,point_unmeet_line,#TODO CLOSURE
      [1,0,0,1,1,0,0,0,1],[1,0,0,0,1,0,1,0,1]);
    Add(maximals,point@factor);
    line:=SubStructure(sl,point_unmeet_line,#TODO CLOSURE
      [1,1,0,0,1,0,0,0,1],[1,0,1,0,1,0,0,0,1]);
    Add(maximals,line@factor);
  fi;
  if Print > 1 then
    Print("Getting imprimitive");
  fi;
  imprim:=SubStructure(sl,DiagonalMat([z^-1,1,z]),#TODO CLOSURE
    DiagonalMat([z^-1,z,1]),[0,1,0,0,0,1,1,0,0],[-1,0,0,0,0,1,0,1,0]);
  Add(maximals,imprim@factor);
  if Print > 1 then
    Print("Getting semilinear");
  fi;
  semilin:=SubStructure(sl,[0,1,0,0,0,1,1,0,0],#TODO CLOSURE
    [z^7,z^7,z^2,z^7,1,z,z^2,z,z^6]);
  Add(maximals,semilin@factor);
  if Print > 1 then
    Print("Getting subfield");
  fi;
  psl3_3:=SubStructure(sl,[1,1,0,0,1,0,0,0,1],#TODO CLOSURE
    [0,0,1,1,0,0,0,1,0]);
  Add(maximals,(psl3_3)@factor);
  if Print > 1 then
    Print("Getting unitary");
  fi;
  psu3_3:=SubStructure(sl,[z,0,0,0,z^2,0,0,0,z^5],#TODO CLOSURE
    [z^5,2,1,2,2,0,1,0,0]);
  Add(maximals,(psu3_3)@factor);
  if Print > 1 then
    Print("Getting orthogonal");
  fi;
  Add(maximals,SO(3,9)@factor);
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
#  ****************************************************
#  * This function ties all the rest together sadly     *
#  * The results have been compared with the ATLAS      *
#  * for p leq 11, and are correct for PSL and PGL.     *
#  * Have not been able to check psl.2 and psl.Sym3 as  *
#  * at present there is no usable homomorphism between *
#  * the socle of these groups and the standard copy of *
#  * psl                                                *
#  *****************************************************
InstallGlobalFunction(L3pIdentify@,
function(group,p)
local Print,max;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  Assert(1,p > 4);
  if p=8 then
    return L3_8Maximals@(group:max:=max,Print:=Print);
  elif p=9 then
    return L3_9Maximals@(group:max:=max,Print:=Print);
  elif ((p-1) mod 3)=0 then
    return NonCoprimeMaximals@(group,p:max:=max,Print:=Print);
  else
    return CoprimeMaximals@(group,p:max:=max,Print:=Print);
  fi;
end);


