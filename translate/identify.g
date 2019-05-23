#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: AGL, ActionOnOrbitsU, AlmostSimpleGroupDatabase, Alt,
#  Append, BlocksAction, CalculateIsomRGQH, Centraliser, Centralizer, Classes,
#  CosetAction, Degree, DirectProduct, Divisors, ElementToSequence,
#  ExistsGroupData, FPGroupStrong, Factorial, Factorisation, GroupData, Id,
#  IdentifyAlmostSimpleGroupH, IdentifyAltEvenDeg, IdentifyAltOddDeg,
#  IdentifyAltSymNatural, IdentifySymEvenDeg, IdentifySymOddDeg,
#  IdentityHomomorphism, ImprimitiveSubgroupsAltSym, Index,
#  IntransitiveSubgroupsAltSym, IsEven, IsFactorial, IsInnerAutomorphism,
#  IsPrime, IsPrimitive, IsSimpleOrder, MaximalPartition, Ngens, Normaliser,
#  NumberOfGroups, OrbitImage, OrbitRepresentatives, Orbits, Order,
#  OuterAutsRGQH, PGL, PSL, Parent, PermRepAlmostSimpleGroupH, PrimitiveGroup,
#  PrimitiveSubgroupsAltSym, Random, RandomSchreier, Rep, SGDBAccess,
#  SolubleResidual, StandardGroup, Sylow, Sym, Type, WreathProduct, phi

#  Defines: ActionOnOrbitsU, CalculateIsomRGQH, IdentifyAlmostSimpleGroup,
#  IdentifyAlmostSimpleGroupH, IdentifyAltEvenDeg, IdentifyAltOddDeg,
#  IdentifyAltSymNatural, IdentifySymEvenDeg, IdentifySymOddDeg,
#  ImprimitiveSubgroupsAltSym, IntransitiveSubgroupsAltSym, OuterAutsRGQH,
#  PermRepAlmostSimpleGroupH, PrimitiveSubgroupsAltSym, SGDBAccess

DeclareGlobalFunction("IdentifyAlmostSimpleGroupH@");

DeclareGlobalFunction("IdentifySymEvenDeg@");

DeclareGlobalFunction("IdentifySymOddDeg@");

DeclareGlobalFunction("IdentifyAltSymNatural@");

DeclareGlobalFunction("IdentifyAltEvenDeg@");

DeclareGlobalFunction("IdentifyAltOddDeg@");

DeclareGlobalFunction("ActionOnOrbitsU@");

DeclareGlobalFunction("IntransitiveSubgroupsAltSym@");

DeclareGlobalFunction("ImprimitiveSubgroupsAltSym@");

DeclareGlobalFunction("PrimitiveSubgroupsAltSym@");

#  
#  *   Written by Derek Holt - updated Dec 2002

#   This file contains the procedures for identifying an almost
#  * simple group G of small order as a subgroup of Aut(T) for some simple T,
#  * reading off its maximal subgroups from stored data, and
#  * finding an injection from G to a permutation representation of Aut(T).
#  *
#  * Note, two of the functions,
#  * OuterAutsRGQH, CalculateIsomRGQH,
#  * are the same as those in autgps/radquot.m
#  *
#  * The function SGDBAccess(resorder,order,ASG) locates a record for an
#  * almost simple group ASG that has order 'order', and soluble residual of
#  * order 'resorder', provided that it has one stored.
#  *
#  * When there is more than one subgroup * stored for that order -
#  * for example, for order=720, there are three -
#  * the sum of the class orders of the ASG is used to identify th
#  * isomorphism type.
#  *
#  * Each simple group T  in the list is defined by two generators,  x  and  y
#  * with orders ox and oy, say.
#  * (x and y  are actually defined as generators of a free group of rank 2.)
#  * x is always chosen so that there is a unique Aut(T)-class of elements
#  * of order ox in T.
#  *
#  * The list returned for G is a record with the following fields:
#  * name - a string, describing the group G.
#  * resname - a string, describing the simple soluble residual T of the group.
#  * geninfo - a list of length two, the elements are 3-tuples
#  *           giving order of element (i.e. ox or oy), length of
#  *        class of element a,y. Ignore third component.
#  * conjelts - in cases where G is not normal in Aut(T), we may have to
#  *        replace the original generators x,y of T by conjugates under
#  *        autmorphisms of T that do not normalise G.
#  *        conjelts is a list of the (nontrivial) conjugating automorphisms.
#  * NOTE - first example of this is PSL(3,4) order 20160
#  * rels - a list of words in  x  and  y which, taken together with
#  *        x^ox and y^oy constitute a set of defining relators for T.
#  * outimages - the images (as words in gens of T) of the generators of T
#  *        under generators of the outer automorphism group of T.
#  * subgens - words in the outer automorphisms generators of T that
#  *           together with T generate G.
#  * maxsubints - the intersections of the maximal subgroups of G that do not
#  *           contain T with T.
#  * permrep - a pemrutation representation of Aut(T), where the generators
#  *           are x,y followed by generating automorphisms.

OuterAutsRGQH@:=function(RGQ,oims,proj,printlevel)
#  /out: Calculate outer automorphisms as automorphisms of RGQ
#  * The list is twice as long as #oims and the corresponding outer
#  * automorphisms are followed by the list of their inverses.

local iso,isoi,oi,rgqauts;
  if printlevel > 2 then
    Print("+Calculating outer automorphisms of simple group.");
  fi;
  rgqauts:=[];
  if Size(oims)<>0 then
    for oi in oims do
      iso:=GroupHomomorphismByImages(RGQ,RGQ,
        GeneratorsOfGroup(RGQ),List(oi,im->im@proj));
      if printlevel > 2 then
        Print("+Defined an outer automorphism.");
      fi;
      Add(rgqauts,iso);
    od;
    #   and append their inverses 
    for oi in oims do
      iso:=GroupHomomorphismByImages(RGQ,RGQ,
        GeneratorsOfGroup(RGQ),List(oi,im->im@proj));
      isoi:=GroupHomomorphismByImages(RGQ,RGQ,
        GeneratorsOfGroup(RGQ),List(List([1..Size(oi)],i->RGQ.i),x->x@@iso));
      Add(rgqauts,isoi);
    od;
  fi;
  if printlevel > 2 then
    Print("+Found outer automorphisms.");
  fi;
  return rgqauts;
end;
;
CalculateIsomRGQH@:=function(RGQ,w,rgqauts)
#  /out: w should be a nontrivial word in the outer automorphism generators,
#  * or a corresponding list of integers.
#  * Calculate and return the corresponding isomorphism of RGQ

local aut,i,noi,sw;
  noi:=Size(rgqauts)/2;
  sw:=ElementToSequence(w);
  #   Inverses in auts come at the end, so change numbering in sw 
  for i in [1..Size(sw)] do
    if sw[i] < 0 then
      sw[i]:=noi-sw[i];
    fi;
  od;
  aut:=rgqauts[sw[1]];
  for i in [2..Size(sw)] do
    aut:=aut*rgqauts[sw[i]];
  od;
  return aut;
end;
;
SGDBAccess@:=function(resorder,order,ASG)
local D,f,fl,invar,n,reco;
  D:=AlmostSimpleGroupDatabase();
  # =v= MULTIASSIGN =v=
  f:=NumberOfGroups(D,resorder,order);
  n:=f.val1;
  f:=f.val2;
  # =^= MULTIASSIGN =^=
  if n=0 then
    return rec(val1:=false,
      val2:=_);
  elif n=1 then
    return rec(val1:=true,
      val2:=GroupData(D,f));
  else
    invar:=Sum(List(Classes(ASG),cl->cl[1]));
    # =v= MULTIASSIGN =v=
    reco:=ExistsGroupData(D,resorder,order,invar);
    fl:=reco.val1;
    reco:=reco.val2;
    # =^= MULTIASSIGN =^=
    if fl=false then
      return rec(val1:=false,
        val2:=_);
    fi;
    #  should not happen
    return rec(val1:=true,
      val2:=reco);
  fi;
end;
;
PermRepAlmostSimpleGroupH@:=function(G,K)
#  /out: q eq 4 or Attempt to find a reasonable degree perm. rep. of the almost
#  simple
#  * group G/K.

local N,P,R,S,fact,ind,m,mb,minind,mp,mpb,p,pg;
  ind:=QuoInt(Size(G),Size(K));
  minind:=ind;
  S:=K;
  R:=SolubleResidual(G);
  for fact in CollectedFactors(ind) do
    p:=fact[1];
    P:=SubStructure(G,K,#TODO CLOSURE
      Sylow(R,p));
    N:=Normaliser(G,P);
    if QuoInt(Size(G),Size(N)) < minind then
      S:=N;
      minind:=QuoInt(Size(G),Size(N));
    fi;
  od;
  # =v= MULTIASSIGN =v=
  pg:=CosetAction(G,S);
  m:=pg.val1;
  pg:=pg.val2;
  # =^= MULTIASSIGN =^=
  if IsPrimitive(pg) then
    return rec(val1:=m,
      val2:=pg);
  fi;
  mp:=MaximalPartition(pg);
  # =v= MULTIASSIGN =v=
  mpb:=BlocksAction(pg,mp);
  mb:=mpb.val1;
  mpb:=mpb.val2;
  # =^= MULTIASSIGN =^=
  return rec(val1:=m*mb,
    val2:=mpb);
end;
;
#  Forward declaration of IdentifySymEvenDeg
#  Forward declaration of IdentifySymOddDeg
#  Forward declaration of IdentifyAltSymNatural
#  Forward declaration of IdentifyAltEvenDeg
#  Forward declaration of IdentifyAltOddDeg
#  Forward declaration of ActionOnOrbitsU
InstallGlobalFunction(IdentifyAlmostSimpleGroupH@,
function(RGQ,GQ,printlevel)
#  /out: GQ should be the normaliser of the simple factor RGQ in a TF-group.
#  * A monomorphism from GQ to a standard permutation representation of
#  * Aut(T) (where T is a simple group in the database) is returned;
#  * together with Aut(T) itself;  if max is true,  the images of the
#  * intersection of the maximal subgroups of GQ that do not contain T in
#  Aut(T),
#  * returned as lists of generators; and optionally a presentation F of T
#  * together with the associated map F->T.
#  * The image of G is uniquely determined by the isomorphism type of G.

local 
   ASG,ASG2,C,F,GQgens,GQnew,H,K,RF,RGQ,S,aut,classical,conjeltct,conjelts,
   copysg,d,el,el_ord,fac,fl,foundgqhom,foundhom,foundx,geninfo,i,imx,imy,inj,
   invar,isinner,isso,k,l,max,msi,msiims,n,newGQ,ogq,oims,ok,orbreps,orgq,
   origimx,origimy,ox,oy,p,phi,pr,prgens,proj,q,rels,rgqauts,sg,sporadic,
   storedgp,subgp,tau,tau2,type,w,wm,ws,x,y;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  S:="unneeded record format";
  orgq:=Size(RGQ);
  C:=Centraliser(GQ,RGQ);
  ogq:=Index(GQ,C);
  if Size(C)=1 then
    ASG:=GQ;
    tau:=IdentityHomomorphism(GQ);
  else
    #    tau, ASG := Action(GQ, GSet(GQ, SequenceToSet(Orbits(C))));
    #  transer to standard perm group to avoid bugs
    #  ASG, tau2 := StandardGroup(ASG);
    #  tau := tau*tau2; 
    # =v= MULTIASSIGN =v=
    ASG:=ActionOnOrbitsU@(GQ,C);
    tau:=ASG.val1;
    ASG:=ASG.val2;
    # =^= MULTIASSIGN =^=
    if Size(ASG)<>ogq then
      #  not faithful
      # =v= MULTIASSIGN =v=
      ASG:=PermRepAlmostSimpleGroupH@(GQ,C);
      tau:=ASG.val1;
      ASG:=ASG.val2;
      # =^= MULTIASSIGN =^=
    fi;
  fi;
  #   At this point ogq is the order of an almost simple group ASG,
  #  * with simple normal subgroup RGQ of order orgq. These groups need to be
  #  * identified.
  #  * This is done either by looking up the groups in the database of
  #  * almost simple groups, or by identifying the group as a member of
  #  * a generic class.
  #  * When introducing new generic classes, it is necessary to observe
  #  * only the following rules.
  #  * We must return three values: phi, A, subims, + two optionals, F, wm.
  #  * A must be a permutation group, containing a normal subgroup S,
  #  * where S is isomorphic to RGQ, and A is isomorphic to the full
  #  automorphism
  #  * group of S; the generators of A must include generators of S.
  #  * phi must be a monmomorphism from ASG to A, mapping RGQ isomorphically
  #  * to S.
  #  * F is a finitely presentation of S with word map wm.
  
  #   deal with large alternating and symmetric groups separately 
  # =v= MULTIASSIGN =v=
  n:=IsFactorial(2*orgq);
  fl:=n.val1;
  n:=n.val2;
  # =^= MULTIASSIGN =^=
  # =v= MULTIASSIGN =v=
  type:=IsSimpleOrder(orgq);
  isso:=type.val1;
  type:=type.val2;
  # =^= MULTIASSIGN =^=
  if not isso then
    Error("Bad simple group order");
  fi;
  if type[1]=17 then
    #   RGQ = Alt(n) case
    n:=type[2];
    if 9 <= n and n <= 999 then
      if printlevel > 1 then
        Print("In Alt case");
      fi;
      orbreps:=OrbitRepresentatives(ASG);
      if ogq > orgq then
        #  Sym(n)
        if printlevel > 0 then
          Print("The almost simple group is Sym(",n,"), with soluble residual 
           Alt(",n,").");
        fi;
        x:=First(orbreps,t->t[1]=n);
        if x<>fail then
          # =v= MULTIASSIGN =v=
          msi:=IdentifyAltSymNatural@(ASG,n,true,x,printlevel:max:=max);
          phi:=msi.val1;
          pr:=msi.val2;
          msi:=msi.val3;
          # =^= MULTIASSIGN =^=
        elif n mod 2=0 then
          # =v= MULTIASSIGN =v=
          msi:=IdentifySymEvenDeg@(ASG,n,printlevel:max:=max);
          phi:=msi.val1;
          pr:=msi.val2;
          msi:=msi.val3;
          # =^= MULTIASSIGN =^=
        else
          # =v= MULTIASSIGN =v=
          msi:=IdentifySymOddDeg@(ASG,n,printlevel:max:=max);
          phi:=msi.val1;
          pr:=msi.val2;
          msi:=msi.val3;
          # =^= MULTIASSIGN =^=
        fi;
        msiims:=[];
        if max then
          for K in msi do
            H:=Intersection(K,AlternatingGroup(n));
            x:=Random(K);
            while x in H do
              x:=Random(K);
            od;
            Add(msiims,rec(generators:=List([1..Ngens(H)],i->H.i),
              order:=QuoInt(Size(K),2),
              normgen:=x));
          od;
        fi;
      else
        #  Alt(n)
        if printlevel > 0 then
          Print("The almost simple group is Alt(",n,").");
        fi;
        x:=First(orbreps,t->t[1]=n);
        if x<>fail then
          # =v= MULTIASSIGN =v=
          msi:=IdentifyAltSymNatural@(ASG,n,false,x,printlevel:max:=max);
          phi:=msi.val1;
          pr:=msi.val2;
          msi:=msi.val3;
          # =^= MULTIASSIGN =^=
        elif IsEvenInt(n) then
          # =v= MULTIASSIGN =v=
          msi:=IdentifyAltEvenDeg@(ASG,n,printlevel:max:=max);
          phi:=msi.val1;
          pr:=msi.val2;
          msi:=msi.val3;
          # =^= MULTIASSIGN =^=
        else
          # =v= MULTIASSIGN =v=
          msi:=IdentifyAltOddDeg@(ASG,n,printlevel:max:=max);
          phi:=msi.val1;
          pr:=msi.val2;
          msi:=msi.val3;
          # =^= MULTIASSIGN =^=
        fi;
        if max then
          msiims:=List(msi,G->rec(generators:=List([1..Ngens(G)],i->G.i),
            order:=Size(G),
            normgen:=One(G)));
        else
          msiims:=[];
        fi;
      fi;
      phi:=tau*phi;
      #   might deal with presentations later!
      return rec(val1:=phi,
        val2:=pr,
        val3:=msiims,
        val4:=_,
        val5:=_);
    fi;
  fi;
  #   deal with some large sporadic/individual groups 
  sporadic:=false;
  if orgq=17971200 then
    #   Tits' group
    # =v= MULTIASSIGN =v=
    wm:=TitsIdentify@(ASG:max:=max,Print:=printlevel);
    phi:=wm.val1;
    pr:=wm.val2;
    msi:=wm.val3;
    F:=wm.val4;
    wm:=wm.val5;
    # =^= MULTIASSIGN =^=
    sporadic:=true;
  elif orgq=42573600 then
    #   U39
    # =v= MULTIASSIGN =v=
    wm:=U39Identify@(ASG:max:=max,Print:=printlevel);
    phi:=wm.val1;
    pr:=wm.val2;
    msi:=wm.val3;
    F:=wm.val4;
    wm:=wm.val5;
    # =^= MULTIASSIGN =^=
    sporadic:=true;
  elif orgq=211341312 then
    #  3D4(2)
    # =v= MULTIASSIGN =v=
    wm:=tw3D42Identify@(ASG:max:=max,Print:=printlevel);
    phi:=wm.val1;
    pr:=wm.val2;
    msi:=wm.val3;
    F:=wm.val4;
    wm:=wm.val5;
    # =^= MULTIASSIGN =^=
    sporadic:=true;
  elif orgq=251596800 then
    #  G24
    # =v= MULTIASSIGN =v=
    wm:=G24Identify@(ASG:max:=max,Print:=printlevel);
    phi:=wm.val1;
    pr:=wm.val2;
    msi:=wm.val3;
    F:=wm.val4;
    wm:=wm.val5;
    # =^= MULTIASSIGN =^=
    sporadic:=true;
  elif orgq=4030387200 then
    #  He
    # =v= MULTIASSIGN =v=
    wm:=HeIdentify@(ASG:max:=max,Print:=printlevel);
    phi:=wm.val1;
    pr:=wm.val2;
    msi:=wm.val3;
    F:=wm.val4;
    wm:=wm.val5;
    # =^= MULTIASSIGN =^=
    sporadic:=true;
  elif orgq=4585351680 then
    #  S63 or O73
    # =v= MULTIASSIGN =v=
    wm:=S63O73Identify@(ASG:max:=max,Print:=printlevel);
    phi:=wm.val1;
    pr:=wm.val2;
    msi:=wm.val3;
    F:=wm.val4;
    wm:=wm.val5;
    # =^= MULTIASSIGN =^=
    sporadic:=true;
  elif orgq=5859000000 then
    #  G25
    # =v= MULTIASSIGN =v=
    wm:=G25Identify@(ASG:max:=max,Print:=printlevel);
    phi:=wm.val1;
    pr:=wm.val2;
    msi:=wm.val3;
    F:=wm.val4;
    wm:=wm.val5;
    # =^= MULTIASSIGN =^=
    sporadic:=true;
  elif orgq=9196830720 then
    #  U62
    # =v= MULTIASSIGN =v=
    wm:=U62Identify@(ASG:max:=max,Print:=printlevel);
    phi:=wm.val1;
    pr:=wm.val2;
    msi:=wm.val3;
    F:=wm.val4;
    wm:=wm.val5;
    # =^= MULTIASSIGN =^=
    sporadic:=true;
  elif orgq=47377612800 then
    #  S82
    # =v= MULTIASSIGN =v=
    wm:=S82Identify@(ASG:max:=max,Print:=printlevel);
    phi:=wm.val1;
    pr:=wm.val2;
    msi:=wm.val3;
    F:=wm.val4;
    wm:=wm.val5;
    # =^= MULTIASSIGN =^=
    sporadic:=true;
  elif orgq=24815256521932800 then
    #  S102
    # =v= MULTIASSIGN =v=
    wm:=S102Identify@(ASG:max:=max,Print:=printlevel);
    phi:=wm.val1;
    pr:=wm.val2;
    msi:=wm.val3;
    F:=wm.val4;
    wm:=wm.val5;
    # =^= MULTIASSIGN =^=
    sporadic:=true;
  elif orgq=495766656000 then
    #  CO3
    # =v= MULTIASSIGN =v=
    wm:=CO3Identify@(ASG:max:=max,Print:=printlevel);
    phi:=wm.val1;
    pr:=wm.val2;
    msi:=wm.val3;
    F:=wm.val4;
    wm:=wm.val5;
    # =^= MULTIASSIGN =^=
    sporadic:=true;
  elif orgq=10151968619520 then
    #  O-(8,3)
    # =v= MULTIASSIGN =v=
    wm:=Om83Identify@(ASG:max:=max,Print:=printlevel);
    phi:=wm.val1;
    pr:=wm.val2;
    msi:=wm.val3;
    F:=wm.val4;
    wm:=wm.val5;
    # =^= MULTIASSIGN =^=
    sporadic:=true;
  elif orgq=23499295948800 then
    #  O+(10,2)
    # =v= MULTIASSIGN =v=
    wm:=Op102Identify@(ASG:max:=max,Print:=printlevel);
    phi:=wm.val1;
    pr:=wm.val2;
    msi:=wm.val3;
    F:=wm.val4;
    wm:=wm.val5;
    # =^= MULTIASSIGN =^=
    sporadic:=true;
  elif orgq=25015379558400 then
    #  O-(10,2)
    # =v= MULTIASSIGN =v=
    wm:=Om102Identify@(ASG:max:=max,Print:=printlevel);
    phi:=wm.val1;
    pr:=wm.val2;
    msi:=wm.val3;
    F:=wm.val4;
    wm:=wm.val5;
    # =^= MULTIASSIGN =^=
    sporadic:=true;
  elif orgq=42305421312000 then
    #  CO2
    # =v= MULTIASSIGN =v=
    wm:=CO2Identify@(ASG:max:=max,Print:=printlevel);
    phi:=wm.val1;
    pr:=wm.val2;
    msi:=wm.val3;
    F:=wm.val4;
    wm:=wm.val5;
    # =^= MULTIASSIGN =^=
    sporadic:=true;
  elif orgq=64561751654400 then
    #  Fi22
    # =v= MULTIASSIGN =v=
    wm:=Fi22Identify@(ASG:max:=max,Print:=printlevel);
    phi:=wm.val1;
    pr:=wm.val2;
    msi:=wm.val3;
    F:=wm.val4;
    wm:=wm.val5;
    # =^= MULTIASSIGN =^=
    sporadic:=true;
  elif orgq=448345497600 then
    #  Suz
    # =v= MULTIASSIGN =v=
    wm:=SuzIdentify@(ASG:max:=max,Print:=printlevel);
    phi:=wm.val1;
    pr:=wm.val2;
    msi:=wm.val3;
    F:=wm.val4;
    wm:=wm.val5;
    # =^= MULTIASSIGN =^=
    sporadic:=true;
  elif orgq=145926144000 then
    #  Ru
    # =v= MULTIASSIGN =v=
    wm:=RuIdentify@(ASG:max:=max,Print:=printlevel);
    phi:=wm.val1;
    pr:=wm.val2;
    msi:=wm.val3;
    F:=wm.val4;
    wm:=wm.val5;
    # =^= MULTIASSIGN =^=
    sporadic:=true;
  fi;
  #   deal with some classicals 
  q:=type[3];
  if q > 0 then
    fac:=CollectedFactors(q);
    p:=fac[1][1];
  fi;
  classical:=false;
  if type[1]=1 and type[2]=1 then
    #  RGQ = PSL(2,q);
    if fac[1][2]=1 and p > 11 then
      #  PSL(2,p)
      if printlevel > 0 then
        Print("In PSL(2,p) case");
      fi;
      classical:=true;
      # =v= MULTIASSIGN =v=
      wm:=L2pIdentify@(ASG,q:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    elif fac[1][2]=2 and p > 3 then
      #  PSL(2,p^2)
      if printlevel > 0 then
        Print("In PSL(2,p^2) case");
      fi;
      classical:=true;
      # =v= MULTIASSIGN =v=
      wm:=L2p2Identify@(ASG,q:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    elif fac[1][2]=3 and p > 2 then
      #  PSL(2,p^3)
      if printlevel > 0 then
        Print("In PSL(2,p^3) case");
      fi;
      classical:=true;
      # =v= MULTIASSIGN =v=
      wm:=L2p3Identify@(ASG,q:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    elif fac[1][2] > 3 then
      #  PSL(2,p^e), e>3
      if printlevel > 0 then
        Print("In general PSL(2,q) case");
      fi;
      classical:=true;
      # =v= MULTIASSIGN =v=
      wm:=L2qIdentify@(ASG,q:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    fi;
  elif type[1]=1 and type[2]=2 then
    #  RGQ = PSL(3,q);
    if (fac[1][2]=1 and p > 3) or q=9 then
      #  PSL(3,p)
      if printlevel > 0 then
        Print("In PSL(3,p) case");
      fi;
      classical:=true;
      # =v= MULTIASSIGN =v=
      wm:=L3pIdentify@(ASG,q:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    elif fac[1][2]=2 and p > 2 then
      #  PSL(3,p^2)
      if printlevel > 0 then
        Print("In PSL(3,p^2) case");
      fi;
      classical:=true;
      # =v= MULTIASSIGN =v=
      wm:=L3p2Identify@(ASG,q:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    elif fac[1][2] > 2 then
      #  PSL(3,p^e), e>3
      if printlevel > 0 then
        Print("In general PSL(3,q) case");
      fi;
      classical:=true;
      # =v= MULTIASSIGN =v=
      wm:=L3qIdentify@(ASG,q:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    fi;
  elif type[1]=1 and type[2]=3 then
    #  RGQ = PSL(4,q);
    if fac[1][2]=1 and p > 3 then
      #  PSL(4,p)
      if printlevel > 0 then
        Print("In PSL(4,p) case");
      fi;
      classical:=true;
      # =v= MULTIASSIGN =v=
      wm:=L4pIdentify@(ASG,q:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    elif fac[1][2] > 1 then
      #  PSL(4,p^e), e > 1
      if printlevel > 0 then
        Print("In PSL(4,q) case");
      fi;
      classical:=true;
      # =v= MULTIASSIGN =v=
      wm:=L4qIdentify@(ASG,q:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    fi;
  elif type[1]=1 and type[2]=4 then
    #  RGQ = PSL(5,q);
    if fac[1][2]=1 and p > 2 then
      #  PSL(5,p)
      if printlevel > 0 then
        Print("In PSL(5,p) case");
      fi;
      classical:=true;
      # =v= MULTIASSIGN =v=
      wm:=L5pIdentify@(ASG,q:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    elif fac[1][2] > 1 then
      if printlevel > 0 then
        Print("In PSL(5,q) case");
      fi;
      classical:=true;
      # =v= MULTIASSIGN =v=
      wm:=L5qIdentify@(ASG,q:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    fi;
  elif type[1]=1 and type[2]=5 and q > 2 then
    #  RGQ = PSL(6,q);
    #   note that PSL(6,2) is in the database
    if fac[1][2]=1 and p > 3 then
      #  PSL(6,p)
      if printlevel > 0 then
        Print("In PSL(6,p) case");
      fi;
      classical:=true;
      # =v= MULTIASSIGN =v=
      wm:=L6pIdentify@(ASG,q:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    elif q=3 then
      #  RGQ = PSL(6,3);
      if printlevel > 0 then
        Print("In PSL(6,3) case");
      fi;
      classical:=true;
      # =v= MULTIASSIGN =v=
      wm:=L63Identify@(ASG:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    elif fac[1][2] > 1 then
      if printlevel > 0 then
        Print("In PSL(6,q) case");
      fi;
      classical:=true;
      # =v= MULTIASSIGN =v=
      wm:=L6qIdentify@(ASG,q:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    fi;
  elif type[1]=1 and type[2]=6 then
    #  RGQ = PSL(7,q);
    if fac[1][2]=1 and p > 3 then
      #  PSL(7,p)
      if printlevel > 0 then
        Print("In PSL(7,p) case");
      fi;
      classical:=true;
      # =v= MULTIASSIGN =v=
      wm:=L7pIdentify@(ASG,q:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    elif q=2 then
      #  RGQ = PSL(7,2);
      if printlevel > 0 then
        Print("In PSL(7,3) case");
      fi;
      classical:=true;
      # =v= MULTIASSIGN =v=
      wm:=L7_2Identify@(ASG:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    elif q=3 then
      #  RGQ = PSL(7,3);
      if printlevel > 0 then
        Print("In PSL(7,3) case");
      fi;
      classical:=true;
      # =v= MULTIASSIGN =v=
      wm:=L73Identify@(ASG:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    elif fac[1][2] > 1 then
      if printlevel > 0 then
        Print("In PSL(7,q) case");
      fi;
      classical:=true;
      # =v= MULTIASSIGN =v=
      wm:=L7qIdentify@(ASG,q:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    fi;
  elif q=2 and type[1]=1 and type[2] >= 7 and type[2] <= 13 then
    #  RGQ = PSL(d,2) 8 <= d <= 14;
    if printlevel > 0 then
      Print("In PSL(",type[2]+1,",2) case");
    fi;
    classical:=true;
    if type[2]+1=8 then
      # =v= MULTIASSIGN =v=
      wm:=L8_2Identify@(ASG:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    elif type[2]+1=9 then
      # =v= MULTIASSIGN =v=
      wm:=L9_2Identify@(ASG:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    elif type[2]+1=10 then
      # =v= MULTIASSIGN =v=
      wm:=L10_2Identify@(ASG:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    elif type[2]+1=11 then
      # =v= MULTIASSIGN =v=
      wm:=L11_2Identify@(ASG:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    elif type[2]+1=12 then
      # =v= MULTIASSIGN =v=
      wm:=L12_2Identify@(ASG:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    elif type[2]+1=13 then
      # =v= MULTIASSIGN =v=
      wm:=L13_2Identify@(ASG:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    elif type[2]+1=14 then
      # =v= MULTIASSIGN =v=
      wm:=L14_2Identify@(ASG:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    fi;
  elif type[1]=2 and type[2]=2 then
    #  RGQ = PSp(4,q);
    if fac[1][2]=1 then
      #  PSp(4,p)
      if p > 3 then
        if printlevel > 0 then
          Print("In PSp(4,p) case");
        fi;
        classical:=true;
        # =v= MULTIASSIGN =v=
        wm:=PSp4pIdentify@(ASG,q:max:=max,Print:=printlevel);
        phi:=wm.val1;
        pr:=wm.val2;
        msi:=wm.val3;
        F:=wm.val4;
        wm:=wm.val5;
        # =^= MULTIASSIGN =^=
      fi;
    else
      #  PSp(4,q)
      if printlevel > 0 then
        Print("In PSp(4,q) case");
      fi;
      classical:=true;
      # =v= MULTIASSIGN =v=
      wm:=PSp4qIdentify@(ASG,q:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    fi;
  elif type[1]=10 and type[2]=2 then
    #  RGQ = PSU(3,q);
    if fac[1][2]=1 then
      #  PSU(3,p)
      if p > 5 then
        if printlevel > 0 then
          Print("In PSU(3,p) case");
        fi;
        classical:=true;
        # =v= MULTIASSIGN =v=
        wm:=U3pIdentify@(ASG,q:max:=max,Print:=printlevel);
        phi:=wm.val1;
        pr:=wm.val2;
        msi:=wm.val3;
        F:=wm.val4;
        wm:=wm.val5;
        # =^= MULTIASSIGN =^=
      fi;
    else
      if printlevel > 0 then
        Print("In PSU(3,q) case");
      fi;
      classical:=true;
      # =v= MULTIASSIGN =v=
      wm:=U3qIdentify@(ASG,q:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    fi;
  elif type[1]=10 and type[2]=3 then
    #  RGQ = PSU(4,q);
    if q > 2 then
      if printlevel > 0 then
        Print("In PSU(4,q) case");
      fi;
      classical:=true;
      # =v= MULTIASSIGN =v=
      wm:=U4qIdentify@(ASG,q:max:=max,Print:=printlevel);
      phi:=wm.val1;
      pr:=wm.val2;
      msi:=wm.val3;
      F:=wm.val4;
      wm:=wm.val5;
      # =^= MULTIASSIGN =^=
    fi;
  elif q=2 and type[1]=4 and type[2]=4 then
    #  RGQ = Omega^+(8,2)
    if printlevel > 0 then
      Print("In Omega^+(8,2) case");
    fi;
    classical:=true;
    # =v= MULTIASSIGN =v=
    wm:=OPlus8_2Identify@(ASG:max:=max,Print:=printlevel);
    phi:=wm.val1;
    pr:=wm.val2;
    msi:=wm.val3;
    F:=wm.val4;
    wm:=wm.val5;
    # =^= MULTIASSIGN =^=
  elif q=2 and type[1]=12 and type[2]=4 then
    #  RGQ = Omega^-(8,2)
    if printlevel > 0 then
      Print("In Omega^-(8,2) case");
    fi;
    classical:=true;
    # =v= MULTIASSIGN =v=
    wm:=OMinus8_2Identify@(ASG:max:=max,Print:=printlevel);
    phi:=wm.val1;
    pr:=wm.val2;
    msi:=wm.val3;
    F:=wm.val4;
    wm:=wm.val5;
    # =^= MULTIASSIGN =^=
  fi;
  if sporadic or classical then
    if max then
      msiims:=List(msi,G->rec(generators:=List([1..Ngens(G)],i->G.i),
        order:=Size(G)));
    else
      msiims:=[];
    fi;
    phi:=tau*phi;
    return rec(val1:=phi,
      val2:=pr,
      val3:=msiims,
      val4:=F,
      val5:=wm);
  fi;
  if orgq > 20158709760 then
    foundx:=false;
  else
    # =v= MULTIASSIGN =v=
    storedgp:=SGDBAccess@(orgq,ogq,ASG);
    foundx:=storedgp.val1;
    storedgp:=storedgp.val2;
    # =^= MULTIASSIGN =^=
  fi;
  if printlevel > 0 then
    Print("In general case");
  fi;
  if not foundx then
    Error("Sorry, the top factor of order",ogq,"is not currently stored");
  fi;
  if printlevel > 0 then
    if ogq > orgq then
      Print("The almost simple group is",storedgp.name,"with soluble 
       residual",storedgp.resname);
    else
      Print("The almost simple group is",storedgp.name);
    fi;
  fi;
  if printlevel > 1 then
    Print("+Mapping group from database onto almost simple group.");
  fi;
  #   print storedgp;
  geninfo:=storedgp.geninfo;
  #   print geninfo;
  ox:=geninfo[1][1];
  oy:=geninfo[2][1];
  rels:=storedgp.rels;
  #   print rels;
  conjelts:=storedgp.conjelts;
  #   print conjelts;
  oims:=storedgp.outimages;
  #    print oims;
  sg:=storedgp.subgens;
  #   print sg;
  pr:=storedgp.permrep;
  #   print pr;
  msi:=storedgp.maxsubints;
  #   print msi;
  # =v= MULTIASSIGN =v=
  proj:=Subquo(Parent(rels[1]),[$.1^ox,$.2^oy,rels]);
  RF:=proj.val1;
  proj:=proj.val2;
  # =^= MULTIASSIGN =^=
  foundx:=false;
  while not foundx do
    el:=Random(RGQ);
    el_ord:=Order(el);
    if el_ord mod ox=0 then
      imx:=el^(QuoInt(el_ord,ox));
      #   	if #Class(RGQ, imx) eq geninfo[1][2] then
      if Index(RGQ,Centralizer(RGQ,imx))=geninfo[1][2] then
        foundx:=true;
      fi;
    fi;
  od;
  foundhom:=false;
  while not foundhom do
    el:=Random(RGQ);
    el_ord:=Order(el);
    if el_ord mod oy<>0 then
      continue;
    fi;
    imy:=el^(QuoInt(el_ord,oy));
    phi:=GroupHomomorphismByImages(RF,RGQ,
      GeneratorsOfGroup(RF),[imx,imy]);
    ok:=true;
    for w in rels do
      if not phi(w)=One(RGQ) then
        ok:=false;
        break;
      fi;
    od;
    if ok then
      foundhom:=true;
    fi;
  od;
  if printlevel > 1 then
    Print("+Found map onto soluble residual of almost simple group");
  fi;
  if Size(conjelts) > 0 then
    origimx:=imx;
    origimy:=imy;
  fi;
  foundgqhom:=false;
  isinner:=true;
  conjeltct:=0;
  while not foundgqhom do
    if conjeltct > 0 then
      if printlevel > 2 then
        Print("+Trying conjugates of generators");
      fi;
      #   We have to replace our elements imx and imy by conjugates
      #  * under the automorphism of RGQ defined by conjelts[conjeltct]
      
      w:=conjelts[conjeltct];
      aut:=CalculateIsomRGQH@(RGQ,w,rgqauts);
      imx:=origimx@aut;
      imy:=origimy@aut;
      phi:=GroupHomomorphismByImages(RF,RGQ,
        GeneratorsOfGroup(RF),[imx,imy]);
    fi;
    RGQ:=SubStructure(RGQ,[imx,imy]);
    GQgens:=[imx,imy];
    prgens:=[pr.1,pr.2];
    #   Next locate specified automorphisms of RGQ in GQ 
    if Size(oims)<>0 then
      rgqauts:=OuterAutsRGQH@(RGQ,oims,proj*GroupHomomorphismByImages(RF,RGQ,
        GeneratorsOfGroup(RF),[imx,imy]),printlevel);
    fi;
    for k in [1..Size(sg)] do
      w:=sg[k];
      aut:=CalculateIsomRGQH@(RGQ,w,rgqauts);
      #   find element of GQ inducing this aut 
      # =v= MULTIASSIGN =v=
      el:=IsInnerAutomorphism(GQ,RGQ,aut);
      isinner:=el.val1;
      el:=el.val2;
      # =^= MULTIASSIGN =^=
      if not isinner then
        if conjeltct=Size(conjelts) then
          Error("Failed to find required inner aut of radical quotient");
        fi;
        conjeltct:=conjeltct+1;
        break;
      fi;
      Add(GQgens,el);
      ws:=ElementToSequence(w);
      el:=One(pr);
      for i in ws do
        if i > 0 then
          el:=el*pr.(i+2);
        else
          el:=el*(pr.(-i+2))^-1;
        fi;
      od;
      Add(prgens,el);
    od;
    if not isinner then
      continue;
    fi;
    foundgqhom:=true;
  od;
  #   while not foundgqhom...
  if printlevel > 1 then
    Print("+Completed identification of almost simple group.");
  fi;
  GQnew:=SubStructure(GQ,GQgens);
  #   We may need to add some extra generators from C to get GQ
  #   BEWARE - Bill Unger's change to avoid verification of GQnew
  if Type(GQ)=GrpPerm then
    IncorporateCentralisingGenerators@(GQ,GQnew,C,prgens);
  else
    while GQnew<>GQ do
      el:=Random(C);
      if not el in GQnew then
        Add(GQgens,el);
        Add(prgens,One(pr));
        GQnew:=SubStructure(GQ,GQgens);
        RandomSchreier(GQnew);
      fi;
    od;
  fi;
  inj:=GroupHomomorphismByImages(GQnew,pr,
    GeneratorsOfGroup(GQnew),prgens);
  msiims:=[];
  if max then
    for subgp in msi do
      copysg:=subgp;
      copysg.generators:=List(subgp.generators,gg->gg@phi@inj);
      Add(msiims,copysg);
    od;
  fi;
  if orgq <= 5000 then
    return rec(val1:=inj,
      val2:=pr,
      val3:=msiims,
      val4:=RF,
      val5:=GroupHomomorphismByImages(RF,pr,
      GeneratorsOfGroup(RF),[pr.1,pr.2]));
  else
    H:=SubStructure(pr,[pr.1,pr.2]);
    H.Order:=orgq;
    # =v= MULTIASSIGN =v=
    wm:=FPGroupStrong(H);
    F:=wm.val1;
    wm:=wm.val2;
    # =^= MULTIASSIGN =^=
    return rec(val1:=inj,
      val2:=pr,
      val3:=msiims,
      val4:=F,
      val5:=wm);
  fi;
end);

#   In the following functions, G should be a permutation group known to be
#  * isomorphic to  Sym(n) or Alt(n) for a given value of n > 8.
#  * An explicit isomorphism G->S_n/A_n is returned plus the image S_n/A_n.
#  * The free group of rank 2 + the the maximal subgroups of G
#  *  are also returned.
#  * (The free group is ignored by calling functions and is there for backward
#  *  compatibility.)
#  * The main point is to find elements of G that map onto the standard
#  * generators (1,2) and (1,2,3,4,...,n) of S_n, or to
#  * (1,2,3), (1,2,3,...,n) or (2,3,..,n) of A_n.
#  * The cases Sym(n), Alt(n), n even or odd are treated in four separate
#  * functions.
#  * The Bratus-Pak algorithm is used, with variations for n < 20.
#  * (Note: Their description for Alt(n) is very incomplete!!)

#  Forward declaration of IntransitiveSubgroupsAltSym
#  Forward declaration of ImprimitiveSubgroupsAltSym
#  Forward declaration of PrimitiveSubgroupsAltSym
InstallGlobalFunction(IdentifySymEvenDeg@,
function(G,n,printlevel)
#  /out: case n even, G=Sym(n)
local P,S,f,g,g1,g2,l,max,seeking,sl,st,subs,t,x;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  #  first seek Goldbach element.
  if printlevel > 2 then
    Print("+Identifying Sym(n) even degree case");
  fi;
  if n <= 8 then
    Error("Use IdentifySymEvenDeg only for degree at least 10");
  fi;
  seeking:=true;
  while seeking do
    g:=Random(G);
    f:=CollectedFactors(Order(g));
    if Size(f)=2 and f[1][2]=1 and f[2][2]=1 and f[1][1]+f[2][1]=n then
      seeking:=false;
      g1:=g^f[2][1];
      g2:=g^f[1][1];
    fi;
  od;
  #  next a transposition
  seeking:=true;
  while seeking do
    t:=Random(G);
    f:=CollectedFactors(Order(t));
    if Size(f)=3 and f[1][1]=2 and f[1][2]=1 and f[2][2]=1 and f[3][2]=1 and 
       f[2][1]+f[3][1]+2=n then
      t:=t^(f[2][1]*f[3][1]);
      seeking:=false;
    fi;
  od;
  #  get a conjugate commuting with neither g1 nor g2.
  seeking:=true;
  while seeking do
    x:=Random(G);
    t:=t^x;
    if Tuple([t,g1])<>One(G) and Tuple([t,g2])<>One(G) then
      seeking:=false;
    fi;
  od;
  #  finally an n-cycle
  l:=g1*t*g2;
  P:=SubStructure(G,l,#TODO CLOSURE
    t);
  if P<>G then
    Error("Generation problem in IdentifySymEvenDeg");
  fi;
  S:=SubStructure(SymmetricGroup(n),AlternatingGroup(n),#TODO CLOSURE
    Tuple([1,2]));
  #   we want alternating generators first.
  sl:=(Concatenation([2..n],[1])) #CAST S
    ;
  st:=Tuple([1,2]) #CAST S
    ;
  if printlevel > 2 then
    Print("+Completed identification - getting maximal subgroups");
  fi;
  # rewritten select statement
  if max then
    subs:=Concatenation(IntransitiveSubgroupsAltSym@(n,true)
     ,ImprimitiveSubgroupsAltSym@(n,true),PrimitiveSubgroupsAltSym@(n,true));
  else
    subs:=[];
  fi;
  return rec(val1:=GroupHomomorphismByImages(P,S,
    sl,st),
    val2:=S,
    val3:=subs);
end);

InstallGlobalFunction(IdentifySymOddDeg@,
function(G,n,printlevel)
#  /out: case n odd, G=Sym(n)
local P,S,f,g,g1,g2,l,max,o,seeking,sl,st,subs,t,u,x;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  if printlevel > 2 then
    Print("+Identifying Sym(n) odd degree case");
  fi;
  #  first seek Goldbach element.
  if n <= 8 then
    Error("Use IdentifySymOddDeg only for degree at least 9");
  fi;
  seeking:=true;
  while seeking do
    g:=Random(G);
    f:=CollectedFactors(Order(g));
    if Size(f)=2 and f[1][2]=1 and f[2][2]=1 and f[1][1]+f[2][1]=n-1 then
      seeking:=false;
      g1:=g^f[2][1];
      g2:=g^f[1][1];
    fi;
  od;
  #  next a transposition
  seeking:=true;
  while seeking do
    t:=Random(G);
    o:=Order(t);
    f:=CollectedFactors(o);
    if (n=9 and o=14) or (n=11 and o=18) or (n=13 and o=22) or (n=15 and o=26) 
       or (n=17 and o=210) or (n=19 and o=34) or (o >= 21 and Size(f)=4 and f[1]
       [1]=2 and f[1][2]=1 and f[2][1]=3 and f[2][2]=1 and f[3][2]=1 and f[4][2]
       =1 and f[3][1]+f[4][1]+5=n) then
      seeking:=false;
      t:=t^(QuoInt(o,2));
    fi;
  od;
  #  get a conjugate commuting with neither g1 nor g2.
  seeking:=true;
  while seeking do
    x:=Random(G);
    t:=t^x;
    if Tuple([t,g1])<>One(G) and Tuple([t,g2])<>One(G) then
      seeking:=false;
    fi;
  od;
  #   get a conjugate of t commuting with g1 but not g2 and touching fixed
  #  point.
  seeking:=true;
  while seeking do
    x:=Random(G);
    u:=t^x;
    if Tuple([u,g1])=One(G) and Tuple([u,g2])<>One(G) and Tuple([u,u^g2])
       <>One(G) and Tuple([u,u^(g2^2)])<>One(G) then
      seeking:=false;
    fi;
  od;
  #  finally an n-cycle
  l:=g1*t*g2*u;
  P:=SubStructure(G,l,#TODO CLOSURE
    t);
  if P<>G then
    Error("Generation problem in IdentifySymOdd");
  fi;
  S:=SubStructure(SymmetricGroup(n),AlternatingGroup(n),#TODO CLOSURE
    Tuple([1,2]));
  #   we want alternating generators first.
  st:=Tuple([1,2]) #CAST S
    ;
  sl:=(Concatenation([2..n],[1])) #CAST S
    ;
  if printlevel > 2 then
    Print("+Completed identification - getting maximal subgroups");
  fi;
  # rewritten select statement
  if max then
    subs:=Concatenation(IntransitiveSubgroupsAltSym@(n,true)
     ,ImprimitiveSubgroupsAltSym@(n,true),PrimitiveSubgroupsAltSym@(n,true));
  else
    subs:=[];
  fi;
  return rec(val1:=GroupHomomorphismByImages(P,S,
    sl,st),
    val2:=S,
    val3:=subs);
end);

InstallGlobalFunction(IdentifyAltOddDeg@,
function(G,n,printlevel)
#  /out: case n odd, G=Alt(n)
local P,S,f,g,g1,g2,l,max,o,seeking,sl,st,subs,t,x;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  if printlevel > 2 then
    Print("+Identifying Alt(n) odd degree case");
  fi;
  #  first seek Goldbach element.
  if n <= 8 then
    Error("Use IdentifyAltOddDeg only for degree at least 9");
  fi;
  seeking:=true;
  while seeking do
    g:=Random(G);
    f:=CollectedFactors(Order(g));
    if Size(f)=2 and f[1][2]=1 and f[2][2]=1 and f[1][1]+f[2][1]=n-1 then
      seeking:=false;
      g1:=g^f[2][1];
      g2:=g^f[1][1];
    fi;
  od;
  #  next a 3-cycle
  seeking:=true;
  while seeking do
    t:=Random(G);
    o:=Order(t);
    f:=CollectedFactors(o);
    if (n=9 and o=15) or (n=11 and o=21) or (n=13 and o=24) or (n=15 and o=105) 
       or (n=17 and o=39) or (o >= 19 and Size(f)=3 and f[1][1]=3 and f[1][2]=1 
       and f[2][2]=1 and f[3][2]=1 and f[2][1]+f[3][1]+3=n) then
      seeking:=false;
      t:=t^(QuoInt(o,3));
    fi;
  od;
  #  get a conjugate commuting with neither g1 nor g2
  #  and touching the fixed point.
  seeking:=true;
  while seeking do
    x:=Random(G);
    t:=t^x;
    if Tuple([t,g1])<>One(G) and Tuple([t,g2])<>One(G) and Tuple([t^g1,t^g2])
       <>One(G) and Tuple([t^g1,t^(g2^2)])<>One(G) and Tuple([t^(g1^2),t^g2])
       <>One(G) and Order(t*t^g1)=2 then
      #   The final condition rules out Order(g1)=3 and t touches g1 twice.
      seeking:=false;
    fi;
  od;
  #  finally an n-cycle - we have to find out whether we want g1*t*g2 or 
   g2*t*g1
  l:=g1*t*g2;
  if Order(t*t^l)<>2 then
    l:=g2*t*g1;
  fi;
  P:=SubStructure(G,l,#TODO CLOSURE
    t);
  if P<>G then
    Error("Generation problem in IdentifyAltOdd");
  fi;
  S:=SubStructure(SymmetricGroup(n),AlternatingGroup(n),#TODO CLOSURE
    Tuple([1,2]));
  #   we want alternating generators first.
  sl:=(Concatenation([2..n],[1])) #CAST S
    ;
  st:=(1,2,3) #CAST S
    ;
  if printlevel > 2 then
    Print("+Completed identification - getting maximal subgroups");
  fi;
  # rewritten select statement
  if max then
    subs:=Concatenation(IntransitiveSubgroupsAltSym@(n,false)
     ,ImprimitiveSubgroupsAltSym@(n,false),PrimitiveSubgroupsAltSym@(n,false));
  else
    subs:=[];
  fi;
  return rec(val1:=GroupHomomorphismByImages(P,S,
    sl,st),
    val2:=S,
    val3:=subs);
end);

InstallGlobalFunction(IdentifyAltEvenDeg@,
function(G,n,printlevel)
#  /out: case n odd, G=Alt(n)
local P,S,f,g,g1,g2,l,max,o,seeking,sl,st,subs,t,u,x;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  if printlevel > 2 then
    Print("+Identifying Alt(n) even degree case");
  fi;
  #  first seek Goldbach element fixing two points.
  if n <= 8 then
    Error("Use IdentifyAltEvenDeg only for degree at least 10");
  fi;
  seeking:=true;
  while seeking do
    g:=Random(G);
    f:=CollectedFactors(Order(g));
    if Size(f)=2 and f[1][2]=1 and f[2][2]=1 and f[1][1]+f[2][1]=n-2 then
      seeking:=false;
      g1:=g^f[2][1];
      g2:=g^f[1][1];
    fi;
  od;
  #  next a 3-cycle
  seeking:=true;
  while seeking do
    t:=Random(G);
    o:=Order(t);
    f:=CollectedFactors(o);
    if (n=10 and o=21) or (n=12 and o=21) or (n=14 and o=33) or (n=16 and o=39) 
       or (n=18 and o=39) or (o >= 20 and Size(f)=3 and f[1][1]=3 and f[1][2]=1 
       and f[2][2]=1 and f[3][2]=1 and f[2][1]+f[3][1]+4=n) then
      seeking:=false;
      t:=t^(QuoInt(o,3));
    fi;
  od;
  #  get a conjugate commuting with neither g1 nor g2
  #  and touching one of the fixed points.
  seeking:=true;
  while seeking do
    x:=Random(G);
    t:=t^x;
    if Tuple([t,g1])<>One(G) and Tuple([t,g2])<>One(G) and Tuple([t^g1,t^g2])
       <>One(G) and Tuple([t^g1,t^(g2^2)])<>One(G) and Tuple([t^(g1^2),t^g2])
       <>One(G) and Order(t*t^g1)=2 then
      #   The final condition rules out Order(g1)=3 and t touches g1 twice.
      seeking:=false;
    fi;
  od;
  #  now an (n-1)-cycle - we have to find out whether we want g1*t*g2 or 
   g2*t*g1
  l:=g1*t*g2;
  if Order(t*t^l)<>2 then
    l:=g2*t*g1;
  fi;
  #  now a conjugate of t commuting with t and fixing the other fixed point of 
   g
  seeking:=true;
  while seeking do
    x:=Random(G);
    u:=t^x;
    if Tuple([u,g1])<>One(G) and Tuple([u,g2])<>One(G) and Tuple([u^g1,u^g2])
       <>One(G) and Tuple([u^g1,u^(g2^2)])<>One(G) and Tuple([u^(g1^2),u^g2])
       <>One(G) and Order(u*u^g1)=2 and t<>u and t<>u^2 and Tuple([t,u])=One(G) 
       then
      seeking:=false;
    fi;
  od;
  #  conjugate t until it does not commute with u
  while Tuple([t,u])=One(G) do
    t:=t^l;
  od;
  #  Now either t^u or t^(u^-1) is a suitable 3-cycle.
  # rewritten select statement
  if Order(t^u*t^(u*l))=3 then
    t:=t^u;
  else
    t:=t^(u^-1);
  fi;
  P:=SubStructure(G,l,#TODO CLOSURE
    t);
  if P<>G then
    Error("Generation problem in IdentifyAltOdd");
  fi;
  S:=SubStructure(SymmetricGroup(n),AlternatingGroup(n),#TODO CLOSURE
    Tuple([1,2]));
  #   we want alternating generators first.
  sl:=(Concatenation([1],[3..n],[2])) #CAST S
    ;
  st:=(1,2,3) #CAST S
    ;
  if printlevel > 2 then
    Print("+Completed identification - getting maximal subgroups");
  fi;
  # rewritten select statement
  if max then
    subs:=Concatenation(IntransitiveSubgroupsAltSym@(n,false)
     ,ImprimitiveSubgroupsAltSym@(n,false),PrimitiveSubgroupsAltSym@(n,false));
  else
    subs:=[];
  fi;
  return rec(val1:=GroupHomomorphismByImages(P,S,
    sl,st),
    val2:=S,
    val3:=subs);
end);

InstallGlobalFunction(IntransitiveSubgroupsAltSym@,
function(n,sym)
#  /out: return the intransitive maximal subgroups of Alt(n) or Sym(n)
local A,P,varX,Y,d,dummy,subs;
  subs:=[];
  A:=AlternatingGroup(n);
  for d in [1..QuoInt((n-1),2)] do
    varX:=SymmetricGroup(d);
    dummy:=Size(varX);
    Y:=SymmetricGroup(n-d);
    dummy:=Size(Y);
    P:=DirectProduct(varX,Y);
    if (sym) then
      Add(subs,P);
    else
      Add(subs,Intersection(P,A));
    fi;
  od;
  return subs;
end);

InstallGlobalFunction(ImprimitiveSubgroupsAltSym@,
function(n,sym)
#  /out: return the imprimitive maximal subgroups of Alt(n) or Sym(n)
#  intersected/out: with Alt(n).  sym is true according to whether we have
#  Sym(n) or Alt(n).
local A,P,varX,Y,d,dummy,subs;
  subs:=[];
  A:=AlternatingGroup(n);
  for d in DivisorsInt(n) do
    if d<>1 and d<>n then
      if n=8 and d=2 and not sym then
        continue;
        #   the only case of nonmaximality - lies in AGL(3,2)
      fi;
      varX:=SymmetricGroup(d);
      dummy:=Size(varX);
      Y:=SymmetricGroup(QuoInt(n,d));
      dummy:=Size(Y);
      P:=WreathProduct(varX,Y);
      if (sym) then
        Add(subs,P);
      else
        Add(subs,Intersection(P,A));
      fi;
    fi;
  od;
  return subs;
end);

InstallGlobalFunction(PrimitiveSubgroupsAltSym@,
function(n,sym)
#  /out: return the primitive maximal subgroups of Alt(n) or Sym(n)
#  intersected/out: with Alt(n). sym is true according to whether we have
#  Sym(n) or Alt(n).
local A,P,d,maxprim,subs,x;
  #   The n-th component of the following list consists of a list of 3 lists.
  #  * (i) those d such that PrimitiveGroup(n,d) is maximal in Sym(n)
  #  * (ii) those d such that PrimitiveGroup(n,d) is maximal in Alt(n)
  #  * (iii) those d as in (ii) for which there are two conjugacy classes
  #  *       of corresponding subgroups in Alt(n). We conjugate
  #  *      PrimitiveGroup(n,d) by (1,2) to get one in the other class.
  
  maxprim:=[[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[3],[2],[]],[[2],[1],[]
   ],[[4],[5],[5]],[[5],[3],[3]],[[7],[6,9],[9]],[[7],[6],[]],[[4],[6],[6]],[[2]
   ,[4],[4]],[[6],[5,7],[7]],[[2],[1],[]],[[],[4],[4]],[[],[20],[20]],[[5],[8]
   ,[8]],[[2],[1],[]],[[6],[5],[]],[[2],[1],[]],[[1,3,7],[2,6],[]],[[2],[1],[]]
   ,[[4],[5],[5]],[[2],[3],[3]],[[22,26],[21,24],[]],[[5],[2],[]],[[11],[13,10]
   ,[13]],[[11],[9,12],[12]],[[],[],[]],[[],[],[]],[[],[9,10],[9,10]],[[],[3]
   ,[3]],[[],[2],[2]],[[],[],[]],[[],[4],[4]],[[19,8],[18,20],[20]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[4,6],[2,5],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[5],[4,7],[7]],[[],[],[]],[[],[],[]],[[],[],[]],[[33,38],[32,37],[]]
   ,[[6],[2,7],[7]],[[],[],[]],[[],[1],[1]],[[],[],[]],[[],[],[]],[[2,3,6],[5]
   ,[]],[[6,7],[2,4],[]],[[],[1,3],[1,3]],[[],[],[]],[[],[],[]],[[5],[4],[]],[[]
   ,[],[]],[[],[],[]],[[4],[1,6],[6]],[[],[64,72],[64,72]],[[2],[1,5,7,11]
   ,[5,7,11]],[[],[5],[5]],[[],[],[]],[[3],[2],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[14],[14]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[2],[2]]
   ,[[2,4],[1,3],[]],[[],[],[]],[[],[],[]],[[145,153],[144,152],[]],[[8],[6],[]]
   ,[[],[],[]],[[3],[1],[]],[[4],[3],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[6],[4,5,8],[4,8]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[32,34,36],[33,35],[]],[[]
   ,[],[]],[[],[1],[1]],[[],[],[]],[[],[],[]],[[3,9],[7,8],[7]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[8],[8]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[3],[3]],[[],[],[]],[[],[2],[2]],[[10]
   ,[8,19,21],[19,21]],[[48,54],[47,53,55],[55]],[[5],[3],[]],[[],[],[]],[[],[]
   ,[]],[[33,43],[32,40],[]],[[12,13,17],[6,8,10,15],[6]],[[],[13],[13]],[[],[3]
   ,[3]],[[],[2],[2]],[[5],[2],[]],[[],[],[]],[[],[],[]],[[],[1],[1]],[[],[],[]]
   ,[[],[3],[3]],[[3,12],[10,11],[10]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[10,12,14],[10,12,14]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[4],[4]],[[],[],[]],[[],[1],[1]],[[3,7],[1,6],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[5],[3],[]],[[],[],[]],[[],[],[]],[[4]
   ,[2,5],[5]],[[],[],[]],[[],[],[]],[[5],[4],[]],[[68,73],[67,72],[]],[[5],[3]
   ,[]],[[2,4],[1,3],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[2],[1,4],[4]],[[]
   ,[3,4],[3,4]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[2],[2]],[[],[],[]],[[],[],[]],[[],[1],[1]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[4],[4]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[8],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[1],[1]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[3],[3]]
   ,[[],[],[]],[[4],[2,3],[2]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[20],[20]],[[],[],[]],[[],[],[]],[[],[],[]],[[3],[2],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[10],[8],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[4],[4]],[[],[],[]],[[],[],[]],[[],[2],[2]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[34],[33],[]],[[4],[3],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[1],[1]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[3,7],[1,2,4,6],[1,4]]
   ,[[],[],[]],[[],[2],[2]],[[],[238,242],[238,242]],[[],[13],[13]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[1],[1]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[6],[6]],[[],[],[]],[[],[2],[2]],[[],[4,6],[4,6]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[11,12,14,22],[9,10,13,19],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[1],[1]],[[2],[1],[]],[[],[],[]],[[],[],[]],[[80,95]
   ,[79,93],[]],[[5],[3],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[2],[1],[]],[[],[],[]],[[],[],[]],[[5,7,9],[2,6,8],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[13],[13]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[2],[1,3],[3]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[8],[],[]],[[10],[7,9,12],[7,12]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[2,4],[2,4]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[6,7],[6,7]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[2],[1],[]],[[],[],[]],[[76,88],[75,85],[]],[[6],[2,5],[2]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[4,7,9]
   ,[3,6,8],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[5],[2]
   ,[]],[[],[],[]],[[],[],[]],[[16],[11],[]],[[86,90],[85,88],[]],[[5],[4],[]]
   ,[[],[],[]],[[5,9],[3,7,8],[7]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[3],[2],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[7,9],[7,9]],[[],[],[]],[[],[],[]],[[],[2],[2]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[2],[2]],[[],[],[]],[[],[],[]],[[],[],[]],[[11,14],[8,9,13],[8]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[2,4],[1,3],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[5],[5]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[1],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[4],[4]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[22],[20]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[2],[2]],[[],[2],[2]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[6],[6]],[[],[],[]],[[],[],[]],[[2,3,5],[1,4],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[8],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[4]
   ,[2,8],[8]],[[],[8,10],[8,10]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[4],[4]],[[],[],[]],[[],[1],[1]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[1],[1]],[[],[36,56],[36,56]],[[]
   ,[9,12],[9,12]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[7],[4,6],[4]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[6],[4,5]
   ,[5]],[[],[],[]],[[],[2],[2]],[[7],[5,6],[5]],[[58,63],[57,61],[]],[[5],[4]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[8],[7],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[1],[1]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[4],[2,3],[2]],[[],[2],[2]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[5],[5]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[1],[1]],[[],[],[]],[[],[9],[9]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[4],[4]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[2],[1],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[2],[2]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[1],[1]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[647,692,696],[646,689,695],[]],[[8],[7],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[2],[2]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[1,5],[1,5]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[2],[2]],[[],[],[]],[[],[],[]],[[5],[2],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[2,4],[1,3],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[2],[2]],[[],[6],[6]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[28],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[2],[1],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[4],[3],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[4],[4]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[2],[1],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[471,495,499]
   ,[470,492,498],[]],[[3,13],[2,12],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[2]
   ,[1],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[1],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[],[5],[5]],[[],[26],[26]],[[],[],[]],[[],[1],[1]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[2],[1],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[1],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[2],[2]],[[]
   ,[1],[1]],[[],[],[]],[[],[],[]],[[],[36],[36]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[2],[2]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[8],[6],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[2],[2]],[[],[],[]],[[],[],[]],[[4],[3,6],[6]],[[2,11,20,22]
   ,[1,8,17,21],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[2,4],[2,4]],[[110,114],[109,113],[]],[[5],[3],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[4],[4]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[1],[1]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[1],[1]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[4],[4]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[8],[],[]],[[],[],[]],[[],[],[]],[[2,4],[1,3],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[3],[1],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[2],[2]],[[],[4],[4]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[5,8],[5,8]]
   ,[[126,132],[125,131],[]],[[5],[4],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[2],[2]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[2],[2]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[2],[1],[]],[[],[],[]],[[],[],[]],[[]
   ,[2],[2]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[105],[105]],[[],[2],[2]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[2,7],[2,7]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[1],[1]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[2],[2]],[[],[105,113]
   ,[105,113]],[[],[2,6],[2,6]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[2],[2]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[3],[1,5],[5]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[1],[1]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[2],[2]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[5],[4],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[2],[2]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[3,9],[2,8],[]],[[2,4],[1,3],[]],[[],[],[]
   ],[[],[],[]],[[],[],[]],[[1],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[8],[7]
   ,[]],[[],[],[]],[[],[],[]],[[5],[4],[]],[[],[25],[25]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[4],[2,3],[3]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[2],[1,5],[5]],[[],[],[]],[[],[2],[2]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[5,14],[14]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[4]
   ,[4]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[2],[1],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[4],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[5,9]
   ,[3,7,8],[7]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[1],[1]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[12,19],[10,18,21],[21]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[2],[1],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[2],[2]],[[],[2],[2]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[127,131,133],[127,131,133]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[2],[2]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[2],[2]],[[],[],[]],[[],[],[]],[[],[],[]],[[2],[1],[]]
   ,[[76,90],[75,89],[]],[[8],[4,7],[4]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[3],[3]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[4,12],[2,6,11],[6]],[[],[],[]],[[],[],[]],[[],[],[]],[[136,140]
   ,[135,138],[]],[[5],[4],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[2,4],[1,3],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[2],[2]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[2],[2]],[[],[4]
   ,[4]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[4],[4]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[1],[1]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[8],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[2,3]
   ,[2,3]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[1],[1]],[[3,6],[1,5],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[2],[1],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[4],[2],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[1,3,5],[1,3,5]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[2,7],[1,5],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[4],[4]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[1],[1]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[4],[1,2,3],[1,2]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[16,19,20],[16,19,20]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[2],[2]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[2],[2]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[188,192],[187,191],[]],[[5],[4],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[3,5],[1,2,4],[1]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[4],[4]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[17],[17]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[24],[24]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[3],[1,4],[4]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[2],[2]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[8],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[4],[4]],[[],[2,4],[2,4]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[2],[1],[]],[[],[],[]],[[],[],[]],[[],[3],[3]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[2],[1],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[2],[2]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[2,4],[1,3],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[126,130],[125,128],[]],[[5],[3],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[1,5],[1,5]],[[],[],[]],[[],[2],[2]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[8],[8]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[1,3],[2],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[2],[1],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[2],[2]],[[],[16,18],[16,18]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[3],[2],[]],[[32,33],[30,34],[34]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[1],[1]],[[],[12],[12]],[[],[2],[2]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[2],[1],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[2],[2]],[[17],[15,16],[15]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[5],[4],[]],[[2],[1],[]],[[],[],[]],[[2],[1],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[4],[],[]],[[],[],[]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[2]
   ,[2]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[1],[1]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[71],[70],[]],[[4],[3],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[158,170],[157,169],[]],[[6],[2,5]
   ,[2]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[70,74],[69,73],[]],[[5],[3],[]]
   ,[[2,4],[1,3],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[1],[1]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[4],[4]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[2],[2]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[3]
   ,[1,2],[1]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[8,10],[8,10]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[2],[1],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[4,6,9],[2,5,8],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[1179,1229,1233]
   ,[1178,1226,1232],[]],[[8],[6],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]
   ],[[],[],[]],[[],[2],[2]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[2],[2]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[5],[2],[]],[[],[],[]],[[],[],[]],[[4],[3],[]],[[],[],[]],[[],[],[]],[[],[]
   ,[]],[[],[],[]],[[],[],[]],[[],[2],[2]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[2],[2]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]]
   ,[[],[],[]],[[],[],[]],[[],[],[]],[[2,4],[1,3],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[]
   ,[],[]],[[],[],[]],[[],[],[]],[[],[],[]],[[],[],[]],#NOP
  ];
  #   1
  #   2
  #   3
  #   4
  #   5
  #   6
  #   7
  #   8
  #   9
  #   10
  #   11
  #   12
  #   13
  #   14
  #   15
  #   16
  #   17
  #   18
  #   19
  #   20
  #   21
  #   22
  #   23
  #   24
  #   25
  #   26
  #   27
  #   28
  #   29
  #   30
  #   31
  #   32
  #   33
  #   34
  #   35
  #   36
  #   37
  #   38
  #   39
  #   40
  #   41
  #   42
  #   43
  #   44
  #   45
  #   46
  #   47
  #   48
  #   49
  #  50
  #  51
  #  52
  #  53
  #  54
  #  55
  #  56
  #  57
  #  58
  #  59
  #  60
  #  61
  #  62
  #  63
  #  64
  #  65
  #  66
  #  67
  #  68
  #  69
  #  70
  #  71
  #  72
  #  73
  #  74
  #  75
  #  76
  #  77
  #  78
  #  79
  #  80
  #  81
  #  82
  #  83
  #  84
  #  85
  #  86
  #  87
  #  88
  #  89
  #  90
  #  91
  #  92
  #  93
  #  94
  #  95
  #  96
  #  97
  #  98
  #  99
  #  100
  #  101
  #  102
  #  103
  #  104
  #  105
  #  106
  #  107
  #  108
  #  109
  #  110
  #  111
  #  112
  #  113
  #  114
  #  115
  #  116
  #  117
  #  118
  #  119
  #  120
  #  121
  #  122
  #  123
  #  124
  #  125
  #  126
  #  127
  #  128
  #  129
  #  130
  #  131
  #  132
  #  133
  #  134
  #  135
  #  136
  #  137
  #  138
  #  139
  #  140
  #  141
  #  142
  #  143
  #  144
  #  145
  #  146
  #  147
  #  148
  #  149
  #  150
  #  151
  #  152
  #  153
  #  154
  #  155
  #  156
  #  157
  #  158
  #  159
  #  160
  #  161
  #  162
  #  163
  #  164
  #  165
  #  166
  #  167
  #  168
  #  169
  #  170
  #  171
  #  172
  #  173
  #  174
  #  175
  #  176
  #  177
  #  178
  #  179
  #  180
  #  181
  #  182
  #  183
  #  184
  #  185
  #  186
  #  187
  #  188
  #  189
  #  190
  #  191
  #  192
  #  193
  #  194
  #  195
  #  196
  #  197
  #  198
  #  199
  #  200
  #  201
  #  202
  #  203
  #  204
  #  205
  #  206
  #  207
  #  208
  #  209
  #  210
  #  211
  #  212
  #  213
  #  214
  #  215
  #  216
  #  217
  #  218
  #  219
  #  220
  #  221
  #  222
  #  223
  #  224
  #  225
  #  226
  #  227
  #  228
  #  229
  #  230
  #  231
  #  232
  #  233
  #  234
  #  235
  #  236
  #  237
  #  238
  #  239
  #  240
  #  241
  #  242
  #  243
  #  244
  #  245
  #  246
  #  247
  #  248
  #  249
  #  250
  #  251
  #  252
  #  253
  #  254
  #  255
  #  256
  #  257
  #  258
  #  259
  #  260
  #  261
  #  262
  #  263
  #  264
  #  265
  #  266
  #  267
  #  268
  #  269
  #  270
  #  271
  #  272
  #  273
  #  274
  #  275
  #  276
  #  277
  #  278
  #  279
  #  280
  #  281
  #  282
  #  283
  #  284
  #  285
  #  286
  #  287
  #  288
  #  289
  #  290
  #  291
  #  292
  #  293
  #  294
  #  295
  #  296
  #  297
  #  298
  #  299
  #  300
  #  301
  #  302
  #  303
  #  304
  #  305
  #  306
  #  307
  #  308
  #  309
  #  310
  #  311
  #  312
  #  313
  #  314
  #  315
  #  316
  #  317
  #  318
  #  319
  #  320
  #  321
  #  322
  #  323
  #  324
  #  325
  #  326
  #  327
  #  328
  #  329
  #  330
  #  331
  #  332
  #  333
  #  334
  #  335
  #  336
  #  337
  #  338
  #  339
  #  340
  #  341
  #  342
  #  343
  #  344
  #  345
  #  346
  #  347
  #  348
  #  349
  #  350
  #  351
  #  352
  #  353
  #  354
  #  355
  #  356
  #  357
  #  358
  #  359
  #  360
  #  361
  #  362
  #  363
  #  364
  #  365
  #  366
  #  367
  #  368
  #  369
  #  370
  #  371
  #  372
  #  373
  #  374
  #  375
  #  376
  #  377
  #  378
  #  379
  #  380
  #  381
  #  382
  #  383
  #  384
  #  385
  #  386
  #  387
  #  388
  #  389
  #  390
  #  391
  #  392
  #  393
  #  394
  #  395
  #  396
  #  397
  #  398
  #  399
  #  400
  #  401
  #  402
  #  403
  #  404
  #  405
  #  406
  #  407
  #  408
  #  409
  #  410
  #  411
  #  412
  #  413
  #  414
  #  415
  #  416
  #  417
  #  418
  #  419
  #  420
  #  421
  #  422
  #  423
  #  424
  #  425
  #  426
  #  427
  #  428
  #  429
  #  430
  #  431
  #  432
  #  433
  #  434
  #  435
  #  436
  #  437
  #  438
  #  439
  #  440
  #  441
  #  442
  #  443
  #  444
  #  445
  #  446
  #  447
  #  448
  #  449
  #  450
  #  451
  #  452
  #  453
  #  454
  #  455
  #  456
  #  457
  #  458
  #  459
  #  460
  #  461
  #  462
  #  463
  #  464
  #  465
  #  466
  #  467
  #  468
  #  469
  #  470
  #  471
  #  472
  #  473
  #  474
  #  475
  #  476
  #  477
  #  478
  #  479
  #  480
  #  481
  #  482
  #  483
  #  484
  #  485
  #  486
  #  487
  #  488
  #  489
  #  490
  #  491
  #  492
  #  493
  #  494
  #  495
  #  496
  #  497
  #  498
  #  499
  #  500
  #  501
  #  502
  #  503
  #  504
  #  505
  #  506
  #  507
  #  508
  #  509
  #  510
  #  511
  #  512
  #  513
  #  514
  #  515
  #  516
  #  517
  #  518
  #  519
  #  520
  #  521
  #  522
  #  523
  #  524
  #  525
  #  526
  #  527
  #  528
  #  529
  #  530
  #  531
  #  532
  #  533
  #  534
  #  535
  #  536
  #  537
  #  538
  #  539
  #  540
  #  541
  #  542
  #  543
  #  544
  #  545
  #  546
  #  547
  #  548
  #  549
  #  550
  #  551
  #  552
  #  553
  #  554
  #  555
  #  556
  #  557
  #  558
  #  559
  #  560
  #  561
  #  562
  #  563
  #  564
  #  565
  #  566
  #  567
  #  568
  #  569
  #  570
  #  571
  #  572
  #  573
  #  574
  #  575
  #  576
  #  577
  #  578
  #  579
  #  580
  #  581
  #  582
  #  583
  #  584
  #  585
  #  586
  #  587
  #  588
  #  589
  #  590
  #  591
  #  592
  #  593
  #  594
  #  595
  #  596
  #  597
  #  598
  #  599
  #  600
  #  601
  #  602
  #  603
  #  604
  #  605
  #  606
  #  607
  #  608
  #  609
  #  610
  #  611
  #  612
  #  613
  #  614
  #  615
  #  616
  #  617
  #  618
  #  619
  #  620
  #  621
  #  622
  #  623
  #  624
  #  625
  #  626
  #  627
  #  628
  #  629
  #  630
  #  631
  #  632
  #  633
  #  634
  #  635
  #  636
  #  637
  #  638
  #  639
  #  640
  #  641
  #  642
  #  643
  #  644
  #  645
  #  646
  #  647
  #  648
  #  649
  #  650
  #  651
  #  652
  #  653
  #  654
  #  655
  #  656
  #  657
  #  658
  #  659
  #  660
  #  661
  #  662
  #  663
  #  664
  #  665
  #  666
  #  667
  #  668
  #  669
  #  670
  #  671
  #  672
  #  673
  #  674
  #  675
  #  676
  #  677
  #  678
  #  679
  #  680
  #  681
  #  682
  #  683
  #  684
  #  685
  #  686
  #  687
  #  688
  #  689
  #  690
  #  691
  #  692
  #  693
  #  694
  #  695
  #  696
  #  697
  #  698
  #  699
  #  700
  #  701
  #  702
  #  703
  #  704
  #  705
  #  706
  #  707
  #  708
  #  709
  #  710
  #  711
  #  712
  #  713
  #  714
  #  715
  #  716
  #  717
  #  718
  #  719
  #  720
  #  721
  #  722
  #  723
  #  724
  #  725
  #  726
  #  727
  #  728
  #  729
  #  730
  #  731
  #  732
  #  733
  #  734
  #  735
  #  736
  #  737
  #  738
  #  739
  #  740
  #  741
  #  742
  #  743
  #  744
  #  745
  #  746
  #  747
  #  748
  #  749
  #  750
  #  751
  #  752
  #  753
  #  754
  #  755
  #  756
  #  757
  #  758
  #  759
  #  760
  #  761
  #  762
  #  763
  #  764
  #  765
  #  766
  #  767
  #  768
  #  769
  #  770
  #  771
  #  772
  #  773
  #  774
  #  775
  #  776
  #  777
  #  778
  #  779
  #  780
  #  781
  #  782
  #  783
  #  784
  #  785
  #  786
  #  787
  #  788
  #  789
  #  790
  #  791
  #  792
  #  793
  #  794
  #  795
  #  796
  #  797
  #  798
  #  799
  #  800
  #  801
  #  802
  #  803
  #  804
  #  805
  #  806
  #  807
  #  808
  #  809
  #  810
  #  811
  #  812
  #  813
  #  814
  #  815
  #  816
  #  817
  #  818
  #  819
  #  820
  #  821
  #  822
  #  823
  #  824
  #  825
  #  826
  #  827
  #  828
  #  829
  #  830
  #  831
  #  832
  #  833
  #  834
  #  835
  #  836
  #  837
  #  838
  #  839
  #  840
  #  841
  #  842
  #  843
  #  844
  #  845
  #  846
  #  847
  #  848
  #  849
  #  850
  #  851
  #  852
  #  853
  #  854
  #  855
  #  856
  #  857
  #  858
  #  859
  #  860
  #  861
  #  862
  #  863
  #  864
  #  865
  #  866
  #  867
  #  868
  #  869
  #  870
  #  871
  #  872
  #  873
  #  874
  #  875
  #  876
  #  877
  #  878
  #  879
  #  880
  #  881
  #  882
  #  883
  #  884
  #  885
  #  886
  #  887
  #  888
  #  889
  #  890
  #  891
  #  892
  #  893
  #  894
  #  895
  #  896
  #  897
  #  898
  #  899
  #  900
  #  901
  #  902
  #  903
  #  904
  #  905
  #  906
  #  907
  #  908
  #  909
  #  910
  #  911
  #  912
  #  913
  #  914
  #  915
  #  916
  #  917
  #  918
  #  919
  #  920
  #  921
  #  922
  #  923
  #  924
  #  925
  #  926
  #  927
  #  928
  #  929
  #  930
  #  931
  #  932
  #  933
  #  934
  #  935
  #  936
  #  937
  #  938
  #  939
  #  940
  #  941
  #  942
  #  943
  #  944
  #  945
  #  946
  #  947
  #  948
  #  949
  #  950
  #  951
  #  952
  #  953
  #  954
  #  955
  #  956
  #  957
  #  958
  #  959
  #  960
  #  961
  #  962
  #  963
  #  964
  #  965
  #  966
  #  967
  #  968
  #  969
  #  970
  #  971
  #  972
  #  973
  #  974
  #  975
  #  976
  #  977
  #  978
  #  979
  #  980
  #  981
  #  982
  #  983
  #  984
  #  985
  #  986
  #  987
  #  988
  #  989
  #  990
  #  991
  #  992
  #  993
  #  994
  #  995
  #  996
  #  997
  #  998
  #  999
  #  1000
  #  1001
  #  1002
  #  1003
  #  1004
  #  1005
  #  1006
  #  1007
  #  1008
  #  1009
  #  1010
  #  1011
  #  1012
  #  1013
  #  1014
  #  1015
  #  1016
  #  1017
  #  1018
  #  1019
  #  1020
  #  1021
  #  1022
  #  1023
  #  1024
  #  1025
  #  1026
  #  1027
  #  1028
  #  1029
  #  1030
  #  1031
  #  1032
  #  1033
  #  1034
  #  1035
  #  1036
  #  1037
  #  1038
  #  1039
  #  1040
  #  1041
  #  1042
  #  1043
  #  1044
  #  1045
  #  1046
  #  1047
  #  1048
  #  1049
  #  1050
  #  1051
  #  1052
  #  1053
  #  1054
  #  1055
  #  1056
  #  1057
  #  1058
  #  1059
  #  1060
  #  1061
  #  1062
  #  1063
  #  1064
  #  1065
  #  1066
  #  1067
  #  1068
  #  1069
  #  1070
  #  1071
  #  1072
  #  1073
  #  1074
  #  1075
  #  1076
  #  1077
  #  1078
  #  1079
  #  1080
  #  1081
  #  1082
  #  1083
  #  1084
  #  1085
  #  1086
  #  1087
  #  1088
  #  1089
  #  1090
  #  1091
  #  1092
  #  1093
  #  1094
  #  1095
  #  1096
  #  1097
  #  1098
  #  1099
  #  1100
  #  1101
  #  1102
  #  1103
  #  1104
  #  1105
  #  1106
  #  1107
  #  1108
  #  1109
  #  1110
  #  1111
  #  1112
  #  1113
  #  1114
  #  1115
  #  1116
  #  1117
  #  1118
  #  1119
  #  1120
  #  1121
  #  1122
  #  1123
  #  1124
  #  1125
  #  1126
  #  1127
  #  1128
  #  1129
  #  1130
  #  1131
  #  1132
  #  1133
  #  1134
  #  1135
  #  1136
  #  1137
  #  1138
  #  1139
  #  1140
  #  1141
  #  1142
  #  1143
  #  1144
  #  1145
  #  1146
  #  1147
  #  1148
  #  1149
  #  1150
  #  1151
  #  1152
  #  1153
  #  1154
  #  1155
  #  1156
  #  1157
  #  1158
  #  1159
  #  1160
  #  1161
  #  1162
  #  1163
  #  1164
  #  1165
  #  1166
  #  1167
  #  1168
  #  1169
  #  1170
  #  1171
  #  1172
  #  1173
  #  1174
  #  1175
  #  1176
  #  1177
  #  1178
  #  1179
  #  1180
  #  1181
  #  1182
  #  1183
  #  1184
  #  1185
  #  1186
  #  1187
  #  1188
  #  1189
  #  1190
  #  1191
  #  1192
  #  1193
  #  1194
  #  1195
  #  1196
  #  1197
  #  1198
  #  1199
  #  1200
  #  1201
  #  1202
  #  1203
  #  1204
  #  1205
  #  1206
  #  1207
  #  1208
  #  1209
  #  1210
  #  1211
  #  1212
  #  1213
  #  1214
  #  1215
  #  1216
  #  1217
  #  1218
  #  1219
  #  1220
  #  1221
  #  1222
  #  1223
  #  1224
  #  1225
  #  1226
  #  1227
  #  1228
  #  1229
  #  1230
  #  1231
  #  1232
  #  1233
  #  1234
  #  1235
  #  1236
  #  1237
  #  1238
  #  1239
  #  1240
  #  1241
  #  1242
  #  1243
  #  1244
  #  1245
  #  1246
  #  1247
  #  1248
  #  1249
  #  1250
  #  1251
  #  1252
  #  1253
  #  1254
  #  1255
  #  1256
  #  1257
  #  1258
  #  1259
  #  1260
  #  1261
  #  1262
  #  1263
  #  1264
  #  1265
  #  1266
  #  1267
  #  1268
  #  1269
  #  1270
  #  1271
  #  1272
  #  1273
  #  1274
  #  1275
  #  1276
  #  1277
  #  1278
  #  1279
  #  1280
  #  1281
  #  1282
  #  1283
  #  1284
  #  1285
  #  1286
  #  1287
  #  1288
  #  1289
  #  1290
  #  1291
  #  1292
  #  1293
  #  1294
  #  1295
  #  1296
  #  1297
  #  1298
  #  1299
  #  1300
  #  1301
  #  1302
  #  1303
  #  1304
  #  1305
  #  1306
  #  1307
  #  1308
  #  1309
  #  1310
  #  1311
  #  1312
  #  1313
  #  1314
  #  1315
  #  1316
  #  1317
  #  1318
  #  1319
  #  1320
  #  1321
  #  1322
  #  1323
  #  1324
  #  1325
  #  1326
  #  1327
  #  1328
  #  1329
  #  1330
  #  1331
  #  1332
  #  1333
  #  1334
  #  1335
  #  1336
  #  1337
  #  1338
  #  1339
  #  1340
  #  1341
  #  1342
  #  1343
  #  1344
  #  1345
  #  1346
  #  1347
  #  1348
  #  1349
  #  1350
  #  1351
  #  1352
  #  1353
  #  1354
  #  1355
  #  1356
  #  1357
  #  1358
  #  1359
  #  1360
  #  1361
  #  1362
  #  1363
  #  1364
  #  1365
  #  1366
  #  1367
  #  1368
  #  1369
  #  1370
  #  1371
  #  1372
  #  1373
  #  1374
  #  1375
  #  1376
  #  1377
  #  1378
  #  1379
  #  1380
  #  1381
  #  1382
  #  1383
  #  1384
  #  1385
  #  1386
  #  1387
  #  1388
  #  1389
  #  1390
  #  1391
  #  1392
  #  1393
  #  1394
  #  1395
  #  1396
  #  1397
  #  1398
  #  1399
  #  1400
  #  1401
  #  1402
  #  1403
  #  1404
  #  1405
  #  1406
  #  1407
  #  1408
  #  1409
  #  1410
  #  1411
  #  1412
  #  1413
  #  1414
  #  1415
  #  1416
  #  1417
  #  1418
  #  1419
  #  1420
  #  1421
  #  1422
  #  1423
  #  1424
  #  1425
  #  1426
  #  1427
  #  1428
  #  1429
  #  1430
  #  1431
  #  1432
  #  1433
  #  1434
  #  1435
  #  1436
  #  1437
  #  1438
  #  1439
  #  1440
  #  1441
  #  1442
  #  1443
  #  1444
  #  1445
  #  1446
  #  1447
  #  1448
  #  1449
  #  1450
  #  1451
  #  1452
  #  1453
  #  1454
  #  1455
  #  1456
  #  1457
  #  1458
  #  1459
  #  1460
  #  1461
  #  1462
  #  1463
  #  1464
  #  1465
  #  1466
  #  1467
  #  1468
  #  1469
  #  1470
  #  1471
  #  1472
  #  1473
  #  1474
  #  1475
  #  1476
  #  1477
  #  1478
  #  1479
  #  1480
  #  1481
  #  1482
  #  1483
  #  1484
  #  1485
  #  1486
  #  1487
  #  1488
  #  1489
  #  1490
  #  1491
  #  1492
  #  1493
  #  1494
  #  1495
  #  1496
  #  1497
  #  1498
  #  1499
  #  1500
  #  1501
  #  1502
  #  1503
  #  1504
  #  1505
  #  1506
  #  1507
  #  1508
  #  1509
  #  1510
  #  1511
  #  1512
  #  1513
  #  1514
  #  1515
  #  1516
  #  1517
  #  1518
  #  1519
  #  1520
  #  1521
  #  1522
  #  1523
  #  1524
  #  1525
  #  1526
  #  1527
  #  1528
  #  1529
  #  1530
  #  1531
  #  1532
  #  1533
  #  1534
  #  1535
  #  1536
  #  1537
  #  1538
  #  1539
  #  1540
  #  1541
  #  1542
  #  1543
  #  1544
  #  1545
  #  1546
  #  1547
  #  1548
  #  1549
  #  1550
  #  1551
  #  1552
  #  1553
  #  1554
  #  1555
  #  1556
  #  1557
  #  1558
  #  1559
  #  1560
  #  1561
  #  1562
  #  1563
  #  1564
  #  1565
  #  1566
  #  1567
  #  1568
  #  1569
  #  1570
  #  1571
  #  1572
  #  1573
  #  1574
  #  1575
  #  1576
  #  1577
  #  1578
  #  1579
  #  1580
  #  1581
  #  1582
  #  1583
  #  1584
  #  1585
  #  1586
  #  1587
  #  1588
  #  1589
  #  1590
  #  1591
  #  1592
  #  1593
  #  1594
  #  1595
  #  1596
  #  1597
  #  1598
  #  1599
  #  1600
  #  1601
  #  1602
  #  1603
  #  1604
  #  1605
  #  1606
  #  1607
  #  1608
  #  1609
  #  1610
  #  1611
  #  1612
  #  1613
  #  1614
  #  1615
  #  1616
  #  1617
  #  1618
  #  1619
  #  1620
  #  1621
  #  1622
  #  1623
  #  1624
  #  1625
  #  1626
  #  1627
  #  1628
  #  1629
  #  1630
  #  1631
  #  1632
  #  1633
  #  1634
  #  1635
  #  1636
  #  1637
  #  1638
  #  1639
  #  1640
  #  1641
  #  1642
  #  1643
  #  1644
  #  1645
  #  1646
  #  1647
  #  1648
  #  1649
  #  1650
  #  1651
  #  1652
  #  1653
  #  1654
  #  1655
  #  1656
  #  1657
  #  1658
  #  1659
  #  1660
  #  1661
  #  1662
  #  1663
  #  1664
  #  1665
  #  1666
  #  1667
  #  1668
  #  1669
  #  1670
  #  1671
  #  1672
  #  1673
  #  1674
  #  1675
  #  1676
  #  1677
  #  1678
  #  1679
  #  1680
  #  1681
  #  1682
  #  1683
  #  1684
  #  1685
  #  1686
  #  1687
  #  1688
  #  1689
  #  1690
  #  1691
  #  1692
  #  1693
  #  1694
  #  1695
  #  1696
  #  1697
  #  1698
  #  1699
  #  1700
  #  1701
  #  1702
  #  1703
  #  1704
  #  1705
  #  1706
  #  1707
  #  1708
  #  1709
  #  1710
  #  1711
  #  1712
  #  1713
  #  1714
  #  1715
  #  1716
  #  1717
  #  1718
  #  1719
  #  1720
  #  1721
  #  1722
  #  1723
  #  1724
  #  1725
  #  1726
  #  1727
  #  1728
  #  1729
  #  1730
  #  1731
  #  1732
  #  1733
  #  1734
  #  1735
  #  1736
  #  1737
  #  1738
  #  1739
  #  1740
  #  1741
  #  1742
  #  1743
  #  1744
  #  1745
  #  1746
  #  1747
  #  1748
  #  1749
  #  1750
  #  1751
  #  1752
  #  1753
  #  1754
  #  1755
  #  1756
  #  1757
  #  1758
  #  1759
  #  1760
  #  1761
  #  1762
  #  1763
  #  1764
  #  1765
  #  1766
  #  1767
  #  1768
  #  1769
  #  1770
  #  1771
  #  1772
  #  1773
  #  1774
  #  1775
  #  1776
  #  1777
  #  1778
  #  1779
  #  1780
  #  1781
  #  1782
  #  1783
  #  1784
  #  1785
  #  1786
  #  1787
  #  1788
  #  1789
  #  1790
  #  1791
  #  1792
  #  1793
  #  1794
  #  1795
  #  1796
  #  1797
  #  1798
  #  1799
  #  1800
  #  1801
  #  1802
  #  1803
  #  1804
  #  1805
  #  1806
  #  1807
  #  1808
  #  1809
  #  1810
  #  1811
  #  1812
  #  1813
  #  1814
  #  1815
  #  1816
  #  1817
  #  1818
  #  1819
  #  1820
  #  1821
  #  1822
  #  1823
  #  1824
  #  1825
  #  1826
  #  1827
  #  1828
  #  1829
  #  1830
  #  1831
  #  1832
  #  1833
  #  1834
  #  1835
  #  1836
  #  1837
  #  1838
  #  1839
  #  1840
  #  1841
  #  1842
  #  1843
  #  1844
  #  1845
  #  1846
  #  1847
  #  1848
  #  1849
  #  1850
  #  1851
  #  1852
  #  1853
  #  1854
  #  1855
  #  1856
  #  1857
  #  1858
  #  1859
  #  1860
  #  1861
  #  1862
  #  1863
  #  1864
  #  1865
  #  1866
  #  1867
  #  1868
  #  1869
  #  1870
  #  1871
  #  1872
  #  1873
  #  1874
  #  1875
  #  1876
  #  1877
  #  1878
  #  1879
  #  1880
  #  1881
  #  1882
  #  1883
  #  1884
  #  1885
  #  1886
  #  1887
  #  1888
  #  1889
  #  1890
  #  1891
  #  1892
  #  1893
  #  1894
  #  1895
  #  1896
  #  1897
  #  1898
  #  1899
  #  1900
  #  1901
  #  1902
  #  1903
  #  1904
  #  1905
  #  1906
  #  1907
  #  1908
  #  1909
  #  1910
  #  1911
  #  1912
  #  1913
  #  1914
  #  1915
  #  1916
  #  1917
  #  1918
  #  1919
  #  1920
  #  1921
  #  1922
  #  1923
  #  1924
  #  1925
  #  1926
  #  1927
  #  1928
  #  1929
  #  1930
  #  1931
  #  1932
  #  1933
  #  1934
  #  1935
  #  1936
  #  1937
  #  1938
  #  1939
  #  1940
  #  1941
  #  1942
  #  1943
  #  1944
  #  1945
  #  1946
  #  1947
  #  1948
  #  1949
  #  1950
  #  1951
  #  1952
  #  1953
  #  1954
  #  1955
  #  1956
  #  1957
  #  1958
  #  1959
  #  1960
  #  1961
  #  1962
  #  1963
  #  1964
  #  1965
  #  1966
  #  1967
  #  1968
  #  1969
  #  1970
  #  1971
  #  1972
  #  1973
  #  1974
  #  1975
  #  1976
  #  1977
  #  1978
  #  1979
  #  1980
  #  1981
  #  1982
  #  1983
  #  1984
  #  1985
  #  1986
  #  1987
  #  1988
  #  1989
  #  1990
  #  1991
  #  1992
  #  1993
  #  1994
  #  1995
  #  1996
  #  1997
  #  1998
  #  1999
  #  2000
  #  2001
  #  2002
  #  2003
  #  2004
  #  2005
  #  2006
  #  2007
  #  2008
  #  2009
  #  2010
  #  2011
  #  2012
  #  2013
  #  2014
  #  2015
  #  2016
  #  2017
  #  2018
  #  2019
  #  2020
  #  2021
  #  2022
  #  2023
  #  2024
  #  2025
  #  2026
  #  2027
  #  2028
  #  2029
  #  2030
  #  2031
  #  2032
  #  2033
  #  2034
  #  2035
  #  2036
  #  2037
  #  2038
  #  2039
  #  2040
  #  2041
  #  2042
  #  2043
  #  2044
  #  2045
  #  2046
  #  2047
  #  2048
  #  2049
  #  2050
  #  2051
  #  2052
  #  2053
  #  2054
  #  2055
  #  2056
  #  2057
  #  2058
  #  2059
  #  2060
  #  2061
  #  2062
  #  2063
  #  2064
  #  2065
  #  2066
  #  2067
  #  2068
  #  2069
  #  2070
  #  2071
  #  2072
  #  2073
  #  2074
  #  2075
  #  2076
  #  2077
  #  2078
  #  2079
  #  2080
  #  2081
  #  2082
  #  2083
  #  2084
  #  2085
  #  2086
  #  2087
  #  2088
  #  2089
  #  2090
  #  2091
  #  2092
  #  2093
  #  2094
  #  2095
  #  2096
  #  2097
  #  2098
  #  2099
  #  2100
  #  2101
  #  2102
  #  2103
  #  2104
  #  2105
  #  2106
  #  2107
  #  2108
  #  2109
  #  2110
  #  2111
  #  2112
  #  2113
  #  2114
  #  2115
  #  2116
  #  2117
  #  2118
  #  2119
  #  2120
  #  2121
  #  2122
  #  2123
  #  2124
  #  2125
  #  2126
  #  2127
  #  2128
  #  2129
  #  2130
  #  2131
  #  2132
  #  2133
  #  2134
  #  2135
  #  2136
  #  2137
  #  2138
  #  2139
  #  2140
  #  2141
  #  2142
  #  2143
  #  2144
  #  2145
  #  2146
  #  2147
  #  2148
  #  2149
  #  2150
  #  2151
  #  2152
  #  2153
  #  2154
  #  2155
  #  2156
  #  2157
  #  2158
  #  2159
  #  2160
  #  2161
  #  2162
  #  2163
  #  2164
  #  2165
  #  2166
  #  2167
  #  2168
  #  2169
  #  2170
  #  2171
  #  2172
  #  2173
  #  2174
  #  2175
  #  2176
  #  2177
  #  2178
  #  2179
  #  2180
  #  2181
  #  2182
  #  2183
  #  2184
  #  2185
  #  2186
  #  2187
  #  2188
  #  2189
  #  2190
  #  2191
  #  2192
  #  2193
  #  2194
  #  2195
  #  2196
  #  2197
  #  2198
  #  2199
  #  2200
  #  2201
  #  2202
  #  2203
  #  2204
  #  2205
  #  2206
  #  2207
  #  2208
  #  2209
  #  2210
  #  2211
  #  2212
  #  2213
  #  2214
  #  2215
  #  2216
  #  2217
  #  2218
  #  2219
  #  2220
  #  2221
  #  2222
  #  2223
  #  2224
  #  2225
  #  2226
  #  2227
  #  2228
  #  2229
  #  2230
  #  2231
  #  2232
  #  2233
  #  2234
  #  2235
  #  2236
  #  2237
  #  2238
  #  2239
  #  2240
  #  2241
  #  2242
  #  2243
  #  2244
  #  2245
  #  2246
  #  2247
  #  2248
  #  2249
  #  2250
  #  2251
  #  2252
  #  2253
  #  2254
  #  2255
  #  2256
  #  2257
  #  2258
  #  2259
  #  2260
  #  2261
  #  2262
  #  2263
  #  2264
  #  2265
  #  2266
  #  2267
  #  2268
  #  2269
  #  2270
  #  2271
  #  2272
  #  2273
  #  2274
  #  2275
  #  2276
  #  2277
  #  2278
  #  2279
  #  2280
  #  2281
  #  2282
  #  2283
  #  2284
  #  2285
  #  2286
  #  2287
  #  2288
  #  2289
  #  2290
  #  2291
  #  2292
  #  2293
  #  2294
  #  2295
  #  2296
  #  2297
  #  2298
  #  2299
  #  2300
  #  2301
  #  2302
  #  2303
  #  2304
  #  2305
  #  2306
  #  2307
  #  2308
  #  2309
  #  2310
  #  2311
  #  2312
  #  2313
  #  2314
  #  2315
  #  2316
  #  2317
  #  2318
  #  2319
  #  2320
  #  2321
  #  2322
  #  2323
  #  2324
  #  2325
  #  2326
  #  2327
  #  2328
  #  2329
  #  2330
  #  2331
  #  2332
  #  2333
  #  2334
  #  2335
  #  2336
  #  2337
  #  2338
  #  2339
  #  2340
  #  2341
  #  2342
  #  2343
  #  2344
  #  2345
  #  2346
  #  2347
  #  2348
  #  2349
  #  2350
  #  2351
  #  2352
  #  2353
  #  2354
  #  2355
  #  2356
  #  2357
  #  2358
  #  2359
  #  2360
  #  2361
  #  2362
  #  2363
  #  2364
  #  2365
  #  2366
  #  2367
  #  2368
  #  2369
  #  2370
  #  2371
  #  2372
  #  2373
  #  2374
  #  2375
  #  2376
  #  2377
  #  2378
  #  2379
  #  2380
  #  2381
  #  2382
  #  2383
  #  2384
  #  2385
  #  2386
  #  2387
  #  2388
  #  2389
  #  2390
  #  2391
  #  2392
  #  2393
  #  2394
  #  2395
  #  2396
  #  2397
  #  2398
  #  2399
  #  2400
  #  2401
  #  2402
  #  2403
  #  2404
  #  2405
  #  2406
  #  2407
  #  2408
  #  2409
  #  2410
  #  2411
  #  2412
  #  2413
  #  2414
  #  2415
  #  2416
  #  2417
  #  2418
  #  2419
  #  2420
  #  2421
  #  2422
  #  2423
  #  2424
  #  2425
  #  2426
  #  2427
  #  2428
  #  2429
  #  2430
  #  2431
  #  2432
  #  2433
  #  2434
  #  2435
  #  2436
  #  2437
  #  2438
  #  2439
  #  2440
  #  2441
  #  2442
  #  2443
  #  2444
  #  2445
  #  2446
  #  2447
  #  2448
  #  2449
  #  2450
  #  2451
  #  2452
  #  2453
  #  2454
  #  2455
  #  2456
  #  2457
  #  2458
  #  2459
  #  2460
  #  2461
  #  2462
  #  2463
  #  2464
  #  2465
  #  2466
  #  2467
  #  2468
  #  2469
  #  2470
  #  2471
  #  2472
  #  2473
  #  2474
  #  2475
  #  2476
  #  2477
  #  2478
  #  2479
  #  2480
  #  2481
  #  2482
  #  2483
  #  2484
  #  2485
  #  2486
  #  2487
  #  2488
  #  2489
  #  2490
  #  2491
  #  2492
  #  2493
  #  2494
  #  2495
  #  2496
  #  2497
  #  2498
  #  2499
  if sym then
    subs:=List(maxprim[n][1],d->PrimitiveGroup(n,d));
  else
    x:=Tuple([1,2]) #CAST SymmetricGroup(n)
      ;
    subs:=[];
    for d in maxprim[n][2] do
      P:=PrimitiveGroup(n,d);
      Add(subs,P);
      if d in maxprim[n][3] then
        Add(subs,P^x);
      fi;
    od;
  fi;
  #  **************************************************
  #  *Finally we deal with the generic cases. AGL(1, p) is
  #  *always Sym(p) maximal if p gt 24, with its normal subgroup
  #  *of index 2 being alt maximal.
  #  *PGL(2, p) is always Sym(p+1) maximal for p gt 23 (so
  #  *degree gt 24), with PSL(2, p) being
  #  *alt(p+1) maximal.
  #  **************************************************
  if n > 23 and IsPrimeInt(n) then
    if sym then
      Add(subs,AGL(1,n));
    else
      Add(subs,PrimitiveGroup(n,Size(DivisorsInt(n-1))-1));
      #  This is n:((n-1)/2)
    fi;
  fi;
  if n > 24 and IsPrimeInt(n-1) then
    if sym then
      Add(subs,PGL(2,n-1));
    else
      Add(subs,PSL(2,n-1));
    fi;
  fi;
  return subs;
end);

IdentifyAlmostSimpleGroup@:=function(G)
#  -> ,Map ,GrpPerm  Look up G in the database of almost simple groups
local I,Print,phi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  # =v= MULTIASSIGN =v=
  I:=IdentifyAlmostSimpleGroupH@(SolubleResidual(G),G,Print);
  phi:=I.val1;
  I:=I.val2;
  # =^= MULTIASSIGN =^=
  return rec(val1:=phi,
    val2:=I);
end;
;
IdentifyAlmostSimpleGroup@:=function(G)
#  -> ,Map ,GrpPerm  Look up G in the database of almost simple groups
local I,Print,phi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  # =v= MULTIASSIGN =v=
  I:=IdentifyAlmostSimpleGroupH@(SolubleResidual(G),G,Print);
  phi:=I.val1;
  I:=I.val2;
  # =^= MULTIASSIGN =^=
  return rec(val1:=phi,
    val2:=I);
end;
;
InstallGlobalFunction(IdentifyAltSymNatural@,
function(G,n,sym,pt,printlevel)
local S,SS,SSS,max,subs;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  if printlevel > 2 then
    Print("+Identifying AltSym by natural action");
  fi;
  if n <= 8 then
    Error("Use IdentifyAltSymNatural only for degree at least 9");
  fi;
  S:=OrbitImage(G,pt);
  Assert(1,Degree(S)=n);
  Assert(1,Ngens(S)=Ngens(G));
  SS:=StandardGroup(S);
  Assert(1,Degree(SS)=n);
  Assert(1,Ngens(SS)=Ngens(G));
  #   Changed by DFH - the functions must have codomain Aut(S) for simple
  #  * groups S, and the generators of S must come first.
  
  SSS:=SubStructure(SymmetricGroup(n),AlternatingGroup(n),#TODO CLOSURE
    Tuple([1,2]));
  SSS.Order:=Factorial(n);
  #  
  #  SSS:=sub< SS | Alt(n) >; // we want alternating generators first.
  #  if sym then
  #  SSS:= sub<SS | SSS, (1,2)>;
  #  SSS`Order := Factorial(n);
  #  else
  #  SSS`Order := Factorial(n) div 2;
  #  end if;
  
  if printlevel > 2 then
    Print("+Completed identification - getting maximal subgroups");
  fi;
  # rewritten select statement
  if max then
    subs:=Concatenation(IntransitiveSubgroupsAltSym@(n,sym)
     ,ImprimitiveSubgroupsAltSym@(n,sym),PrimitiveSubgroupsAltSym@(n,sym));
  else
    subs:=[];
  fi;
  #  DFH changed iso to hom below
  return rec(val1:=GroupHomomorphismByImages(G,SSS,
    GeneratorsOfGroup(G),List([1..Ngens(G)],i->SS.i)),
    val2:=SSS,
    val3:=subs);
end);

InstallGlobalFunction(ActionOnOrbitsU@,
function(G,K)
local I,S,d,f,g,i,im,images,j,norbs,orb,orbit_num,orbit_rep,orbs;
  orbs:=Orbits(K);
  d:=Degree(G);
  norbs:=Size(orbs);
  orbit_num:=[];
  orbit_rep:=[];
  for i in [1..norbs] do
    orb:=orbs[i];
    orbit_rep[i]:=Rep(orb);
    for j in orb do
      orbit_num[j]:=i;
    od;
  od;
  S:=SymmetricGroup(norbs);
  images:=[];
  for i in [1..Ngens(G)] do
    g:=G.i;
    im:=List([1..norbs],j->orbit_num[orbit_rep[j]^g]);
    Add(images,im);
  od;
  I:=SubStructure(S,images);
  f:=GroupHomomorphismByImages(G,I,
    GeneratorsOfGroup(G),images);
  return rec(val1:=f,
    val2:=I);
end);


