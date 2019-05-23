#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, AssertAttribute, BSGS, CentraliseInvol,
#  Centraliser, ChangeBase, Cputime, DerivedSubgroup, DihedralTrick, Domain,
#  FPGroupStrong, FindGoodGens, FindInvolution, FindThreeElement, Fix, GF, GL,
#  GetAlt4, GetAlt5, GetReducible, GetSemilin, GetSym4, Integers, IsAbelian,
#  IsConjugate, IsPrime, IsSquare, MakeHomom, Orbit, OrbitAction, Order, PSL,
#  PolynomialRing, PrimitiveElement, Quotrem, RSpace, Random, RandomProcess,
#  ReduceGenerators, Root, Roots, SL, Stabiliser, homom

#  Defines: CentraliseInvol, DihedralTrick, FindGoodGens, FindInvolution,
#  FindThreeElement, GetAlt4, GetAlt5, GetReducible, GetSemilin, GetSym4,
#  L2pIdentify, MakeHomom

DeclareGlobalFunction("DihedralTrick@");

DeclareGlobalFunction("FindGoodGens@");

DeclareGlobalFunction("FindInvolution@");

DeclareGlobalFunction("FindThreeElement@");

DeclareGlobalFunction("L2pIdentify@");

#  
#  Constructively recognise and find maximal subgroups  of L(2,p).?
#  Recognition by Derek Holt.
#  maximals by Colva Roney-Dougal

#  ******************************************************
#  * This function uses the Bray trick to find the        *
#  * centraliser of an involution "elt" in a subgroup     *
#  * "group" of a group isomorphic to psl "psl". the      *
#  * parameter "grpsize" is how big we expect the         *
#  * resulting group to be. OK to test group order cos in *
#  * situation where we use it the groups are rather      *
#  * small.                                               *
#  *******************************************************
CentraliseInvol@:=function(group,psl,elt,grpsize)
#  /out:"centralising invol";
local added_elt,com,grp,made,o,process,q,r,x;
  Assert(1,Order(elt)=2);
  process:=RandomProcess(group);
  made:=false;
  grp:=SubStructure(psl,elt);
  while not made do
    x:=Random(process);
    com:=Tuple([elt,x]);
    o:=Order(com);
    #  "o =", o;
    # =v= MULTIASSIGN =v=
    r:=QuotientRemainder(o,2);
    q:=r.val1;
    r:=r.val2;
    # =^= MULTIASSIGN =^=
    if r=1 then
      added_elt:=x*(com^q);
      grp:=SubStructure(psl,grp,#TODO CLOSURE
        added_elt);
      if Size(grp)=grpsize then
        made:=true;
      fi;
    else
      grp:=SubStructure(psl,grp,#TODO CLOSURE
        com^q,Tuple([elt,x^-1])^q);
      if Size(grp)=grpsize then
        made:=true;
      fi;
    fi;
  od;
  return grp;
end;
;
#  *******************************************************
#  * This function uses the dihedral trick to find         *
#  * an  element conjugating elt1 to elt 2 (both of which  *
#  * have order 2)                                         *
#  ********************************************************
InstallGlobalFunction(DihedralTrick@,
function(elt1,elt2,process)
#  /out:"dihedral trick";
local q,r,x;
  x:=Random(process);
  while (Order((elt1^x)*elt2) mod 2=0) do
    x:=Random(process);
  od;
  # =v= MULTIASSIGN =v=
  r:=QuotientRemainder(Order((elt1^x)*elt2),2);
  q:=r.val1;
  r:=r.val2;
  # =^= MULTIASSIGN =^=
  return x*(elt2*(elt1^x))^q;
end);

#  *******************************************************
#  * This function finds a group isomorphic to Alt(4) by   *
#  * taking two matrices of order 4 in SL(2, p) whose      *
#  * square is -I, and whose product is another mat        *
#  * of order 4, taking the image of these in PSL          *
#  * (this is the Sylow 2-subgroup of PSL), and then       *
#  * using the "extended dihedral trick" to find a 3-cycle *
#  * which permutes them.                                  *
#  * "factor" is the homomorphism from sl to psl, all other*
#  * variable names are pretty obvious.                    *
#  *******************************************************
GetAlt4@:=function(factor,p,sl,psl)
local 
   a,alt4,b,bool,cent,cent2,conj1,conj2,conj3,first_group,i,invols,j,process,x;
  process:=RandomProcess(psl);
  a:=[0,-1,1,0] #CAST sl
    ;
  j:=0;
  for i in [1..p-1] do
    # =v= MULTIASSIGN =v=
    x:=IsSquare((-1-i^2) #CAST GF(p)
      );
    bool:=x.val1;
    x:=x.val2;
    # =^= MULTIASSIGN =^=
    if bool then
      j:=i #CAST GF(p)
        ;
      break;
    fi;
  od;
  b:=[j,x,x,-j] #CAST sl
    ;
  first_group:=SubStructure(sl,a,#TODO CLOSURE
    b);
  Assert(1,Size(first_group)=8);
  #   first_group is now the extraspecial 2-group inside sl.
  
  invols:=[a@factor,b@factor,(a*b)@factor];
  #   invols are the generators of the elementary abelian group
  #  * inside psl.
  #  * the idea is that we find a 3-cycle permuting them. this
  #  * gives us alt4.
  
  conj1:=DihedralTrick@(invols[1],invols[2],process);
  if (p mod 4)=3 then
    cent:=CentraliseInvol@(psl,psl,invols[1],p+1);
  else
    cent:=CentraliseInvol@(psl,psl,invols[1],p-1);
  fi;
  conj2:=DihedralTrick@(invols[2],invols[3]^(conj1^-1),RandomProcess(cent));
  cent2:=CentraliseInvol@(cent,psl,invols[2],4);
  conj3:=DihedralTrick@(invols[3],invols[1]^(conj1^-1*conj2^-1)
   ,RandomProcess(cent2));
  alt4:=SubStructure(psl,invols[1],#TODO CLOSURE
    invols[2],conj3*conj2*conj1);
  Assert(1,Size(alt4)=12);
  return alt4;
end;
;
#  ********************************************************
#  *    This function finds a group isomorphic to Sym(4),   *
#  *    by finding an elt a of order 2, and elt b of        *
#  *    order 3, and replacing b by random conjugates of    *
#  *    itself until Order(a*b) eq 4. Really should         *
#  *    modify it to use the alt4 code, as I think this     *
#  *    will be much faster.                                *
#  *********************************************************
GetSym4@:=function(group)
local a,b,founda,foundb,foundfirstb,o,proc,q,r,sym4,x;
  proc:=RandomProcess(group);
  founda:=false;
  foundb:=false;
  while not founda do
    x:=Random(proc);
    o:=Order(x);
    # =v= MULTIASSIGN =v=
    r:=QuotientRemainder(o,2);
    q:=r.val1;
    r:=r.val2;
    # =^= MULTIASSIGN =^=
    if r=0 then
      a:=x^q;
      founda:=true;
      #  "a = ", a;
    fi;
  od;
  foundfirstb:=false;
  while not foundfirstb do
    x:=Random(proc);
    o:=Order(x);
    # =v= MULTIASSIGN =v=
    r:=QuotientRemainder(o,3);
    q:=r.val1;
    r:=r.val2;
    # =^= MULTIASSIGN =^=
    if r=0 then
      b:=x^q;
      foundfirstb:=true;
      #  "firstb = ", b;
    fi;
  od;
  while not foundb do
    b:=b^Random(proc);
    if Order(a*b)=4 then
      foundb:=true;
    fi;
  od;
  sym4:=SubStructure(group,a,#TODO CLOSURE
    b);
  Assert(1,Size(sym4)=24);
  Assert(1,not IsAbelian(sym4));
  return sym4;
end;
;
#  
#  * This function produces the reducible subgroup as a
#  * subgroup of SL(2, p). input is p and my copy of SL(2, p).

GetReducible@:=function(p,sl)
local grp,z;
  z:=PrimitiveElement(GF(p));
  grp:=SubStructure(sl,[z,0,0,z^-1],#TODO CLOSURE
    [1,1,0,1]);
  #  assert #grp eq Integers()!(p*(p-1));
  return grp;
end;
;
#  *********************************************************
#   This function produces the semilinear group, by
#  * looking for a random pair of involutions that
#  * generate a dihedral group of the correct order, p+1.
#  * input is a group isomorphic to PSL and the prime p. In practice
#  * this is currently used with the *standard* copy of PSL, as this
#  * is likely to have smaller degree than the "black box" PSL generated
#  * by the user.

GetSemilin@:=function(group,p)
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
    if Order(invol*y)=((p+1)/2) #CAST Integers()
       then
      made_semilin:=true;
    fi;
  od;
  return SubStructure(group,invol,#TODO CLOSURE
    y);
end;
;
#  ******************************************************
#  ********************************************************
#  *   This function produces Alt(5), as a group generated  *
#  *   by two mats [0, 1, -1, 0] and [a, b, c, d] where     *
#  *   this latter matrix has trace -1 and the product      *
#  *   has trace (1-sqrt(5)/2)                              *
#  *********************************************************
GetAlt5@:=function(p)
local P,a,b,c,d,f,found,grp,roots,sigma;
  Assert(1,IsPrimeInt(p));
  sigma:=((1-Root(5 #CAST GF(p)
    ,2))/2) #CAST GF(p)
    ;
  a:=0 #CAST GF(p)
    ;
  P:=PolynomialRing(GF(p));
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
  grp:=SubStructure(SL(2,p),[0,1,-1,0] #CAST SL(2,p)
    ,#TODO CLOSURE
    [a,b,c,d] #CAST SL(2,p)
    );
  if not Size(grp)=120 then
    Info(InfoWarning,1,"failed to make Alt(5)");
  fi;
  return grp;
end;
;
#  
#  * The first stage is to find generators a and b of group such that a has
#  * order 2, b has order 3 and ab has order p. These generate g, and
#  * are unique up to automorphisms of g, and hence the mapping between
#  * any pair of them is an isomorphism.

InstallGlobalFunction(FindInvolution@,
function(G)
local foundinvol,invol,o,proc,q,r,x;
  proc:=RandomProcess(G);
  foundinvol:=false;
  while not foundinvol do
    x:=Random(proc);
    o:=Order(x);
    # =v= MULTIASSIGN =v=
    r:=QuotientRemainder(o,2);
    q:=r.val1;
    r:=r.val2;
    # =^= MULTIASSIGN =^=
    if r=0 then
      invol:=x^q;
      foundinvol:=true;
    fi;
  od;
  return invol;
end);

InstallGlobalFunction(FindThreeElement@,
function(G)
local foundthree_elt,o,proc,q,r,three_elt,y;
  proc:=RandomProcess(G);
  foundthree_elt:=false;
  while not foundthree_elt do
    y:=Random(proc);
    o:=Order(y);
    # =v= MULTIASSIGN =v=
    r:=QuotientRemainder(o,3);
    q:=r.val1;
    r:=r.val2;
    # =^= MULTIASSIGN =^=
    if r=0 then
      three_elt:=y^q;
      foundthree_elt:=true;
    fi;
  od;
  return three_elt;
end);

InstallGlobalFunction(FindGoodGens@,
function(group,p)
local invol,made_grp,proc,three_elt;
  proc:=RandomProcess(group);
  invol:=FindInvolution@(group);
  three_elt:=FindThreeElement@(group);
  made_grp:=false;
  while not made_grp do
    three_elt:=three_elt^Random(proc);
    if Order(invol*three_elt)=p then
      made_grp:=true;
    fi;
  od;
  return rec(val1:=invol,
    val2:=three_elt);
end);

#  
#  * The following function constructs the isomorphism between the
#  * permutation group "group" and our standard copy of psl "psl".
#  * It does this by finding standard generators first for "psl" and
#  * then for "group". These are unique up to group automorphisms, and
#  * hence one may define an isomorphism by mapping the ordered pair
#  * to the ordered pair.
#  * If group is pgl, then it identifies psl first as above, and then
#  * locates an outer automorphism.

MakeHomom@:=function(dgroup,group,p,psl,pgl)
local F,Print,a,a1,ac,b,b1,bc,c,c1,dgs,g,gs,homom,isc,phi,proc,psls,t,x;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  # =v= MULTIASSIGN =v=
  c1:=FindGoodGens@(psl,p);
  a1:=c1.val1;
  c1:=c1.val2;
  # =^= MULTIASSIGN =^=
  # =v= MULTIASSIGN =v=
  c:=FindGoodGens@(dgroup,p);
  a:=c.val1;
  c:=c.val2;
  # =^= MULTIASSIGN =^=
  #   We will use elements of order 2 and p as out generators, because the
  #   p-element fixes a unique point.
  b1:=a1*c1;
  b:=a*c;
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
  dgs:=SubStructure(dgroup,a,#TODO CLOSURE
    b);
  AssertAttribute(dgs,"Order",Size(psl));
  homom:=GroupHomomorphismByImages(dgs,pgl,
    GeneratorsOfGroup(dgs),[a1,b1]);
  if dgroup=group then
    return rec(val1:=homom,
      val2:=F,
      val3:=phi);
  fi;
  proc:=RandomProcess(group);
  c:=Random(proc);
  while c in dgroup do
    c:=Random(proc);
  od;
  ac:=(a^c)@homom;
  bc:=(b^c)@homom;
  proc:=RandomProcess(pgl);
  c1:=Random(proc);
  while c1 in psl do
    c1:=Random(proc);
  od;
  proc:=RandomProcess(psl);
  g:=DihedralTrick@(a1^c1,ac,proc);
  c1:=c1*g;
  #  print "Getting there!";
  # =v= MULTIASSIGN =v=
  g:=IsConjugate(Centraliser(psl,ac),b1^c1,bc);
  isc:=g.val1;
  g:=g.val2;
  # =^= MULTIASSIGN =^=
  c1:=c1*g;
  gs:=SubStructure(group,a,#TODO CLOSURE
    b,c);
  AssertAttribute(gs,"Order",Size(psl)*2);
  homom:=GroupHomomorphismByImages(gs,pgl,
    GeneratorsOfGroup(gs),[a1,b1,c1]);
  return rec(val1:=homom,
    val2:=F,
    val3:=phi);
end;
;
#  ******************************************************************
#  *                   The main function                              *
#  *******************************************************************
InstallGlobalFunction(L2pIdentify@,
function(group,p)
local 
   F,IsPSL,Print,alt5_1,alt5_2,conj_invol,dgroup,dh,factor,gl,homom,max,
   maximals,mod16,mod5,o,pgl,phi,psl,sl,sym4_1,sym4_2;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  Assert(1,IsPrimeInt(p));
  Assert(1,p > 11);
  if Print > 1 then
    Info(InfoWarning,1,"Making standard pgl");
  fi;
  sl:=SL(2,p);
  gl:=GL(2,p);
  # =v= MULTIASSIGN =v=
  pgl:=OrbitAction(gl,Orbit(gl,SubStructure(RSpace(gl),[1,0])));
  factor:=pgl.val1;
  pgl:=pgl.val2;
  # =^= MULTIASSIGN =^=
  if Print > 1 then
    Info(InfoWarning,1,"Making standard psl");
  fi;
  psl:=sl@factor;
  AssertAttribute(psl,"Order",Size(PSL(2,p)));
  if Print > 1 then
    Info(InfoWarning,1,"Making outer involution");
  fi;
  conj_invol:=([PrimitiveElement(GF(p)),0,0,1] #CAST gl
    )@factor;
  o:=Size(group);
  IsPSL:=o=Size(psl);
  dgroup:=DerivedSubgroup(group);
  if Print > 1 then
    Info(InfoWarning,1,"Setting up homomorphism");
  fi;
  # =v= MULTIASSIGN =v=
  phi:=MakeHomom@(dgroup,group,p,psl,pgl:Print:=Print);
  homom:=phi.val1;
  F:=phi.val2;
  phi:=phi.val3;
  # =^= MULTIASSIGN =^=
  dh:=Domain(homom);
  pgl:=SubStructure(pgl,homom(dh.1),#TODO CLOSURE
    homom(dh.2),conj_invol);
  AssertAttribute(pgl,"Order",Size(psl)*2);
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=pgl,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  #  
  #  * Reducible - isomorphic to p:(p-1)/2
  
  if Print > 1 then
    Info(InfoWarning,1,"Making reducible");
  fi;
  Add(maximals,(GetReducible@(p,sl)@factor));
  #  
  #  * Imprimitive - isomorphic to D_{p-1}. The former technique appears
  #  * to be faster.
  
  if Print > 1 then
    Info(InfoWarning,1,"Making imprimitive");
  fi;
  Add(maximals,Stabiliser(psl,Set([1,2])));
  #  
  #  * Semilinear - isomorphic to D_{p+1}
  
  if Print > 1 then
    Info(InfoWarning,1,"Making semilinear");
  fi;
  Add(maximals,GetSemilin@(psl,p));
  #  
  #  *Extra-Special p-group - depends on congruence of p.
  
  mod16:=p^2 mod 16;
  mod5:=p mod 5;
  if mod16=1 then
    if IsPSL then
      if Print > 1 then
        Info(InfoWarning,1,"Making sym4");
      fi;
      sym4_1:=GetSym4@(psl);
      sym4_2:=sym4_1^conj_invol;
      Add(maximals,sym4_1);
      Add(maximals,sym4_2);
    else
      #  Sym4s fuse under PGL, so no maximals to find
    fi;
  elif (mod5=1 or mod5=4) then
    if IsPSL then
    else
      if Print > 1 then
        Info(InfoWarning,1,"Making alt(4)");
      fi;
      Add(maximals,GetAlt4@(factor,p,sl,psl));
    fi;
  else
    if Print > 1 then
      Info(InfoWarning,1,"Making alt(4)");
    fi;
    Add(maximals,GetAlt4@(factor,p,sl,psl));
  fi;
  #   Alt(5). These are C_9 subgroups of PSL(2, p), fusing under PGL(2, p)
  
  if ((mod5=1 or mod5=4) and IsPSL) then
    if Print > 1 then
      Info(InfoWarning,1,"Making alt5");
    fi;
    alt5_1:=(GetAlt5@(p)@factor);
    alt5_2:=alt5_1^conj_invol;
    Add(maximals,alt5_1);
    Add(maximals,alt5_2);
  fi;
  if Print > 1 then
    Print("Found maximals in standard copy");
  fi;
  return rec(val1:=homom,
    val2:=pgl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);


