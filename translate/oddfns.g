#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, AssertAttribute, BlocksAction, Centraliser,
#  CosetAction, Degree, DirectProduct, Domain, ElementToSequence, FPGroup,
#  Factorisation, FreeGroup, Generators, Id, Image, Include, Index,
#  IsConjugate, IsPrimitive, LHS, MaximalPartition, MinimalPartitions, Ngens,
#  Normaliser, Orbits, Position, RHS, RandomSchreier, Relations,
#  RepresentationSum, Representative, Reverse, SolubleResidual, Stabiliser,
#  Sylow, TestHomomorphism, Universe, liftQ, pA, pC, pQ

#  Defines: ConjugatingElement, DirectProductWithEmbeddingsAndProjectionsH,
#  IsConjugateSequencesH, IsHomomorphismH, MinimalOvergroupsH,
#  PermRepAlmostSimpleGroupH, PermutationRepresentationSumH,
#  PresentationSubgroupTF, SubgroupTF, WreathComplementTail

DeclareGlobalFunction("ConjugatingElement@");

DeclareGlobalFunction("DirectProductWithEmbeddingsAndProjectionsH@");

DeclareGlobalFunction("IsConjugateSequencesH@");

DeclareGlobalFunction("IsHomomorphismH@");

DeclareGlobalFunction("MinimalOvergroupsH@");

DeclareGlobalFunction("PermRepAlmostSimpleGroupH@");

DeclareGlobalFunction("PermutationRepresentationSumH@");

DeclareGlobalFunction("PresentationSubgroupTF@");

DeclareGlobalFunction("SubgroupTF@");

DeclareGlobalFunction("WreathComplementTail@");

#  
#  Various utility functions for computing maximal subgroups.
#  Written by Derek Holt.

InstallGlobalFunction(IsHomomorphismH@,
function(phi,genims)
#  /out: Checks whether a map phi (defined by generator images genims) on a
#  * permutation group is a homomorphism.

local P;
  P:=Domain(phi);
  return TestHomomorphism(P,genims);
end);

InstallGlobalFunction(PermRepAlmostSimpleGroupH@,
function(G,K)
#  /out: Attempt to find a reasonable degree perm. rep. of the almost simple
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
end);

InstallGlobalFunction(DirectProductWithEmbeddingsAndProjectionsH@,
function(G,H)
#  /out: G and H should be permutation groups.
#  * The direct product P of G and H as computed by DirectProduct is
#  * returned.
#  * The embeddings of G into P and H into P are also returned,
#  * followed by the projections of P onto G and H.

local P,e,p;
  # =v= MULTIASSIGN =v=
  p:=DirectProduct(G,H);
  P:=p.val1;
  e:=p.val2;
  p:=p.val3;
  # =^= MULTIASSIGN =^=
  return rec(val1:=P,
    val2:=e[1],
    val3:=e[2],
    val4:=p[1],
    val5:=p[2]);
end);

InstallGlobalFunction(IsConjugateSequencesH@,
function(G,s1,s2)
#  /out: s1 and s2 should be sequences of elements of the group G of the same
#  * length. This function tests whether there is an element g in G with
#  * s1[i]^g eq s2[i] for all i.
#  * It returns true of false, and also a conjugating element g if it exists.

local C,conj,el,g,i;
  if Universe(s1)<>G or Universe(s2)<>G then
    Error("Universes of s1 and s2 must be group G in 
     IsConjugateSequenceH(G,s1,s2)");
  fi;
  if Size(s1)<>Size(s2) then
    return rec(val1:=false,
      val2:=_);
  fi;
  el:=One(G);
  C:=G;
  for i in [1..Size(s1)] do
    # =v= MULTIASSIGN =v=
    g:=IsConjugate(C,s1[i]^el,s2[i]);
    conj:=g.val1;
    g:=g.val2;
    # =^= MULTIASSIGN =^=
    if not conj then
      return rec(val1:=false,
        val2:=_);
    fi;
    el:=el*g;
    C:=Centraliser(C,s2[i]);
  od;
  return rec(val1:=true,
    val2:=el);
end);

InstallGlobalFunction(PermutationRepresentationSumH@,
function(G,reps)
#  /out: reps should be a list of homomorphisms from group G to permutation
#  * groups (subgroups of Sym(n_i)). The summed permutation representation
#  * reps[1]+..resp[r] of degree n_1+n_2+..n_r is returned, together
#  * with the image group.

local phi;
  phi:=RepresentationSum(G,reps);
  return rec(val1:=phi,
    val2:=Image(phi));
end);

InstallGlobalFunction(PresentationSubgroupTF@,
function(genlist,preslist,projlist,fplist)
#  /out: This function computes a presentation of a maximal subgroup  H of a
#  * TF permutation group.
#  * H has a normal subgroup N of fairly small index which is a direct
#  * product of groups N_1,...,N_r, which are permuted under conjugation
#  * by H.
#  * genlist, preslist, projlist and fplist should each be lists, where
#  * genlist has length r+1 and the others have length r.
#  * genlist[i] should be a list of generators of N_i (1 <= i <= r).
#  * (but some of these lists may be empty, which happens when H is a partly
#  *  diagonal)
#  * genlist[r+1] should contain an irredundant list of elements of H that
#  * generate  H modulo N.
#  * preslist[i] should be a presentation of N_i on these generators.
#  * projlist[i] should be the natural projection N -> N_i.
#  * fplist[i] should be the word map of N_i.
#  * (These conditions are not checked!)
#  *
#  * The group H with generating set the union of the generators in genlist,
#  * together with a presentation of H on these generators is returned.

local 
   F,Frels,H,N,Q,actgroup,actperms,ct,dn,dx,dy,factors,g,gensH,h,i,j,k,liftQ,n,
   ngx,o,pQ,presQ,r,rQ,rS,rel,relval,subgpptr,w,x,y;
  r:=Size(genlist)-1;
  ct:=1;
  while Size(genlist[ct])=0 do
    ct:=ct+1;
  od;
  n:=Degree(Universe(genlist[ct]));
  gensH:=Concatenation((genlist));
  #  H := PermutationGroup<n|gensH>;
  H:=SubStructure(Universe(gensH),gensH);
  N:=SubStructure(H,Concatenation((List([1..r],i->genlist[i]))));
  factors:=List([1..r],i->SubStructure(H,genlist[i]));
  #   subgpptr will be used to locate the generators of each factor within H
  subgpptr:=[];
  subgpptr[1]:=0;
  for i in [2..r+1] do
    subgpptr[i]:=subgpptr[i-1]+Size(genlist[i-1]);
  od;
  #   The permutations in genlist[r+1] permute the N_i by conjugation,
  #  * and we will define the corresponding permutations on [1..r]
  
  actperms:=[];
  for i in [1..Size(genlist[r+1])] do
    g:=genlist[r+1][i];
    actperms[i]:=[];
    for j in [1..r] do
      if Size(genlist[j])=0 or r=1 then
        actperms[i][j]:=j;
      else
        actperms[i][j]:=Position(factors,factors[j]^g);
      fi;
    od;
  od;
  F:=FreeGroup(Size(gensH));
  Frels:=[];
  #   Now we start to set up the defining relations.
  #   First, for each orbit of H on the factors we want a presentation
  #   of one factor in the orbit, + commutativity relations with other factors.
  actgroup:=SubPermutationGroup(r,[actperms]);
  for o in Orbits(actgroup) do
    x:=Representative(o);
    if Size(genlist[x])=0 then
      continue;
    fi;
    dx:=subgpptr[x];
    for rS in Relations(preslist[x]) do
      w:=ElementToSequence(LHS(rS)*RHS(rS)^-1);
      # rewritten select statement
      if 0 then
        w:=List(w,i->i > dx+i);
      else
        w:=List(w,i->i > -(dx-i));
      fi;
      Add(Frels,w);
    od;
    ngx:=Ngens(factors[x]);
    for y in [1..r] do
      if y<>x and Size(genlist[y])<>0 then
        dy:=subgpptr[y];
        for i in [1..ngx] do
          for j in [1..Ngens(factors[y])] do
            if Position(Frels,Tuple([F.(dy+j),F.(dx+i)]))=0 then
              #   avoid using the same commutator twice!
              Add(Frels,Tuple([F.(dx+i),F.(dy+j)]));
            fi;
          od;
        od;
      fi;
    od;
  od;
  if Index(H,N)=1 then
    return rec(val1:=H,
      val2:=Subquo(F,[Frels]));
  fi;
  #   Next the relations of the action of H on the factors
  dn:=subgpptr[r+1];
  for i in [1..Size(genlist[r+1])] do
    g:=genlist[r+1][i];
    for x in [1..r] do
      if Size(genlist[x])<>0 then
        dx:=subgpptr[x];
        y:=actperms[i][x];
        dy:=subgpptr[y];
        for k in [1..Size(genlist[x])] do
          h:=genlist[x][k];
          w:=ElementToSequence((h^g)@projlist[y]@@fplist[y]);
          #   h^g should be in N_y.
          #   relator will be (F.(dn+i))^-1*F.(dx+k)*F.(dn+i)*w^-1;
          # rewritten select statement
          if 0 then
            w:=List(w,j->j > -dy-j);
          else
            w:=List(w,j->j > dy-j);
          fi;
          w:=Concatenation(w,[dn+i,dx+k,-dn-i]);
          Reversed(w);
          Add(Frels,w);
        od;
      fi;
    od;
  od;
  #  Finally the relators derived from those of H/N.
  # =v= MULTIASSIGN =v=
  pQ:=Subquo(H,[N]);
  Q:=pQ.val1;
  pQ:=pQ.val2;
  # =^= MULTIASSIGN =^=
  #  Q, pQ := SocleQuotient(H);
  #   generators of this should correspond to genlist[r+1] but to be safe:
  Q:=SubStructure(Q,List(genlist[r+1],g->pQ(g)));
  presQ:=FPGroup(Q);
  #   define an inverse 'hom' for evaluating relators in N.
  liftQ:=GroupHomomorphismByImages(presQ,H,
    GeneratorsOfGroup(presQ),genlist[r+1]);
  for rQ in Relations(presQ) do
    w:=LHS(rQ)*RHS(rQ)^-1;
    relval:=liftQ(w);
    w:=ElementToSequence(w);
    # rewritten select statement
    if 0 then
      rel:=List(w,i->i > dn+i);
    else
      rel:=List(w,i->i > -(dn-i));
    fi;
    #   Now we append the inverses of the components of relval to rel
    for x in [1..r] do
      if Size(genlist[x])<>0 then
        dx:=subgpptr[x];
        w:=ElementToSequence(relval@projlist[x]@@fplist[x]);
        for j in Reversed(w) do
          if j > 0 then
            #   rel := rel * (F.(dx+j))^-1;
            Add(rel,-(dx+j));
          else
            #   rel := rel * F.(dx-j);
            Add(rel,dx-j);
          fi;
        od;
      fi;
    od;
    Add(Frels,rel);
  od;
  return rec(val1:=H,
    val2:=Subquo(F,[Frels]));
end);

InstallGlobalFunction(SubgroupTF@,
function(genlist)
#  /out: This function is a cut down version of PresentationSubgroupTF, with
#  * the same (now a bit redundant) parameters, that just creates the
#  * maximal subgroup, without a presentation.

local H,ct,gensH,n,r;
  r:=Size(genlist)-1;
  ct:=1;
  while Size(genlist[ct])=0 do
    ct:=ct+1;
  od;
  n:=Degree(Universe(genlist[ct]));
  gensH:=Concatenation((genlist));
  #  H := PermutationGroup<n|gensH>;
  H:=SubStructure(Universe(gensH),gensH);
  return H;
end);

InstallGlobalFunction(MinimalOvergroupsH@,
function(G,H)
#  /out: H is a proper subgroup of G.
#  * return all minimal subgroups K with H < K <= G.

local P,overgps,p,stab,theta;
  # =v= MULTIASSIGN =v=
  P:=CosetAction(G,H);
  theta:=P.val1;
  P:=P.val2;
  # =^= MULTIASSIGN =^=
  if IsPrimitive(P) then
    overgps:=Set([G]);
  else
    overgps:=Set([]);
    for p in MinimalPartitions(P) do
      stab:=Stabiliser(P,Filtered(p,x->1 in x)[1]);
      #   i.e. stabiliser of the block containing 1 -
      #   pullback to G will be a minimal overgroup of N.
      UniteSet(overgps,stab@@theta);
    od;
  fi;
  return overgps;
end);

InstallGlobalFunction(WreathComplementTail@,
function(W,A,B,C,g)
#  /out: A technical function.
#  * W is a wreath product of A by a group P.
#  * A is a factor of the base group and B is the direct product of all
#  * other factors (so base group = A x B).
#  * C/B is a complement of (A x B)/B in X/B
#  * (perhaps from call of Complement(X,sub<W|A,B>,B).) where X = N_W(A).
#  * An element a of A is returned such that g = c a for some c in C.

local BG,XN,gensA,gensB,pA,pC;
  gensA:=List([1..Ngens(A)],i->A.i);
  gensB:=List([1..Ngens(B)],i->B.i);
  BG:=SubStructure(W,Concatenation(gensA,gensB));
  #   base group of W
  AssertAttribute(BG,"Order",Size(A)*Size(B));
  RandomSchreier(BG);
  pA:=GroupHomomorphismByImages(BG,A,
    GeneratorsOfGroup(BG),Concatenation(gensA,List([1..Ngens(B)],i->One(A))));
  #  projection of BG onto A.
  #  
  #  H := sub<W | g,BG >;
  #  I := H meet C;
  #  for c in Transversal(I,B) do
  #  y := c^-1 * g;
  #  if y in BG then
  #  return pA(y);
  #  end if;
  #  end for;
  
  XN:=SubStructure(W,Concatenation(List([1..Ngens(C)],i->C.i),List([1..Ngens(A)]
   ,i->A.i)));
  AssertAttribute(XN,"Order",Size(C)*Size(A));
  RandomSchreier(XN);
  #   XN = Normaliser(W,A)
  pC:=GroupHomomorphismByImages(XN,C,
    GeneratorsOfGroup(XN),Concatenation(List([1..Ngens(C)],i->C.i)
   ,List([1..Ngens(A)],i->One(C))));
  return pA(pC(g)^-1*g);
end);

InstallGlobalFunction(ConjugatingElement@,
function(G,x)
#  /out: find an element of G with same conjugation action on G as x
#  * give error if no such element.

local C,el,g,y,yes;
  C:=G;
  y:=One(G);
  for g in Generators(G) do
    # =v= MULTIASSIGN =v=
    el:=IsConjugate(C,g^y,g^x);
    yes:=el.val1;
    el:=el.val2;
    # =^= MULTIASSIGN =^=
    if not yes then
      Error("No conjugating element in ConjugatingElement");
    fi;
    y:=y*el;
    C:=Centraliser(C,g^x);
  od;
  return y;
end);


