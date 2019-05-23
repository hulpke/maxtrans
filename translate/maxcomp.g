#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, AssertAttribute, Category, Centraliser,
#  Codomain, CompositionFactors, CosetAction, Degree, ElementaryAbelianSeries,
#  Exclude, FPGroup, FPGroupStrong, FreeGroup, Generators, Id, Image, Index,
#  InternalType1Maximals, InternalType2Maximals, InternalType3Maximals,
#  IsAltsym, IsConjugate, IsNormal, IsSoluble, IsTrivial, Kernel, Max,
#  MaxSubsH, MaxSubsTF, MaximalSubgroups, MaximalSubgroupsAltSym, Ngens,
#  Normaliser, Orbit, OrbitImage, Orbits, Position, PowerStructure, Radical,
#  RadicalQuotient, Random, RandomSchreier, Representative, SA, Socle,
#  SocleAction, SocleFactors, SocleQuotient, SolubleRadical, Stabiliser,
#  Stabilizer, SubgroupsLift, Sym, TMPEval, Transversal, Type4Maximals,
#  Type5Maximals, WreathProduct, WreathProductEmbeddings, pNQ, pQ, pSA, pSQ,
#  pT, phi, rho, theta

#  Defines: MaxSubsH, MaxSubsTF, MaxSubsTF2, MaxSubsTF4, MaximalSubgroupsH,
#  MaximalSubgroupsTF, Type4Maximals, Type5Maximals, WreathProductEmbeddings

DeclareGlobalFunction("MaxSubsTF@");

DeclareGlobalFunction("MaxSubsTF@");

DeclareGlobalFunction("MaxSubsH@");

DeclareGlobalFunction("Type4Maximals@");

DeclareGlobalFunction("Type5Maximals@");

DeclareGlobalFunction("WreathProductEmbeddings@");

#  
#  Package written by Derek Holt - last update Dec 2002 -
#  to compute maximal subgroups of a permutation group.

#  Forward declaration of MaxSubsTF
#  Forward declaration of MaxSubsH
MaximalSubgroupsTF@:=function(G)
#  -> ,SeqEnum  G should be a permutation group with trivial soluble radical (
#  i . e . a TF - group ) . The maximal subgroups of G are computed , including
#  G . A list subgroup records := returned .
local Presentation,Print,SmallSimpleFactor;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  SmallSimpleFactor:=ValueOption("SmallSimpleFactor");
  if SmallSimpleFactor=fail then
    SmallSimpleFactor:=5000;
  fi;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=false;
  fi;
  if Category(G)<>GrpPerm then
    Error("Argument for MaximalSubgroupsTF must be a permutation group");
  fi;
  if Size(SolubleRadical(G))<>1 then
    Error("Soluble radical of group must be trivial in MaximalSubgroupsTF");
  fi;
  return MaxSubsTF@(G,SubStructure(G,#NOP
  ):Print:=Print,SSF:=SmallSimpleFactor,Presentation:=Presentation);
end;
;
MaxSubsTF2@:=function(G,Print)
#  -> ,SeqEnum  For internal use
local Presentation;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=false;
  fi;
  if Category(G)<>GrpPerm then
    Error("Argument for MaximalSubgroupsTF must be a permutation group");
  fi;
  if Size(SolubleRadical(G))<>1 then
    Error("Soluble radical of group must be trivial in MaximalSubgroupsTF");
  fi;
  return MaxSubsTF@(G,SubStructure(G,#NOP
  ):Print:=Print,SSF:=5000,Presentation:=Presentation);
end;
;
MaxSubsTF4@:=function(G,Print,TrivRad,Pres)
#  -> ,SeqEnum  For internal use
if Category(G)<>GrpPerm then
    Error("Argument for MaximalSubgroupsTF must be a permutation group");
  fi;
  if Size(SolubleRadical(G))<>1 then
    Error("Soluble radical of group must be trivial in MaximalSubgroupsTF");
  fi;
  return MaxSubsTF@(G,SubStructure(G,#NOP
  ):Print:=Print,SSF:=5000,TrivRad:=TrivRad,Presentation:=Pres);
end;
;
MaximalSubgroupsH@:=function(G,N)
#  -> ,SeqEnum  Find maximal subgroups of G modulo the soluble normal subgroup
#  N . Use MaximalSubgroupsTF on the radical quotient where necessary . A list
#  subgroup records := returned .
local Presentation,Print,SmallSimpleFactor,orig;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  SmallSimpleFactor:=ValueOption("SmallSimpleFactor");
  if SmallSimpleFactor=fail then
    SmallSimpleFactor:=5000;
  fi;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=false;
  fi;
  if Category(G)<>GrpPerm or Category(N)<>GrpPerm then
    Error("Arguments for MaximalSubgroupsH must be permutation groups");
  fi;
  if not IsSubset(G,N) or not IsNormal(G,N) then
    Error("Arg. 2 of MaximalSubgroupsH must be normal in Arg. 1");
  fi;
  orig:=true;
  if orig then
    return 
     PMaxSubsH@(G,N:Print:=Print,SSF:=SmallSimpleFactor,
     Presentation:=Presentation);
  else
    return MaxSubsH@(G,N:Print:=Print,SSF:=SmallSimpleFactor);
  fi;
end;
;
MaximalSubgroupsH@:=function(G)
#  -> ,SeqEnum  Find maximal subgroups of G . Use MaximalSubgroupsTF on the
#  radical quotient where necessary . A list subgroup records := returned .
local Presentation,Print,SmallSimpleFactor,orig;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  SmallSimpleFactor:=ValueOption("SmallSimpleFactor");
  if SmallSimpleFactor=fail then
    SmallSimpleFactor:=5000;
  fi;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=false;
  fi;
  if Category(G)<>GrpPerm then
    Error("Argument for MaximalSubgroupsH must be permutation group");
  fi;
  orig:=true;
  if orig then
    return PMaxSubsH@(G,SubStructure(G,#NOP
    ):Print:=Print,SSF:=SmallSimpleFactor,Presentation:=Presentation);
  else
    return MaxSubsH@(G,SubStructure(G,#NOP
    ):Print:=Print,SSF:=SmallSimpleFactor);
  fi;
end;
;
#  Forward declaration of Type4Maximals
#  Forward declaration of Type5Maximals
#  Forward declaration of WreathProductEmbeddings
InstallGlobalFunction(MaxSubsTF@,
function(G,S)
#  /out: G should be a permutation group with trivial soluble radical (i.e. a
#  * TF-group). The maximal subgroups of G are computed, including G.
#  * Normally this function will be applied to TF-groups in which the socle
#  * is not simple, and the socle factors are fairly small groups.
#  * The second group S is usually sub<G|> and ignored, but on recursive
#  * calls to MaxSubsTF it may be one of the socle factors of G, for which
#  * we are specifically seeking Type 3 (2-orbit diagonal) maximals.

local 
   F,GR,H,M,O,OI,Presentation,Print,Q,Q1,RFG@,RFMSTF,RM,SA,SAK,SC,SF,SP,SPX,SQ,
   SQH,SSF,TrivRad,varX,cfac,fac,gens1,gens2,i,k,m,n,nSF,newgenlist,newpreslist,
   nfac,orig,pQ,pQ1,pRQ,pSQ,pSQH,phi,pres,projlist,reco,res,rho,socreps,sri,
   srino,srjno,t,x;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  SSF:=ValueOption("SSF");
  if SSF=fail then
    SSF:=5000;
  fi;
  TrivRad:=ValueOption("TrivRad");
  if TrivRad=fail then
    TrivRad:=false;
  fi;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=false;
  fi;
  RFG@:="unneeded record format";
  RFMSTF:="unneeded record format";
  GR:=rec(group:=G,
    RFG:=RFG@,
    maxsubs:=[],
    printlevel:=Print,
    smallsimplefactor:=SSF,
    trivrad:=TrivRad,
    presentation:=Presentation);
  if IsTrivial(G) then
    n:=Max(Ngens(G),1);
    pres:=Subquo(FreeGroup(n),[List([1..n],i->$.i)]);
    return [rec(order:=1,
      subgroup:=G,
      length:=1,
      presentation:=pres)];
  fi;
  if not Presentation and Degree(G) >= 10 and IsAltsym(G) then
    res:=MaximalSubgroupsAltSym@(G);
    reco:=rec();
    reco.subgroup:=G;
    reco.length:=1;
    reco.order:=Size(G);
    Add(res,reco);
    return res;
  fi;
  orig:=true;
  # =v= MULTIASSIGN =v=
  SAK:=SocleAction(G);
  SA:=SAK.val1;
  SP:=SAK.val2;
  SAK:=SAK.val3;
  # =^= MULTIASSIGN =^=
  # =v= MULTIASSIGN =v=
  M:=SocleQuotient(G);
  SQ:=M.val1;
  pSQ:=M.val2;
  M:=M.val3;
  # =^= MULTIASSIGN =^=
  SF:=SocleFactors(G);
  nSF:=Size(SF);
  O:=Orbits(SP);
  socreps:=List(Orbits(SP),o->Representative(o));
  GR.SF:=SF;
  GR.SA:=SA;
  GR.pSQ:=pSQ;
  GR.socle:=M;
  GR.socreps:=socreps;
  projlist:=[];
  for k in [1..nSF] do
    fac:=SF[k];
    gens1:=List([1..Ngens(fac)],i->fac.i);
    #   cfac := Centraliser(G,fac); Bill U change - next 2 lines
    nfac:=Stabiliser(SP,k)@@SA;
    cfac:=Centraliser(nfac,fac);
    gens2:=List([1..Ngens(cfac)],i->cfac.i);
    SC:=SubStructure(G,Concatenation(gens1,gens2));
    AssertAttribute(SC,"Order",Size(fac)*Size(cfac));
    RandomSchreier(SC);
    projlist[k]:=GroupHomomorphismByImages(SC,fac,
      GeneratorsOfGroup(SC),Concatenation(gens1,List([1..Size(gens2)]
     ,x->One(fac))));
  od;
  GR.projlist:=projlist;
  #   The following lists are computed on the first loop through the
  #  * representative socle factors - this is before we start finding
  #  * maximal subgroups.
  
  GR.wpembeddings:=[];
  GR.transversals:=[];
  GR.asembeddings:=# [*-list:
  [];
  GR.msints:=[];
  GR.genlist:=[];
  GR.preslist:=[];
  GR.fplist:=[];
  WreathProductEmbeddings@(GR);
  #   Find generators of G mod Socle(G).
  H:=SubStructure(SQ,#NOP
  );
  while H<>SQ do
    x:=Random(SQ);
    if not x in H then
      H:=SubStructure(SQ,H,#TODO CLOSURE
        x);
    fi;
  od;
  GR.modsocgens:=List(Generators(H),x->x@@pSQ);
  #   assert sub<G|GR`modsocgens, GR`socle> eq G;
  #   Now we can start finding the maximal subgroups.
  if Size(S)=1 then
    for srino in [1..Size(socreps)] do
      if orig then
        PType1Maximals@(GR,srino);
        PType2Maximals@(GR,srino);
      else
        InternalType1Maximals(GR,srino);
        InternalType2Maximals(GR,srino);
      fi;
      #   if the action of SP on the orbits other than srino is not soluble
      #  * then we could conceivably get some Type 3 maximals recursively,
      #  * by first factoring out the socle factors in the other orbits.
      #  * We have to investigate that possibility!
      #  * First get action of SP on other orbits
      
      varX:=Set([]);
      for i in [1..Size(O)] do
        if i<>srino then
          varX:=Union(varX,O[i]);
        fi;
      od;
      # rewritten select statement
      if varX=Set([]) then
        SPX:=SubStructure(SP,#NOP
        );
      else
        SPX:=OrbitImage(SP,varX);
      fi;
      rho:=GR.wpembeddings[srino][1];
      if not IsSoluble(SPX) and Size(SPX) >= Size(Image(rho)) then
        #   Must try this out! We form a perm. rep. of the required quotient
        #   by summing the representations given by rho and pSQ
        # =v= MULTIASSIGN =v=
        Q1:=PermutationRepresentationSumH@(G,[rho,pSQ]);
        pQ1:=Q1.val1;
        Q1:=Q1.val2;
        # =^= MULTIASSIGN =^=
        # =v= MULTIASSIGN =v=
        pRQ:=RadicalQuotient(Q1);
        Q:=pRQ.val1;
        pRQ:=pRQ.val2;
        # =^= MULTIASSIGN =^=
        pQ:=pQ1*pRQ;
        if Print > 0 then
          Print("RECURSIVE CALL of MaximalSubgroupsTF to quotient of 
           order",Size(Q));
        fi;
        RM:=MaxSubsTF@(Q,pQ(SF[socreps[srino]])
         :Print:=Print,SSF:=SSF,Presentation:=Presentation);
        if Print > 0 then
          Print("END OF RECURSIVE CALL");
        fi;
        for i in [1..Size(RM)] do
          m:=RM[i];
          if GR.presentation then
            sri:=socreps[srino];
            newgenlist:=GR.genlist;
            newpreslist:=GR.preslist;
            for t in GR.transversals[srino] do
              #  was: newgenlist[sri^(GR`SA)(t)]:=[];
              newgenlist[TMPEval(sri^(GR.SA),t)]:=[];
            od;
            H:=m.subgroup;
            newgenlist[nSF+1]:=List([1..Ngens(H)],i->(H.i)@@pQ);
            if Size(Kernel(pRQ)) > 1 then
              newgenlist[nSF+1]:=Concatenation(newgenlist[nSF+1]
               ,List(Generators(Kernel(pRQ)),g->g@@pQ1));
            fi;
            #  we have to re-calculate presentation of G/socle in this case!
            H:=SubStructure(G,newgenlist[nSF+1]);
            pSQH:=GroupHomomorphismByImages(H,SQ,
              GeneratorsOfGroup(H),List(newgenlist[nSF+1],g->pSQ(g)));
            SQH:=SubStructure(SQ,List(newgenlist[nSF+1],g->pSQ(g)));
            if Size(SQH) <= GR.smallsimplefactor then
              # =v= MULTIASSIGN =v=
              phi:=FPGroup(SQH:StrongGenerators:=false);
              F:=phi.val1;
              phi:=phi.val2;
              # =^= MULTIASSIGN =^=
            else
              # =v= MULTIASSIGN =v=
              phi:=FPGroup(SQH:StrongGenerators:=true);
              F:=phi.val1;
              phi:=phi.val2;
              # =^= MULTIASSIGN =^=
            fi;
            newpreslist[nSF+1]:=F;
            for i in [Ngens(SQH)+1..Ngens(F)] do
              Add(newgenlist[nSF+1],F.i@phi@@pSQH);
            od;
            # =v= MULTIASSIGN =v=
            m.presentation:=PresentationSubgroupTF@(newgenlist,newpreslist,
             GR.projlist,GR.fplist);
            m.subgroup:=m.presentation.val1;
            m.presentation:=m.presentation.val2;
            # =^= MULTIASSIGN =^=
          else
            m.subgroup:=(m.subgroup)@@pQ;
          fi;
          m.order:=Size(m).subgroup;
          Add(GR.maxsubs,m);
        od;
      fi;
    od;
  fi;
  #   Now the Type 3 maximals - those that are diagonals across two equivalent
  #  * orbits of the socle factors
  
  for srino in [1..Size(socreps)] do
    if Size(S) > 1 and not IsConjugate(G,S,SF[socreps[srino]]) then
      continue;
    fi;
    for srjno in [1..Size(socreps)] do
      if srjno=srino then
        if Size(S)=1 then
          break;
        else
          continue;
        fi;
      fi;
      if orig then
        PType3Maximals@(GR,srino,srjno);
      else
        InternalType3Maximals(GR,srino,srjno);
      fi;
    od;
  od;
  if Size(S) > 1 then
    return GR.maxsubs;
  fi;
  for srino in [1..Size(socreps)] do
    OI:=OrbitImage(SP,Orbit(SP,socreps[srino]));
    if Size(OI) >= 6 and not IsSoluble(Stabiliser(OI,1)) then
      #   there could be Type 4 maximals (twisted wreathproduct types)
      if orig then
        PType4Maximals@(GR,srino);
      else
        Type4Maximals@(GR,srino);
      fi;
    fi;
  od;
  if orig then
    PType5Maximals@(GR);
  else
    Type5Maximals@(GR);
  fi;
  return GR.maxsubs;
end);

InstallGlobalFunction(WreathProductEmbeddings@,
function(TILDEVAR~GR)
#  /out: Calculate the wreath product embeddings associated with the orbits of
#  * the socle action on the socle factors of G.

local 
   A,F,Fhom,G,N,P,Print,S,SA,SF,T,W,_,badrec,compsub,dP,eG,eP,g,genlist,i,im,
   ims,msilist,phi,pl,psi,rho,socreps,sri,srino,srit,t,tcomp,theta;
  G:=GR.group;
  socreps:=GR.socreps;
  SF:=GR.SF;
  SA:=GR.SA;
  genlist:=GR.genlist;
  Print:=GR.printlevel;
  for srino in [1..Size(socreps)] do
    sri:=socreps[srino];
    pl:=GR.projlist[sri];
    S:=SF[sri];
    if Print > 0 then
      Print("Considering socle factor number ",sri);
    fi;
    if Print > 1 then
      Print(S);
    fi;
    N:=Stabilizer(Image(SA),sri)@@SA;
    #   assert N eq Normaliser(G,S);
    # =v= MULTIASSIGN =v=
    Fhom:=IdentifyAlmostSimpleGroupH@(S,N,Print);
    psi:=Fhom.val1;
    A:=Fhom.val2;
    msilist:=Fhom.val3;
    F:=Fhom.val4;
    Fhom:=Fhom.val5;
    # =^= MULTIASSIGN =^=
    #  msilist can contain trivial subgroup generators, which can cause
    #  problems later, so eliminate
    for i in [1..Size(msilist)] do
      if One(A) in msilist[i].generators then
        badrec:=msilist[i];
        repeat
          RemoveSet(badrec.generators,One(A));
          
        until not One(A) in badrec.generators;
        msilist[i]:=badrec;
      fi;
    od;
    # =v= MULTIASSIGN =v=
    P:=CosetAction(G,N);
    theta:=P.val1;
    P:=P.val2;
    # =^= MULTIASSIGN =^=
    dP:=Degree(P);
    T:=[One(G)];
    #   transversal of N in G.
    for i in [2..dP] do
      # =v= MULTIASSIGN =v=
      t:=IsConjugate(P,1,i);
      _:=t.val1;
      t:=t.val2;
      # =^= MULTIASSIGN =^=
      T[i]:=t@@theta;
    od;
    genlist[sri]:=[];
    for i in [1..Ngens(A)] do
      if A.i in Socle(A) then
        Add(genlist[sri],A.i@@psi@pl);
      fi;
    od;
    for t in T do
      if t<>One(G) then
        srit:=sri^SA(t);
        genlist[srit]:=List(genlist[sri],g->g^t);
      fi;
    od;
    for t in T do
      srit:=sri^SA(t);
      compsub:=SubStructure(G,genlist[srit]);
      compsub.Order:=Size(S);
      #   BEWARE - Bill U's addition
      if Size(compsub) <= GR.smallsimplefactor then
        # =v= MULTIASSIGN =v=
        phi:=FPGroup(compsub);
        F:=phi.val1;
        phi:=phi.val2;
        # =^= MULTIASSIGN =^=
        GR.preslist[srit]:=F;
        GR.fplist[srit]:=phi;
        #   Surely Ngens(F) = Ngens(compsub) in this case ? 
        for i in [Ngens(compsub)+1..Ngens(F)] do
          Error("This cannot be!");
          Add(genlist[srit],phi(F.i));
        od;
      else
        if IsBound(Fhom) then
          #   complicated homomorphism
          #  phi := hom < F->compsub | x :-> (x @ Fhom @@ psi @ pl)^t,
          #                             x :-> (x^(t^-1)) @@ pl @ psi @@ Fhom >;
          Error("complicated homomorphism");
          phi:=phi;
        else
          # =v= MULTIASSIGN =v=
          phi:=FPGroupStrong(compsub);
          F:=phi.val1;
          phi:=phi.val2;
          # =^= MULTIASSIGN =^=
        fi;
        GR.preslist[srit]:=F;
        GR.fplist[srit]:=phi;
        for i in [Ngens(compsub)+1..Ngens(F)] do
          Add(genlist[srit],phi(F.i));
        od;
      fi;
    od;
    #   Next we define the natural map rho: G -> A Wr P (with image
    #  * contained in N/C Wr P) induced by the insertion N -> G.
    
    # =v= MULTIASSIGN =v=
    eP:=WreathProduct(A,SymmetricGroup(dP));
    W:=eP.val1;
    eG:=eP.val2;
    eP:=eP.val3;
    # =^= MULTIASSIGN =^=
    #   We use Sym(dP) rather than P as the second factor, because we may need
    #   the embedding into Sym(dP) for Type 3 maximals below.
    ims:=[];
    for g in List([1..Ngens(G)],i->G.i) do
      im:=g@theta@eP;
      for i in [1..dP] do
        t:=T[i];
        tcomp:=(T[1^theta(t*g^-1)]*g*t^-1)@psi@eG[i];
        im:=im*tcomp;
      od;
      Add(ims,im);
    od;
    rho:=GroupHomomorphismByImages(G,W,
      GeneratorsOfGroup(G),ims);
    #   rho is an embedding taking S to the first factor.
    if Print > 1 then
      Print("+Constructed embedding into wreath product");
    fi;
    GR.wpembeddings[srino]:=[rho,eG];
    GR.transversals[srino]:=T;
    GR.asembeddings[srino]:=psi;
    GR.msints[srino]:=msilist;
    GR.genlist:=genlist;
  od;
  return rec();
end);

InstallGlobalFunction(Type4Maximals@,
function(TILDEVAR~GR,srino)
#  /out: Find the maximal subgroups of Type 4 coming from socle factor
#  * S = SF[socreps[srino]]. That is, those of twisted wreath product type.
#  * They are certain types of complements of the base group in the
#  * wreath product, so the computation will be carried out in the image
#  * of the wreath product embedding.

local 
   A,B,BG,C,CA,CSA,CWA,Cgen,Cgens,Comps,D,DE,DT@,varE,G,Ggens,H,M,NA,NQ,NWA,
   NWAn,Print,Qgens,SA,SB,SBG,SQ,T,W,a,comp,d,eG,extends,g,gensA,gensCWA,gensD,
   ims,overgps,pNQ,pSA,pSQ,pT,reco,rho,t,tail,u,x;
  Print:=GR.printlevel;
  if Print > 0 then
    Print("Finding Type 4 (twisted wreath-type) maximal subgroups for socle 
     factor",GR.socreps[srino]);
  fi;
  rho:=GR.wpembeddings[srino][1];
  W:=Codomain(rho);
  G:=Image(rho);
  eG:=GR.wpembeddings[srino][2];
  A:=Image(eG[1]);
  #   term of base group.
  B:=SubStructure(W,List([2..Size(eG)],i->Image(eG[i])));
  #  Base group = A x B.
  AssertAttribute(B,"Order",Size(A)^(Size(eG)-1));
  RandomSchreier(B);
  BG:=SubStructure(W,A,#TODO CLOSURE
    B);
  AssertAttribute(BG,"Order",Size(A)^Size(eG));
  RandomSchreier(BG);
  SBG:=Intersection(BG,G);
  if SBG<>Socle(BG) then
    if Print > 1 then
      Print("+This is not a twisted wreath product of a simple group.");
    fi;
    return rec();
  fi;
  SA:=Intersection(A,SBG);
  SB:=Intersection(B,SBG);
  NWA:=Normaliser(W,A);
  CWA:=Centraliser(NWA,A);
  NA:=Intersection(NWA,G);
  CA:=Intersection(CWA,NA);
  #   NWA = CWA X A, so we will use this fact to get a perm. rep. of NA/(SB)
  gensA:=List([1..Ngens(A)],i->A.i);
  gensCWA:=List([1..Ngens(CWA)],i->CWA.i);
  NWAn:=SubStructure(W,Concatenation(gensA,gensCWA));
  if NWA<>NWAn then
    Error("Normaliser generation error in Type4Maximals");
  fi;
  NWA:=NWAn;
  pSA:=GroupHomomorphismByImages(NWA,A,
    GeneratorsOfGroup(NWA),Concatenation(gensA,List([1..Ngens(CWA)],i->One(A))))
   ;
  #  projection of NWA onto A.
  pSA:=GroupHomomorphismByFunction(NA,A,
    a->pSA(a));
  #  restriction to NA.
  # =v= MULTIASSIGN =v=
  pSQ:=SocleQuotient(NA);
  SQ:=pSQ.val1;
  pSQ:=pSQ.val2;
  # =^= MULTIASSIGN =^=
  # =v= MULTIASSIGN =v=
  NQ:=PermutationRepresentationSumH@(NA,[pSA,pSQ]);
  pNQ:=NQ.val1;
  NQ:=NQ.val2;
  # =^= MULTIASSIGN =^=
  if Size(NQ)<>Index(NA,SB) then
    Error("Normaliser perm. rep. error in Type4Maximals");
  fi;
  # =v= MULTIASSIGN =v=
  pT:=Transversal(G,NA);
  T:=pT.val1;
  pT:=pT.val2;
  # =^= MULTIASSIGN =^=
  #   We only want the maximal complements, so the following is inefficient:
  #  * Comps := Complements(NQ,pNQ(SA));
  #  * Go via maximal subgroups instead!
  
  Comps:=MaximalSubgroups(NQ);
  Comps:=List(Filtered(Comps,m->m.order=Index(NQ,pNQ(SA)) and 
   Size((Intersection(m.subgroup,pNQ(SA))))=1),m->m.subgroup);
  #   get some generators of G mod SBG.
  Qgens:=List(Filtered(GR.modsocgens,elt->rho(elt)<>One(G)),elt->rho(elt));
  for comp in Comps do
    C:=comp@@pNQ;
    #   extend this complement to a complement of SBG in G.
    #   This might be maximal
    Cgens:=[];
    for g in Qgens do
      Cgen:=g;
      for t in T do
        u:=pT(t*g);
        tail:=WreathComplementTail@(G,SA,SB,C,t*g*u^-1);
        Cgen:=Cgen*(tail^-1)^u;
      od;
      Add(Cgens,Cgen);
    od;
    varE:=SubStructure(G,Cgens);
    if Size(varE)<>Index(G,SBG) then
      Error("Bad complement construction in Type4Maximals");
    fi;
    if Print > 1 then
      Print("+Have a complement in wreath product");
    fi;
    D:=Intersection(varE,NA);
    #   now set up the conjugation map D->Aut(A)=A
    ims:=[];
    gensD:=List([1..Ngens(D)],i->D.i);
    for d in gensD do
      Add(ims,ConjugatingElement@(A,d));
      #   element of A inducing same action on A as d
    od;
    if not IsSubset(SubStructure(A,ims),SA) then
      #  image subset does not contain Inn(SA) so E is not maximal.
      if Print > 1 then
        Print("+Image does not contain Inn(A) - complement not maximal.");
      fi;
      continue;
    fi;
    #   If there are fewer than 42 socle factors, then we can skip the
    #   next check.
    #   We now have to check whether the homomorphism D->A defined above
    #   extends to a homomorphism DE -> A for any DE with D < DE <= E.
    #   If so then E is not maximal.
    #   We use a brute force check for this, except that we check that
    #   SA is at least a composition factor of the overgroup.
    CSA:=CompositionFactors(SA);
    if not Size(CSA)=1 then
      Error("SA not simple");
    fi;
    overgps:=MinimalOvergroupsH@(varE,D);
    for H in overgps do
      if Position(CompositionFactors(H),CSA[1])=0 then
        extends:=false;
        continue;
      fi;
      t:=Random(H);
      while t in D do
        t:=Random(H);
      od;
      DE:=SubStructure(varE,Concatenation(gensD,[t]));
      extends:=false;
      for a in A do
        if IsHomomorphismH@(GroupHomomorphismByImages(DE,A,
          GeneratorsOfGroup(DE),Concatenation(ims,[a])),Concatenation(ims,[a])) 
           then
          if Print > 1 then
            Print("+Homomorphism to Aut(SA) extends - complement not maximal.")
             ;
          fi;
          extends:=true;
          break;
        fi;
      od;
      if extends then
        break;
      fi;
    od;
    if extends then
      continue;
    fi;
    reco:=rec();
    reco.subgroup:=varE@@rho;
    reco.order:=Size(reco).subgroup;
    # rewritten select statement
    if IsNormal(GR.group,reco.subgroup) then
      reco.length:=1;
    else
      reco.length:=Index(GR.group,reco.subgroup);
    fi;
    Add(GR.maxsubs,reco);
    if Print > 0 then
      Print("+Maximal subgroup of order",reco.order,"twisted wreath type.");
      if Print > 2 then
        Print(reco.subgroup);
      fi;
    fi;
  od;
  return rec();
end);

InstallGlobalFunction(Type5Maximals@,
function(TILDEVAR~GR)
#  /out: Find maximal subgroups containing the socle, including the whole
#  group. 
local G,Print,S,SF,SQ,m,nSF,newgenlist,pSQ,reco;
  G:=GR.group;
  SF:=GR.SF;
  pSQ:=GR.pSQ;
  SQ:=Image(pSQ);
  pSQ:=GR.pSQ;
  nSF:=Size(SF);
  Print:=GR.printlevel;
  if Print > 0 then
    Print("Finding Type 5 maximal subgroups - those containing the socle.");
  fi;
  if Size(SQ)<>1 then
    S:=MaximalSubgroups(SQ);
    for m in S do
      reco:=rec();
      reco.subgroup:=(m.subgroup)@@pSQ;
      reco.order:=QuoInt(Size(G),Index(SQ,m.subgroup));
      AssertAttribute(reco.subgroup,"Order",reco.order);
      reco.order:=Size(reco).subgroup;
      reco.length:=m.length;
      Add(GR.maxsubs,reco);
      if Print > 0 then
        Print("+Maximal subgroup of order",reco.order,"containing socle.");
        if Print > 2 then
          Print(reco.subgroup);
        fi;
      fi;
    od;
  fi;
  #   finally do G.
  newgenlist:=GR.genlist;
  newgenlist[nSF+1]:=GR.modsocgens;
  reco:=rec();
  if GR.trivrad then
    reco.subgroup:=G;
  else
    # =v= MULTIASSIGN =v=
    reco.presentation:=PresentationSubgroupTF@(newgenlist,GR.preslist,
     GR.projlist,GR.fplist);
    reco.subgroup:=reco.presentation.val1;
    reco.presentation:=reco.presentation.val2;
    # =^= MULTIASSIGN =^=
  fi;
  reco.order:=Size(G);
  reco.length:=1;
  Add(GR.maxsubs,reco);
  if Print > 0 then
    Print("+Full group of order",reco.order);
    if Print > 2 then
      Print(reco.subgroup);
    fi;
  fi;
end);

InstallGlobalFunction(MaxSubsH@,
function(G,N)
#  /out: Find maximal subgroups of G modulo the soluble normal subgroup N.
#  * Use MaximalSubgroupsTF on the radical quotient where necessary.

local L,M,MM,Print,Q,Res,SSF,i,m,mm,pQ,s;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  SSF:=ValueOption("SSF");
  if SSF=fail then
    SSF:=5000;
  fi;
  L:=ElementaryAbelianSeries(G,N);
  if L[1]=G then
    #   group is soluble
    return MaximalSubgroups(G,N);
  fi;
  # =v= MULTIASSIGN =v=
  pQ:=RadicalQuotient(G);
  Q:=pQ.val1;
  pQ:=pQ.val2;
  # =^= MULTIASSIGN =^=
  #   Otherwise try MaximalSubgroupsTF.
  M:=MaxSubsTF@(Q,SubStructure(Q,#NOP
  ):Print:=Print,SSF:=SSF);
  MM:=[];
  Res:=[];
  for m in M do
    mm:=m;
    s:=m.subgroup;
    if s=Q then
      mm.subgroup:=SubStructure(G,List([1..Ngens(s)],i->s.i@@pQ));
      Add(MM,mm);
    else
      mm.subgroup:=s@@pQ;
      mm.order:=mm.order*Size(Radical(G));
      Add(Res,mm);
    fi;
  od;
  for i in [1..Size(L)-1] do
    Assert(1,Size(MM)=1);
    M:=SubgroupsLift(G,L[i],L[i+1],MM:Al:="Maximal");
    MM:=[];
    for m in M do
      mm:=m;
      s:=SubStructure(G,m.subgroup,#TODO CLOSURE
        L[i+1]);
      if s=G then
        Add(MM,mm);
      else
        mm.subgroup:=s;
        mm.order:=mm.order*Size(L[i+1]);
        Add(Res,mm);
      fi;
    od;
  od;
  return Res;
end);


