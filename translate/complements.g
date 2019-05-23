#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, AssertAttribute, BaseRing, Category,
#  ComplementVectors, Core, Dimension, Eltseq, FPGroupStrong, Factorisation,
#  GModule, Generators, Group, ISA, Id, Index, Integers, IsConjugate, IsNormal,
#  IsPrimePower, IsSoluble, LHS, LiftComplementsElAb, LiftComplementsSection,
#  LiftedPresentation, MaximalSubgroups, MaximalSubmodules, ModuleExtension,
#  Ngens, Normaliser, Orbits, Position, RHS, RadicalQuotient, Relations,
#  Representation, Representative, Reverse, RightTransversal, SequenceToSet,
#  SolubleResidual, Sylow, Sym, Type, f, pCentralSeries, refine_section,
#  section_complements, section_supplements

#  Defines: Complement, Complements, HasComplement, HasSupplement,
#  LiftComplementsElAb, LiftComplementsSection, LiftedPresentation,
#  RefineSection, Supplement, Supplements, refine_section, section_complements,
#  section_supplements

DeclareGlobalFunction("LiftComplementsElAb@");

DeclareGlobalFunction("refine_section@");

DeclareGlobalFunction("section_complements@");

DeclareGlobalFunction("section_supplements@");

DeclareGlobalFunction("LiftComplementsSection@");

DeclareGlobalFunction("LiftedPresentation@");

#   NOTE - these functions currently call the functions in ~/maxcomp
#  Forward declaration of LiftComplementsElAb
#  Forward declaration of refine_section
#  Forward declaration of section_complements
#  Forward declaration of section_supplements
#  Forward declaration of LiftComplementsSection
#  Forward declaration of LiftedPresentation
#   Extension to allow non-abelian normal subgroup. 21/11/99
#   Written by Derek Holt.
#  ============================================================================
#  ===========
Complements@:=function(G,M)
#  -> ,SeqEnum  Given a finite permutation group G , with normal subgroup M ,
#  if M has a complement in G return a list of representatives of the conjugacy
#  classes of complements in G . If M does not have a complement in G , the
#  empty sequence := returned
local Comps,Presentation,fl;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=0;
  fi;
  if not ISA(Category(G),GrpPerm) then
    Error("First argument for Complements must be a perm-group");
  fi;
  if not (ISA(Category(M),GrpPerm) and IsNormal(G,M)) then
    Error("Second argument for Complements must be a normal subgroup of first")
     ;
  fi;
  if not Presentation=0 or Type(Presentation)=GrpFP then
    Error("Presentation must be an FP-group");
  fi;
  if not (Presentation=0) and Ngens(G)<>Ngens(Presentation) then
    Error("Presentation and G must have corresponding generators");
  fi;
  # =v= MULTIASSIGN =v=
  Comps:=section_complements@(G,M,SubStructure(G,#NOP
  ):comps:=2,presentation:=Presentation);
  fl:=Comps.val1;
  Comps:=Comps.val2;
  # =^= MULTIASSIGN =^=
  return Comps;
end;
;
#  ============================================================================
#  ===========
HasComplement@:=function(G,M)
#  -> ,BoolElt ,GrpPerm  Given a finite permutation group G , with normal
#  subgroup M , if M has a complement in G return true , otherwise false . A
#  single complement := also returned .
local C,Presentation,fl;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=0;
  fi;
  if Category(G)<>GrpPerm then
    Error("First argument for HasComplement must be a perm-group");
  fi;
  if Category(M)<>GrpPerm or not IsNormal(G,M) then
    Error("Second argument for HasComplement must be a normal subgroup of G");
  fi;
  if not Presentation=0 or Type(Presentation)=GrpFP then
    Error("Presentation must be an FP-group");
  fi;
  if not (Presentation=0) and Ngens(G)<>Ngens(Presentation) then
    Error("Presentation and G must have corresponding generators");
  fi;
  # =v= MULTIASSIGN =v=
  C:=section_complements@(G,M,SubStructure(G,#NOP
  ):comps:=1,presentation:=Presentation);
  fl:=C.val1;
  C:=C.val2;
  # =^= MULTIASSIGN =^=
  if fl then
    return rec(val1:=fl,
      val2:=C[1]);
  else
    return rec(val1:=fl,
      val2:=_);
  fi;
end;
;
#  ============================================================================
#  ===========
RefineSection@:=function(G,M,N)
#  -> ,SeqEnum  Given a finite permutation group G , with normal subgroups N
#  and M , such that N < = M , this returns a list L of subgroups of G , all
#  satisfying N < L [ i ] < M , such that L [ 1 ] / N and L [ i + 1 ] / L [ i ]
#  are elementary abelian or direct products of nonabelian simple groups for
#  all i , and L [ # L ] = M
local L;
  if not IsNormal(G,M) then
    Error("Second argument for Complement must be a normal subgroup of G");
  fi;
  if not IsNormal(G,N) then
    Error("Third argument for Complement must be a normal subgroup of G");
  fi;
  if not IsSubset(M,N) or N=M then
    Error("Second argument for Complement must be a proper subgroup of third");
  fi;
  L:=refine_section@(G,M,N);
  return L;
end;
;
Complements@:=function(G,M,N)
#  -> ,SeqEnum  Given a finite permutation group G , with normal subgroups N
#  and M , such that N < M , if M / N has a complement in G / N return a list
#  of representatives of the conjugacy classes of complements in G / N . If M /
#  N does not have a complement in G / N , the empty sequence := returned
local Comp,Presentation,fl;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=0;
  fi;
  if Category(G)<>GrpPerm then
    Error("First argument for Complement must be a perm-group");
  fi;
  if Category(M)<>GrpPerm or not IsNormal(G,M) then
    Error("Second argument for Complement must be a normal subgroup of G");
  fi;
  if Category(N)<>GrpPerm or not IsNormal(G,N) then
    Error("Third argument for Complement must be a normal subgroup of G");
  fi;
  if not IsSubset(M,N) or N=M then
    Error("Second argument for Complement must be a proper subgroup of third");
  fi;
  if not Presentation=0 or Type(Presentation)=GrpFP then
    Error("Presentation must be an FP-group");
  fi;
  if not (Presentation=0) and Ngens(G)<>Ngens(Presentation) then
    Error("Presentation and G must have corresponding generators");
  fi;
  # =v= MULTIASSIGN =v=
  Comp:=section_complements@(G,M,N:comps:=2,presentation:=Presentation);
  fl:=Comp.val1;
  Comp:=Comp.val2;
  # =^= MULTIASSIGN =^=
  return Comp;
end;
;
Complement@:=function(G,M,N)
#  -> ,SeqEnum  Given a finite permutation group G , with normal subgroups N
#  and M , such that N < M , if M / N has a complement in G / N return a list
#  of representatives of the conjugacy classes of complements in G / N . If M /
#  N does not have a complement in G / N , the empty sequence := returned
local Comp,Presentation,fl;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=0;
  fi;
  if Category(G)<>GrpPerm then
    Error("First argument for Complement must be a perm-group");
  fi;
  if Category(M)<>GrpPerm or not IsNormal(G,M) then
    Error("Second argument for Complement must be a normal subgroup of G");
  fi;
  if Category(N)<>GrpPerm or not IsNormal(G,N) then
    Error("Third argument for Complement must be a normal subgroup of G");
  fi;
  if not IsSubset(M,N) or N=M then
    Error("Second argument for Complement must be a proper subgroup of third");
  fi;
  if not Presentation=0 or Type(Presentation)=GrpFP then
    Error("Presentation must be an FP-group");
  fi;
  if not (Presentation=0) and Ngens(G)<>Ngens(Presentation) then
    Error("Presentation and G must have corresponding generators");
  fi;
  # =v= MULTIASSIGN =v=
  Comp:=section_complements@(G,M,N:comps:=2,presentation:=Presentation);
  fl:=Comp.val1;
  Comp:=Comp.val2;
  # =^= MULTIASSIGN =^=
  return Comp;
end;
;
Supplements@:=function(G,M)
#  -> ,SeqEnum  Given a finite permutation group G , with soluble normal
#  subgroup M , if M has a supplement in G return a list of representatives of
#  the conjugacy classes of supplements in G . If M does not have a supplement
#  in G , the empty sequence := returned
local Supps,fl;
  if Category(G)<>GrpPerm then
    Error("First argument for Supplements must be a perm-group");
  fi;
  if Category(M)<>GrpPerm or not IsNormal(G,M) then
    Error("Second argument for Supplements must be a normal subgroup of G");
  fi;
  # =v= MULTIASSIGN =v=
  Supps:=section_supplements@(G,M,SubStructure(G,#NOP
  ):supps:=2);
  fl:=Supps.val1;
  Supps:=Supps.val2;
  # =^= MULTIASSIGN =^=
  return Supps;
end;
;
#  ============================================================================
#  ===========
HasSupplement@:=function(G,M)
#  -> ,BoolElt ,GrpPerm  Given a finite permutation group G , with soluble
#  normal subgroup M , if M has a supplement in G return true , otherwise false
#  . A single supplement := also returned .
local C,fl;
  if Category(G)<>GrpPerm then
    Error("First argument for HasSupplement must be a perm-group");
  fi;
  if Category(M)<>GrpPerm or not IsNormal(G,M) then
    Error("Second argument for HasSupplement must be a normal subgroup of G");
  fi;
  # =v= MULTIASSIGN =v=
  C:=section_supplements@(G,M,SubStructure(G,#NOP
  ):supps:=1);
  fl:=C.val1;
  C:=C.val2;
  # =^= MULTIASSIGN =^=
  if fl then
    return rec(val1:=fl,
      val2:=C[1]);
  else
    return rec(val1:=fl,
      val2:=_);
  fi;
end;
;
#  ============================================================================
#  ===========
Supplements@:=function(G,M,N)
#  -> ,SeqEnum  Given a finite permutation group G , with normal subgroups N
#  and M , such that N < M and M / N := soluble , if M / N has a supplement in
#  G / N return a list of representatives of the conjugacy classes of M / N in
#  G / N . If M / N does not have a supplement in G / N , the empty sequence :=
#  returned
local Supp,fl;
  if Category(G)<>GrpPerm then
    Error("First argument for Supplement must be a perm-group");
  fi;
  if Category(M)<>GrpPerm or not IsNormal(G,M) then
    Error("Second argument for Supplement must be a normal subgroup of G");
  fi;
  if Category(N)<>GrpPerm or not IsNormal(G,N) then
    Error("Third argument for Supplement must be a normal subgroup of G");
  fi;
  if not IsSubset(M,N) or N=M then
    Error("Third argument for Supplement must be a proper subgroup of Second");
  fi;
  # =v= MULTIASSIGN =v=
  Supp:=section_supplements@(G,M,N:supps:=2);
  fl:=Supp.val1;
  Supp:=Supp.val2;
  # =^= MULTIASSIGN =^=
  return Supp;
end;
;
Supplement@:=function(G,M,N)
#  -> ,SeqEnum  Given a finite permutation group G , with normal subgroups N
#  and M , such that N < M and M / N := soluble , if M / N has a supplement in
#  G / N return a list of representatives of the conjugacy classes of M / N in
#  G / N . If M / N does not have a supplement in G / N , the empty sequence :=
#  returned
local Supp,fl;
  if Category(G)<>GrpPerm then
    Error("First argument for Supplement must be a perm-group");
  fi;
  if Category(M)<>GrpPerm or not IsNormal(G,M) then
    Error("Second argument for Supplement must be a normal subgroup of G");
  fi;
  if Category(N)<>GrpPerm or not IsNormal(G,N) then
    Error("Third argument for Supplement must be a normal subgroup of G");
  fi;
  if not IsSubset(M,N) or N=M then
    Error("Third argument for Supplement must be a proper subgroup of Second");
  fi;
  # =v= MULTIASSIGN =v=
  Supp:=section_supplements@(G,M,N:supps:=2);
  fl:=Supp.val1;
  Supp:=Supp.val2;
  # =^= MULTIASSIGN =^=
  return Supp;
end;
;
#  ============================================================================
#  ===========
InstallGlobalFunction(section_complements@,
function(G,M,N)
#  /out: G should be a finite permutation group, with normal subgroups N and M,
#  * where N < M.
#  * SectionComplement decides whether M/N has a complement in G/N, and
#  * returns true or false accordingly.
#  * If the optional parameter comps=0, that is all it returns.
#  * If comps=1 and there are complements, then it returns one complement.
#  * If comps=2 (default) and there are complements, then it returns
#  * a list of representatives of the conjugacy classes of complements of
#  * M/N in G/N.

local Comps,F,FG,comp,comps,f,g,presentation,rels,split,x;
  comps:=ValueOption("comps");
  if comps=fail then
    comps:=2;
  fi;
  presentation:=ValueOption("presentation");
  if presentation=fail then
    presentation:=0;
  fi;
  if G=M then
    if comps=0 then
      return rec(val1:=true,
        val2:=[]);
    fi;
    return rec(val1:=true,
      val2:=[N]);
  fi;
  if M=N then
    if comps=0 then
      return rec(val1:=true,
        val2:=[]);
    fi;
    return rec(val1:=true,
      val2:=[G]);
  fi;
  if presentation=0 then
    #   We need to construct a presentation of G/M (and hence of any
    #  * complements that there are). We do it on the strong generators of
    #  * G, using the function FPGroup. The generators of M will be added
    #  * as extra relators, to get the required presentation of G/M.
    
    # =v= MULTIASSIGN =v=
    f:=FPGroupStrong(G);
    FG:=f.val1;
    f:=f.val2;
    # =^= MULTIASSIGN =^=
    rels:=[];
    for g in Generators(M) do
      Add(rels,g@@f);
    od;
    F:=Subquo(FG,[rels]);
    #   The individual complements will be stored as lists of generators,
    #  * which correspond to those of F and FG.
    #  * (We store them as lists rather than as subgroups, since some of the
    #  *  elements in the list might be trivial, and we don't want them to get
    #  * deleted, or we would ruin the correspondence with F.
    #  * Initially, there is a single complement (of A/A in G/A).
    
    Comps:=[List([1..Ngens(FG)],i->(FG.i)@f)];
  else
    F:=presentation;
    Comps:=[List([1..Ngens(G)],i->G.i)];
  fi;
  # =v= MULTIASSIGN =v=
  Comps:=LiftComplementsSection@(G,M,N,F,Comps,comps);
  split:=Comps.val1;
  Comps:=Comps.val2;
  # =^= MULTIASSIGN =^=
  if not split then
    return rec(val1:=false,
      val2:=[]);
  fi;
  #   Change the complements from lists of generators to genuine subgroups
  #  * containing N.
  
  if comps=0 then
    Comps:=[];
  elif comps=1 then
    Comps:=[SubStructure(G,(Difference((Union(Generators(N)
     ,SequenceToSet(Comps[1]))),Set([One(G)]))))];
  else
    Comps:=List(Comps,comp->SubStructure(G,(Difference((Union(Generators(N)
     ,SequenceToSet(comp))),Set([One(G)])))));
  fi;
  for x in Comps do
    AssertAttribute(x,"Order",QuoInt(Size(G),(QuoInt(Size(M),Size(N)))));
  od;
  return rec(val1:=true,
    val2:=Comps);
end);

InstallGlobalFunction(section_supplements@,
function(G,M,N)
#  /out: G should be a finite permutation group, with normal subgroups N and M,
#  * where N < M and M/N must be soluble.
#  * SectionSupplement decides whether M/N has proper supplements in G/N, and
#  * returns true or false accordingly.
#  * If the optional parameter comps=0, that is all it returns.
#  * If supps=1 and there are supplements, then it returns one supplement.
#  * If supps=2 (default) and there are supplements, then it returns
#  * a list of representatives of the conjugacy classes of minimal
#  * supplements of M/N in G/N.

local 
   A,B,CS,ES,F,FG,H,L,LiftSupps,MinSupps,RF,S,Se,Supps,T,cs,f,g,i,index,layer,
   len,liftpres,lifts,lm,lphi,ls,m,ms,new,phi,pres,rels,s,sol,split,supp,suppct,
   supps,suppsexist;
  supps:=ValueOption("supps");
  if supps=fail then
    supps:=2;
  fi;
  RF:="unneeded record format";
  if M=N then
    return rec(val1:=false,
      val2:=[]);
  fi;
  if G=M then
    if supps=0 then
      return rec(val1:=true,
        val2:=[]);
    fi;
    return rec(val1:=true,
      val2:=[N]);
  fi;
  #   We need to construct a presentation of G/M .
  #  * We do it on the strong generators of
  #  * G, using the function FPGroup. The generators of M will be added
  #  * as extra relators, to get the required presentation of G/M.
  
  # =v= MULTIASSIGN =v=
  f:=FPGroupStrong(G);
  FG:=f.val1;
  f:=f.val2;
  # =^= MULTIASSIGN =^=
  rels:=[];
  for g in Generators(M) do
    Add(rels,g@@f);
  od;
  F:=Subquo(FG,[rels]);
  #   Now find an elementary series from N to M to lift through.
  # =v= MULTIASSIGN =v=
  sol:=refine_section@(G,M,N);
  L:=sol.val1;
  sol:=sol.val2;
  # =^= MULTIASSIGN =^=
  len:=Size(L);
  if not sol then
    Error("Error in Supplements routine. The section M/N must be soluble");
  fi;
  index:=[QuoInt(Size(L[1]),Size(N))];
  for i in [2..len] do
    Add(index,Index(L[i],L[i-1]));
  od;
  #  print "Indices of ascending subgroup chain: ", Reverse(index);
  #   We lift the supplements through the layers A/B of the series, where
  #  * at each stage we lift only the minimal supplements from the previous
  #  * stage.
  #  * During the lifting process, each supplement is stored as a RF record,
  #  * where the components are
  #  * supp: list of generators of the supplement mod A
  #  * pres: presentation of the supplement mod A generators corresponding
  #  *       to those in the list 'supp'.
  #  * int : a module representing the current intersection of the supplement
  #  *       with A/B.
  #  * modmap: the map from <supp,int> to the module int.
  #  * Initially, there is a single supplement <G,M>.
  #  * A supplement S becomes a minimal supplement in an elementary
  #  * section A/B when it does not split over any maximal normal
  #  * subgroups of (S meet A)/B.
  
  suppsexist:=false;
  Supps:=[rec(supp:=List([1..Ngens(FG)],i->f(FG.i)),
    pres:=F)];
  A:=M;
  for layer in Reversed([1..len]) do
    #  print "layer = ",layer;
    MinSupps:=[];
    # rewritten select statement
    if (layer=1) then
      B:=N;
    else
      B:=L[layer-1];
    fi;
    #   initially all supplements have intersection the whole of A/B.
    CS:=[];
    for s in Supps do
      H:=SubStructure(G,s.supp,#TODO CLOSURE
        A);
      # =v= MULTIASSIGN =v=
      phi:=GModule(H,A,B);
      m:=phi.val1;
      phi:=phi.val2;
      # =^= MULTIASSIGN =^=
      cs:=s;
      cs.int:=m;
      cs.modmap:=phi;
      Add(CS,cs);
    od;
    Supps:=CS;
    #   Now we go through all of the supplements to see if they split
    #  * over a maximal submodule of their current intersection with m.
    #  * A supplement thatdoesn't split becomes a minimal supplement at
    #  * this layer.
    
    suppct:=1;
    while suppct <= Size(Supps) do
      S:=Supps[suppct].supp;
      m:=Supps[suppct].int;
      phi:=Supps[suppct].modmap;
      pres:=Supps[suppct].pres;
      H:=Group(m);
      #   Run through maximal submodules of m 
      lifts:=false;
      if DimensionOfMatrixGroup(m) > 0 then
        for ms in MaximalSubmodules(m) do
          # =v= MULTIASSIGN =v=
          LiftSupps:=LiftComplementsElAb@(G,m@@phi,ms@@phi,pres,[S],2);
          lifts:=LiftSupps.val1;
          LiftSupps:=LiftSupps.val2;
          # =^= MULTIASSIGN =^=
          if lifts then
            suppsexist:=true;
            for ES in LiftSupps do
              ls:=SubStructure(H,ES,#TODO CLOSURE
                B);
              if Intersection(ls,A)=B then
                Add(Supps,rec(supp:=ES,
                  pres:=pres,
                  int:=ms,
                  modmap:=phi));
                #  GModule won't work, but Dim(ms)=0, so that's OK.
              else
                # =v= MULTIASSIGN =v=
                lphi:=GModule(ls,Intersection(ls,A),B);
                lm:=lphi.val1;
                lphi:=lphi.val2;
                # =^= MULTIASSIGN =^=
                Add(Supps,rec(supp:=ES,
                  pres:=pres,
                  int:=lm,
                  modmap:=lphi));
              fi;
            od;
            break;
          fi;
        od;
      fi;
      if lifts then
        new:=false;
      else
        #   this is a minimal suupplement, but we must check it for
        #   conjugacy with existing ones.
        new:=true;
        T:=SubStructure(G,S,#TODO CLOSURE
          B);
        for s in MinSupps do
          if IsConjugate(G,T,SubStructure(G,s.supp,#TODO CLOSURE
            B)) then
            new:=false;
            break;
          fi;
        od;
      fi;
      if new and (layer > 1 or SubStructure(G,S,#TODO CLOSURE
        B)<>G) and (layer > 1 or supps=2 or (supps=1 and Size(MinSupps)=0)) 
         then
        if layer=1 then
          Add(MinSupps,rec(supp:=S));
        else
          if DimensionOfMatrixGroup(m)=0 then
            Se:=S;
            liftpres:=pres;
          else
            # =v= MULTIASSIGN =v=
            liftpres:=LiftedPresentation@(S,pres,m,phi);
            Se:=liftpres.val1;
            liftpres:=liftpres.val2;
            # =^= MULTIASSIGN =^=
          fi;
          Add(MinSupps,rec(supp:=Se,
            pres:=liftpres));
        fi;
      fi;
      suppct:=suppct+1;
    od;
    Supps:=MinSupps;
    A:=B;
  od;
  if not suppsexist then
    return rec(val1:=false,
      val2:=[]);
  fi;
  #   Change the supplements from lists of generators to genuine subgroups
  #  * containing N.
  
  if supps=0 then
    Supps:=[];
  elif supps=1 then
    Supps:=[SubStructure(G,N,#TODO CLOSURE
      Supps[1].supp)];
  else
    Supps:=List(Supps,s->SubStructure(G,N,#TODO CLOSURE
      s.supp));
  fi;
  return rec(val1:=true,
    val2:=Supps);
end);

InstallGlobalFunction(LiftComplementsSection@,
function(G,M,N,F,Comps,comps)
local 
   A,B,Comps,H,L,LiftComps,MSL,Q,S,Supps,Suppsubs,T,varX,comp,ecomps,g,got,i,
   index,len,newcomp,onesplit,p,pQ,split,supp,t,usesylp;
  usesylp:=true;
  L:=refine_section@(G,M,N);
  len:=Size(L);
  index:=[QuoInt(Size(L[1]),Size(N))];
  for i in [2..len] do
    Add(index,Index(L[i],L[i-1]));
  od;
  #  print "Indices of ascending subgroup chain: ", Reverse(index);
  #   Now comes the lifting phase through the layers. 
  A:=M;
  for i in Reversed([1..len]) do
    #  print "i = ",i;
    # rewritten select statement
    if (i=1) then
      B:=N;
    else
      B:=L[i-1];
    fi;
    # rewritten select statement
    if (i=1) then
      ecomps:=comps;
    else
      ecomps:=2;
    fi;
    #   At the intermediate steps we need to return conjugacy class reps.
    #  * of complements, in order to see if they extend further.
    #  * At the final step, we only return them if the caller wants them.
    
    if IsPrimePower(QuoInt(Size(A),Size(B))) then
      #  elementary abelian section
      # =v= MULTIASSIGN =v=
      LiftComps:=LiftComplementsElAb@(G,A,B,F,Comps,ecomps);
      split:=LiftComps.val1;
      LiftComps:=LiftComps.val2;
      # =^= MULTIASSIGN =^=
      #   mix-up with returned type!
      if ecomps=1 and split then
        LiftComps:=[LiftComps];
      fi;
    else
      #  nonabelian section
      split:=false;
      LiftComps:=[];
      #  print "#Comps =",#Comps;
      for comp in Comps do
        #  print "Next comp";
        H:=SubStructure(G,comp,#TODO CLOSURE
          A);
        if usesylp and IsPrimePower(QuoInt(Size(H),Size(A))) then
          p:=CollectedFactors(QuoInt(Size(H),Size(A)))[1][1];
          Suppsubs:=[SubStructure(H,Sylow(H,p),#TODO CLOSURE
            B)];
        else
          if IsSoluble(B) then
            #  print "Getting maximals soluble case";
            MSL:=MaximalSubgroups(H,B);
            MSL:=List(MSL,m->SubStructure(H,m.subgroup,#TODO CLOSURE
              B));
            #  print #MSL, "maximals";
          else
            #  print "Getting maximals insoluble case";
            if Size(B)=1 then
              MSL:=MaximalSubgroups(H,SubStructure(H,#NOP
              ));
              MSL:=List(MSL,m->m.subgroup);
            else
              # =v= MULTIASSIGN =v=
              pQ:=Subquo(H,[B]);
              Q:=pQ.val1;
              pQ:=pQ.val2;
              # =^= MULTIASSIGN =^=
              MSL:=MaximalSubgroups(Q,SubStructure(Q,#NOP
              ));
              MSL:=List(MSL,m->m.subgroup@@pQ);
            fi;
          fi;
          #  print "Got maximals";
          Suppsubs:=Filtered(MSL,m->SubStructure(H,m,#TODO CLOSURE
            A)=H and not IsSubset(m,A));
        fi;
        #   For each such subgroup we need to find elements mapping
        #   onto the same elements of G/A as those in comp.
        #   and then find complements of it recursively.
        #  print "#Suppsubs=",#Suppsubs;
        for supp in Suppsubs do
          #  print "supp of order",#supp;
          newcomp:=[];
          for g in comp do
            varX:=Intersection(SubStructure(H,A,#TODO CLOSURE
              g),supp);
            T:=RightTransversal(varX,Intersection(varX,A));
            for t in T do
              if t^-1*g in A then
                Add(newcomp,t);
                break;
              fi;
            od;
          od;
          if Intersection(supp,A)=B then
            onesplit:=true;
            Supps:=[newcomp];
          else
            # =v= MULTIASSIGN =v=
            Supps:=LiftComplementsSection@(supp,(Intersection(supp,A))
             ,B,F,[newcomp],ecomps);
            onesplit:=Supps.val1;
            Supps:=Supps.val2;
            # =^= MULTIASSIGN =^=
            #  print "end of recursive call";
          fi;
          if onesplit then
            split:=true;
            #   only add new supplements ifthey are not conjugate to existing
            #  ones.
            for supp in Supps do
              S:=SubStructure(G,supp,#TODO CLOSURE
                B);
              got:=false;
              for comp in LiftComps do
                if IsConjugate(G,S,SubStructure(G,comp,#TODO CLOSURE
                  B)) then
                  got:=true;
                  break;
                fi;
              od;
              if not got then
                LiftComps:=Concatenation(LiftComps,[supp]);
              fi;
            od;
          fi;
        od;
      od;
    fi;
    if not split then
      return rec(val1:=false,
        val2:=[]);
    fi;
    Comps:=LiftComps;
    A:=B;
  od;
  return rec(val1:=true,
    val2:=Comps);
end);

#  ============================================================================
#  =============
InstallGlobalFunction(refine_section@,
function(G,M,N)
#  /out: (This is essentially the same as ElAbSeries, but with M as upper limit
#  * of series).
#  * G should be a finite permutation group, with normal subgroups N and M,
#  * where N < M.
#  * This function calculates and returns a list L of subgroups of G,
#  * all satisfying N < L[i] < M, such that L[1]/N and L[i+1]/L[i] are
#  * elementary abelian or direct products of nonabelian simple groups
#  * for all i, and L[#L] = M.
#  * It does it by looking for normal p-subgroups and refining,
#  * and then factoring them out when there are no more to find, and
#  * working in the factor group.
#  * It also returns true or false, according to whether M/N is soluble or not.

local CS,L,NN,P,Q,R,fac,fact,i,len,p,pR,phi,primes,projP,quoP,sol,syls;
  #   First compute all the relevant Sylow-subgroups of G 
  sol:=true;
  fac:=CollectedFactors(QuoInt(Size(M),Size(N)));
  primes:=[];
  syls:=[];
  for fact in fac do
    p:=fact[1];
    Add(primes,p);
    Add(syls,Sylow(G,p));
  od;
  L:=[];
  len:=0;
  #   len = length of L 
  NN:=N;
  #   NN will be a normal subgroup of G 
  while true do
    fac:=CollectedFactors(QuoInt(Size(M),Size(NN)));
    for fact in fac do
      p:=fact[1];
      Q:=syls[Position(primes,p)];
      #   a Sylow p-subgroup of G 
      if Size(Q)=Size(G) then
        P:=M;
      else
        P:=Intersection(Core(G,SubStructure(G,NN,#TODO CLOSURE
          Q)),M);
      fi;
      if Size(P)<>Size(NN) then
        #   Split P/NN up into elementary layers and append to L 
        # =v= MULTIASSIGN =v=
        projP:=Subquo(P,[NN]);
        quoP:=projP.val1;
        projP:=projP.val2;
        # =^= MULTIASSIGN =^=
        CS:=pCentralSeries(quoP,p);
        for i in Reversed([1..Size(CS)-1]) do
          len:=len+1;
          if len=1 then
            L[len]:=SubStructure(G,CS[i]@@projP);
          else
            L[len]:=SubStructure(G,L[len-1],#TODO CLOSURE
              CS[i]@@projP);
          fi;
        od;
      fi;
    od;
    if len=0 or L[len]=NN then
      #   L[len]/N = soluble radical of M/N, so M/N is not soluble, and we
      #  * take the nonabelian soluble residual as next layer
      
      sol:=false;
      if IsSoluble(N) then
        #   NN is the soluble radical of M.
        # =v= MULTIASSIGN =v=
        pR:=RadicalQuotient(M);
        R:=pR.val1;
        pR:=pR.val2;
        # =^= MULTIASSIGN =^=
      else
        # =v= MULTIASSIGN =v=
        pR:=Subquo(M,[NN]);
        R:=pR.val1;
        pR:=pR.val2;
        # =^= MULTIASSIGN =^=
      fi;
      len:=len+1;
      L[len]:=SolubleResidual(R)@@pR;
    fi;
    NN:=L[len];
    if NN=M then
      break;
    fi;
  od;
  return rec(val1:=L,
    val2:=sol);
end);

#  ============================================================================
#  =============
InstallGlobalFunction(LiftComplementsElAb@,
function(G,A,B,F,Comps,ecomps)
#  /out: This function is called by section_complements and
#  section_supplements.
#  * A and B are normal subgroups of a subgroup H of the permutation group G
#  with
#  * B < A and A/B elementary abelian.
#  * Comps is a list of generators of subgroups of H, that form complements
#  * of some section M/A in H/A, when taken modulo A.
#  * F is a finitely presented group isomorphic to these complements, with
#  * corresponding generators to those in the lists.
#  * LiftComplementsElAb attempts to lift these complements to complements
#  * of M/B in H/B.
#  * It returns true or false, according to whether some complement lifts.
#  * If ecomps=0 it returns just this.
#  * If ecomps=1 it returns one such complement (if there are any).
#  * If ecomps=2 it returns a list containing representatives of the
#  * conjugacy classes of these lifted complements in H.
#  * (The complements are defined as lists of their generators in H.)

local 
   CCS,EC,ECR,FM,FRV,FtoG,K,LiftComps,M,NCS,NG,NewComps,RV,Rep,S,SA,varZ,c,comp,
   conjcomp,d,dim,gen,i,j,liftgens,newcomp,ng,ngorbs,ngp,nnc,normSA,normgens,nr,
   phi,rel,rels,sns,split,vec,w;
  LiftComps:=[];
  #   This will be the lifted complement-list to be returned.
  NG:=Intersection(Normaliser(G,A),Normaliser(G,B));
  #  usually G, but not always when called from
  #  section_supplements on a proper subgroup.
  varZ:=Integers();
  # =v= MULTIASSIGN =v=
  phi:=GModule(NG,A,B);
  M:=phi.val1;
  phi:=phi.val2;
  # =^= MULTIASSIGN =^=
  dim:=DimensionOfMatrixGroup(M);
  K:=BaseRing(M);
  Rep:=Representation(M);
  ng:=Ngens(F);
  rels:=Relations(F);
  nr:=Size(rels);
  #   Now we find all liftings to H/B of each complement in the list 
  #   print "  +Lifting",#Comps,"complements through next layer, of size",#M;
  for comp in Comps do
    #  print "    +Lifting next complement.";
    FtoG:=GroupHomomorphismByImages(F,NG,
      GeneratorsOfGroup(F),comp);
    #   This is not a genuine homomorphism - the whole point is that we want to
    #  * work out the images of the relators of F in A/B
    
    FM:=GModule(F,List([1..ng],i->comp[i]@Rep));
    #   FM is essentially the same module as M=A/B but regarded as an F-module 
    RV:=[];
    for rel in rels do
      w:=LHS(rel)*RHS(rel)^-1;
      Add(RV,w@FtoG@phi);
    od;
    #    We need to coerce the values of RV into this FM 
    FRV:=List([1..nr],i->Eltseq(RV[i]) #CAST FM
      );
    #   Now we can do the cohomology calculation! 
    # =v= MULTIASSIGN =v=
    NewComps:=ComplementVectors(FM,FRV);
    split:=NewComps.val1;
    NewComps:=NewComps.val2;
    # =^= MULTIASSIGN =^=
    if split and ecomps=0 then
      #  print "Extension splits.";
      return rec(val1:=true,
        val2:=0);
    fi;
    if not split then
      #  print "       No lifts for this complement.";
    else
      nnc:=Size(NewComps);
      #  print "      ",nnc,"lifts for this complement.";
      #   Now, for each complement, we can work out the generators of the
      #  * corresponding lifted complement.
      
      EC:=[];
      for newcomp in NewComps do
        liftgens:=[];
        for i in [1..ng] do
          gen:=comp[i];
          vec:=newcomp[i];
          for j in [1..dim] do
            gen:=gen*(M.j)@@phi^(vec[j] #CAST varZ
              );
          od;
          Add(liftgens,gen);
        od;
        #   A check follows that can be omitted when program is reliable! 
        #  print "AAAAA";
        S:=SubStructure(G,liftgens);
        if Intersection(S,A)<>Intersection(S,B) then
          Error("Subgroup",S,"is not a complement!");
        fi;
        #  print "BBBBB";
        if ecomps=1 then
          return rec(val1:=true,
            val2:=liftgens);
        fi;
        Add(EC,liftgens);
      od;
      SA:=SubStructure(G,A,#TODO CLOSURE
        comp);
      #  print Index(G,SA);
      normSA:=Intersection(Normaliser(G,SA),Normaliser(G,B));
      #  print "Got normaliser";
      if nnc > 1 and normSA<>SA then
        #   We have to work out the action of the normaliser of the complement
        #  * being lifted on the lifts.
        #  * We will do this using IsConjugate Subgroup, to avoid the
        #  * complications of doing it using the cohomology.
        
        #  print "       +Calculating normaliser action on complements.";
        normgens:=[];
        sns:=SA;
        for gen in Generators(normSA) do
          if not gen in sns then
            Add(normgens,gen);
            sns:=SubStructure(G,sns,#TODO CLOSURE
              gen);
          fi;
        od;
        #  print "        ",#normgens,"normalising generators for this
        #  subgroup.";
        #   Now we are ready to work out the action of normsub on the set
        #  * of complements. We won't set this up as a formal G-action on the
        #  * set, but simply build the corresponding permutations ngp[i] of the
        #  * set {1,2,..,nnc} induced by the generator normgens[i], where
        #  * the image ngp[i][j] of j under ngp[i] corresponds to conjugation
        #  * of NewComps[j] by normgens[i].
        #  * First we must form the subgroups generated by the complements.
        
        NCS:=List(EC,newcomp->SubStructure(G,B,#TODO CLOSURE
          newcomp));
        ngp:=[];
        for i in [1..Size(normgens)] do
          ngp[i]:=[];
          gen:=normgens[i];
          for c in [1..nnc] do
            conjcomp:=NCS[c]^gen;
            for d in [1..nnc] do
              if IsConjugate(SA,conjcomp,NCS[d]) then
                ngp[i][c]:=d;
                break;
              fi;
            od;
          od;
        od;
        ngorbs:=Orbits(SubStructure(SymmetricGroup(nnc),ngp));
        ECR:=List([1..Size(ngorbs)],k->EC[Representative(ngorbs[k])]);
        #   print "       -",#ECR,"orbits on complements.";
      else
        ECR:=EC;
      fi;
      LiftComps:=Concatenation(LiftComps,ECR);
    fi;
  od;
  #  print "  +Total of",#LiftComps,"complements found at next level.";
  if Size(LiftComps)=0 then
    return rec(val1:=false,
      val2:=0);
  fi;
  return rec(val1:=true,
    val2:=LiftComps);
end);

InstallGlobalFunction(LiftedPresentation@,
function(supp,F,m,phi)
#  /out: supp should be a list of permutations generating a subgroup S of
#  * a group H with normal subgroups B<A, such that SB=A.
#  * F should be a presentation of S/A with generators corresponding
#  * to those of S.
#  * m should be the section A/B as an H-module with natural map phi:A->m.
#  * An extended list of generators suppe of S is returned  containing
#  * a basis of S meet A mod B, together with a presentation of S/B on
#  * this generating set.

local FRV,Fm,FtoH,H,RV,Rep,d,ng,rel,rels,suppe,w;
  ng:=Ngens(F);
  d:=DimensionOfMatrixGroup(m);
  suppe:=Concatenation(supp,List([1..d],i->m.i@@phi));
  #  extended supp generators
  H:=Group(m);
  FtoH:=GroupHomomorphismByImages(F,H,
    GeneratorsOfGroup(F),List([1..ng],i->supp[i]));
  rels:=Relations(F);
  Rep:=Representation(m);
  Fm:=GModule(F,List([1..ng],i->supp[i]@Rep));
  #  Fm is essentially the same module as m=A/B but regarded as an F-module
  #   calculate values of relations of F in m - we need these for the
  #   presentation
  RV:=[];
  for rel in rels do
    w:=LHS(rel)*RHS(rel)^-1;
    Add(RV,w@FtoH@phi);
  od;
  #    We need to coerce the values of RV into this Fm 
  FRV:=List(RV,r->Eltseq(r) #CAST Fm
    );
  return rec(val1:=suppe,
    val2:=ModuleExtension(Fm,FRV));
end);


