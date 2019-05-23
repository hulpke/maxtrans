#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, AssertAttribute, Centraliser, Codomain,
#  CompositionFactors, Domain, ElementaryAbelianSeries, FPGroup, FPGroupStrong,
#  Format, Generators, Generic, Id, Image, Index, IsConjugate, IsIdentity,
#  MaximalSubgroups, MaximalSubgroupsH, Names, Ngens, Orbit, Position, Radical,
#  RadicalQuotient, Random, RandomSchreier, ReduceGenerators, RightTransversal,
#  SA, Socle, SocleQuotient, Stabilizer, SubgroupsLift, Sym, TGHrep, TR,
#  Transversal, ei, ej, pC, pNQ, pQi, pSA1, pT, psi, rho, rhoi, rhoj

#  Defines: PMaxSubsH, PType1Maximals, PType2Maximals, PType3Maximals,
#  PType4Maximals, PType5Maximals

DeclareGlobalFunction("PMaxSubsH@");

DeclareGlobalFunction("PType1Maximals@");

DeclareGlobalFunction("PType2Maximals@");

DeclareGlobalFunction("PType3Maximals@");

DeclareGlobalFunction("PType4Maximals@");

DeclareGlobalFunction("PType5Maximals@");

DeclareGlobalFunction("PMaxSubsH@");

#  
#  Part of maximal subgroups package.
#  Written by Derek Holt.

#  Forward declaration of PMaxSubsH
#  import "normconj.m": PartitionIsConjugate;
InstallGlobalFunction(PType1Maximals@,
function(TILDEVAR~GR,srino)
#  /out: Find the maximal subgroups of Type 1 coming from socle factor
#  * SF[socreps[srino]]. That is, those coming from maximal subgroups
#  * of the corresponding almost simple group.

local 
   A,F,G,H,I,Impsi,N,Orbitsri,Print,S,SA,SF,SQ,SocImpsi,T,aux,compsub,con,dummy,
   elt,genlist,msi,msigens,msilist,nSF,newfplist,newgenlist,newpreslist,p,pSQ,
   pSQH,phi,projlist,psi,q,reco,socreps,sri,srit,subgp,symnorm,t,x,y,yy;
  G:=GR.group;
  socreps:=GR.socreps;
  SF:=GR.SF;
  SA:=GR.SA;
  genlist:=GR.genlist;
  projlist:=GR.projlist;
  Print:=GR.printlevel;
  nSF:=Size(SF);
  pSQ:=GR.pSQ;
  SQ:=Codomain(pSQ);
  sri:=socreps[srino];
  S:=SF[sri];
  if Print > 0 then
    Print("Finding Type 1 maximal subgroups for socle factor number ",sri);
  fi;
  T:=GR.transversals[srino];
  psi:=GR.asembeddings[srino];
  N:=Domain(psi);
  A:=Codomain(psi);
  Impsi:=Image(psi);
  SocImpsi:=Socle(Impsi);
  Orbitsri:=Orbit(Image(SA),sri);
  msilist:=GR.msints[srino];
  for subgp in msilist do
    newgenlist:=genlist;
    newpreslist:=GR.preslist;
    newfplist:=GR.fplist;
    msigens:=List(subgp.generators,g->g@@psi@projlist[sri]);
    if GR.presentation then
      #   compute presentations of the subgroups in msilist
      msi:=SubStructure(G,msigens);
      #   BEWARE - Verify needed
      msi.Order:=subgp.order;
      #   BEWARE - this is billu's addition
      if Size(msi) <= GR.smallsimplefactor then
        # =v= MULTIASSIGN =v=
        phi:=FPGroup(msi);
        F:=phi.val1;
        phi:=phi.val2;
        # =^= MULTIASSIGN =^=
      else
        # =v= MULTIASSIGN =v=
        phi:=FPGroupStrong(msi);
        F:=phi.val1;
        phi:=phi.val2;
        # =^= MULTIASSIGN =^=
        msigens:=List([1..Ngens(F)],i->F.i@phi);
      fi;
    fi;
    compsub:=[];
    for t in T do
      srit:=sri^SA(t);
      newgenlist[srit]:=List(msigens,g->(g^t)@projlist[srit]);
      #  NOTE Evaluation of projlist SLOW!
      compsub[srit]:=SubStructure(G,newgenlist[srit]);
      compsub[srit].Order:=subgp.order;
      #   BEWARE - this is billu's addition
      if GR.presentation then
        #   print "Type 1 pres";
        newpreslist[srit]:=F;
        #   DFH's code was: newfplist[srit] := hom< F->compsub[srit] |
        #  newgenlist[srit] >;
        #   billu's replacement to get shorter words from @@newfplist[srit] (2
        #  lines):
        aux:=GroupHomomorphismByImages(F,compsub[srit],
          GeneratorsOfGroup(F),newgenlist[srit]);
        #  newfplist[srit] := hom< F->compsub[srit] | x :-> x@aux, y :->
        #  (y^(t^-1))@@phi>;
        newfplist[srit]:=newfplist[srit];
      fi;
    od;
    #   I := sub< G | &cat(newgenlist) >;  only needed for sanity check
    #   intersection of the subgroup we are computing with Soc(G)
    #   DONT NEED THIS ANY MORE !
    #  * In the case G=Sym(n) for n>=9, a generator of the normaliser of each
    #  * subgroup outside of Alt(n) should have been returned with the
    #  subgroup.
    #  * If there is only one socle factor in this orbit, then we can use
    #  * this information.
    #  *
    #  if #T eq 1 and "normgen" in Names(Format(subgp)) and
    #  assigned subgp`normgen then
    #  newgenlist[nSF+1] := [(subgp`normgen) @@ psi];
    #  // CORRECTION!  We also need generators outside socle that
    #  // centralize S.
    #  H := pSQ(sub<G|GR`socle,(subgp`normgen) @@ psi>);
    #  if H ne SQ then
    #  C:=Centraliser(G,S);
    #  while H ne SQ do
    #  x:=Random(C);
    #  if not pSQ(x) in H then
    #  Append(~newgenlist[nSF+1],x);
    #  H:=sub<SQ|H,pSQ(x)>;
    #  end if;
    #  end while;
    #  end if;
    #  if GR`presentation then
    #  //we have to re-calculate presentation of G/socle in this case!
    #  H := sub< G | newgenlist[nSF+1] >;
    #  pSQH := hom< H->SQ | [pSQ(g) : g in newgenlist[nSF+1]] >;
    #  SQH := sub< SQ | [pSQ(g) : g in newgenlist[nSF+1]] >;
    #  if #SQH le GR`smallsimplefactor then
    #  F,phi := FPGroup(SQH);
    #  else
    #  F,phi := FPGroupStrong(SQH);
    #  end if;
    #  newpreslist[nSF+1] := F;
    #  for i in [Ngens(SQH)+1..Ngens(F)] do
    #  Append(~newgenlist[nSF+1],F.i @ phi @@ pSQH);
    #  end for;
    #  end if;
    #  else
    
    #   Now we build generators of the normaliser of I in G
    #   (modulo the subgroup)
    #   We do this, because calling 'Normaliser' can be very slow!
    newgenlist[nSF+1]:=[];
    for elt in GR.modsocgens do
      x:=elt;
      #  multiply x by suitable elements of socle factors until it
      #  normalises I.
      symnorm:=false;
      for p in Orbitsri do
        q:=p^SA(x);
        if "normgen" in Names(Format(subgp)) and IsBound(subgp.normgen) then
          symnorm:=true;
          dummy:=tp:=ForAny(T,t->sri^SA(t)=p);
          Assert(1,dummy);
          dummy:=tq:=ForAny(T,t->sri^SA(t)=q);
          Assert(1,dummy);
          yy:=tq*x^-1*tp^-1;
          if not psi(yy) in SocImpsi then
            yy:=yy*subgp.normgen@@psi;
          fi;
          y:=(yy^tq)@projlist[q];
        else
          # =v= MULTIASSIGN =v=
          y:=IsConjugate(SF[q],compsub[p]^x,compsub[q]);
          con:=y.val1;
          y:=y.val2;
          # =^= MULTIASSIGN =^=
          if not con then
            #   SF[q], compsub[p]^x, compsub[q]:Magma;
            Error("Conjugation error while calculating 
             normaliser",Size(compsub[q]));
          fi;
        fi;
        x:=x*y;
      od;
      #   BEWARE - Bill U removed this check
      #  if symnorm and not I^x eq I then
      #  error "Computed element does not normalise subgroup";
      #  end if;
      
      Add(newgenlist[nSF+1],x);
    od;
    #    end if; 
    reco:=rec();
    if GR.presentation then
      # =v= MULTIASSIGN =v=
      reco.presentation:=PresentationSubgroupTF@(newgenlist,newpreslist,
       GR.projlist,newfplist);
      reco.subgroup:=reco.presentation.val1;
      reco.presentation:=reco.presentation.val2;
      # =^= MULTIASSIGN =^=
    else
      reco.subgroup:=SubgroupTF@(newgenlist);
    fi;
    reco.length:=(QuoInt(Size(S),subgp.order))^Size(T);
    reco.order:=QuoInt(Size(G),reco.length);
    AssertAttribute(reco.subgroup,"Order",reco.order);
    #   assert not IsNormal(G,reco`subgroup);
    Add(GR.maxsubs,reco);
    if Print > 0 then
      Print("+Maximal subgroup of order",reco.order,"induced from almost simple 
       group.");
      if Print > 2 then
        Print(reco.subgroup);
      fi;
    fi;
  od;
  return rec();
end);

InstallGlobalFunction(PType2Maximals@,
function(TILDEVAR~GR,srino)
#  /out: Find the maximal subgroups of Type 2 coming from socle factor
#  * S = SF[socreps[srino]]. That is, those of diagonal type. They
#  * correspond to homomorphisms from H/M to A/S that extend the map N/M->A/S
#  * induced by psi, for all minimal overgroups H of N=N(S), where A if the
#  * almost simple group associated with N. The overgroups correspond to
#  * minimal block systems of P (= CosetImage(G,N)).

local 
   A,A0,G,H,H0,I,M,N,N0,Print,S,SA,SF,T,TGH,TGHrep,THN,THNlift,a,con,conngl1,
   conngl1c,connglt,elt,g,gensN0,i,imgensN0,impsi0,indGH,indHN,j,liftpsi0,nSF,
   newgenlist,overgps,pA0,pSQ,projlist,psi,psi0,reco,socreps,sri,srit,sritv,
   sriu,sriv,t,u,v,w,x,x0,y,z;
  G:=GR.group;
  socreps:=GR.socreps;
  SF:=GR.SF;
  SA:=GR.SA;
  pSQ:=GR.pSQ;
  projlist:=GR.projlist;
  Print:=GR.printlevel;
  nSF:=Size(SF);
  sri:=socreps[srino];
  S:=SF[sri];
  if Print > 0 then
    Print("Finding Type 2 (diagonal) maximal subgroups for socle factor number 
     ",sri);
  fi;
  T:=GR.transversals[srino];
  psi:=GR.asembeddings[srino];
  N:=Domain(psi);
  A:=Codomain(psi);
  if N=G then
    return rec();
  fi;
  N0:=N@pSQ;
  #   N/M
  # =v= MULTIASSIGN =v=
  pA0:=Subquo(A,[Socle(A)]);
  A0:=pA0.val1;
  pA0:=pA0.val2;
  # =^= MULTIASSIGN =^=
  gensN0:=List([1..Ngens(N0)],i->N0.i);
  imgensN0:=List([1..Size(gensN0)],i->gensN0[i]@@pSQ@psi@pA0);
  psi0:=GroupHomomorphismByImages(N0,A0,
    GeneratorsOfGroup(N0),imgensN0);
  impsi0:=Image(psi0);
  overgps:=MinimalOvergroupsH@(G,N);
  if Print > 1 then
    Print("+",Size(overgps),"minimal overgroups found for this socle factor.");
  fi;
  for H in overgps do
    if Print > 1 then
      Print("+Overgroup of order",Size(H));
      if Print > 2 then
        Print(H);
      fi;
    fi;
    x:=One(H);
    while x in N do
      x:=Random(H);
    od;
    #   BEWARE - Bill U removed this check
    #  "Check";
    #  if sub<G|N,x> ne H  then
    #  error "Minimal overgroup error.";
    #  end if;
    #  "End check"; 
    H0:=H@pSQ;
    #   H/M
    x0:=x@pSQ;
    H0:=SubStructure(H0,gensN0,#TODO CLOSURE
      x0);
    if Print > 1 then
      Print("+Extra generator:",x0);
    fi;
    #   for each lifting, if any, we will need some transversal data
    THN:=Filtered(T,t->t in H);
    indHN:=Size(THN);
    # =v= MULTIASSIGN =v=
    TGHrep:=RightTransversal(G,H);
    TGH:=TGHrep.val1;
    TGHrep:=TGHrep.val2;
    # =^= MULTIASSIGN =^=
    indGH:=Size(TGH);
    #   Now look for all homomorphism extensions of psi0 for this overgroup.
    for a in A0 do
      liftpsi0:=GroupHomomorphismByImages(H0,A0,
        GeneratorsOfGroup(H0),Concatenation(imgensN0,[a]));
      if IsHomomorphismH@(liftpsi0,Concatenation(imgensN0,[a])) then
        if Print > 1 then
          Print("+Found a lifting. Extra generator -> ",a);
        fi;
        #   Now construct the corresponding diagonal-type subgroup.
        #   Again, we first find the intersection with M and then
        #   compute the normaliser.
        newgenlist:=GR.genlist;
        #   fplist and preslist can stay as they are for diagonals.
        THNlift:=List([1..indHN],i->THN[i]@pSQ@liftpsi0@@pA0);
        for t in T do
          newgenlist[sri^SA(t)]:=[];
        od;
        newgenlist[sri]:=[];
        for z in GR.genlist[sri] do
          w:=One(G);
          for i in [1..Size(THN)] do
            g:=THN[i];
            srit:=sri^SA(g);
            w:=w*(((THNlift[i]*psi(z)*THNlift[i]^-1)@@psi)^g)@projlist[srit];
          od;
          Add(newgenlist[sri],w);
          for t in TGH do
            if not t in H then
              Add(newgenlist[sri^SA(t)],w^t);
            fi;
          od;
        od;
        #   I := sub< G | &cat(newgenlist) >; only needed for sanity check
        #   Now we build generators of the normaliser of I in G
        #   (modulo the subgroup)
        #   We do this, because calling 'Normaliser' can be very slow!
        newgenlist[nSF+1]:=[];
        for elt in GR.modsocgens do
          x:=elt;
          #  multiply x by suitable elements of socle factors until it
          #  normalises I.
          for i in [1..Size(TGH)] do
            u:=TGH[i];
            v:=TGHrep(u*x);
            sriu:=sri^SA(u);
            sriv:=sri^SA(v);
            conngl1:=List(newgenlist[sriu],z->((z^x)@projlist[sriv])^(v^-1));
            for j in [1..Size(THN)] do
              t:=THN[j];
              if not t in N then
                srit:=sri^SA(t);
                sritv:=sri^SA(t*v);
                conngl1c:=List(newgenlist[sriu],z->(z^x)@projlist[sritv]);
                connglt:=List(conngl1,z->((((THNlift[j]*psi(z)*THNlift[j]^-1)
                 @@psi)^(t*v))@projlist[sritv]));
                #  print SF[srit], Universe(connglt), Universe(conngl1c);
                # =v= MULTIASSIGN =v=
                y:=IsConjugateSequencesH@(SF[sritv],conngl1c,connglt);
                con:=y.val1;
                y:=y.val2;
                # =^= MULTIASSIGN =^=
                if not con then
                  Error("Normaliser error in Type2Maximals");
                fi;
                x:=x*y;
              fi;
            od;
          od;
          #   BEWARE - Bill U removed this check
          #  "Check normalizer";
          #  if not I^x eq I then
          #  error "Computed element does not normalise subgroup";
          #  end if;
          #  "Check normalizer ended";
          
          Add(newgenlist[nSF+1],x);
        od;
        reco:=rec();
        if GR.presentation then
          #   print "Type 2 pres";
          # =v= MULTIASSIGN =v=
          reco.presentation:=PresentationSubgroupTF@(newgenlist,GR.preslist,
           GR.projlist,GR.fplist);
          reco.subgroup:=reco.presentation.val1;
          reco.presentation:=reco.presentation.val2;
          # =^= MULTIASSIGN =^=
        else
          reco.subgroup:=SubgroupTF@(newgenlist);
        fi;
        reco.length:=Size(S)^(Size(T)-Size(TGH));
        reco.order:=QuoInt(Size(G),reco.length);
        AssertAttribute(reco.subgroup,"Order",reco.order);
        #   assert not IsNormal(G,reco`subgroup);
        Add(GR.maxsubs,reco);
        if Print > 0 then
          Print("+Maximal subgroup of order",reco.order,"of diagonal type.");
          if Print > 2 then
            Print(reco.subgroup);
          fi;
        fi;
      fi;
    od;
  od;
  return rec();
end);

InstallGlobalFunction(PType3Maximals@,
function(TILDEVAR~GR,srino,srjno)
#  /out: Find the maximal subgroups of Type 3 coming from socle factors
#  * SF[socreps[srino]] and SF[socreps[srjno]]. That is, those that are
#  * diagonals across two equivalent orbits of the socle factors.

local 
   A,G,I,ImP,Imi,Imj,Mi,N,P,Print,QImi,QImigens,QImj,Qi,Qiso,Qisoims,S,SA,SF,T,
   TR,Wi,Wj,c,ce,con,conj,conjel,conngl1,conngl1c,connglt,ei,ej,elt,g,h,nSF,
   newgenlist,pQi,pi,pj,projlist,psi,reco,rhoP,rhoi,rhoj,socreps,sri,srit,sriv,
   srj,srjt,srjv,t,v,x,y,z,zi;
  G:=GR.group;
  socreps:=GR.socreps;
  SF:=GR.SF;
  SA:=GR.SA;
  projlist:=GR.projlist;
  Print:=GR.printlevel;
  nSF:=Size(SF);
  sri:=socreps[srino];
  srj:=socreps[srjno];
  if Print > 0 then
    Print("Finding Type 3 (2-orbit diagonal) maximal subgroups for socle 
     factors",sri,"and",srj);
  fi;
  S:=SF[sri];
  rhoi:=GR.wpembeddings[srino][1];
  Wi:=Codomain(rhoi);
  Imi:=Image(rhoi);
  # =v= MULTIASSIGN =v=
  Mi:=SocleQuotient(Wi);
  Qi:=Mi.val1;
  pQi:=Mi.val2;
  Mi:=Mi.val3;
  # =^= MULTIASSIGN =^=
  QImi:=pQi(Imi);
  psi:=GR.asembeddings[srino];
  A:=Codomain(psi);
  # =v= MULTIASSIGN =v=
  TR:=Transversal(G,Domain(psi));
  T:=TR.val1;
  TR:=TR.val2;
  # =^= MULTIASSIGN =^=
  rhoj:=GR.wpembeddings[srjno][1];
  Wj:=Codomain(rhoj);
  if Wi<>Wj then
    return rec();
    #   socle orbits are inequivalent.
  fi;
  Imj:=Image(rhoj);
  if Size(Imi)<>Size(Imj) then
    return rec();
    #   socle orbits are inequivalent.
  fi;
  QImj:=pQi(Imj);
  if Print > 1 then
    Print("+Orbits of Socle factors ",sri,"and",srj,"could be equivalent.");
  fi;
  #   Construct the diagonal of the two embeddings.
  # =v= MULTIASSIGN =v=
  pj:=DirectProductWithEmbeddingsAndProjectionsH@(Wi,Wj);
  P:=pj.val1;
  ei:=pj.val2;
  ej:=pj.val3;
  pi:=pj.val4;
  pj:=pj.val5;
  # =^= MULTIASSIGN =^=
  rhoP:=GroupHomomorphismByImages(G,P,
    GeneratorsOfGroup(G),List([1..Ngens(G)],k->ei(rhoi(G.k))*ej(rhoj(G.k))));
  ImP:=Image(rhoP);
  if QuoInt(Size(ImP),Size(Socle(ImP)))<>Size(QImi) then
    if Print > 1 then
      Print("+Embedding is not diagonal - orbits are inequivalent.");
    fi;
    return rec();
  fi;
  #   Construct the induced isomorphism from Qi to Qj
  QImigens:=List([1..Ngens(QImi)],k->QImi.k);
  Qisoims:=List(QImigens,q->q@@pQi@@rhoi@rhoP@pj@pQi);
  Qiso:=GroupHomomorphismByImages(QImi,QImj,
    GeneratorsOfGroup(QImi),Qisoims);
  if not IsHomomorphismH@(Qiso,Qisoims) or Image(Qiso)<>QImj then
    Error("Induced isomorphism QImi->QImj incorrect.");
  fi;
  # =v= MULTIASSIGN =v=
  conjel:=IsConjugateSequencesH@(Qi,QImigens,Qisoims);
  conj:=conjel.val1;
  conjel:=conjel.val2;
  # =^= MULTIASSIGN =^=
  if not conj then
    if Print > 1 then
      Print("+Diagonal embedding induce no isomorphism - orbits are 
       inequivalent.");
    fi;
    return rec();
  fi;
  for c in Centraliser(Qi,QImj) do
    ce:=(conjel*c)@@pQi;
    newgenlist:=GR.genlist;
    #   as usual we construct the generators of the intersection of
    #   the maximal with Socle(G) - first find the images of these
    #   generators in P.
    #  h := Representative({t: t in T | rhoi(S)^(ce^-1) eq rhoi(S^t)});
    h:=h;
    #  Now socle factor sri corresponds to srj^SA(h^-1) in the isomorphism
    #  between orbit of sri and orbit of srj.
    for t in T do
      srit:=sri^SA(t);
      srjt:=srj^SA(h^-1*t);
      newgenlist[srit]:=[];
      newgenlist[srjt]:=[];
      for z in GR.genlist[srit] do
        zi:=z@rhoi;
        #  g := (ei(zi) @@ rhoP @ projlist[srit]) *
        #      (ej(zi^ce) @@ rhoP @ projlist[srjt]);
        g:=(z@projlist[srit])*((zi^ce)@@rhoj@projlist[srjt]);
        Add(newgenlist[srit],g);
      od;
    od;
    #   I := sub< G | &cat(newgenlist) >; only needed for sanity check
    #   Now we build generators of the normaliser of I in G
    #   (modulo the subgroup)
    #   We do this, because calling 'Normaliser' can be very slow!
    newgenlist[nSF+1]:=[];
    for elt in GR.modsocgens do
      x:=elt;
      #  multiply x by suitable elements of socle factors until it
      #  normalises I.
      for t in T do
        srit:=sri^SA(t);
        srjt:=srj^SA(h^-1*t);
        v:=TR(t*x);
        sriv:=sri^SA(v);
        srjv:=srj^SA(h^-1*v);
        conngl1:=List(newgenlist[srit],z->(z^x)@projlist[sriv]);
        conngl1c:=List(newgenlist[srit],z->(z^x)@projlist[srjv]);
        #  connglt  := [ ej((z @ rhoi)^ce) @@ rhoP @ projlist[srjv] :
        #                                                 z in conngl1 ];
        connglt:=List(conngl1,z->((z@rhoi)^ce)@@rhoj@projlist[srjv]);
        # =v= MULTIASSIGN =v=
        y:=IsConjugateSequencesH@(SF[srjv],conngl1c,connglt);
        con:=y.val1;
        y:=y.val2;
        # =^= MULTIASSIGN =^=
        if not con then
          Error("Normaliser error in Type3Maximals");
        fi;
        x:=x*y;
      od;
      #   BEWARE - Bill U removed this check
      #  if not I^x eq I then
      #  error "Computed element does not normalise subgroup";
      #  end if;
      
      Add(newgenlist[nSF+1],x);
    od;
    reco:=rec();
    if GR.presentation then
      #   print "Type 3 pres";
      # =v= MULTIASSIGN =v=
      reco.presentation:=PresentationSubgroupTF@(newgenlist,GR.preslist,
       GR.projlist,GR.fplist);
      reco.subgroup:=reco.presentation.val1;
      reco.presentation:=reco.presentation.val2;
      # =^= MULTIASSIGN =^=
    else
      reco.subgroup:=SubgroupTF@(newgenlist);
    fi;
    reco.length:=Size(S)^Size(T);
    reco.order:=QuoInt(Size(G),reco.length);
    AssertAttribute(reco.subgroup,"Order",reco.order);
    #   assert not IsNormal(G,reco`subgroup);
    Add(GR.maxsubs,reco);
    if Print > 0 then
      Print("+Maximal subgroup of order",reco.order,"2-orbit diagonal.");
      if Print > 2 then
        Print(reco.subgroup);
      fi;
    fi;
  od;
  return rec();
end);

InstallGlobalFunction(PType4Maximals@,
function(TILDEVAR~GR,srino)
#  /out: Find the maximal subgroups of Type 4 coming from socle factor
#  * S = SF[socreps[srino]]. That is, those of twisted wreath product type.
#  * They are certain types of complements of the base group in the
#  * wreath product, so the computation will be carried out in the image
#  * of the wreath product embedding.

local 
   A,B,BG,C,CA,CSA,CWA,Cgen,Cgens,Comps,D,DE,DT@,varE,G,Gact,Ggens,H,M,NA,NQ,
   NWA,NWAn,Print,Qgens,S,SA,SB,SBG,SQ,T,W,Wact,a,comp,ct,d,eG,extends,fac_reps,
   factors,fl,g,gensA,gensCWA,gensD,i,im,ims,j,nSF,newgenlist,overgps,pC,pCdom,
   pNQ,pSA,pSA1,pSQ,pT,reco,rho,sri,t,tail,u,x;
  Print:=GR.printlevel;
  if Print > 0 then
    Print("Finding Type 4 (twisted wreath-type) maximal subgroups for socle 
     factor",GR.socreps[srino]);
  fi;
  rho:=GR.wpembeddings[srino][1];
  if GR.presentation then
    #   print "Type 4 pres";
    nSF:=Size(GR).SF;
    newgenlist:=GR.genlist;
    sri:=(GR.socreps)[srino];
    T:=GR.transversals[srino];
    for t in T do
      #  newgenlist[sri^(GR`SA)(t)]:=[];
      newgenlist:=newgenlist;
    od;
  fi;
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
  #   SA := A meet G; Bill U change
  SA:=Intersection(A,SBG);
  #   SB := B meet G; Bill U change
  SB:=Intersection(B,SBG);
  #   NWA := Normaliser(W,A); Bill U change - many extra lines
  #   to avoid the call to Normaliser
  #   Compute Normaliser(W,A) as stabilizer of point in conjugation action
  #   First set up the conj action
  factors:=List([1..Size(eG)],i->Image(eG[i]));
  fac_reps:=[];
  for i in [1..Size(factors)] do
    fl:=x:=ForAny(Generators(factors[i]),x->not IsIdentity(x));
    Assert(1,fl);
    Add(fac_reps,x);
  od;
  S:=SymmetricGroup(Size(factors));
  ims:=[];
  for i in [1..Ngens(W)] do
    im:=[];
    for j in [1..Size(factors)] do
      x:=fac_reps[j]^W.i;
      fl:=k:=ForAny([1..Size(factors)],k->x in factors[k]);
      Assert(1,fl);
      im[j]:=k;
    od;
    Add(ims,im);
  od;
  Wact:=GroupHomomorphismByImages(W,S,
    GeneratorsOfGroup(W),ims);
  #   action of W, by conjugation, on factors
  #   and now get the normaliser
  NWA:=Stabilizer(Image(Wact),1)@@Wact;
  #   end Bill U change
  #   CWA := Centraliser(W,A); Bill U change
  CWA:=Centraliser(NWA,A);
  #   NA := NWA meet G; Bill U change
  #   Another normaliser by stabiliser of point.
  #   NA is Normaliser(G,A)
  Gact:=GroupHomomorphismByImages(G,S,
    GeneratorsOfGroup(G),List([1..Ngens(G)],i->G.i@Wact));
  NA:=Stabilizer(Image(Gact),1)@@Gact;
  #   end Bill U change
  #   CA := CWA meet G; Bill U change
  CA:=Intersection(CWA,NA);
  #   NWA = CWA X A, so we will use this fact to get a perm. rep. of NA/(SB)
  gensA:=List([1..Ngens(A)],i->A.i);
  gensCWA:=List([1..Ngens(CWA)],i->CWA.i);
  NWAn:=SubStructure(W,Concatenation(gensA,gensCWA));
  #   Once we are happy that all is well with NWA, A, and CWA, we should
  #   replace the following if statement by
  #   NWAn`Order := #NWA;
  if NWA<>NWAn then
    Error("Normaliser generation error in Type4Maximals");
  fi;
  NWA:=NWAn;
  pSA1:=GroupHomomorphismByImages(NWA,A,
    GeneratorsOfGroup(NWA),Concatenation(gensA,List([1..Ngens(CWA)],i->One(A))))
   ;
  #  projection of NWA onto A.
  pSA:=GroupHomomorphismByFunction(NA,A,
    a->pSA1(a));
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
    #   This might be maximal.
    #   Next lines Bill U change to get rid of WreathComplementTail call,
    #   which makes far too many RandomSchreier calls.
    pCdom:=SubStructure(G,Concatenation(List([1..Ngens(C)],i->C.i)
     ,List([1..Ngens(SA)],i->SA.i)));
    pCdom.Order:=Size(C)*Size(SA);
    pC:=GroupHomomorphismByImages(pCdom,C,
      GeneratorsOfGroup(pCdom),Concatenation(List([1..Ngens(C)],i->C.i)
     ,List([1..Ngens(SA)],i->One(C))));
    #   end Bill U change
    Cgens:=[];
    for g in Qgens do
      Cgen:=g;
      for t in T do
        u:=pT(t*g);
        #   tail := WreathComplementTail(G,SA,SB,C,t*g*u^-1); Bill U change
        tail:=pSA1(pC(x)^-1*x);
        #  POSTPONED `where'
        x:=t*g*u^-1;
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
    if GR.presentation then
      ct:=0;
      newgenlist[nSF+1]:=[];
      for g in GR.modsocgens do
        if rho(g)=One(G) then
          Add(newgenlist[nSF+1],g);
        else
          ct:=ct+1;
          Add(newgenlist[nSF+1],(varE.ct)@@rho);
        fi;
      od;
      # =v= MULTIASSIGN =v=
      reco.presentation:=PresentationSubgroupTF@(newgenlist,GR.preslist,
       GR.projlist,GR.fplist);
      reco.subgroup:=reco.presentation.val1;
      reco.presentation:=reco.presentation.val2;
      # =^= MULTIASSIGN =^=
    else
      reco.subgroup:=varE@@rho;
    fi;
    reco.order:=Size(reco).subgroup;
    #   assert not IsNormal(GR`group, reco`subgroup);
    reco.length:=Index(GR.group,reco.subgroup);
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

InstallGlobalFunction(PType5Maximals@,
function(TILDEVAR~GR)
#  /out: Find maximal subgroups containing the socle, including the whole
#  group. 
local G,Print,S,SF,SQ,m,ms,nSF,newgenlist,newpreslist,pSQ,reco;
  G:=GR.group;
  SF:=GR.SF;
  pSQ:=GR.pSQ;
  SQ:=Image(pSQ);
  pSQ:=GR.pSQ;
  nSF:=Size(SF);
  newgenlist:=GR.genlist;
  newpreslist:=GR.preslist;
  Print:=GR.printlevel;
  if Print > 0 then
    Print("Finding Type 5 maximal subgroups - those containing the socle.");
  fi;
  if Size(SQ)<>1 then
    S:=MaximalSubgroupsH@(SQ,SubStructure(SQ,#NOP
    ):Presentation:=GR.presentation,Print:=Print);
    for m in S do
      reco:=rec();
      ms:=m.subgroup;
      if GR.presentation then
        #   print "Type 5 pres";
        newpreslist[nSF+1]:=m.presentation;
        newgenlist[nSF+1]:=List(List([1..Ngens(ms)],i->ms.i),g->g@@pSQ);
        # =v= MULTIASSIGN =v=
        reco.presentation:=PresentationSubgroupTF@(newgenlist,newpreslist,
         GR.projlist,GR.fplist);
        reco.subgroup:=reco.presentation.val1;
        reco.presentation:=reco.presentation.val2;
        # =^= MULTIASSIGN =^=
      else
        reco.subgroup:=ms@@pSQ;
      fi;
      reco.order:=QuoInt(Size(G),Index(SQ,m.subgroup));
      AssertAttribute(reco.subgroup,"Order",reco.order);
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
  if not GR.trivrad then
    newgenlist[nSF+1]:=GR.modsocgens;
    reco:=rec();
    # =v= MULTIASSIGN =v=
    reco.presentation:=PresentationSubgroupTF@(newgenlist,GR.preslist,
     GR.projlist,GR.fplist);
    reco.subgroup:=reco.presentation.val1;
    reco.presentation:=reco.presentation.val2;
    # =^= MULTIASSIGN =^=
    reco.order:=Size(G);
    reco.length:=1;
    Add(GR.maxsubs,reco);
    if Print > 0 then
      Print("+Full group of order",reco.order);
      if Print > 2 then
        Print(reco.subgroup);
      fi;
    fi;
  fi;
  return rec();
end);

InstallGlobalFunction(PMaxSubsH@,
function(G,N)
#  /out: Find maximal subgroups of G modulo the soluble normal subgroup N.
#  * Use MaximalSubgroupsTF on the radical quotient where necessary.

local L,M,MM,Presentation,Print,Q,Res,SSF,i,m,mm,pQ,s,ss;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  SSF:=ValueOption("SSF");
  if SSF=fail then
    SSF:=5000;
  fi;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=false;
  fi;
  L:=ElementaryAbelianSeries(G,N);
  if L[1]=G then
    #   group is soluble
    return MaximalSubgroups(G,N:Presentation:=Presentation);
  fi;
  # =v= MULTIASSIGN =v=
  pQ:=RadicalQuotient(G);
  Q:=pQ.val1;
  pQ:=pQ.val2;
  # =^= MULTIASSIGN =^=
  #   Otherwise try MaximalSubgroupsTF.
  M:=MaxSubsTF@(Q,SubStructure(Q,#NOP
  ):Print:=Print,SSF:=SSF,TrivRad:=(Size(Q)=Size(G)),Presentation:=Presentation)
   ;
  if Print > 1 then
    Print(Size(M),"subgroups of radical quotient found");
  fi;
  if Presentation then
    MM:=[];
    for m in M do
      #  print m`order;
      s:=m.subgroup;
      mm:=m;
      mm.subgroup:=SubStructure(G,List([1..Ngens(s)],i->s.i@@pQ));
      Add(MM,mm);
    od;
  else
    MM:=[];
    Res:=[];
    for m in M do
      mm:=m;
      s:=m.subgroup;
      if s=Q then
        mm.subgroup:=SubStructure(G,List([1..Ngens(s)],i->s.i@@pQ));
        Add(MM,mm);
      else
        ss:=s@@pQ;
        ReduceGenerators(ss);
        mm.subgroup:=ss;
        mm.order:=mm.order*Size(Radical(G));
        Add(Res,mm);
      fi;
    od;
  fi;
  for i in [1..Size(L)-1] do
    if Presentation then
      M:=SubgroupsLift(G,L[i],L[i+1],MM:Al:="Maximal",Presentation:=true);
      MM:=M;
    else
      Assert(1,Size(MM)=1);
      M:=SubgroupsLift(G,L[i],L[i+1],MM:Al:="Maximal",Presentation:=false);
      if Print > 1 then
        Print(Size(M),"subgroups after lifting through layer",i);
      fi;
      MM:=[];
      for m in M do
        mm:=m;
        if m.order*Size(L[i+1])=Size(G) then
          Add(MM,mm);
        else
          s:=SubStructure(G,m.subgroup,#TODO CLOSURE
            L[i+1]);
          ReduceGenerators(s);
          mm.subgroup:=s;
          mm.order:=mm.order*Size(L[i+1]);
          if IsBound(mm.presentation) then
            Unbind(mm.presentation);
          fi;
          Add(Res,mm);
        fi;
      od;
    fi;
  od;
  if Presentation then
    return MM;
  else
    return Res;
  fi;
end);


