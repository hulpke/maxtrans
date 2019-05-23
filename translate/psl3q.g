#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, CoprimeMaximals, FPGroupStrong,
#  Factorisation, GL, Gcd, Generators, Image, Index, IsEven, IsOdd, IsPrime,
#  L3qReducts, Ngens, NonCoprimeMaximals, Order, PSL, Random, RandomSchreier,
#  SL, SO, SU, SimpleGroupOrder, Socle, proj

#  Defines: CoprimeMaximals, L3qIdentify, L3qReducts, NonCoprimeMaximals

DeclareGlobalFunction("L3qIdentify@");

#  
#  * This file will contain the functions to construct the maximal
#  * subgroups of any almost simple group $G$ with $PSL(3, p^e) < G <
#  * PGammaL2(3, p^e), with $e>2$.

#  
#  function names in this file:
#  L3qReducts(q, is_novelty)
#  SubfieldSL(p, e, f)
#  NonCoprimeWhichGroup(group, p, e)
#  CoprimeMaximals(group, p, e)
#  NonCoprimeMaximals(group, p, e)
#  L3qMaximals(group, q)

#  ****************************************************************
L3qReducts@:=function(q,is_novelty)
local groups;
  groups:=[];
  if not is_novelty then
    Add(groups,SLPointStab@(3,q));
    Add(groups,SLStabOfNSpace@(3,q,2));
  else
    Add(groups,SLPointMeetHyperplane@(3,q));
    Add(groups,SLPointUnmeetHyperplane@(3,q));
  fi;
  return groups;
end;
;
#  ***************************************************************
CoprimeMaximals@:=function(soc,group,p,e,factor,Print)
local f,grp,indices,maximals,out,reducts,soc,subf,x;
  Assert(1,Gcd(p^e-1,3)=1);
  soc:=Socle(group);
  out:=QuoInt(Size(group),(Size(PSL(3,p^e))));
  if Print > 1 then
    Info(InfoWarning,1,"getting reducibles");
  fi;
  reducts:=L3qReducts@(p^e,IsEvenInt(out));
  maximals:=List(reducts,x->x@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting imprimitives");
  fi;
  Add(maximals,ImprimsMeetSL@(3,p^e,3)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting superfields");
  fi;
  Add(maximals,GammaLMeetSL@(3,p^e,3)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting subfields");
  fi;
  indices:=CollectedFactors(e);
  for x in indices do
    f:=QuoInt(e,x[1]);
    subf:=SubfieldSL@(3,p,e,f);
    Add(maximals,subf@factor);
  od;
  if not IsEvenInt(p) then
    if Print > 1 then
      Info(InfoWarning,1,"getting orthogonal group");
    fi;
    grp:=SO(3,p^e);
    Add(maximals,grp@factor);
  fi;
  if IsEvenInt(e) then
    if Print > 1 then
      Info(InfoWarning,1,"getting unitary group");
    fi;
    Assert(1,p=3);
    f:=QuoInt(e,2);
    Add(maximals,SU(3,p^f)@factor);
  fi;
  #  no alt_6 as either p=3 or e is odd.
  return maximals;
end;
;
#  *************************************************************
NonCoprimeMaximals@:=function(group,psl,homom,p,e,factor,Print)
local 
   apsl,comsub,cop,delta,diag,f,groupquot,image,indices,invol,iota,max_su,
   maximals,newgens,ngq,nmr_copies,novelty,phi,proj,quot,reducts,so,su,subf,x;
  Assert(1,IsPrimeInt(p));
  Assert(1,e > 2);
  Assert(1,Gcd(p^e-1,3)=3);
  #  else are coprime.
  diag:=GL(3,p^e).1@factor;
  #  We now set 3 variables, which determine the types of maximal subgroups:
  #  1. A boolean novelty which is true if G/PSL \not\leq <\delta, \phi> and is
  #     false otherwise. i.e. it's true if there's novelty reducible
  #     subgroups.
  #  2. A number nmr_copies 0, 1, 3 which is:
  #       3 if G/PSL \leq conjugate of <\phi> and p = 1(3).
  #         if G/PSL \leq conjugate of <\phi^2, \phi\iota> and p = 2(3).
  #       1 if G/PSL \leq conjugate of <\phi, \iota> and previous 2 cases are
  #         false.
  #       0 otherwise.
  #  This number is the number of copies of various subgroups that need
  #  to be created.
  #  3. If nmr_copies = 1 then we're going to need the outer
  #  involution invol to feed to SelectGroupGeneral.
  if Print > 1 then
    Print("Identifying group");
  fi;
  apsl:=PGammaL2@(3,p^e);
  # =v= MULTIASSIGN =v=
  proj:=Subquo(apsl,[psl]);
  quot:=proj.val1;
  proj:=proj.val2;
  # =^= MULTIASSIGN =^=
  delta:=proj(apsl.1);
  Assert(1,Order(delta)=3);
  #  diagonal aut.
  phi:=proj(apsl.3);
  Assert(1,Order(phi)=e);
  #  field aut.
  iota:=proj(apsl.4);
  Assert(1,Order(iota)=2);
  #  graph aut
  newgens:=List([1..Ngens(group)],i->group.i@homom);
  groupquot:=SubStructure(quot,List(newgens,g->proj(g)));
  image:=Image(homom);
  novelty:=not IsSubset(SubStructure(quot,delta,#TODO CLOSURE
    phi),groupquot);
  if delta in SubStructure(quot,groupquot,#TODO CLOSURE
    phi^2) then
    nmr_copies:=0;
  else
    comsub:=SubStructure(quot,phi^2,#TODO CLOSURE
      delta);
    ngq:=SubStructure(quot,comsub,#TODO CLOSURE
      groupquot);
    if p mod 3=1 and IsSubset(SubStructure(quot,delta,#TODO CLOSURE
      phi),ngq) then
      nmr_copies:=3;
    elif p mod 3=2 and IsSubset(SubStructure(quot,delta,#TODO CLOSURE
      phi^2,phi*iota),ngq) then
      nmr_copies:=3;
    else
      nmr_copies:=1;
      #   have to choose outer involution carefully
      invol:=Random(image);
      if Index(ngq,comsub)=2 then
        while proj(invol) in comsub do
          invol:=Random(image);
        od;
      else
        while not proj(invol)*iota in comsub do
          invol:=Random(image);
        od;
      fi;
    fi;
  fi;
  #  print novelty, nmr_copies, #apsl;
  if Print > 1 then
    Info(InfoWarning,1,"getting reducibles");
  fi;
  reducts:=L3qReducts@(p^e,novelty);
  maximals:=List(reducts,x->x@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting imprimitives");
  fi;
  Add(maximals,ImprimsMeetSL@(3,p^e,3)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting superfields");
  fi;
  Add(maximals,GammaLMeetSL@(3,p^e,3)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting subfields");
  fi;
  indices:=CollectedFactors(e);
  for x in indices do
    f:=QuoInt(e,x[1]);
    cop:=QuoInt((Gcd(x[1],3)*3),Gcd(p^f-1,3));
    if not (cop=3 and nmr_copies=0) then
      subf:=SubfieldSL@(3,p,e,f)@factor;
      if cop=1 then
        Add(maximals,subf);
      elif nmr_copies=3 then
        subf:=ImageCopies@(subf,3,diag);
        maximals:=Concatenation(maximals,subf);
      else
        #  we have to select one copy out of the three
        Assert(1,nmr_copies=1);
        subf:=SelectGroupGeneral@(psl,subf,diag,invol);
        Add(maximals,subf);
      fi;
    fi;
  od;
  if nmr_copies=1 and IsOddInt(p) then
    if Print > 1 then
      Info(InfoWarning,1,"getting orthogonal group");
    fi;
    so:=SelectGroupGeneral@(psl,SO(3,p^e)@factor,diag,invol);
    Add(maximals,so);
  elif nmr_copies=3 and IsOddInt(p) then
    if Print > 1 then
      Info(InfoWarning,1,"getting orthogonal groups");
    fi;
    so:=ImageCopies@(SO(3,p^e)@factor,3,diag);
    Add(maximals,so@homom);
  fi;
  if IsEvenInt(e) then
    max_su:=Gcd(p^(QuoInt(e,2))-1,3);
    if max_su=1 then
      if Print > 1 then
        Info(InfoWarning,1,"getting unitary group");
      fi;
      Add(maximals,SU(3,p^(QuoInt(e,2)))@factor);
    else
      Assert(1,max_su=3);
      if nmr_copies=1 then
        if Print > 1 then
          Info(InfoWarning,1,"getting unitary group using select group");
        fi;
        su:=SelectGroupGeneral@(psl,SU(3,p^(QuoInt(e,2)))@factor,diag,invol);
        Add(maximals,su);
      elif nmr_copies=3 then
        if Print > 1 then
          Info(InfoWarning,1,"getting unitary groups");
        fi;
        su:=ImageCopies@(SU(3,p^(QuoInt(e,2)))@factor,3,diag);
        maximals:=Concatenation(maximals,su);
      fi;
    fi;
  fi;
  #  no alt_6.
  return maximals;
end;
;
#  ***************************************************************
InstallGlobalFunction(L3qIdentify@,
function(group,q)
local 
   F,Print,apsl,d,e,fac,factor,g,gl,group,homom,max,maximals,newgens,p,phi,psl,
   sl,soc,subapsl;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  fac:=CollectedFactors(q);
  p:=fac[1][1];
  e:=fac[1][2];
  Assert(1,e > 2);
  if Print > 1 then
    Print("Making standard group");
  fi;
  gl:=GL(3,p^e);
  sl:=SL(3,p^e);
  apsl:=PGammaL2@(3,p^e);
  factor:=GroupHomomorphismByImages(gl,apsl,
    apsl.1,apsl.2);
  psl:=sl@factor;
  psl.Order:=SimpleGroupOrder([1,2,q]);
  if Print > 1 then
    Print("Setting up isomorphism");
  fi;
  # =v= MULTIASSIGN =v=
  group:=MakeHomomGeneral@(group,3,p,e,psl,apsl,factor:Print:=0);
  homom:=group.val1;
  soc:=group.val2;
  group:=group.val3;
  # =^= MULTIASSIGN =^=
  if Print > 1 then
    Print("Calling FPGroupStrong");
  fi;
  # =v= MULTIASSIGN =v=
  phi:=FPGroupStrong(SubStructure(psl,List([1..Ngens(soc)],i->soc.i@homom)));
  F:=phi.val1;
  phi:=phi.val2;
  # =^= MULTIASSIGN =^=
  #  get apsl right
  newgens:=List([1..Ngens(group)],i->group.i@homom);
  subapsl:=SubStructure(apsl,newgens);
  RandomSchreier(subapsl);
  for g in Generators(apsl) do
    if not g in subapsl then
      Add(newgens,g);
      subapsl:=SubStructure(apsl,newgens);
      RandomSchreier(subapsl);
    fi;
  od;
  apsl:=subapsl;
  if not max then
    return rec(val1:=homom,
      val2:=apsl,
      val3:=[],
      val4:=F,
      val5:=phi);
  fi;
  d:=Gcd(q-1,3);
  if d=1 then
    if Print > 1 then
      Info(InfoWarning,1,"coprime case");
    fi;
    maximals:=CoprimeMaximals@(soc,group,p,e,factor,Print);
  else
    if Print > 1 then
      Info(InfoWarning,1,"non coprime case");
    fi;
    maximals:=NonCoprimeMaximals@(group,psl,homom,p,e,factor,Print);
  fi;
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);


