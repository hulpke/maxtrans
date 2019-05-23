#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: AandB, Append, CoprimeMaximals, CoprimeWhichGroup,
#  CorrectForm, D_eq_2_Maximals, D_eq_4_Maximals, Deq2WhichGroup,
#  Deq4WhichGroup, Determinant, DiagonalMatrix, Eltseq, FPGroupStrong,
#  Factorisation, GF, GL, GOMinus, GU, Gcd, Generators, Id, IsEven, IsPrime,
#  IsSquare, Lcm, Ngens, NormOfOMinus, NormOfOPlus, NormOfSU, Order,
#  OrthogonalForm, PrimitiveElement, Random, SL, SOMinus, SOPlus, SU,
#  ScalarMatrix, Sp, proj

#  Defines: AandB, CoprimeMaximals, CoprimeWhichGroup, D_eq_2_Maximals,
#  D_eq_4_Maximals, Deq2WhichGroup, Deq4WhichGroup, L4qIdentify, NormOfOMinus,
#  NormOfOPlus, NormOfSU

DeclareGlobalFunction("L4qIdentify@");

#  
#  * This file will contain the functions to construct the maximal
#  * subgroups of any almost simple group $G$ with $PSL(4, p^e) < G <
#  * PGammaL2(4, p^e), with $e>2$.

#   function names in this file:
#  CoprimeWhichGroup(group, p)
#  NonCoprimeWhichGroup(group, p)
#  A7(p)
#  U4_2(p)
#  AandB(p)
#  NormOfOMinus(p)
#  NormOfOPlus(p)
#  CoprimeMaximals(p, factor, homom, type)
#  NonCoprimeMaximals(group, p, factor, homom, type, soc)
#  L4pMaximals(group, p)

#  **************************************************************
#  The following three functions still have to be written..
#   input: almost simple group socle PSL(4, 2^e).
#  output: socle, and boolean which is true iff group has novelty
#  reducible subgroups (i.e. if group \not\leq PSigmaL(4, p^e).

CoprimeWhichGroup@:=function(quot,groupquot,phi)
local is_novelty;
  is_novelty:=not IsSubset(SubStructure(quot,phi),groupquot);
  return is_novelty;
end;
;
#  
#  input: almost simple group with socle PSL(4, p^e) where (p^e-1, 4) = 2.
#  output: socle and two booleans. The first is true iff the group
#  has novelty reducible subgroups (i.e. if group \not\leq PGammaL(4,
#  p^e)). the second is true iff the group has two copies of each
#  possible subgroup i.e. if group/PSL \leq <\phi, \iota>.

Deq2WhichGroup@:=function(quot,groupquot,delta,phi,iota)
local in_stab,is_novelty;
  is_novelty:=not IsSubset(SubStructure(quot,delta,#TODO CLOSURE
    phi),groupquot);
  in_stab:=IsSubset(SubStructure(quot,phi,#TODO CLOSURE
    iota),groupquot);
  return rec(val1:=is_novelty,
    val2:=in_stab);
end;
;
#  
#  input: almost simple group with socle PSL(4, p^e) where (p^e-1, 4) = 4.
#  
#  output: socle, 5 booleans and (maybe) outer involution.
#  The first is true iff the group has novelty reducible
#  subgroups (i.e. if group \not\leq PGammaL(4, p^e).
#  
#  if p = 1 mod 4 then the second is true iff group \leq
#  PSigmaL(4, p) (which i think is normal?)
#  if p = 3 mod 4 then the second is true iff group/PSL \leq a conjugate
#  of <\phi^2, \iota.\phi> (which is probably also normal)
#  in either case the group may have 4 copies of a subfield group
#  and/or 4 copies of a unitary group.
#  
#  the third boolean is true iff group/PSL \leq a conjugate of
#  <\phi, \iota>. This implies has two classes of subfield groups
#  (out of up to 4), and has two classes of unitary groups (out of up to 4).
#  
#  the fourth boolean is true iff group/PSL \leq a conjugate of <\delta^2,
#  \phi,
#  \iota>. This implies that the group has two copies of subfield
#  groups if the maximum possible is two, has two copies of Sp(4, q)
#  and two copies of PSO^+(4, q). The group also has two copies of the
#  unitary subgroup *iff* the maximum possible is two (i.e. if
#  (p^(e/2)-1, 4) = 2).
#  
#  the final, fifth boolean is true iff
#  p = 1 mod 4 and group /PSL \leq a conjgate of
#  <\delta^2, \phi, \iota\delta> OR
#  p = 3 mod 4 and group/PSL \leq a conjgate of
#  <\delta^2, \phi\delta, \iota\delta>.
#  This implies that has two classes of PSO^-(4, q).
#  
#  *if* the third boolean is true, and the second isn't, then we need
#  an outer involution that lies in the relevant conjugate of
#  <\phi, \iota>\setminus<\phi> if p = 1 mod 4 and in
#  the relevant conjugate of  <\phi, \iota>\setminus<\phi^2,
#  \iota\phi> if p = 3 (4).
#  
#  If the second boolean is true, then the third and fourth must be,
#  if the third is true then the fourth must be.
#  

Deq4WhichGroup@:=function(quot,groupquot,delta,phi,iota,p)
local in_kernel,invol,is_novelty,stab_2,stab_4,two_orthminus;
  is_novelty:=not IsSubset(SubStructure(quot,delta,#TODO CLOSURE
    phi),groupquot);
  # rewritten select statement
  if p mod 4=1 then
    in_kernel:=IsSubset(SubStructure(quot,phi),groupquot);
  else
    in_kernel:=IsSubset(SubStructure(quot,phi^2,#TODO CLOSURE
      iota*phi),groupquot);
  fi;
  stab_4:=IsSubset(SubStructure(quot,phi,#TODO CLOSURE
    iota),groupquot) or IsSubset(SubStructure(quot,phi,#TODO CLOSURE
    iota)^delta,groupquot);
  stab_2:=IsSubset(SubStructure(quot,delta^2,#TODO CLOSURE
    phi,iota),groupquot);
  # rewritten select statement
  if p mod 4=1 then
    two_orthminus:=IsSubset(SubStructure(quot,delta^2,#TODO CLOSURE
      phi,iota*delta),groupquot);
  else
    two_orthminus:=IsSubset(SubStructure(quot,delta^2,#TODO CLOSURE
      phi*delta,iota*delta),groupquot);
  fi;
  if stab_4 and not in_kernel then
    invol:=Random(groupquot);
    while (p mod 4=1 and invol in SubStructure(quot,phi,#TODO CLOSURE
      delta^2)) or (p mod 4=3 and invol in SubStructure(quot,phi^2,#TODO 
     CLOSURE
      iota*phi,delta^2)) do
      invol:=Random(groupquot);
    od;
  else
    invol:=One(groupquot);
  fi;
  return rec(val1:=is_novelty,
    val2:=in_kernel,
    val3:=stab_4,
    val4:=stab_2,
    val5:=two_orthminus,
    val6:=invol);
end;
;
#  *******************************************************************
#  
#  * The elements a and b of GF(q) are needed to make the
#  * normaliser in SL of O^-(4, q). They satisfy a^2+b^2 = z.
#  * See Kleidman + Liebeck, p39 for details.

AandB@:=function(q)
local a,b,bool,z;
  z:=PrimitiveElement(GF(q));
  for b in GF(q) do
    # =v= MULTIASSIGN =v=
    a:=IsSquare(z-b #CAST GF(q)
      ^2);
    bool:=a.val1;
    a:=a.val2;
    # =^= MULTIASSIGN =^=
    if bool then
      return rec(val1:=a,
        val2:=b);
    fi;
  od;
  Print("couldn't find a and b in GF(",q,")");
  return rec(val1:=false,
    val2:=_);
end;
;
#  *****************************************************************
#  Makes the normaliser of SOMinus(4, q) in SL(4,q): only designed for
#  p=3 mod 4,
NormOfOMinus@:=function(p)
local a,b,bool,form,g1,group,mat2,norm_mat,type,z;
  g1:=SOMinus(4,p);
  # =v= MULTIASSIGN =v=
  form:=OrthogonalForm(g1);
  bool:=form.val1;
  type:=form.val2;
  form:=form.val3;
  # =^= MULTIASSIGN =^=
  mat2:=CorrectForm(form,4,p,"orth-") #CAST GL(4,p)
    ;
  # =v= MULTIASSIGN =v=
  b:=AandB@(p);
  a:=b.val1;
  b:=b.val2;
  # =^= MULTIASSIGN =^=
  z:=PrimitiveElement(GF(p));
  norm_mat:=[a,b,0,0,b,-a,0,0,0,0,0,1,0,0,z,0] #CAST GL(4,p)
    ;
  if p mod 4=3 then
    norm_mat:=(norm_mat^(QuoInt((p-1),2)))^(mat2^-1);
  else
    norm_mat:=((norm_mat^(QuoInt((p-1),4)))^(mat2^-1))*GOMinus(4,p).4;
  fi;
  Assert(1,not norm_mat in g1);
  Assert(1,DeterminantMat(norm_mat)=1);
  group:=SubStructure(SL(4,p),g1,#TODO CLOSURE
    norm_mat);
  return group;
end;
;
#  *************************************************************
#  Makes the normaliser in SL(4, q) of SOPlus(4, q): only for q =
#  1(4).
NormOfOPlus@:=function(q)
local bool,form,g1,group,mat1,norm1,norm2,type,z;
  g1:=SOPlus(4,q);
  # =v= MULTIASSIGN =v=
  form:=OrthogonalForm(g1);
  bool:=form.val1;
  type:=form.val2;
  form:=form.val3;
  # =^= MULTIASSIGN =^=
  mat1:=CorrectForm(form,4,q,"orth+");
  norm1:=DiagonalMat([-1,1,1,1]) #CAST GL(4,q)
    ;
  norm1:=norm1^(mat1^-1);
  z:=PrimitiveElement(GF(q));
  norm2:=DiagonalMat([1,1,z,z]) #CAST GL(4,q)
    ;
  norm2:=norm2^(QuoInt((q-1),4));
  group:=SubStructure(SL(4,q),g1,#TODO CLOSURE
    norm1*norm2);
  return group;
end;
;
#  *************************************************************
NormOfSU@:=function(p,e)
local elt,i,su,x1;
  i:=DiagonalMat([1,1,-1,-1]) #CAST GL(4,p^e)
    ;
  if p^(QuoInt(e,2)) mod 4=3 then
    su:=SubStructure(SL(4,p^e),SU(4,p^(QuoInt(e,2))),#TODO CLOSURE
      i);
  else
    x1:=GU(4,p^(QuoInt(e,2))).1;
    elt:=PrimitiveElement(GF(p^e))^(QuoInt((p^(QuoInt(e,2))-1),4));
    su:=SubStructure(SL(4,p^e),SU(4,p^(QuoInt(e,2))),#TODO CLOSURE
      x1*ScalarMat(4,elt));
  fi;
  return su;
end;
;
#  ******************************************************************
#  This makes those maximal subgroups which behave differently when
#  d = 1 (i.e. q is even)
CoprimeMaximals@:=function(p,e,factor,is_novelty,Print)
local f,fac,maximals,q,sp,x;
  Assert(1,p=2);
  q:=2^e;
  maximals:=[];
  if Print > 1 then
    Info(InfoWarning,1,"getting reducibles");
  fi;
  if not is_novelty then
    Add(maximals,SLPointStab@(4,q)@factor);
    Add(maximals,SLStabOfNSpace@(4,q,3)@factor);
  else
    Add(maximals,SLStabOfNSpaceMeetDual@(4,q,1)@factor);
    Add(maximals,SLStabOfNSpaceMissDual@(4,q,1)@factor);
  fi;
  Add(maximals,SLStabOfHalfDim@(4,q)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting imprimitives");
  fi;
  if q > 4 then
    Add(maximals,ImprimsMeetSL@(4,q,4)@factor);
  fi;
  Add(maximals,ImprimsMeetSL@(4,q,2)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting semilinears");
  fi;
  Add(maximals,GammaLMeetSL@(4,q,2)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting subfields");
  fi;
  fac:=CollectedFactors(e);
  for x in fac do
    f:=QuoInt(e,x[1]);
    Add(maximals,SubStructure(SL(4,q),Eltseq(SL(4,2^f).1),#TODO CLOSURE
      Eltseq(SL(4,2^f).2))@factor);
  od;
  if Print > 1 then
    Info(InfoWarning,1,"getting classicals");
  fi;
  sp:=SubStructure(SL(4,q),SP(4,q));
  Add(maximals,sp@factor);
  if IsEvenInt(e) then
    Add(maximals,SU(4,2^(QuoInt(e,2)))@factor);
  fi;
  return maximals;
end;
;
#  ******************************************************************
#  Those maximal subgroups which behave differently when p=1 mod 4.
D_eq_2_Maximals@:=function(p,e,factor,is_novelty,in_stab,Print)
local c,diag,f,fac,groups,i,maximals,ominus,oplus,q,sp,su,subf,x;
  Assert(1,p^e mod 4=3);
  q:=p^e;
  #  is_novelty, in_stab;
  diag:=GL(4,q).1@factor;
  maximals:=[];
  if Print > 1 then
    Info(InfoWarning,1,"getting reducibles");
  fi;
  if not is_novelty then
    Add(maximals,SLPointStab@(4,q)@factor);
    Add(maximals,SLStabOfNSpace@(4,q,3)@factor);
  else
    Add(maximals,SLStabOfNSpaceMeetDual@(4,q,1)@factor);
    Add(maximals,SLStabOfNSpaceMissDual@(4,q,1)@factor);
  fi;
  Add(maximals,SLStabOfHalfDim@(4,q)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting imprimitives");
  fi;
  Add(maximals,ImprimsMeetSL@(4,q,4)@factor);
  Add(maximals,ImprimsMeetSL@(4,q,2)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting semilinear");
  fi;
  Add(maximals,GammaLMeetSL@(4,q,2)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting subfield groups");
  fi;
  fac:=CollectedFactors(e);
  for x in fac do
    f:=QuoInt(e,x[1]);
    c:=QuoInt((q-1),Lcm(p^f-1,QuoInt((q-1),2)));
    #  d eq 2;
    cAssert(1,(c=1 or c=2));
    if c=1 then
      Add(maximals,SubfieldSL@(4,p,e,f)@factor);
    elif in_stab then
      subf:=SubfieldSL@(p,e,f)@factor;
      groups:=ImageCopies@(subf,2,diag);
      maximals:=Concatenation(maximals,groups);
    fi;
  od;
  i:=DiagonalMat([1,1,-1,-1]) #CAST SL(4,q)
    ;
  if in_stab then
    if Print > 1 then
      Info(InfoWarning,1,"getting symplectic group");
    fi;
    sp:=SubStructure(SL(4,q),SP(4,q),#TODO CLOSURE
      i)@factor;
    groups:=ImageCopies@(sp,2,diag);
    maximals:=Concatenation(maximals,groups);
  fi;
  if Print > 1 then
    Info(InfoWarning,1,"getting orthogonal groups");
  fi;
  oplus:=SubStructure(SL(4,q),SOPlus(4,q),#TODO CLOSURE
    i);
  Add(maximals,oplus@factor);
  ominus:=NormOfOMinus@(q);
  Add(maximals,ominus@factor);
  if IsEvenInt(e) and in_stab then
    if Print > 1 then
      Info(InfoWarning,1,"getting unitary groups");
    fi;
    su:=NormOfSU@(p,e)@factor;
    groups:=ImageCopies@(su,2,diag);
    maximals:=Concatenation(maximals,groups);
  fi;
  return maximals;
end;
;
#  ****************************************************************
D_eq_4_Maximals@:=function(p,e,factor,psl,is_novelty,in_kernel,stab_4,stab_2,
 two_orthminus,invol,Print)
local c,diag,f,fac,groups,grp_ominus,i,maximals,oplus,q,sp,su,subf,x;
  Assert(1,IsPrimeInt(p));
  Assert(1,Gcd(p^e-1,4)=4);
  q:=p^e;
  diag:=GL(4,q).1@factor;
  maximals:=[];
  if Print > 1 then
    Info(InfoWarning,1,"getting reducibles");
  fi;
  if not is_novelty then
    Add(maximals,SLPointStab@(4,q)@factor);
    Add(maximals,SLStabOfNSpace@(4,q,3)@factor);
  else
    Add(maximals,SLStabOfNSpaceMeetDual@(4,q,1)@factor);
    Add(maximals,SLStabOfNSpaceMissDual@(4,q,1)@factor);
  fi;
  Add(maximals,SLStabOfHalfDim@(4,q)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting imprimitive groups");
  fi;
  Add(maximals,ImprimsMeetSL@(4,q,4)@factor);
  Add(maximals,ImprimsMeetSL@(4,q,2)@factor);
  if Print > 1 then
    Info(InfoWarning,1,"getting superfield group");
  fi;
  Add(maximals,GammaLMeetSL@(4,q,2)@factor);
  fac:=CollectedFactors(e);
  for x in fac do
    f:=QuoInt(e,x[1]);
    c:=QuoInt((q-1),Lcm(p^f-1,QuoInt((q-1),4)));
    #  d eq 4;
    Assert(1,(c=1 or c=2 or c=4));
    subf:=SubfieldSL@(4,p,e,f)@factor;
    if c=1 then
      if Print > 1 then
        Info(InfoWarning,1,"getting subfield group");
      fi;
      Add(maximals,subf@factor);
    elif c=2 and stab_2 then
      if Print > 1 then
        Info(InfoWarning,1,"getting subfield groups");
      fi;
      groups:=ImageCopies@(subf,2,diag);
      maximals:=Concatenation(maximals,groups);
    elif c=4 and in_kernel then
      if Print > 1 then
        Info(InfoWarning,1,"getting subfield groups");
      fi;
      groups:=ImageCopies@(subf,4,diag);
      maximals:=Concatenation(maximals,groups);
    elif c=4 and stab_4 then
      if Print > 1 then
        Info(InfoWarning,1,"getting subfield groups");
      fi;
      subf:=SelectGroupGeneral@(psl,subf,diag,invol);
      Add(maximals,subf);
      Add(maximals,subf^(diag^2));
    fi;
  od;
  if stab_2 then
    if Print > 1 then
      Info(InfoWarning,1,"getting symplectic groups");
    fi;
    i:=DiagonalMat([1,1,-1,-1]) #CAST SL(4,q)
      ;
    sp:=SubStructure(SL(4,q),SP(4,q),#TODO CLOSURE
      i)@factor;
    groups:=ImageCopies@(sp,2,diag);
    maximals:=Concatenation(maximals,groups);
    if Print > 1 then
      Info(InfoWarning,1,"getting orthogonal plus groups");
    fi;
    oplus:=NormOfOPlus@(q)@factor;
    groups:=ImageCopies@(oplus,2,diag);
    maximals:=Concatenation(maximals,groups);
  fi;
  if two_orthminus then
    if Print > 1 then
      Info(InfoWarning,1,"getting orthogonal minus groups");
    fi;
    grp_ominus:=NormOfOMinus@(q)@factor;
    groups:=ImageCopies@(grp_ominus,2,diag);
    maximals:=Concatenation(maximals,groups);
  fi;
  if IsEvenInt(e) then
    su:=NormOfSU@(p,e)@factor;
    c:=Gcd(p^(QuoInt(e,2))-1,4);
    Assert(1,(c=2 or c=4));
    if c=2 and stab_2 then
      if Print > 1 then
        Info(InfoWarning,1,"getting unitary groups");
      fi;
      groups:=ImageCopies@(su,2,diag);
      maximals:=Concatenation(maximals,groups);
    elif c=4 and in_kernel then
      if Print > 1 then
        Info(InfoWarning,1,"getting unitary groups");
      fi;
      groups:=ImageCopies@(su,4,diag);
      maximals:=Concatenation(maximals,groups);
    elif c=4 and stab_4 then
      if Print > 1 then
        Info(InfoWarning,1,"getting unitary groups");
      fi;
      su:=SelectGroupGeneral@(psl,su,diag,invol);
      Add(maximals,su);
      Add(maximals,su^(diag^2));
    fi;
  fi;
  return maximals;
end;
;
#  ***************************************************************
InstallGlobalFunction(L4qIdentify@,
function(group,q)
local 
   F,Print,apsl,d,delta,e,fac,factor,g,gl,group,groupquot,homom,in_kernel,
   in_stab,invol,iota,is_novelty,max,maximals,newgens,p,phi,phia,proj,psl,quot,
   sl,soc,stab_2,stab_4,subapsl,two_orthminus;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  fac:=CollectedFactors(q);
  Assert(1,Size(fac)=1);
  p:=fac[1][1];
  e:=fac[1][2];
  Assert(1,e > 1);
  if Print > 1 then
    Print("Making standard group");
  fi;
  gl:=GL(4,p^e);
  sl:=SL(4,p^e);
  apsl:=PGammaL2@(4,p^e);
  factor:=GroupHomomorphismByImages(gl,apsl,
    apsl.1,apsl.2);
  psl:=sl@factor;
  if Print > 1 then
    Print("Setting up isomorphism");
  fi;
  # =v= MULTIASSIGN =v=
  group:=MakeHomomGeneral@(group,4,p,e,psl,apsl,factor:Print:=0);
  homom:=group.val1;
  soc:=group.val2;
  group:=group.val3;
  # =^= MULTIASSIGN =^=
  #   Set up the subgroup of the outer automorphism group induced by group
  if max then
    d:=Gcd(q-1,4);
    # =v= MULTIASSIGN =v=
    proj:=Subquo(apsl,[psl]);
    quot:=proj.val1;
    proj:=proj.val2;
    # =^= MULTIASSIGN =^=
    delta:=proj(apsl.1);
    Assert(1,Order(delta)=d);
    #  diagonal aut.
    phia:=proj(apsl.3);
    Assert(1,Order(phia)=e);
    #  field aut.
    #  had used phi twice!
    iota:=proj(apsl.4);
    Assert(1,Order(iota)=2);
    #  graph aut
    newgens:=List([1..Ngens(group)],i->group.i@homom);
    groupquot:=SubStructure(quot,List(newgens,g->proj(g)));
  fi;
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
  for g in Generators(apsl) do
    if not g in subapsl then
      Add(newgens,g);
      subapsl:=SubStructure(apsl,newgens);
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
  if d=1 then
    Assert(1,p=2);
    is_novelty:=CoprimeWhichGroup@(quot,groupquot,phia);
    maximals:=CoprimeMaximals@(p,e,factor,is_novelty,Print);
  elif d=2 then
    # =v= MULTIASSIGN =v=
    in_stab:=Deq2WhichGroup@(quot,groupquot,delta,phia,iota);
    is_novelty:=in_stab.val1;
    in_stab:=in_stab.val2;
    # =^= MULTIASSIGN =^=
    maximals:=D_eq_2_Maximals@(p,e,factor,is_novelty,in_stab,Print);
  elif d=4 then
    # =v= MULTIASSIGN =v=
    invol:=Deq4WhichGroup@(quot,groupquot,delta,phia,iota,p);
    is_novelty:=invol.val1;
    in_kernel:=invol.val2;
    stab_4:=invol.val3;
    stab_2:=invol.val4;
    two_orthminus:=invol.val5;
    invol:=invol.val6;
    # =^= MULTIASSIGN =^=
    invol:=invol@@proj;
    maximals:=D_eq_4_Maximals@(p,e,factor,psl,is_novelty,in_kernel,stab_4,
     stab_2,two_orthminus,invol,Print);
  fi;
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);


