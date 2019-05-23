#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, Domain, FPGroupStrong, GF, GL, Generators,
#  Identification, L3_4, M24, Ngens, Random, SL, Socle, Sp, Sym, TP,
#  TensorWreathProduct, Transpose

#  Defines: Identification, L10_2Identify, L11_2Identify, L12_2Identify,
#  L13_2Identify, L14_2Identify, L3_4, L7_2Identify, L8_2Identify,
#  L9_2Identify, M24, TP

DeclareGlobalFunction("L10_2Identify@");

DeclareGlobalFunction("L11_2Identify@");

DeclareGlobalFunction("L12_2Identify@");

DeclareGlobalFunction("L13_2Identify@");

DeclareGlobalFunction("L14_2Identify@");

DeclareGlobalFunction("L7_2Identify@");

DeclareGlobalFunction("L8_2Identify@");

DeclareGlobalFunction("L9_2Identify@");

#  ********************************************************************
Identification@:=function(d,group,Print)
#  /out: The initial part of the code common to all Ld_2Identify
local 
   F,apsl,dh,factor,g,gl,group,homom,invol,newgens,phi,psl,sl,soc,temp,type,x;
  if Print > 1 then
    Print("Making standard group");
  fi;
  gl:=GL(d,2);
  sl:=SL(d,2);
  apsl:=PGammaL2@(d,2);
  factor:=GroupHomomorphismByImages(gl,apsl,
    apsl.1,apsl.2);
  psl:=sl@factor;
  if Print > 1 then
    Print("Setting up isomorphism");
  fi;
  soc:=Socle(group);
  #   Reduce number of generators of soc, and
  #  * rearrange generators of group to get those of soc coming first
  
  newgens:=[Random(soc),Random(soc)];
  while SubStructure(soc,newgens)<>soc do
    x:=Random(soc);
    while x in SubStructure(soc,newgens) do
      x:=Random(soc);
    od;
    Add(newgens,x);
  od;
  soc:=SubStructure(soc,newgens);
  for g in Generators(group) do
    if not g in SubStructure(group,newgens) then
      Add(newgens,g);
    fi;
  od;
  group:=SubStructure(group,newgens);
  homom:=MakeHomomGeneral@(group,d,2,1,psl,apsl,factor:Print:=0);
  dh:=Domain(homom);
  if Print > 1 then
    Print("Calling FPGroupStrong");
  fi;
  temp:=List(Filtered([1..Ngens(dh)],i->dh.i in Socle(dh)),i->dh.i);
  # =v= MULTIASSIGN =v=
  phi:=FPGroupStrong(SubStructure(psl,temp@homom));
  F:=phi.val1;
  phi:=phi.val2;
  # =^= MULTIASSIGN =^=
  if Print > 1 then
    Print("Identifying group");
  fi;
  #   Also get the generators of apsl correct
  newgens:=List([1..Ngens(dh)],i->dh.i@homom);
  # rewritten select statement
  if Size(group)=Size(apsl) then
    type:="psl.2";
  else
    type:="psl";
  fi;
  if type="psl" then
    Add(newgens,apsl.3);
  fi;
  invol:=apsl.3;
  #  outer involution
  if Print > 1 then
    Print("Type = ",type);
  fi;
  apsl:=SubStructure(apsl,newgens);
  return rec(val1:=apsl,
    val2:=homom,
    val3:=F,
    val4:=phi,
    val5:=factor,
    val6:=type,
    val7:=invol);
end;
;
#  *******************************************************************
#  functions for L7(2)
InstallGlobalFunction(L7_2Identify@,
function(group)
local F,Print,apsl,factor,g,homom,i,max,maximals,phi,type;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  # =v= MULTIASSIGN =v=
  type:=Identification@(7,group,Print);
  apsl:=type.val1;
  homom:=type.val2;
  F:=type.val3;
  phi:=type.val4;
  factor:=type.val5;
  type:=type.val6;
  # =^= MULTIASSIGN =^=
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=apsl,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  if Print > 1 then
    Print("Getting reducibles");
  fi;
  if type="psl" then
    Add(maximals,SLPointStab@(7,2)@factor);
    for i in [2..6] do
      g:=SLStabOfNSpace@(7,2,i);
      Add(maximals,g@factor);
    od;
  else
    Add(maximals,SLPointMeetHyperplane@(7,2)@factor);
    Add(maximals,SLPointUnmeetHyperplane@(7,2)@factor);
    for i in [2,3] do
      Add(maximals,SLStabOfNSpaceMissDual@(7,2,i)@factor);
      Add(maximals,SLStabOfNSpaceMeetDual@(7,2,i)@factor);
    od;
  fi;
  if Print > 1 then
    Print("Getting semilinear");
  fi;
  Add(maximals,GammaLMeetSL@(7,2,7)@factor);
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);

#  *******************************************************************
#  functions for L8(2)
InstallGlobalFunction(L8_2Identify@,
function(group)
local F,Print,apsl,factor,g,homom,i,max,maximals,phi,type;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  # =v= MULTIASSIGN =v=
  type:=Identification@(8,group,Print);
  apsl:=type.val1;
  homom:=type.val2;
  F:=type.val3;
  phi:=type.val4;
  factor:=type.val5;
  type:=type.val6;
  # =^= MULTIASSIGN =^=
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=apsl,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  if Print > 1 then
    Print("Getting reducibles");
  fi;
  if type="psl" then
    Add(maximals,SLPointStab@(8,2)@factor);
    for i in [2,3] do
      g:=SLStabOfNSpace@(8,2,i);
      Add(maximals,g@factor);
    od;
    Add(maximals,SLStabOfHalfDim@(8,2)@factor);
    for i in [5..7] do
      g:=SLStabOfNSpace@(8,2,i);
      Add(maximals,g@factor);
    od;
  else
    Add(maximals,SLPointMeetHyperplane@(8,2)@factor);
    Add(maximals,SLPointUnmeetHyperplane@(8,2)@factor);
    for i in [2,3] do
      Add(maximals,SLStabOfNSpaceMissDual@(8,2,i)@factor);
      Add(maximals,SLStabOfNSpaceMeetDual@(8,2,i)@factor);
    od;
    Add(maximals,SLStabOfHalfDim@(8,2)@factor);
  fi;
  if Print > 1 then
    Print("Getting imprimitive");
  fi;
  Add(maximals,ImprimsMeetSL@(8,2,2)@factor);
  if Print > 1 then
    Print("Getting semilinear");
  fi;
  Add(maximals,GammaLMeetSL@(8,2,2)@factor);
  if Print > 1 then
    Print("Getting classicals");
  fi;
  Add(maximals,SP(8,2)@factor);
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);

#  *********************************************************
#  code for PSL(9, 2)
L3_4@:=function()
local grp;
  grp:=SubMatrixGroup(9,GF(2),[[[0,1,0,1,0,0,0,1,1],[0,0,0,1,1,0,1,1,0]
   ,[1,0,0,0,1,0,1,0,0],[0,0,0,1,1,0,0,0,0],[0,0,0,1,0,1,0,0,1]
   ,[1,1,1,1,0,1,1,1,0],[0,0,1,1,0,1,1,0,0],[0,0,0,0,0,0,1,0,0]
   ,[1,0,0,1,0,1,0,0,1]]
,[[0,0,1,0,0,0,0,0,0],[0,0,0,0,0,1,0,0,0],[0,0,0,0,1,0,0,0,0]
   ,[0,1,1,0,0,0,0,0,0],[0,0,1,1,1,0,1,0,0],[0,0,0,1,1,0,0,1,1]
   ,[0,0,0,0,1,0,1,1,0],[0,1,0,0,1,1,1,0,1],[1,0,0,0,0,1,1,0,1]]
]);
  #   order = 120960 = 2^7 * 3^3 * 5 * 7 
  return grp;
end;
;
InstallGlobalFunction(L9_2Identify@,
function(group)
local F,Print,apsl,factor,g,homom,i,max,maximals,phi,type;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  # =v= MULTIASSIGN =v=
  type:=Identification@(9,group,Print);
  apsl:=type.val1;
  homom:=type.val2;
  F:=type.val3;
  phi:=type.val4;
  factor:=type.val5;
  type:=type.val6;
  # =^= MULTIASSIGN =^=
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=apsl,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  if Print > 1 then
    Print("Getting reducibles");
  fi;
  if type="psl" then
    Add(maximals,SLPointStab@(9,2)@factor);
    for i in [2..8] do
      g:=SLStabOfNSpace@(9,2,i);
      Add(maximals,g@factor);
    od;
  else
    Add(maximals,SLPointMeetHyperplane@(9,2)@factor);
    Add(maximals,SLPointUnmeetHyperplane@(9,2)@factor);
    for i in [2,3,4] do
      Add(maximals,SLStabOfNSpaceMissDual@(9,2,i)@factor);
      Add(maximals,SLStabOfNSpaceMeetDual@(9,2,i)@factor);
    od;
  fi;
  if Print > 1 then
    Print("Getting imprimitive");
  fi;
  Add(maximals,ImprimsMeetSL@(9,2,3)@factor);
  if Print > 1 then
    Print("Getting semilinear");
  fi;
  Add(maximals,GammaLMeetSL@(9,2,3)@factor);
  if Print > 1 then
    Print("Getting tensor induced groups");
  fi;
  Add(maximals,TensorWreathProduct(SL(3,2),SymmetricGroup(2))@factor);
  if Print > 1 then
    Print("Getting C_9s");
  fi;
  Add(maximals,L3_4@()@factor);
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);

#  ********************************************************************
#  functions for L10(2)
InstallGlobalFunction(L10_2Identify@,
function(group)
local F,L52,M22_2,Print,apsl,factor,g,homom,i,invol,max,maximals,phi,type;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  L52:=SubMatrixGroup(10,GF(2),[[[1,0,0,0,0,0,0,0,0,0],[1,1,0,0,0,0,0,0,0,0]
   ,[0,0,1,0,0,0,0,0,0,0],[0,0,0,1,0,0,0,0,0,0],[0,0,0,0,1,0,0,1,0,0]
   ,[0,0,0,1,0,1,0,0,0,0],[0,0,0,0,0,0,1,0,0,0],[0,0,0,0,0,0,0,1,0,0]
   ,[0,0,0,0,0,0,0,0,1,0],[0,0,0,0,0,0,0,0,0,1]]
,[[0,0,0,0,1,0,0,0,0,0],[0,0,1,0,0,0,0,0,0,0],[1,0,0,0,0,0,0,0,0,0]
   ,[0,1,0,0,0,0,0,0,0,0],[0,0,0,1,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,1]
   ,[0,0,0,0,0,1,0,0,0,0],[0,0,0,0,0,0,1,0,0,0],[0,0,0,0,0,0,0,1,0,0]
   ,[0,0,0,0,0,0,0,0,1,0]]
]);
  #   order = 9999360 = 2^10 * 3^2 * 5 * 7 * 31 
  #  I think that Colva has forgotten about M22.2 !
  M22_2:=SubMatrixGroup(10,GF(2),[[[1,0,0,0,0,0,0,0,0,0],[0,0,1,0,0,0,0,0,0,0]
   ,[0,1,0,0,0,0,0,0,0,0],[0,0,1,1,1,0,0,0,0,0],[0,1,1,0,1,0,0,0,0,0]
   ,[1,0,0,1,0,1,1,0,0,0],[0,0,1,0,1,0,1,0,0,0],[0,0,1,0,1,0,0,1,0,0]
   ,[1,1,0,1,1,0,1,0,1,0],[0,1,0,0,1,0,0,0,0,1]]
,[[0,1,0,0,0,0,0,0,0,0],[1,0,0,1,0,0,0,0,0,0],[0,0,0,1,0,0,0,0,0,0]
   ,[0,0,1,0,0,0,0,0,0,0],[1,0,1,0,0,1,0,0,0,0],[0,0,0,1,0,1,1,1,0,0]
   ,[1,1,1,1,0,1,0,1,1,0],[1,0,0,1,1,0,0,1,1,0],[1,1,0,0,0,0,1,1,0,1]
   ,[1,1,0,1,0,0,1,1,1,0]]
]);
  #   order = 887040 = 2^8 * 3^2 * 5 * 7 * 11 
  # =v= MULTIASSIGN =v=
  invol:=Identification@(10,group,Print);
  apsl:=invol.val1;
  homom:=invol.val2;
  F:=invol.val3;
  phi:=invol.val4;
  factor:=invol.val5;
  type:=invol.val6;
  invol:=invol.val7;
  # =^= MULTIASSIGN =^=
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=apsl,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  if Print > 1 then
    Print("Getting reducibles");
  fi;
  if type="psl" then
    Add(maximals,SLPointStab@(10,2)@factor);
    for i in [2..4] do
      g:=SLStabOfNSpace@(10,2,i);
      Add(maximals,g@factor);
    od;
    Add(maximals,SLStabOfHalfDim@(10,2)@factor);
    for i in [6..9] do
      g:=SLStabOfNSpace@(10,2,i);
      Add(maximals,g@factor);
    od;
  else
    Add(maximals,SLPointMeetHyperplane@(10,2)@factor);
    Add(maximals,SLPointUnmeetHyperplane@(10,2)@factor);
    for i in [2..4] do
      Add(maximals,SLStabOfNSpaceMissDual@(10,2,i)@factor);
      Add(maximals,SLStabOfNSpaceMeetDual@(10,2,i)@factor);
    od;
    Add(maximals,SLStabOfHalfDim@(10,2)@factor);
  fi;
  if Print > 1 then
    Print("Getting imprimitive");
  fi;
  Add(maximals,ImprimsMeetSL@(10,2,2)@factor);
  if Print > 1 then
    Print("Getting semilinears");
  fi;
  Add(maximals,GammaLMeetSL@(10,2,2)@factor);
  Add(maximals,GammaLMeetSL@(10,2,5)@factor);
  if Print > 1 then
    Print("Getting classical");
  fi;
  Add(maximals,SP(10,2)@factor);
  if Print > 1 then
    Print("Getting L5_2");
  fi;
  Add(maximals,L52@factor);
  if type="psl" then
    if Print > 1 then
      Print("Getting M22.2s");
    fi;
    Add(maximals,M22_2@factor);
    Add(maximals,(M22_2@factor)^invol);
  fi;
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);

#  **************************************************************
#  functions for L11(2)
M24@:=function()
local grp,grp2;
  grp:=SubMatrixGroup(11,GF(2),[[[0,1,0,0,0,0,0,0,0,0,0],[1,0,0,0,0,0,0,0,0,0,0]
   ,[0,0,0,1,0,0,0,0,0,0,0],[0,0,1,0,0,0,0,0,0,0,0],[0,0,0,0,0,1,0,0,0,0,0]
   ,[0,0,0,0,1,0,0,0,0,0,0],[0,0,0,0,0,0,0,1,0,0,0],[0,0,0,0,0,0,1,0,0,0,0]
   ,[0,0,0,0,0,0,0,0,0,1,0],[0,0,0,0,0,0,0,0,1,0,0],[0,0,1,1,0,0,0,0,1,1,1]]
,[[0,0,1,0,0,0,0,0,0,0,0],[0,1,1,0,0,0,0,0,0,0,0],[1,0,1,0,0,0,0,0,0,0,0]
   ,[0,0,0,0,1,0,0,0,0,0,0],[0,0,0,0,0,0,1,0,0,0,0],[1,0,1,1,1,1,0,0,0,0,0]
   ,[0,0,0,1,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,1,0,0],[0,0,0,0,0,0,0,0,0,0,1]
   ,[1,0,0,0,0,0,0,0,0,1,0],[0,0,0,0,0,0,0,1,0,0,0]]
]);
  #   order = 244823040 = 2^10 * 3^3 * 5 * 7 * 11 * 23 
  grp.Order:=244823040;
  grp2:=SubMatrixGroup(11,GF(2),[TransposedMat(grp.-1),TransposedMat(grp.-2)]);
  grp2.Order:=244823040;
  return rec(val1:=grp,
    val2:=grp2);
end;
;
InstallGlobalFunction(L11_2Identify@,
function(group)
local F,Print,apsl,factor,g,g1,g2,homom,i,max,maximals,phi,type;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  # =v= MULTIASSIGN =v=
  type:=Identification@(11,group,Print);
  apsl:=type.val1;
  homom:=type.val2;
  F:=type.val3;
  phi:=type.val4;
  factor:=type.val5;
  type:=type.val6;
  # =^= MULTIASSIGN =^=
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=apsl,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  if Print > 1 then
    Print("Getting reducibles");
  fi;
  if type="psl" then
    Add(maximals,SLPointStab@(11,2)@factor);
    for i in [2..10] do
      g:=SLStabOfNSpace@(11,2,i);
      Add(maximals,g@factor);
    od;
  else
    Add(maximals,SLPointMeetHyperplane@(11,2)@factor);
    Add(maximals,SLPointUnmeetHyperplane@(11,2)@factor);
    for i in [2..5] do
      Add(maximals,SLStabOfNSpaceMissDual@(11,2,i)@factor);
      Add(maximals,SLStabOfNSpaceMeetDual@(11,2,i)@factor);
    od;
  fi;
  if Print > 1 then
    Print("Getting semilinear");
  fi;
  Add(maximals,GammaLMeetSL@(11,2,11)@factor);
  if type="psl" then
    if Print > 1 then
      Print("Getting C_9s");
    fi;
    # =v= MULTIASSIGN =v=
    g2:=M24@();
    g1:=g2.val1;
    g2:=g2.val2;
    # =^= MULTIASSIGN =^=
    Add(maximals,g1@factor);
    Add(maximals,g2@factor);
  fi;
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);

#  ********************************************************************
#  functions for L12(2)
TP@:=function()
local grp;
  grp:=SubMatrixGroup(12,GF(2),[[[1,1,1,1,0,0,0,0,1,1,1,1]
   ,[1,1,0,0,0,0,0,0,1,1,0,0],[1,0,0,1,0,0,0,0,1,0,0,1]
   ,[0,0,0,1,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,1,1,1,1]
   ,[0,0,0,0,0,0,0,0,1,1,0,0],[0,0,0,0,0,0,0,0,1,0,0,1]
   ,[0,0,0,0,0,0,0,0,0,0,0,1],[0,0,0,0,1,1,1,1,0,0,0,0]
   ,[0,0,0,0,1,1,0,0,0,0,0,0],[0,0,0,0,1,0,0,1,0,0,0,0]
   ,[0,0,0,0,0,0,0,1,0,0,0,0]]
,[[1,0,1,1,0,0,0,0,1,0,1,1],[0,1,1,0,0,0,0,0,0,1,1,0],[1,0,0,0,0,0,0,0,1,0,0,0]
   ,[1,1,0,0,0,0,0,0,1,1,0,0],[1,0,1,1,1,0,1,1,0,0,0,0]
   ,[0,1,1,0,0,1,1,0,0,0,0,0],[1,0,0,0,1,0,0,0,0,0,0,0]
   ,[1,1,0,0,1,1,0,0,0,0,0,0],[1,0,1,1,1,0,1,1,1,0,1,1]
   ,[0,1,1,0,0,1,1,0,0,1,1,0],[1,0,0,0,1,0,0,0,1,0,0,0]
   ,[1,1,0,0,1,1,0,0,1,1,0,0]]
]);
  #   order = 3386880 = 2^9 * 3^3 * 5 * 7^2 
  return grp;
end;
;
InstallGlobalFunction(L12_2Identify@,
function(group)
local F,Print,apsl,factor,g,homom,i,max,maximals,phi,type;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  # =v= MULTIASSIGN =v=
  type:=Identification@(12,group,Print);
  apsl:=type.val1;
  homom:=type.val2;
  F:=type.val3;
  phi:=type.val4;
  factor:=type.val5;
  type:=type.val6;
  # =^= MULTIASSIGN =^=
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=apsl,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  if Print > 1 then
    Print("Getting reducibles");
  fi;
  if type="psl" then
    Add(maximals,SLPointStab@(12,2)@factor);
    for i in [2..5] do
      g:=SLStabOfNSpace@(12,2,i);
      Add(maximals,g@factor);
    od;
    Add(maximals,SLStabOfHalfDim@(12,2)@factor);
    for i in [7..11] do
      g:=SLStabOfNSpace@(12,2,i);
      Add(maximals,g@factor);
    od;
  else
    Add(maximals,SLPointMeetHyperplane@(12,2)@factor);
    Add(maximals,SLPointUnmeetHyperplane@(12,2)@factor);
    for i in [2..5] do
      Add(maximals,SLStabOfNSpaceMissDual@(12,2,i)@factor);
      Add(maximals,SLStabOfNSpaceMeetDual@(12,2,i)@factor);
    od;
    Add(maximals,SLStabOfHalfDim@(12,2)@factor);
  fi;
  if Print > 1 then
    Print("Getting imprimitive");
  fi;
  for i in [2,3,4] do
    Add(maximals,ImprimsMeetSL@(12,2,i)@factor);
  od;
  if Print > 1 then
    Print("Getting semilinears");
  fi;
  Add(maximals,GammaLMeetSL@(12,2,2)@factor);
  Add(maximals,GammaLMeetSL@(12,2,3)@factor);
  if Print > 1 then
    Print("Getting tensor product");
  fi;
  Add(maximals,TP@()@factor);
  if Print > 1 then
    Print("Getting classical");
  fi;
  Add(maximals,SP(12,2)@factor);
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);

InstallGlobalFunction(L13_2Identify@,
function(group)
local F,Print,apsl,factor,g,homom,i,max,maximals,phi,type;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  # =v= MULTIASSIGN =v=
  type:=Identification@(13,group,Print);
  apsl:=type.val1;
  homom:=type.val2;
  F:=type.val3;
  phi:=type.val4;
  factor:=type.val5;
  type:=type.val6;
  # =^= MULTIASSIGN =^=
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=apsl,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  if Print > 1 then
    Print("Getting reducibles");
  fi;
  if type="psl" then
    Add(maximals,SLPointStab@(13,2)@factor);
    for i in [2..12] do
      g:=SLStabOfNSpace@(13,2,i);
      Add(maximals,g@factor);
    od;
  else
    Add(maximals,SLPointMeetHyperplane@(13,2)@factor);
    Add(maximals,SLPointUnmeetHyperplane@(13,2)@factor);
    for i in [2..6] do
      Add(maximals,SLStabOfNSpaceMissDual@(13,2,i)@factor);
      Add(maximals,SLStabOfNSpaceMeetDual@(13,2,i)@factor);
    od;
  fi;
  if Print > 1 then
    Print("Getting semilinear");
  fi;
  Add(maximals,GammaLMeetSL@(13,2,13)@factor);
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);

InstallGlobalFunction(L14_2Identify@,
function(group)
local F,Print,apsl,factor,g,homom,i,max,maximals,phi,type;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  # =v= MULTIASSIGN =v=
  type:=Identification@(14,group,Print);
  apsl:=type.val1;
  homom:=type.val2;
  F:=type.val3;
  phi:=type.val4;
  factor:=type.val5;
  type:=type.val6;
  # =^= MULTIASSIGN =^=
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=apsl,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  if Print > 1 then
    Print("Getting reducibles");
  fi;
  if type="psl" then
    Add(maximals,SLPointStab@(14,2)@factor);
    for i in [2..6] do
      g:=SLStabOfNSpace@(14,2,i);
      Add(maximals,g@factor);
    od;
    Add(maximals,SLStabOfHalfDim@(14,2)@factor);
    for i in [8..13] do
      g:=SLStabOfNSpace@(14,2,i);
      Add(maximals,g@factor);
    od;
  else
    Add(maximals,SLPointMeetHyperplane@(14,2)@factor);
    Add(maximals,SLPointUnmeetHyperplane@(14,2)@factor);
    for i in [2..6] do
      Add(maximals,SLStabOfNSpaceMissDual@(14,2,i)@factor);
      Add(maximals,SLStabOfNSpaceMeetDual@(14,2,i)@factor);
    od;
    Add(maximals,SLStabOfHalfDim@(14,2)@factor);
  fi;
  if Print > 1 then
    Print("Getting imprimitive");
  fi;
  Add(maximals,ImprimsMeetSL@(14,2,2)@factor);
  if Print > 1 then
    Print("Getting semilinears");
  fi;
  Add(maximals,GammaLMeetSL@(14,2,2)@factor);
  Add(maximals,GammaLMeetSL@(14,2,7)@factor);
  if Print > 1 then
    Print("Getting classical");
  fi;
  Add(maximals,SP(14,2)@factor);
  return rec(val1:=homom,
    val2:=apsl,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);


