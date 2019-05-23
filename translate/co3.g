#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, Centraliser, Centre, DerivedSubgroup,
#  FPGroupStrong, Normaliser, Order, Random, Stabiliser, Stabilizer, Sylow, Sym

#  Defines: CO3Identify

DeclareGlobalFunction("CO3Identify@");

#   Code for maximal subgroups of co3 
InstallGlobalFunction(CO3Identify@,
function(group)
#  /out: group should be already knwon to be isomorphic to co3
local F,Print,S2,S3,a,ag,b,bg,co3,group,homom,max,maximals,phi,soc,x;
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
  co3:=SubStructure(SymmetricGroup(276),(2,24,3)(4,5,7)(8,189,150)(9,184,144)
   (10,190,149)(11,183,143)(12,192,156)(13,191,153)(14,181,154)(15,182,155)
   (16,196,146)(17,194,148)(18,195,147)(19,193,145)(20,188,151)(21,186,152)
   (22,185,141)(23,187,142)(25,26,27)(29,49,200)(30,50,199)(31,51,198)
   (32,52,197)(33,57,226)(34,58,225)(35,59,228)(36,60,227)(37,55,204)(38,56,203)
   (39,53,202)(40,54,201)(41,47,206)(42,48,205)(43,45,208)(44,46,207)
   (61,121,172)(62,122,171)(63,123,169)(64,124,170)(65,127,158)(66,128,157)
   (67,125,160)(68,126,159)(69,138,162)(70,137,161)(71,139,164)(72,140,163)
   (73,118,174)(74,117,173)(75,120,176)(76,119,175)(77,131,177)(78,132,178)
   (79,130,180)(80,129,179)(81,134,168)(82,133,167)(83,136,166)(84,135,165)
   (85,91,97)(86,90,98)(89,100,95)(92,99,96)(101,107,113)(102,108,114)
   (103,105,115)(104,106,116)(209,232,266)(210,236,268)(211,239,272)
   (212,233,263)(213,231,271)(214,241,265)(215,244,275)(216,237,267)
   (217,242,269)(218,235,274)(219,229,264)(220,234,273)(221,240,261)
   (222,243,262)(223,230,270)(224,238,276)(245,255,248)(246,258,253)
   (247,250,257)(251,252,259),#TODO CLOSURE
    (1,117,120,125)(2,78,113,111)(4,167,166,89)(5,148,174,170)(6,12,56,214)
   (7,33,250,141)(8,181,25,71)(9,136,124,119)(10,20,132,178)(11,31,155,213)
   (13,35,187,264)(14,193,51,210)(15,240,191,216)(16,152,59,212)(17,137,60,29)
   (18,134,46,55)(19,231,233,61)(21,130,58,232)(22,199,189,222)(23,118,197,201)
   (24,86,92,159)(26,112,70,267)(27,263,235,194)(28,198,62,228)(30,224,266,218)
   (32,140,50,154)(34,40,47,248)(36,244,225,239)(37,153)(38,176,249,87)
   (39,165,158,252)(41,150,145,234)(42,256,162,99)(43,49,52,220)(44,259,192,67)
   (45,114,79,82)(48,175,149,247)(53,223,202,207)(54,205,126,122)
   (57,188,274,138)(63,80,275,237)(64,72,206,219)(65,236)(66,186,106,268)
   (68,271,257,177)(69,273,171,217)(73,164,246,229)(74,102,103,93)
   (76,183,258,243)(77,226,196,242)(81,251,168,115)(83,109)(84,157,173,97)
   (88,238)(90,262,245,180)(91,95,104,108)(94,253,116,98)(96,161,107,269)
   (110,270,215,241)(121,143,146,142)(128,221)(131,190,139,151)(133,211)
   (135,200)(147,179,265,261)(163,260)(169,276,272,185)(172,254)
   (182,184,208,227)(195,255));
  #  find standard generators
  x:=Random(co3);
  while not Order(x) in Set([9,18,24,30]) do
    x:=Random(co3);
  od;
  a:=x^(QuoInt(Order(x),3));
  x:=Random(co3);
  while Order(x)<>20 do
    x:=Random(co3);
  od;
  b:=x^5;
  while Order(a*b)<>14 do
    b:=b^Random(co3);
  od;
  co3:=SubStructure(co3,a,#TODO CLOSURE
    b);
  if Print > 1 then
    Print("Calling FPGroupStrong");
  fi;
  # =v= MULTIASSIGN =v=
  phi:=FPGroupStrong(co3);
  F:=phi.val1;
  phi:=phi.val2;
  # =^= MULTIASSIGN =^=
  if Print > 1 then
    Print("Setting up isomorphism");
  fi;
  #  Find standard generators of soc
  soc:=group;
  x:=Random(soc);
  while not Order(x) in Set([9,18,24,30]) do
    x:=Random(soc);
  od;
  ag:=x^(QuoInt(Order(x),3));
  x:=Random(soc);
  while Order(x)<>20 do
    x:=Random(soc);
  od;
  bg:=x^5;
  while Order(ag*bg)<>14 do
    bg:=bg^Random(soc);
  od;
  group:=SubStructure(group,ag,#TODO CLOSURE
    bg);
  homom:=GroupHomomorphismByImages(group,co3,
    GeneratorsOfGroup(group),[a,b]);
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=co3,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  if Print > 1 then
    Print("getting maximals");
  fi;
  Add(maximals,Stabilizer(co3,1));
  #  McL:2
  Add(maximals,Stabilizer(co3,[1..100]));
  #  HS
  Add(maximals,Stabilizer(co3,[1..2]));
  #  U_4(3):2^2
  Add(maximals,Stabilizer(co3,[1..23]));
  #  M23
  S2:=Sylow(co3,2);
  S3:=Sylow(co3,3);
  Add(maximals,Normaliser(co3,Centraliser(S3,DerivedSubgroup(S3))));
  #  3^5:(2xM11)
  Add(maximals,Normaliser(co3,Centre(S2)));
  #  2.S_6(2)
  Add(maximals,Stabiliser(co3,Set([101,102,103,104,105,106,109,110,111,112,113,
   114,117,118,119,120,125,126,127,128,129,130,131,132,135,136,137,138,139,140,
   143,144,145,146,147,148,149,150,151,152,154,155,159,160,161,162,163,164,165,
   168,169,171,179,180,181,182,184,185,186,187,188,189,193,194,195,196,197,198,
   199,200,201,202,205,206,207,208,209,210,211,214,215,217,219,220,221,222,223,
   224,225,226,229,230,232,233,234,236,237,238,239,240,243,244,245,246,247,249,
   251,254,255,256,257,258,259,260,261,262,264,265,266,268,269,270,271,272,274,
   275])));
  #  U_3(5):S_3
  Add(maximals,Normaliser(co3,Centre(S3)));
  #  3^(1+4):4S_6
  Add(maximals,Stabiliser(co3,Set([19,71,92,209,250,253,255,265])));
  #  2^4.A8
  Add(maximals,Stabiliser(co3,Set([1,2,3])));
  #  L_3(4):D_12
  Add(maximals,Stabiliser(co3,Set([24,98,105,118,121,137,154,187,196,197,270,
   274])));
  #  2xM_12
  Add(maximals,Normaliser(co3,DerivedSubgroup(DerivedSubgroup(S2))));
  #  2^{2+6}.3^3.2^2
  Add(maximals,Stabiliser(co3,Set([2,6,10,11,13,14,18,19,20,25,33,38,41,42,45,
   51,53,57,59,61,62,63,64,66,74,75,76,81,82,85,92,96,97,98,99,100,104,106,109,
   112,114,115,116,122,123,126,128,129,130,134,141,142,143,148,149,151,152,155,
   157,162,165,168,172,175,176,181,184,187,188,190,191,194,197,199,200,204,205,
   211,212,214,215,220,223,224,226,228,229,230,233,234,236,238,240,241,243,244,
   247,248,253,256,260,261,262,263,266,269,271,276])));
  #  S_3xL_2(8):3
  Add(maximals,Stabiliser(co3,Set([2,6,19,53,61,63,75,97,99,100,104,106,116,129,
   143,149,152,157,162,172,175,184,187,194,204,224,226,234,238,240,241,243,260,
   262,263,269])));
  #  A_4 x S_5
  return rec(val1:=homom,
    val2:=co3,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);


