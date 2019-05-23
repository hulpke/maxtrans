#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, BasicStabilizer, Centraliser, FPGroupStrong,
#  FreeGroup, Generators, Id, Index, IsConjugate, Ngens, O73Identify, Order,
#  Random, RandomProcess, S63Identify, Socle, Sym,
#  distinguish_o73_with_standard_gens, get_standard_gens_s63, homom

#  Defines: O73Identify, S63Identify, S63O73Identify,
#  distinguish_o73_with_standard_gens, get_standard_gens_o73,
#  get_standard_gens_s63

DeclareGlobalFunction("S63O73Identify@");

#  
#  Code to identify and get maximal subgroups of almost simple groups with
#  socle either S(6,3) or O(7,3).
#  
#  Standard generators and maximal subgroups taken from Rob Wilson's
#  Birmingham Atlas, version 2, Nov-Dec 2003.
#  
#  Black box algorithm for standard gens of O(7,3) from same source.
#  
#  Other code and algorithms by Bill Unger, Nov-Dec 2003.
#  This includes:
#  - generators for maximal subgroups
#  - algorithm get_standard_gens_s63
#  - algorithm distinguish_o73_with_standard_gens
#  
#  Subgroups here have been checked to be maximal under the assumption that
#  the list of classes of maximal subgroups on the web pages is complete.

get_standard_gens_s63@:=function(G)
#  /out: Algorithm by Bill Unger 
local P,a,b,ord,x,y;
  P:=RandomProcess(G);
  repeat
    x:=Random(P);
    ord:=Order(x);
    
  until ord in Set([10,20,30]);
  #   1 in 8
  a:=x^(QuoInt(ord,2));
  #   a in 2A
  y:=x^(QuoInt(ord,5));
  repeat
    b:=y^Random(P);
    
  until Order(a*b)=13 and Order(a*b^2)=14;
  #   80 in 2457, about 1 in 31
  return rec(val1:=a,
    val2:=b);
end;
;
S63Identify@:=function(group,soc)
local 
   CG,F,M,Print,S,a,as63,aut,b,c,ce,g,ga,gb,group,h,homom,i,ims,isc,j,max,
   maximals,newgens,phi,soc,ssimp;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  S:=SymmetricGroup(364);
  a:=(2,300)(3,317)(4,169)(5,295)(6,184)(7,51)(9,77)(10,27)(11,60)(13,33)
   (14,336)(15,302)(17,165)(18,286)(19,29)(20,111)(21,88)(22,253)(23,193)
   (25,331)(26,208)(28,59)(30,101)(31,348)(34,161)(35,309)(36,65)(37,87)(38,343)
   (39,280)(40,241)(41,259)(42,301)(43,236)(44,337)(45,117)(46,316)(47,160)
   (48,335)(49,120)(50,58)(52,308)(53,174)(54,274)(55,172)(56,310)(57,190)
   (61,342)(62,179)(63,292)(64,108)(66,98)(67,188)(68,233)(69,268)(70,276)
   (71,318)(72,109)(73,150)(74,212)(75,271)(76,81)(78,237)(79,142)(80,359)
   (82,243)(84,352)(85,322)(86,139)(89,219)(90,133)(91,238)(93,248)(95,186)
   (96,226)(99,249)(100,130)(102,240)(103,181)(104,127)(105,326)(106,283)
   (110,242)(112,144)(113,314)(114,278)(116,350)(119,215)(121,176)(122,257)
   (123,354)(125,221)(126,223)(128,247)(129,138)(131,158)(132,327)(136,196)
   (140,211)(141,338)(143,166)(145,230)(146,361)(147,355)(148,151)(149,287)
   (152,225)(153,340)(154,216)(155,210)(156,256)(157,202)(159,333)(163,177)
   (164,204)(167,258)(168,319)(170,194)(171,351)(173,207)(175,224)(178,306)
   (180,251)(182,220)(185,187)(189,229)(195,298)(197,320)(198,273)(201,307)
   (205,252)(206,294)(209,360)(218,299)(222,234)(228,323)(231,288)(232,289)
   (235,244)(239,353)(245,315)(246,261)(250,285)(254,290)(255,269)(260,266)
   (264,341)(265,282)(272,305)(275,303)(277,329)(279,284)(297,357)(304,312)
   (313,345)(325,346)(328,349)(330,339)(347,364)(358,363) #CAST S
    ;
  b:=(1,178,119,300,69)(2,167,103,148,195)(3,202,44,356,187)(4,26,219,109,180)
   (5,319,248,266,61)(6,348,233,283,64)(7,83,144,255,203)(8,349,336,284,155)
   (9,194,294,350,45)(10,363,169,282,205)(11,171,232,296,247)(12,215,198,329,39)
   (13,50,107,79,150)(14,78,265,53,114)(15,364,206,136,310)(16,359,67,174,309)
   (17,115,170,289,276)(18,142,93,345,147)(19,43,101,288,342)
   (20,352,261,320,354)(21,243,256,324,87)(22,307,278,327,165)
   (23,335,200,66,347)(24,186,76,272,118)(25,182,196,153,226)
   (27,360,116,188,154)(28,315,133,149,236)(29,89,229,214,361)
   (30,110,157,275,88)(31,260,274,102,250)(32,332,211,264,213)
   (33,312,73,244,326)(34,129,96,132,277)(35,91,227,253,308)(36,245,303,285,218)
   (37,241,314,299,58)(38,252,62,334,55)(40,141,189,95,240)(41,313,113,325,304)
   (42,130,192,108,138)(46,340,351,193,273)(47,99,84,302,161)
   (48,254,191,190,298)(49,122,337,146,287)(51,328,331,97,139)
   (52,225,160,127,59)(54,305,185,85,355)(56,106,293,100,63)(57,268,86,270,228)
   (60,301,321,341,204)(65,201,152,184,346)(68,246,117,168,259)
   (70,316,230,72,199)(71,126,237,343,216)(74,231,286,162,156)
   (75,92,269,234,183)(77,137,238,80,197)(82,362,212,111,104)
   (90,295,123,242,257)(94,164,322,338,121)(98,280,112,311,222)
   (120,207,179,172,208)(124,290,306,217,166)(125,281,357,358,239)
   (128,317,173,318,159)(131,267,330,279,209)(134,221,224,223,177)
   (135,344,251,181,333)(140,291,292,145,176)(143,339,163,297,210)
   (151,258,353,262,175)(158,271,323,263,220) #CAST S
    ;
  c:=(1,68)(2,234)(3,336)(5,303)(6,286)(7,209)(8,170)(9,14)(10,325)(11,268)
   (13,350)(15,128)(16,253)(17,342)(18,275)(19,248)(20,222)(21,243)(22,233)
   (23,231)(25,290)(26,106)(27,93)(28,206)(29,256)(30,198)(31,329)(32,319)
   (33,100)(35,192)(36,133)(37,69)(38,144)(39,177)(40,53)(41,279)(43,91)(44,277)
   (45,332)(46,330)(47,312)(48,51)(49,247)(50,62)(52,309)(54,89)(55,108)(56,65)
   (57,190)(58,301)(59,80)(60,352)(61,339)(63,221)(64,276)(66,226)(67,258)
   (70,172)(71,145)(72,125)(73,260)(74,160)(75,250)(76,215)(77,121)(78,311)
   (79,225)(81,354)(82,88)(83,112)(84,188)(85,102)(86,361)(87,167)(90,185)
   (92,362)(94,333)(95,266)(96,115)(97,183)(98,199)(99,123)(101,169)(103,161)
   (104,116)(105,119)(107,314)(109,254)(110,257)(111,269)(113,117)(114,320)
   (118,324)(120,349)(122,242)(124,218)(126,163)(127,322)(129,194)(130,240)
   (131,344)(132,200)(135,318)(136,176)(137,343)(138,263)(139,146)(140,207)
   (141,321)(142,229)(143,288)(148,154)(149,289)(150,304)(151,255)(153,364)
   (155,220)(156,351)(157,295)(158,297)(162,308)(164,294)(165,238)(166,252)
   (168,338)(171,346)(173,205)(174,359)(175,249)(178,334)(180,337)(181,323)
   (182,203)(184,345)(186,212)(187,208)(193,211)(196,315)(197,262)(201,331)
   (202,313)(204,241)(210,291)(213,341)(214,270)(216,300)(217,357)(219,274)
   (223,360)(224,326)(227,261)(230,267)(232,302)(236,316)(239,356)(245,317)
   (246,299)(251,285)(259,363)(264,353)(265,358)(271,348)(278,281)(280,335)
   (282,347)(283,310)(284,340)(287,328)(292,307) #CAST S
    ;
  ssimp:=SubStructure(S,a,#TODO CLOSURE
    b);
  ssimp.Order:=4585351680;
  # =v= MULTIASSIGN =v=
  phi:=FPGroupStrong(ssimp);
  F:=phi.val1;
  phi:=phi.val2;
  # =^= MULTIASSIGN =^=
  #   soc := Socle(group);
  aut:=Index(group,soc);
  if Print > 1 then
    Print("group is S(6,3):[%o]\n",aut);
  fi;
  # =v= MULTIASSIGN =v=
  gb:=get_standard_gens_s63@(soc);
  ga:=gb.val1;
  gb:=gb.val2;
  # =^= MULTIASSIGN =^=
  soc:=SubStructure(soc,ga,#TODO CLOSURE
    gb);
  soc.Order:=4585351680;
  newgens:=[ga,gb];
  for g in Generators(group) do
    if not g in SubStructure(group,newgens) then
      Add(newgens,g);
    fi;
  od;
  group:=SubStructure(group,newgens);
  as63:=SubStructure(S,a,#TODO CLOSURE
    b,c);
  ims:=[a,b];
  homom:=GroupHomomorphismByImages(soc,ssimp,
    GeneratorsOfGroup(soc),ims);
  for i in [Ngens(soc)+1..Ngens(group)] do
    g:=group.i;
    CG:=as63;
    ce:=One(as63);
    for j in [1..2] do
      # =v= MULTIASSIGN =v=
      h:=IsConjugate(CG,ssimp.j^ce,homom(soc.j^g));
      isc:=h.val1;
      h:=h.val2;
      # =^= MULTIASSIGN =^=
      if not isc then
        Error("Conjugation error in Aut(S(6,3))");
      fi;
      CG:=Centraliser(CG,homom(soc.j^g));
      ce:=ce*h;
    od;
    Add(ims,ce);
  od;
  newgens:=ims;
  for g in Generators(as63) do
    if not g in SubStructure(as63,ims) then
      Add(ims,g);
    fi;
  od;
  as63:=SubStructure(S,ims);
  homom:=GroupHomomorphismByImages(group,as63,
    GeneratorsOfGroup(group),newgens);
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=as63,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  Add(maximals,BasicStabilizer(ssimp,2));
  #   3^(1+4):2.U(4,2)
  #   3^6:L(3,3)
  M:=SubStructure(ssimp,b^-2*a*b^-2*a*b*a,#TODO CLOSURE
    a*b^-2*a*b^-2*a*b^-2*a*b^-1*a);
  M.Order:=4094064;
  Add(maximals,M);
  #   3^(3+4):2.(S4 x A4)
  M:=SubStructure(ssimp,b^-1*a*b^-1*a*b*a*b,#TODO CLOSURE
    b*a*b^-1*a*b^-1*a*b^2*a*b*a*b*a*b^2*a*b^-1,
   b*a*b^-2*a*b*a*b*a*b^2*a*b^2*a*b*a*b^-1);
  M.Order:=1259712;
  Add(maximals,M);
  #   2.(A4 × U4(2))
  M:=SubStructure(ssimp,b*a*b^-1*a*b,#TODO CLOSURE
    b^-2*a*b^2*a*b^-2);
  M.Order:=622080;
  Add(maximals,M);
  #   2^(2+6):3^3:S3
  M:=SubStructure(ssimp,b^-2*a*b^-1*a*b^-2*a*b^2*a*b*a*b^2,#TODO CLOSURE
    a*b^-1*a*b^2*a*b*a*b*a*b^-1*a*b^-1*a*b^-2*a*b*a,
   a*b*a*b^-1*a*b^-1*a*b*a*b^-2*a*b*a*b^-2*a*b*a*b^-2,
   a*b^-1*a*b^-1*a*b*a*b*a*b^-1*a*b^2*a*b^-1*a*b^2*a*b^-1*a*b^-2*a);
  M.Order:=41472;
  Add(maximals,M);
  #   L(2,27):3
  M:=SubStructure(ssimp,b*a*b^-1*a*b^2*a*b*a*b*a*b^-1*a*b^2*a*b^-2*a*b^-1,#TODO 
   CLOSURE
    a*b*a*b*a*b*a*b^2*a*b*a*b^2*a*b*a*b*a*b*a*b^2);
  M.Order:=29484;
  Add(maximals,M);
  #   U3(3):2 × 2
  M:=SubStructure(ssimp,a*b^2,#TODO CLOSURE
    b^-1*a*b^-1*a*b^-1*a*b*a*b*a*b^2*a*b^2*a*b*a*b^-2*a*b*a*b^-2*a*b^-1*a*b^-2*a\
*b);

     M.Order:=24192;
  Add(maximals,M);
  #   L(3,3):2
  M:=SubStructure(ssimp,a*b*a*b*a*b^2*a*b*a*b*a*b^2*a*b*a*b*a*b^2,#TODO CLOSURE
    a*b^2*a*b^2*a*b^2*a*b^2*a*b^2*a*b^2*a*b^2);
  M.Order:=11232;
  Add(maximals,M);
  if aut=1 then
    #   L(2,13) twice
    M:=SubStructure(ssimp,((a*b*b)^7)^(b*(a*b^-1)^4),#TODO CLOSURE
      a*b);
    M.Order:=1092;
    Add(maximals,M);
    Add(maximals,M^c);
  fi;
  #   Above all checked to be maximal using IsMaximal 
  #   A5
  M:=SubStructure(ssimp,
   b^-1*a*b^-1*a*b^-1*a*b^-1*a*b*a*b*a*b^2*a*b^-1*a*b^-1*a*b^2*a*b^2*a*b^-1*a*b*\
a*b*a*b^2*a*b*a,#TODO CLOSURE

       a*b^-2*a*b*a*b*a*b*a*b^-2*a*b^-1*a*b^2*a*b^2*a*b*a*b^-2*a*b^2*a*b*a*b*a*b\
^-2*a*b);

     M.Order:=60;
  Add(maximals,M);
  #   This A5 is maximal (provided the list is complete) as from orders it
  #  can only be a subgroup of Nos 1 & 4 above, and they have orbits of
  #  length 1 & 4 resp, and this A5 has shortest orbit length 12, so it
  #  isn't contained in any conjugate of any above 
  return rec(val1:=homom,
    val2:=as63,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end;
;
get_standard_gens_o73@:=function(G)
local P,a,b,x,y;
  P:=RandomProcess(G);
  repeat
    x:=Random(P);
    
  until Order(x)=14;
  #   1 in 14
  a:=x^7;
  #   a in 2A
  y:=x^2;
  repeat
    b:=y^Random(P);
    
  until Order(a*b)=13 and Order(a*b^2)=20;
  #   28 in 351
  return rec(val1:=a,
    val2:=b);
end;
;
O73Identify@:=function(group,soc,ga,gb)
local 
   CG,F,F2,M,Print,S,a,ao73,aut,b,c,ce,g,group,h,homom,i,ims,isc,j,max,maximals,
   newgens,osimp,phi,phi2,soc;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  S:=SymmetricGroup(351);
  a:=(1,105)(2,81)(3,328)(4,166)(6,75)(7,134)(8,311)(10,327)(11,51)(12,99)
   (19,314)(20,200)(21,66)(22,83)(24,67)(26,345)(27,82)(29,107)(30,215)(31,84)
   (33,135)(35,233)(38,344)(42,152)(43,169)(46,291)(47,136)(49,223)(50,338)
   (53,287)(54,324)(55,322)(56,239)(58,181)(59,165)(60,68)(63,80)(64,182)
   (65,350)(69,241)(71,164)(74,119)(76,300)(77,214)(78,315)(87,121)(89,283)
   (90,307)(91,229)(92,336)(94,261)(95,234)(97,282)(98,111)(101,154)(102,290)
   (110,269)(112,190)(113,250)(116,177)(120,221)(122,183)(127,351)(128,144)
   (129,274)(130,232)(131,349)(137,224)(138,276)(140,302)(142,273)(145,326)
   (146,195)(149,231)(150,206)(151,186)(156,319)(157,303)(159,216)(161,226)
   (162,238)(163,194)(167,203)(170,180)(174,211)(175,246)(184,279)(185,202)
   (187,272)(188,295)(192,296)(201,243)(213,330)(217,309)(222,247)(225,297)
   (228,258)(237,280)(242,331)(244,321)(248,342)(251,268)(253,263)(257,325)
   (262,332)(275,343)(281,329)(292,305)(294,347)(306,316)(310,320)(334,339) 
   #CAST S
    ;
  b:=(1,347,67,10,139,308,350)(2,338,345,318,295,264,7)(3,270,5,337,306,276,31)
   (4,203,15,289,275,246,266)(6,146,263,321,51,190,173)
   (8,329,46,283,277,236,237)(9,154,225,191,17,252,256)
   (11,117,297,144,105,96,118)(12,152,197,309,323,50,229)
   (13,199,278,313,348,294,162)(14,231,193,125,258,37,79)
   (16,112,251,330,187,188,94)(18,214,26,164,60,265,242)
   (19,90,315,36,182,35,201)(20,232,38,58,93,47,336)(21,55,101,212,49,153,114)
   (22,44,89,63,175,228,75)(23,68,183,303,198,181,136)
   (24,304,325,52,213,259,200)(25,98,312,317,150,106,123)
   (27,29,33,227,233,293,157)(28,224,222,126,39,319,202)
   (30,159,172,268,148,107,42)(32,272,255,163,85,87,130)
   (34,291,141,311,285,332,244)(40,110,83,111,69,282,140)
   (41,59,53,192,298,86,61)(43,273,254,248,269,322,260)
   (45,207,279,151,240,82,189)(48,274,145,109,310,120,143)
   (54,245,180,97,119,206,95)(56,104,281,205,243,267,70)
   (57,132,215,346,138,290,333)(62,186,342,100,340,133,71)
   (64,171,241,250,74,72,351)(65,116,160,261,223,262,102)
   (66,195,219,299,327,121,238)(73,335,230,88,296,174,131)
   (76,239,331,127,178,334,169)(77,287,218,92,176,284,328)
   (78,134,196,216,339,286,288)(80,307,108,128,324,184,209)
   (81,103,124,220,253,84,301)(91,158,168,147,99,349,165)
   (113,247,343,226,292,221,156)(115,122,179,326,257,194,166)
   (129,341,167,170,185,137,302)(135,316,204,210,344,235,211)
   (142,280,271,234,177,149,320)(155,305,300,208,314,161,249) #CAST S
    ;
  c:=(1,4)(2,7)(5,13)(6,12)(11,22)(14,23)(16,25)(21,29)(26,38)(27,47)(30,42)
   (36,41)(37,57)(39,62)(44,70)(45,73)(46,76)(49,64)(50,65)(51,83)(58,91)(59,95)
   (60,98)(61,100)(66,107)(68,111)(69,113)(71,116)(72,118)(74,122)(75,99)
   (77,128)(78,102)(79,103)(81,134)(82,136)(92,145)(93,147)(94,150)(96,153)
   (97,156)(101,161)(105,166)(106,168)(109,172)(110,174)(112,149)(114,179)
   (115,171)(117,155)(119,183)(120,184)(123,158)(124,189)(125,160)(126,193)
   (127,131)(129,162)(130,163)(132,196)(133,198)(137,170)(139,204)(141,208)
   (144,214)(146,216)(148,218)(151,222)(152,215)(154,226)(157,228)(159,195)
   (164,177)(165,234)(173,240)(175,188)(176,219)(178,220)(180,224)(181,229)
   (182,223)(186,247)(190,231)(191,230)(194,232)(201,237)(206,261)(210,266)
   (211,269)(212,271)(221,279)(227,285)(238,274)(241,250)(242,244)(243,280)
   (246,295)(249,267)(254,289)(256,298)(258,303)(259,304)(264,308)(270,313)
   (277,286)(282,319)(290,315)(291,300)(293,317)(301,323)(321,331)(326,336)
   (333,340)(338,350)(341,348)(344,345)(349,351) #CAST S
    ;
  osimp:=SubStructure(S,a,#TODO CLOSURE
    b);
  osimp.Order:=4585351680;
  # =v= MULTIASSIGN =v=
  phi:=FPGroupStrong(osimp);
  F:=phi.val1;
  phi:=phi.val2;
  # =^= MULTIASSIGN =^=
  #   soc := Socle(group);
  aut:=Index(group,soc);
  if Print > 1 then
    Print("group is O(7,3):[%o]\n",aut);
  fi;
  #   ga, gb:= get_standard_gens_o73(soc);
  soc:=SubStructure(soc,ga,#TODO CLOSURE
    gb);
  soc.Order:=4585351680;
  newgens:=[ga,gb];
  for g in Generators(group) do
    if not g in SubStructure(group,newgens) then
      Add(newgens,g);
    fi;
  od;
  group:=SubStructure(group,newgens);
  ao73:=SubStructure(S,a,#TODO CLOSURE
    b,c);
  ims:=[a,b];
  homom:=GroupHomomorphismByImages(soc,osimp,
    GeneratorsOfGroup(soc),ims);
  for i in [Ngens(soc)+1..Ngens(group)] do
    g:=group.i;
    CG:=ao73;
    ce:=One(ao73);
    for j in [1..2] do
      # =v= MULTIASSIGN =v=
      h:=IsConjugate(CG,osimp.j^ce,homom(soc.j^g));
      isc:=h.val1;
      h:=h.val2;
      # =^= MULTIASSIGN =^=
      if not isc then
        Error("Conjugation error in Aut(O(7,3))");
      fi;
      CG:=Centraliser(CG,homom(soc.j^g));
      ce:=ce*h;
    od;
    Add(ims,ce);
  od;
  newgens:=ims;
  for g in Generators(ao73) do
    if not g in SubStructure(ao73,ims) then
      Add(ims,g);
    fi;
  od;
  ao73:=SubStructure(S,ims);
  homom:=GroupHomomorphismByImages(group,ao73,
    GeneratorsOfGroup(group),newgens);
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=ao73,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  F2:=FreeGroup(2);
  phi2:=GroupHomomorphismByImages(F2,osimp,
    a,b);
  Add(maximals,BasicStabilizer(osimp,2));
  #   2U(4,3).2
  #   3^5:U(4,2):2
  M:=SubStructure(osimp,[[1,2,2,1,-2,-2,-1],[1,-2,-2,1,2,2,-1]
   ,[1,-2,1,2,2,1,-2,-2,-1,-2,-2,-1,2]]@phi2);
  M.Order:=12597120;
  Add(maximals,M);
  #   L(4,3):2
  M:=SubStructure(osimp,[[1],[2,1,-2],[2,2,1,-2,-2],[-2,-2,1,2,2]
   ,[2,2,2,1,2,1,-2,-1,-2,-2,-2],[-2,1,-2,1,-2,1,2,-1,2,-1,2]]@phi2);
  M.Order:=12130560;
  Add(maximals,M);
  #    3^(3+3):L(3,3)
  M:=SubStructure(osimp,[[1,2,1,2,1,2,2,-1,2,-1,2],[1,2,2,2,1,-2,-1,2,2,-1,-2]]
   @phi2);
  M.Order:=4094064;
  Add(maximals,M);
  #   3^(1+6):(2A4 x A4).2
  M:=SubStructure(osimp,[[2,1,2,2,2,1,-2,-2,-1,-2,-1,-2]
   ,[2,2,2,1,2,2,1,2,2,-1,2,2,-1,2,-1,-2]
   ,[1,2,1,2,1,2,2,1,-2,-1,-2,-1,2,-1,2,2,2]]@phi2);
  M.Order:=1259712;
  Add(maximals,M);
  #   (2^2 x U(4,2)):2
  M:=SubStructure(osimp,[[2,1,-2],[-2,-2,-2,1,2,2,2]
   ,[-2,1,-2,-2,1,-2,1,2,-1,2,2,-1,2],[2,2,1,2,1,-2,1,-2,-2,-1,-2,-2,-1,2,2]
   ,[2,2,1,2,2,1,2,1,-2,-1,-2,-2,-1,-2,-2]]@phi2);
  M.Order:=207360;
  Add(maximals,M);
  #   2^6:A7
  M:=SubStructure(osimp,[[2,1,2,1,2,1,-2,-1,-2,-1,-2,-1]
   ,[2,2,1,-2,1,2,2,-1,-2,-1,-2,-1,-2,-2]]@phi2);
  M.Order:=161280;
  Add(maximals,M);
  #   S4 x S6
  M:=SubStructure(osimp,[[-2,1,2],[1,2,1,-2,1,-2,1,2,-1,2,2,-1,-2,-2,-1]
   ,[1,-2,-2,-2,1,-2,1,-2,-2,-1,-2,-2,-1,2,2,-1,-2,-1]
   ,[2,1,-2,-2,1,-2,1,-2,1,2,-1,2,-1,2,2,-1,-2]
   ,[2,1,-2,1,2,2,1,2,1,2,1,-2,-1,-2,-1,-2,-2,-1,2,-1,-2]]@phi2);
  M.Order:=17280;
  Add(maximals,M);
  #   S4 x 2(A4 x A4).2
  M:=SubStructure(osimp,[[-2,1,2,1,2,1,-2,1,-2,1,-2,-2,-1,2,2,-1,2,-1,2,-1,-2,
   -1],[-2,-2,1,2,1,2,2,1,-2,1,-2,-2,-1,-2,-2,-1,-2,-1,-2,-1,-2,-2]
   ,[-2,-2,-2,1,-2,1,-2,1,-2,-2,1,-2,-2,-1,-2,-1,-2,-2,-1,-2,-1,-2,-1,2]]@phi2)
   ;
  M.Order:=13824;
  Add(maximals,M);
  if aut=2 then
    return rec(val1:=homom,
      val2:=ao73,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  #   Three more pairs for the simple group:
  #   G(2,3)
  M:=SubStructure(osimp,[[1,2,1,2,1,2,-1,2,2,2,-1],[1,-2,-2,1,2,1,2,2,2,-1,-2]]
   @phi2);
  M.Order:=4245696;
  Add(maximals,M);
  Add(maximals,M^c);
  #   S(6,2)
  M:=SubStructure(osimp,[[-2,1,2],[2,1,-2,1,-2,1,2,-1,-2,-2,-2,-1,2,-1]]@phi2);
  M.Order:=1451520;
  Add(maximals,M);
  Add(maximals,M^c);
  #   S9
  M:=SubStructure(osimp,[[2,1,-2,-2,1,-2,-2,1,-2,-1,2,-1,-2,-2,-2,-1,2,-1]
   ,[1,-2,-2,1,2,2,-1],[2,1,2,1,-2,-1,-2]]@phi2);
  M.Order:=362880;
  Add(maximals,M);
  Add(maximals,M^c);
  return rec(val1:=homom,
    val2:=ao73,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end;
;
distinguish_o73_with_standard_gens@:=function(G)
#  /out: G is either s63 or o73, tell them apart/out: if it is o73, return
#  true, a, b where a,b are standard gens/out: if it is s63, return false, _, _
local P,a,ab,ar,b,b2,found_14,ord,pr,r;
  P:=RandomProcess(G);
  found_14:=false;
  repeat
    r:=Random(P);
    ord:=Order(r);
    if ord > 20 then
      return rec(val1:=false,
        val2:=_,
        val3:=_);
    fi;
    #   proof it is s63 
    if found_14 then
      ar:=a^r;
      pr:=Set([Order(ar*b),Order(ar*b2)]);
      if pr=Set([10,18]) then
        #   proof it is o73, find standard gens 
        repeat
          b:=b^Random(P);
          ab:=a*b;
          ord:=Order(ab);
          
        until ord=13 and Order(ab*b)=20;
        return rec(val1:=true,
          val2:=a,
          val3:=b);
      fi;
    else
      if ord=14 then
        found_14:=true;
        a:=r^7;
        #   s63 => 2B, o73 => 2A
        b:=r^2;
        b2:=b^2;
      fi;
    fi;
    
  until false;
end;
;
InstallGlobalFunction(S63O73Identify@,
function(group)
#  /out:
#  group must be isomorphic to one of S(6,3), S(6,3).2, O(7,3) or O(7,3).2
#  Work out which simple group it is and call the appropriate
#  subroutine to complete the maximal subgroups stuff.

local Print,ga,gb,max,o_flag,soc;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  soc:=Socle(group);
  # =v= MULTIASSIGN =v=
  gb:=distinguish_o73_with_standard_gens@(soc);
  o_flag:=gb.val1;
  ga:=gb.val2;
  gb:=gb.val3;
  # =^= MULTIASSIGN =^=
  if o_flag then
    return O73Identify@(group,soc,ga,gb:max:=max,Print:=Print);
  else
    return S63Identify@(group,soc:max:=max,Print:=Print);
  fi;
end);


