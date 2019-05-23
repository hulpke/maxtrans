
#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.34, 10/22/15 by AH

#  Global Variables used: Append, Centraliser, FPGroupStrong, Generators, Id,
#  Index, IsConjugate, Ngens, Order, Random, RandomProcess, Socle, Sym,
#  get_standard_gens_g24, homom

#  Defines: G24Identify, get_standard_gens_g24

DeclareGlobalFunction("G24Identify@");

get_standard_gens_g24@:=function(G)
local P,a,ab,b,ord,x;
  #   standard gens and algorithm from Birmingham web page 
  #   assumes G is isomorphic to G2(4) 
  repeat
    x:=PseudoRandom(G);
    ord:=Order(x);
  until ord in [4,8,12];
  a:=x^QuoInt(ord,2);
  repeat
    repeat
      x:=PseudoRandom(G);
      ord:=Order(x);
    until ord in [5,10,15];
    x:=x^QuoInt(ord,5);
    repeat
      b:=x^PseudoRandom(G);
      ab:=a*b;
    until Order(ab)=13 and Order(ab*b)=13;
    ord:=Order(ab*ab*b);
    Assert(1,ord in [10,15]);
    
  until ord=15;
  return rec(val1:=a,
    val2:=b);
  
end;

InstallGlobalFunction(G24Identify@,
function(group)
local 
   CG,F,M,S,a,ag24,aut,b,c,ce,g,ga,gb,homom,ims,isc,maximals,newgens,
   simp,soc,max,phi,newgens_grp,ims_grp,h,i,j,x,CGx;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  a:=(1,39)(2,254)(3,61)(4,65)(5,243)(6,26)(7,50)(8,343)(9,143)(10,114)
   (11,56)(12,76)(13,289)(14,53)(16,62)(17,325)(18,67)(19,46)(20,216)
   (21,308)(22,252)(23,335)(28,305)(29,275)(30,121)(31,351)(32,81)(33,259)
   (34,109)(35,390)(36,128)(37,383)(38,186)(40,241)(41,414)(42,402)(43,274)
   (44,359)(47,365)(48,110)(49,363)(51,292)(52,101)(54,228)(55,93)(57,66)
   (58,168)(59,122)(60,358)(63,130)(64,326)(68,372)(69,209)(70,313)(71,336)
   (72,398)(73,385)(74,182)(75,163)(77,257)(78,276)(79,105)(82,231)(83,159)
   (84,407)(85,181)(86,188)(87,340)(88,160)(89,323)(90,346)(91,394)(92,369)
   (94,183)(95,416)(97,226)(98,187)(99,401)(100,202)(102,320)(103,176)
   (104,157)(106,223)(107,352)(108,294)(111,137)(112,251)(113,253)(115,240)
   (117,269)(118,317)(119,341)(120,380)(123,342)(124,131)(125,411)(127,238)
   (133,370)(135,172)(136,156)(139,368)(140,300)(141,349)(142,366)(144,395)
   (146,162)(147,212)(148,195)(149,406)(150,242)(151,250)(152,222)(153,355)
   (154,167)(155,166)(158,210)(161,399)(164,268)(165,281)(169,400)(170,197)
   (171,235)(173,174)(175,249)(178,258)(179,237)(180,203)(185,264)(189,260)
   (190,318)(191,304)(192,344)(193,298)(194,337)(196,290)(198,256)(199,376)
   (200,246)(201,347)(204,329)(205,384)(206,373)(207,272)(208,338)(211,405)
   (213,367)(214,332)(215,302)(217,230)(218,357)(220,393)(221,288)(224,354)
   (225,280)(227,371)(229,283)(232,330)(233,248)(234,389)(239,387)(244,273)
   (245,315)(255,334)(261,301)(262,379)(263,361)(266,348)(267,328)(270,296)
   (271,327)(277,278)(279,311)(282,291)(284,375)(287,392)(293,412)(295,410)
   (297,321)(303,396)(306,404)(307,386)(309,374)(310,356)(322,415)(324,388)
   (331,350)(333,409)(345,382)(353,403)(360,377)(378,397)(391,413);
  b:=(1,361,150,197,241)(2,333,132,273,123)(3,343,177,281,335)
   (4,18,391,283,354)(5,299,109,230,171)(6,349,34,124,402)(7,47,166,312,48)
   (8,399,242,318,413)(9,116,148,307,217)(10,277,308,342,195)
   (11,266,292,284,101)(12,117,218,237,368)(13,214,225,134,143)
   (14,337,260,340,228)(15,321,383,268,411)(16,315,130,20,174)
   (17,240,270,316,157)(19,190,145,239,98)(21,71,381,59,115)
   (22,334,261,151,362)(23,104,212,390,248)(24,357,54,70,404)
   (25,272,135,183,85)(26,170,339,49,398)(27,139,397,295,263)
   (28,46,395,207,185)(29,305,39,112,414)(30,146,100,369,90)
   (31,189,128,366,84)(32,252,294,161,341)(33,314,336,73,221)
   (35,159,209,94,365)(36,121,55,40,346)(37,303,350,211,370)
   (38,91,387,67,165)(41,222,97,287,235)(42,271,45,77,291)(43,79,282,110,53)
   (44,255,274,163,259)(50,64,324,158,172)(51,213,63,168,198)
   (52,78,265,236,296)(56,326,92,416,409)(57,147,219,243,206)
   (58,179,201,372,358)(60,199,144,373,363)(61,105,320,205,175)
   (62,229,96,208,87)(65,162,415,375,122)(66,345,278,126,106)
   (68,328,136,75,348)(69,384,301,389,142)(72,325,156,245,360)
   (74,302,249,80,155)(76,374,108,223,319)(81,385,244,408,355)
   (83,403,410,388,352)(86,359,380,224,180)(88,167,251,184,119)
   (89,356,113,279,327)(93,293,99,297,264)(95,188,330,246,323)
   (102,313,120,153,367)(103,164,338,111,378)(107,152,203,376,405)
   (118,169,351,193,407)(125,262,250,269,280)(127,275,187,310,138)
   (129,232,377,234,137)(131,286,276,254,216)(133,322,215,154,290)
   (140,400,386,186,353)(141,182,160,194,331)(149,289,306,288,181)
   (173,392,285,412,233)(191,347,344,300,204)(192,396,311,382,317)
   (196,371,258,210,202)(200,238,401,406,257)(226,256,329,379,267)
   (231,298,393,394,253)(247,304,364,309,332);
  c:=(1,2)(3,5)(6,8)(7,10)(9,13)(11,15)(12,17)(14,20)(16,23)(18,25)(19,27)
   (21,30)(22,32)(24,35)(26,37)(28,39)(29,41)(33,45)(34,47)(36,50)(38,53)
   (40,56)(42,58)(43,60)(44,62)(46,55)(48,65)(49,67)(51,70)(52,71)(54,74)
   (59,80)(61,82)(63,84)(66,88)(68,90)(69,92)(72,96)(73,98)(75,101)(76,85)
   (79,104)(81,107)(83,110)(86,113)(87,115)(89,118)(91,97)(93,122)(95,106)
   (99,127)(100,129)(102,132)(103,134)(108,139)(109,140)(111,143)(112,144)
   (114,146)(116,141)(117,148)(119,151)(121,154)(123,156)(124,157)(125,159)
   (126,161)(128,163)(130,164)(131,166)(133,169)(135,170)(136,172)(138,174)
   (142,177)(145,180)(147,182)(149,184)(150,186)(153,188)(158,191)(162,193)
   (165,196)(167,198)(168,178)(171,203)(173,206)(175,208)(176,210)(179,213)
   (183,217)(185,220)(187,222)(189,224)(190,225)(192,228)(194,215)(195,231)
   (200,232)(201,227)(202,235)(205,238)(207,241)(209,244)(211,246)(214,248)
   (216,250)(219,253)(221,255)(223,249)(226,259)(229,263)(234,269)(236,271)
   (237,273)(239,276)(240,278)(242,280)(243,264)(245,277)(247,284)(251,286)
   (252,288)(254,291)(256,293)(257,295)(260,299)(261,300)(262,302)(265,304)
   (266,306)(267,307)(268,308)(270,310)(272,312)(274,314)(275,316)(281,319)
   (282,315)(283,321)(285,323)(287,324)(289,326)(290,327)(292,330)(294,331)
   (297,334)(298,336)(303,328)(305,340)(309,343)(311,325)(313,348)(317,349)
   (318,341)(320,354)(322,350)(329,360)(333,364)(335,347)(337,367)(338,368)
   (339,370)(351,378)(352,361)(353,377)(355,381)(357,384)(358,366)(359,386)
   (362,388)(363,390)(369,379)(371,396)(372,397)(373,398)(374,383)(375,395)
   (376,385)(380,402)(382,403)(389,393)(391,405)(392,406)(394,408)(399,400)
   (404,413)(407,412)(409,414)(415,416);
  simp:=Group(a,b);
  SetSize(simp,251596800);
  phi:=IsomorphismFpGroup(simp:NoPrecomputedData);
  F:=Range(phi);
  phi:=InverseGeneralMapping(phi);
  soc:=Socle(group);
  aut:=Index(group,soc);
  Info(InfoClassmax,1,"group is G(2,4):[",aut,"]\n");
  # =v= MULTIASSIGN =v=
  gb:=get_standard_gens_g24@(soc);
  ga:=gb.val1;
  gb:=gb.val2;
  # =^= MULTIASSIGN =^=
  soc:=SubgroupNC(soc,[ga, gb]);
  SetSize(soc,251596800);
  newgens:=[ga,gb];
  newgens_grp:=SubgroupNC(group,newgens);
  SetSize(newgens_grp,251596800);
  for g in GeneratorsOfGroup(group) do
    if not g in newgens_grp then
      Add(newgens,g);
      newgens_grp:=ClosureSubgroupNC(newgens_grp,g);
      SetSize(newgens_grp,2*251596800);
    fi;
  od;
  group:=newgens_grp;
  ag24:=Group(a,b,c);
  SetSize(ag24,2*251596800);
  ims:=[a,b];
  homom:=GroupHomomorphismByImagesNC(soc,simp,[ga,gb],ims);
  for i in [Length(GeneratorsOfGroup(soc))+1..Length(GeneratorsOfGroup(group))] do
    g:=GeneratorsOfGroup(group)[i];
    CG:=ag24;
    ce:=One(ag24);
    for j in [1,2] do
      x:=ImagesRepresentative(homom,GeneratorsOfGroup(soc)[j]^g);
      CGx:=Centraliser(CG,x);
      h:=RepresentativeAction(CG,GeneratorsOfGroup(simp)[j]^ce,x);
      if h=fail then
        Error("Conjugation error in Aut(G(2,4)");
      fi;
      CG:=CGx;
      ce:=ce*h;
    od;
    Add(ims,ce);
  od;
  newgens:=ims;
  ims_grp:=SubgroupNC(ag24,ims);
  SetSize(ims_grp,Size(group));
  for g in GeneratorsOfGroup(ag24) do
    if not g in ims_grp then
      Add(ims,g);
      ims_grp:=SubgroupNC(ag24,ims);
      SetSize(ims_grp,2*251596800);
    fi;
  od;
  ag24:=ims_grp;
  homom:=GroupHomomorphismByImagesNC(group,ag24,
	  GeneratorsOfGroup(group),newgens{[1..Length(GeneratorsOfGroup(group))]});

  maximals:=[];
  if not max then
    return rec(iso:=homom,
      autom:=ag24,
      maxes:=maximals,
      free:=F,
      epi:=phi);
  fi;
  #  
  #  Maximal subgroups from Birmingham web page.
  #  If their list is complete then all is well.
  #  The below have all been tested for maximality using IsMaximal,
  #  and each M is simp-conjugate to M^c.
  #  The two with the same order (184320) have different chief factors.
  #  Generators as words in a,b by Bill Unger. They have no particular
  #  merit, apart from giving the right groups.
  
  #   J2 [point stabilizer]
  M:=SubgroupNC(simp,[a, b^(a*b*a*b^2)]);
  SetSize(M,604800);
  Add(maximals,M);
  #   2^(4+6):(A5 x 3) [2^(4+6) normal in 2-Sylow]
  M:=SubgroupNC(simp,[
	a ^ (b^2 * a * b^-1), 
	a * b^2 * a * b^-2 * a * b * a * b * a * b^2 ]);
  SetSize(M,184320);
  Add(maximals,M);
  #   2^(2+8):(A5 x 3) [2^(2+8) normal in 2-Sylow]
  M:=SubgroupNC(simp,[
	b * a * b^-2 * a * b * a * b^-2 * a * b,
	a * b * a * b * a * b * a * b * a * b^-1 ]);
  SetSize(M,184320);
  Add(maximals,M);
  #   U(3,4):2
  M:=SubgroupNC(simp,[
	b^-1 * a * b^2 * a * b^-1, 
	a * b * a * b * a * b * a * b^-1 * a * b^2 * a * b^2 * a ]);
  SetSize(M,124800);
  Add(maximals,M);
  #   3.L(3,4):2 [Normalizer of subgrp of order 3]
  M:=SubgroupNC(simp,[a, b * a * b^-1 * a * b^2 * a * b^2 * a * b^2 ]);
  SetSize(M,120960);
  Add(maximals,M);
  #   U3(3):2 [Centralizer of an outer involution]
  M:=SubgroupNC(simp,[
	a * b * a * b^2 * a * b^-1 * a * b^2 * a * b^-1 * a * b * a * 
	    b * a * b,
	    a * b^-1 * a * b * a * b * a * b^-2 * a * b * a * b * a * b^-1]);
  SetSize(M,12096);
  Add(maximals,M);
  #   A5 x A5
  M:=SubgroupNC(simp,[
	b^2 * a * b^2 * a * b^-2 * a * b^-1 * a * b * a * b^2 * a * b * a,
	b^-1 * a * b^2 * a * b^-1 * a * b * a * b * a * b * a * b^-2 * a * 
	  b * a ]);
  SetSize(M,3600);
  Add(maximals,M);
  #   L(2,13)
  M:=SubgroupNC(simp,[
	a * b^-1 * a * b * a * b * a * b^-2 * a * b^-1 * a * b^-1 * a * b * 
	    a * b * a * b^-2,
	b^-2 * a * b^-2 * a * b^-1 * a * b^2 * a * b * a * b^2 
	    * a * b^2 * a * b * a * b^-1 ]);
  SetSize(M,1092);
  Add(maximals,M);
  return rec(iso:=homom,
    autom:=ag24,
    maxes:=maximals,
    free:=F,
    epi:=phi);
  
end);

