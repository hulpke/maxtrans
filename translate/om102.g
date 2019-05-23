#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, Centraliser, FPGroupStrong, Generators, Id,
#  Index, IsConjugate, Ngens, Order, Random, RandomProcess, Socle, Sym,
#  get_standard_gens_om102, homom

#  Defines: Om102Identify, get_standard_gens_om102

DeclareGlobalFunction("Om102Identify@");

#  
#  Info from Birmingham website 8/1/2004
#  All maximals checked correct, subject to list at that date being
#  complete.
#  
#  18/2/04
#  Added 3^5:2^4:S5 after inspection of Atlas of Brauer Characters Appendix 2
#  and checked not included in any other subgroup here.

get_standard_gens_om102@:=function(G)
#  /out:
#  Find standard generators of O-(10,2).
#  Assumes G is O-(10,2).
#  Algorithm and code by Bill Unger 8/1/2004.
#  Standard gens as defined in Birmingham Atlas at that date.

local P,a,ab,b,count,found_5B,ord,x;
  P:=RandomProcess(G);
  repeat
    x:=Random(P);
    
  until Order(x)=24;
  #   1 in 16
  a:=x^12;
  #   a is in 2A
  repeat
    repeat
      x:=Random(P);
      ord:=Order(x);
      
    until ord in Set([5,10,15,30]);
    #   519 in 2800
    x:=x^(QuoInt(ord,5));
    #   Now x could be in 5A or 5B. Try to prove it is in 5B.
    #   If this fails in 10 tries then we get a new x.
    #   112 in 173 are in 5B, a little less than 2 in 3.
    count:=0;
    repeat
      count:=count+1;
      b:=x^Random(P);
      found_5B:=Order(a*b) > 15;
      #   640 in 1309 if x in 5B
      
    until found_5B or count >= 10;
    
  until found_5B;
  #   x is in 5B
  repeat
    b:=x^Random(P);
    ab:=a*b;
    
  until Order(ab)=33 and Order(ab^3*b)=18;
  #   120 in 1309
  return rec(val1:=a,
    val2:=b);
end;
;
InstallGlobalFunction(Om102Identify@,
function(group)
local 
   CG,F,M,Print,S,a,ag,aom102,aut,b,bg,c,ce,g,group,h,homom,i,ims,isc,j,max,
   maximals,newgens,om102,phi,soc;
  max:=ValueOption("max");
  if max=fail then
    max:=true;
  fi;
  Print:=ValueOption("Print");
  if Print=fail then
    Print:=0;
  fi;
  S:=SymmetricGroup(495);
  a:=(1,122)(3,129)(4,246)(5,341)(6,346)(7,435)(8,241)(9,309)(10,455)(12,90)
   (13,445)(14,232)(15,227)(16,35)(17,463)(20,440)(21,185)(23,134)(24,224)
   (25,26)(27,369)(28,166)(29,219)(31,340)(32,396)(33,175)(34,103)(36,85)
   (37,265)(38,361)(40,142)(43,356)(46,131)(48,323)(49,305)(50,189)(51,203)
   (53,58)(54,389)(55,299)(56,364)(57,380)(60,100)(61,415)(62,394)(63,386)
   (64,293)(65,366)(66,495)(67,349)(68,442)(69,428)(70,266)(71,421)(74,336)
   (75,184)(77,244)(79,119)(80,211)(82,315)(84,441)(86,212)(87,109)(88,200)
   (89,146)(91,376)(92,254)(95,322)(96,160)(97,280)(98,434)(99,215)(101,446)
   (102,486)(104,470)(105,159)(107,370)(108,452)(110,196)(111,197)(112,116)
   (113,152)(114,313)(115,158)(117,472)(120,214)(121,272)(123,261)(124,476)
   (125,411)(126,458)(127,447)(128,374)(130,330)(135,190)(138,350)(139,467)
   (140,147)(143,270)(144,387)(145,298)(148,403)(150,177)(151,465)(154,378)
   (156,321)(161,328)(162,392)(164,412)(167,429)(168,352)(169,327)(171,391)
   (173,301)(176,181)(178,416)(182,262)(183,450)(187,239)(188,357)(192,304)
   (193,490)(198,344)(199,308)(204,371)(208,462)(210,335)(213,223)(216,385)
   (218,397)(222,290)(225,493)(226,314)(228,461)(231,382)(233,306)(235,388)
   (236,289)(238,399)(242,250)(243,475)(245,425)(247,427)(249,423)(253,307)
   (256,395)(257,263)(259,401)(260,297)(268,345)(269,332)(273,295)(277,381)
   (278,320)(279,365)(282,390)(283,351)(284,348)(285,480)(286,485)(291,431)
   (292,408)(300,464)(303,373)(311,413)(312,414)(316,343)(317,353)(324,477)
   (325,438)(329,339)(331,354)(333,491)(338,359)(347,473)(360,436)(363,492)
   (372,400)(375,402)(379,481)(383,384)(404,468)(406,437)(407,443)(418,439)
   (419,474)(426,479)(433,457)(444,469)(449,483)(454,494)(471,489) #CAST S
    ;
  b:=(1,311,430,135,279)(2,77,114,162,15)(3,238,301,416,352)(4,278,239,269,468)
   (5,285,391,444,125)(6,277,109,221,334)(7,471,168,460,388)(8,103,408,451,126)
   (9,372,392,41,421)(10,18,134,394,183)(11,448,107,390,483)(12,24,396,470,442)
   (13,332,219,330,263)(14,40,252,469,178)(16,398,118,389,461)
   (17,196,210,61,331)(19,170,203,486,324)(20,271,39,59,150)(21,99,419,234,139)
   (22,105,276,60,307)(23,256,83,312,289)(25,235,383,153,305)
   (26,149,138,354,491)(27,274,417,233,197)(28,217,146,264,94)
   (29,488,169,58,244)(30,374,207,447,414)(31,184,479,314,164)
   (32,253,167,224,453)(33,255,98,402,91)(34,243,361,412,124)(35,48,358,186,82)
   (36,205,328,484,299)(37,400,357,476,308)(38,463,487,436,258)
   (42,296,129,85,176)(43,49,292,490,104)(44,65,356,209,321)(45,106,410,343,200)
   (46,294,288,441,115)(47,214,477,212,397)(50,208,87,325,242)
   (51,180,245,413,418)(52,102,108,493,206)(53,432,113,190,188)
   (54,399,241,290,156)(55,228,345,204,128)(56,173,225,159,434)
   (57,462,249,350,450)(62,96,237,393,185)(63,172,443,367,440)
   (64,455,300,395,100)(66,342,143,459,297)(67,218,363,112,316)
   (68,426,427,74,320)(69,71,282,136,291)(70,456,236,355,140)
   (72,429,341,337,347)(73,229,86,131,431)(75,385,166,359,286)
   (76,272,232,376,302)(78,110,309,116,319)(79,147,489,378,268)
   (80,401,368,420,191)(81,422,454,362,201)(84,380,198,474,473)
   (88,152,267,130,445)(89,366,187,349,192)(90,339,261,384,317)
   (92,273,120,485,259)(93,310,254,122,119)(95,494,458,379,284)
   (97,313,365,265,472)(101,478,439,174,250)(111,163,175,467,405)
   (117,446,306,179,492)(121,154,182,415,160)(123,406,189,322,132)
   (127,318,144,230,303)(133,202,386,260,423)(137,227,211,213,231)
   (141,323,270,161,465)(142,360,373,195,480)(145,157,240,151,346)
   (148,435,246,247,287)(155,283,482,181,177)(158,304,220,193,293)
   (165,336,226,333,475)(171,281,348,344,375)(194,464,215,364,481)
   (199,295,275,369,433)(216,377,438,466,353)(222,326,428,409,457)
   (223,257,382,327,340)(248,338,452,411,329)(251,424,449,425,371)
   (262,298,407,351,315)(266,403,437,280,404)(335,381,495,387,370) #CAST S
    ;
  c:=(2,4)(5,7)(8,12)(10,15)(14,21)(19,27)(20,29)(22,31)(28,39)(34,47)(35,49)
   (36,51)(41,57)(46,63)(48,66)(50,69)(55,75)(58,74)(62,84)(67,91)(71,97)(72,99)
   (73,101)(77,107)(81,111)(82,113)(83,112)(86,118)(87,120)(93,127)(100,117)
   (102,139)(103,141)(105,144)(114,155)(115,156)(116,157)(122,164)(124,167)
   (126,170)(130,175)(135,150)(137,182)(140,186)(147,195)(148,151)(149,197)
   (162,210)(163,212)(165,215)(166,217)(168,221)(171,200)(172,226)(174,228)
   (176,231)(179,235)(187,243)(192,248)(193,250)(198,253)(205,257)(207,259)
   (209,262)(211,266)(213,270)(218,261)(225,286)(233,296)(234,263)(246,281)
   (249,275)(258,316)(260,320)(268,327)(271,304)(273,333)(276,314)(287,340)
   (288,343)(290,346)(291,348)(298,354)(303,310)(306,362)(308,363)(309,365)
   (313,367)(319,373)(325,378)(326,380)(328,374)(329,383)(334,388)(338,393)
   (351,404)(352,405)(353,389)(356,408)(358,401)(359,377)(361,395)(364,413)
   (369,417)(371,419)(372,407)(379,426)(398,423)(399,418)(409,446)(410,447)
   (415,450)(416,452)(427,434)(430,461)(444,471)(445,473)(458,478)(462,470)
   (464,480) #CAST S
    ;
  om102:=SubStructure(S,a,#TODO CLOSURE
    b);
  om102.Order:=25015379558400;
  # =v= MULTIASSIGN =v=
  phi:=FPGroupStrong(om102);
  F:=phi.val1;
  phi:=phi.val2;
  # =^= MULTIASSIGN =^=
  if Print > 1 then
    Print("Setting up isomorphism");
  fi;
  soc:=Socle(group);
  aut:=Index(group,soc);
  #  Find standard generators of socle
  # =v= MULTIASSIGN =v=
  bg:=get_standard_gens_om102@(soc);
  ag:=bg.val1;
  bg:=bg.val2;
  # =^= MULTIASSIGN =^=
  soc:=SubStructure(soc,ag,#TODO CLOSURE
    bg);
  soc.Order:=25015379558400;
  newgens:=[ag,bg];
  for g in Generators(group) do
    if not g in SubStructure(group,newgens) then
      Add(newgens,g);
    fi;
  od;
  group:=SubStructure(group,newgens);
  aom102:=SubStructure(S,a,#TODO CLOSURE
    b,c);
  ims:=[a,b];
  homom:=GroupHomomorphismByImages(soc,om102,
    GeneratorsOfGroup(soc),ims);
  for i in [Ngens(soc)+1..Ngens(group)] do
    g:=group.i;
    CG:=aom102;
    ce:=One(aom102);
    for j in [1..2] do
      # =v= MULTIASSIGN =v=
      h:=IsConjugate(CG,om102.j^ce,homom(soc.j^g));
      isc:=h.val1;
      h:=h.val2;
      # =^= MULTIASSIGN =^=
      if not isc then
        Error("Conjugation error in Aut(O-(10,2))");
      fi;
      CG:=Centraliser(CG,homom(soc.j^g));
      ce:=ce*h;
    od;
    Add(ims,ce);
  od;
  newgens:=ims;
  for g in Generators(aom102) do
    if not g in SubStructure(aom102,ims) then
      Add(ims,g);
    fi;
  od;
  aom102:=SubStructure(S,ims);
  homom:=GroupHomomorphismByImages(group,aom102,
    GeneratorsOfGroup(group),newgens);
  maximals:=[];
  if not max then
    return rec(val1:=homom,
      val2:=aom102,
      val3:=maximals,
      val4:=F,
      val5:=phi);
  fi;
  if Print > 1 then
    Print("getting maximals");
  fi;
  #   2^8:O-(8,2)
  M:=SubStructure(om102,a*b^-1*a*b*a,#TODO CLOSURE
    b^2*a*b^-2*a*b^-1*a*b^2*a);
  M.Order:=50536120320;
  Add(maximals,M);
  #   S(8,2)
  M:=SubStructure(om102,a,#TODO CLOSURE
    b^-2*a*b^2,b*a*b^-2*a*b*a*b^-2);
  M.Order:=47377612800;
  Add(maximals,M);
  #   2^(1+12):(U(4,2) x S3)
  M:=SubStructure(om102,a*b^-1*a*b^-1*a*b^-2*a*b^-2*a*b^-1,#TODO CLOSURE
    a*b^-2*a*b^2*a*b^-1*a*b^-1*a*b*a*b^2*a*b);
  M.Order:=1274019840;
  Add(maximals,M);
  #   (3 x O+(8,2)):2
  M:=SubStructure(om102,b^-1*a*b*a*b^-2*a*b^-1*a*b^-2*a*b^-1*a*b^2*a*b^-1,#TODO 
   CLOSURE
    b^-1*a*b^-1*a*b^-1*a*b*a*b*a*b*a*b*a*b*a*b^-1*a);
  M.Order:=1045094400;
  Add(maximals,M);
  #   2^(6+8):(3 x A8).
  M:=SubStructure(om102,a*b^-1*a*b*a*b^2*a*b*a*b^-1*a*b^-2*a*b^-1*a*b*a,#TODO 
   CLOSURE
    b*a*b^-2*a*b^-2*a*b^2*a*b*a*b^-1*a*b^-2*a*b^2*a*b*a*b*a*b^-1,
   b^-1*a*b^-1*a*b*a*b^2*a*b^-2*a*b^-1*a*b*a*b,
   b^-2*a*b^-1*a*b^-1*a*b^-2*a*b^2*a*b^-1*a*b*a*b*a);
  M.Order:=990904320;
  Add(maximals,M);
  #   2^(3+12):(L(3,2) x A5)
  M:=SubStructure(om102,b^-1*a*b^2*a*b^-2*a*b^-1*a*b^-2*a*b^-1,#TODO CLOSURE
    b^-1*a*b*a*b^-2*a*b^2*a*b*a*b*a*b^2*a);
  M.Order:=330301440;
  Add(maximals,M);
  #   A12
  M:=SubStructure(om102,b^2*a*b^-2*a*b^-1*a*b^-2*a*b^2*a*b*a,#TODO CLOSURE
    a*b^-1*a*b^-1*a*b^-2*a*b^2*a*b*a*b^2*a*b^-1*a,
   b^-1*a*b^-1*a*b^-1*a*b^-1*a*b^-1*a*b*a*b^2*a*b^-1*a*b^-1*a*b);
  M.Order:=239500800;
  Add(maximals,M);
  #   3 x U(5,2) (centralizer of (a*b)^11)
  M:=SubStructure(om102,a*b,#TODO CLOSURE
    b*a*b^-2*a*b^-2*a*b^2*a*b^2*a*b^-1);
  M.Order:=41057280;
  Add(maximals,M);
  #   (A5 x A8):2
  M:=SubStructure(om102,
   b*a*b^-1*a*b^-2*a*b*a*b*a*b*a*b^-1*a*b^-1*a*b^-1*a*b^2*a,#TODO CLOSURE
    b*a*b^-1*a*b^-1*a*b^-2*a*b^-1*a*b*a*b*a*b^-2*a*b^2*a*b*a*b^-1*a*b^-2*a);
  M.Order:=2419200;
  Add(maximals,M);
  #   (S3 x S3 x U(4,2)):2
  M:=SubStructure(om102,a*b^-2*a*b^2*a*b*a*b^-2*a*b^2*a*b^-1*a*b^-2*a*b^2*a,
   #TODO CLOSURE
    b^-1*a*b^-1*a*b^2*a*b*a*b^-2*a*b^2*a*b^-1*a*b^-2*a*b*a*b,
   b^2*a*b*a*b^-1*a*b^-2*a*b^-1*a*b^2*a*b^2*a*b^-2*a*b*a*b*a*b^2,
   b^-1*a*b^-2*a*b*a*b^-2*a*b*a*b^2*a*b^2*a*b^-2*a*b^-1*a*b^-1*a*b^-1*a*b^-1,
   a*b^-1*a*b^-1*a*b^2*a*b*a*b*a*b^2*a*b^-2*a*b^-1*a*b^-1*a*b^-2*a*b*a*b*a);
  M.Order:=1866240;
  Add(maximals,M);
  #   3^5:2^4:S5
  M:=SubStructure(om102,
   a*b^-2*a*b*a*b*a*b*a*b^-1*a*b^-1*a*b^-2*a*b^-2*a*b^-1*a*b^2*a*b^-2*a*b*a*b^2*\
a*b*a*b^2*a,#TODO CLOSURE

       b*a*b*a*b^-1*a*b^-1*a*b^-2*a*b^-2*a*b^2*a*b^2*a*b*a*b*a*b^-1*a*b^-1,
   a*b*a*b^-1*a*b^-1*a*b*a*b*a*b^-1*a*b^-2*a*b^2*a*b*a*b^-1*a*b^-2*a*b*a*b,
   b*a*b^-1*a*b^2*a*b*a*b^-2*a*b^-2*a*b^2*a*b^2*a*b^-1*a*b^-2*a*b*a*b^-1);
  M.Order:=466560;
  Add(maximals,M);
  if aut=2 then
    #   add novelty
    #   M12:2 (intersection with simple is M12, contained in an A12)
    M:=SubStructure(om102,
     b^-1*a*b*a*b^-2*a*b^-2*a*b^2*a*b*a*b^2*a*b^-1*a*b^-1*a*b*a,#TODO CLOSURE
      a*b^2*a*b^2*a*b^-1*a*b^2*a*b^2*a*b^-2*a*b^2*a*b*a*b^-1*a*b^-2*a,
     b^2*a*b^-1*a*b^2*a*b^-1*a*b^-1*a*b*a*b*a*b*a*b^-1*a*b^-1*a*b*a*b*a*b^-1*a*b\
^-2*a*b^-1);

         M.Order:=95040;
    Add(maximals,M);
  fi;
  return rec(val1:=homom,
    val2:=aom102,
    val3:=maximals,
    val4:=F,
    val5:=phi);
end);


