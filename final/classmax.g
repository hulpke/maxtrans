#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: ActionGroup, Append, ChevalleyGroup, Constituents,
#  CorrectForm, Degree, Dimension, Divisors, Dual, Exclude, Factorisation, G2,
#  GCD, GConjugates, GF, GL, GModule, GOMinus, GOPlus, GetLibraryRoot,
#  Integers, IsEven, IsOdd, IsPower, Order, Position, PrimitiveElement, Read,
#  Remove, SOMinus, SOPlus, ScalarMatrix, SymplecticForm, Sz, TransformForm,
#  Universe

#  Defines: ClassicalMaximals, GConjugates

GConjugates@:=function(S,C,r)
#  /out:S is a maximal subgroup of a classical group./out:The list of r
#  conjugates of S under GL/GU/GSp that are not/out:conjugates under SL/SU/Sp
#  is returned.
return List([0..r-1],i->S^(C^i));
end;
;
ClassicalMaximals@:=function(type,d,q)
#  -> ,SeqEnum  Maximal subgroups of quasisimple classical group of type ( d ,
#  q ) .
local 
   A,C,CG,CN,CS,S,S1,S2,varZ,_LR,_LRS,all,asmax,c9lib,cl,classes,d1,d2,dim,divs,
   e,ee,ex,f,fac,face,form,general,half,i,isit,isp,k,lim,m,n,nconj,normaliser,
   novelties,p,pf,primes,qq,r,rq,s,sign,sign1,special,t,trans,type,z;
  classes:=ValueOption("classes");
  if classes=fail then
    classes:=[1..9];
  fi;
  all:=ValueOption("all");
  if all=fail then
    all:=true;
  fi;
  novelties:=ValueOption("novelties");
  if novelties=fail then
    novelties:=false;
  fi;
  special:=ValueOption("special");
  if special=fail then
    special:=false;
  fi;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  normaliser:=ValueOption("normaliser");
  if normaliser=fail then
    normaliser:=false;
  fi;
  #   Maximal subgroups of quasisimple classical groups in the Aschbacher
  #  classes.
  #  * type must currently be "L", "S", "U", "O+" or "O-" (d even), or "O" (d
  #  odd)
  #  * classes must be a nonempty subset of {1..9} and signifies the
  #  * Aschbacher classes required as follows:
  #  * 1 = reducibles
  #  * 2 = imprimitives
  #  * 3 = semiliear (superfield)
  #  * 4 = tensor product
  #  * 5 = subfield
  #  * 6 = normalizer of symplectic-types/extraspecials
  #  * 7 = tensor induced
  #  * 8 = classicals
  #  * 9 = non-classical almost simples
  #  *
  #  * Class 9 only works up to dimension 11 at present
  #  *
  #  * if `novelties' is true, then only the Novelty subgroups (see ATLAS for
  #  * definition) under the appropriate outer automorphisms are returned.
  #  *
  #  * if `all' is true, then conjugacy class representatives in the perfect
  #  * classical group are returned - otherwise, representatives up to
  #  * conjugacy in the automorphism group are returned.
  #  *
  #  * By default, the subgroup of the relevant quasisimple group is returned.
  #  * If special is true (case O only), normaliser in SO is returned.
  #  * If general is true (cases L/U/O), normaliser in GL, GU, GO is returned.
  #  * If normaliser is true (cases Sp/U/O) normaliser in GL is returned.
  
  if type<>"L" and type<>"S" and type<>"U" and type<>"O+" and type<>"O-" and 
     type<>"O" then
    Print("<type> must be \"L\" (linear), \"S\" (symplectic), \"U\" (unitary),")
     ;
    Print("\"O+\", \"O-\", or \"O\" (orthogonal).");
    Error("");
  fi;
  if (type="L" and d < 2) or (type<>"L" and d < 3) then
    Error("dimension <d> is too small");
  fi;
  if (type="L" and d=2 and q <= 3) then
    Error("L(2,2) and L(2,3) are solvable");
  fi;
  if (type="O" and d=3 and q <= 3) then
    Error("O(3,2) and O(3,3) are solvable");
  fi;
  if (type="U" and d=3 and q=2) then
    Error("U(3,2) is solvable");
  fi;
  if type="S" and d=4 and q=2 then
    Error("Sp(4,2) is not quasisimple");
  fi;
  if type="O" then
    if IsEvenInt(d) then
      Error("Degree must be odd for type \"O\"");
    fi;
    sign:=0;
  fi;
  if type="O+" or type="O-" then
    if IsOddInt(d) then
      Error("Degree must be even for type \"O+\" or \"O-\"");
    fi;
    if type="O+" then
      if d=4 then
        Error("O^+(4,q) is not quasisimple");
      fi;
      sign:=1;
    else
      sign:=-1;
    fi;
    type:="O";
  fi;
  if Universe(classes)<>Integers() or not IsSubset([1..9],classes) then
    Error("<classes> must be a subset of {1..9}");
  fi;
  if 9 in classes and d > 12 then
    Info(InfoWarning,1,
      "*WARNING*: Aschbacher Class 9 subgroups are not returned for dimensions")
     ;
    Info(InfoWarning,1,
      "greater than 12. List of subgroups will be incomplete.");
  fi;
  if normaliser or general and type="L" then
    general:=true;
    normaliser:=true;
    #   avoids a few problems e.g. SL2 fixes symplectic form.
  fi;
  if Size(Collected(Factors(q)))<>1 then
    Error("<q> must be a prime power");
  fi;
  # rewritten select statement
  if type="U" then
    qq:=q^2;
  else
    qq:=q;
  fi;
  #  makes life easier!
  z:=PrimitiveElement(GF(qq));
  fac:=Collected(Factors(q));
  p:=fac[1][1];
  e:=fac[1][2];
  # rewritten select statement
  if type="U" then
    ee:=2*e;
  else
    ee:=e;
  fi;
  #  Make matrix C form making conjugates of subgroups under GL/GU/GSp
  if type="L" then
    C:=GLMinusSL@(d,qq);
  elif type="U" then
    C:=GUMinusSU@(d,q);
  elif type="S" then
    C:=NormSpMinusSp@(d,qq);
  else
    CS:=SOMinusOmega@(d,qq,sign);
    if IsOddInt(q) then
      CG:=GOMinusSO@(d,qq,sign);
      if IsEvenInt(d) then
        CN:=NormGOMinusGO@(d,qq,sign);
      fi;
    fi;
  fi;
  asmax:=[];
  # c9lib:=Concatenation(GetLibraryRoot(),"/c9lattices/"); # TODO Fix this
  for cl in classes do
    if cl=1 then
      if type="L" then
        if novelties then
          for i in [1..QuoInt((d-1),2)] do
            Add(asmax,SLStabOfNSpaceMeetDual@(d,q,i:general:=general));
            Add(asmax,SLStabOfNSpaceMissDual@(d,q,i:general:=general));
          od;
        else
          # rewritten select statement
          if all then
            lim:=d-1;
          else
            lim:=QuoInt(d,2);
          fi;
          for i in [1..lim] do
            if general then
              Add(asmax,GLStabOfNSpace@(d,q,i));
            else
              Add(asmax,SLStabOfNSpace@(d,q,i));
            fi;
          od;
        fi;
#     elif type="S" then
#       if d=4 and IsEvenInt(q) and novelties then
#         asmax:=Concatenation(asmax,[NoveltyReduct@(q:normaliser:=normaliser)])
#          ;
#       elif not novelties then
#         if d=4 and IsEvenInt(q) and not all then
#           Add(asmax,PointStabSp@(d,q:normaliser:=normaliser));
#           #  for d=4, q even, PointStabSp(d, q) and IsotropicStabSp(d, q, 2)
#           #  are conjugate under the graph automorphism
#         else
#           Add(asmax,PointStabSp@(d,q:normaliser:=normaliser));
#           half:=QuoInt(d,2);
#           for i in [2..half] do
#             Add(asmax,IsotropicStabSp@(d,q,i:normaliser:=normaliser));
#           od;
#           for i in [2..half-1] do
#             if IsEvenInt(i) then
#               Add(asmax,SymplecticStab@(d,q,i:normaliser:=normaliser));
#             fi;
#           od;
#         fi;
#       fi;
#     elif type="U" and not novelties then
#       for i in [1..QuoInt(d,2)] do
#         Add(asmax,IsotropKStab@(d,q,i:general:=general,normaliser:=normaliser)
#          );
#       od;
#       for i in [1..QuoInt((d-1),2)] do
#         Add(asmax,NonisotropKStab@(d,q,i:general:=general,
#          normaliser:=normaliser));
#       od;
#     elif type="O" then
#       half:=QuoInt(d,2);
#       if novelties then
#         if d=3 and q in Set([7,9,11]) then
#           Add(asmax,NonDegenStabOmega@(d,q,sign,2,1:special:=special,
#            general:=general,normaliser:=normaliser));
#           if q<>11 then
#             Add(asmax,NonDegenStabOmega@(d,q,sign,2,-1:special:=special,
#              general:=general,normaliser:=normaliser));
#           fi;
#         fi;
#         if IsEvenInt(d) then
#           if sign=1 then
#             Add(asmax,IsotropicStabOmega@(d,q,half-1,sign:special:=special,
#              general:=general,normaliser:=normaliser));
#           fi;
#           if q=3 then
#             Add(asmax,NonDegenStabOmega@(d,q,sign,2,1:special:=special,
#              general:=general,normaliser:=normaliser));
#           fi;
#         fi;
#         if d=8 and sign=1 then
#           Add(asmax,KlLine4@(q:special:=special,general:=general,
#            normaliser:=normaliser));
#           S:=KlLine7@(q:special:=special,general:=general,
#            normaliser:=normaliser);
#           if all then
#             if IsOddInt(q) then
#               asmax:=Concatenation(asmax,[S,S^CG]);
#             else
#               asmax:=Concatenation(asmax,[S,S^CS]);
#             fi;
#           else
#             Add(asmax,S);
#           fi;
#           S:=KlLine15@(q:special:=special,general:=general,
#            normaliser:=normaliser);
#           if all and IsOddInt(q) then
#             asmax:=Concatenation(asmax,[S,S^CS,S^CN,S^(CS*CN)]);
#           else
#             Add(asmax,S);
#           fi;
#           Add(asmax,KlLine22@(q:special:=special,general:=general,
#            normaliser:=normaliser));
#           Add(asmax,KlLine26@(q:special:=special,general:=general,
#            normaliser:=normaliser));
#         fi;
#         continue;
#       fi;
#       for i in [1..half] do
#         if (i=half-1 and sign=1) or (i=half and sign=-1) then
#           #  KL <= P_{n/2}
#           continue;
#         fi;
#         S:=IsotropicStabOmega@(d,q,i,sign:special:=special,general:=general,
#          normaliser:=normaliser);
#         Add(asmax,S);
#         if sign=1 and i=half and all then
#           #  c=2
#           if IsEvenInt(q) then
#             Add(asmax,S^CS);
#           else
#             Add(asmax,S^CG);
#           fi;
#         fi;
#       od;
#       if IsOddInt(d) then
#         for i in [2,2+2..d-1] do
#           if i > 2 or q > 3 then
#             if d > 3 or q > 11 then
#               Add(asmax,NonDegenStabOmega@(d,q,sign,i,1:special:=special,
#                general:=general,normaliser:=normaliser));
#             fi;
#           fi;
#           if (d > 3 or not q in Set([7,9])) and (d<>5 or i<>2 or q<>3) then
#             Add(asmax,NonDegenStabOmega@(d,q,sign,i,-1:special:=special,
#              general:=general,normaliser:=normaliser));
#           fi;
#         od;
#       else
#         #  d even
#         for i in [1..half] do
#           if IsEvenInt(i) then
#             if sign=1 then
#               if i<>half then
#                 #  else in imprimitive group
#                 if i > 2 or q > 3 then
#                   Add(asmax,NonDegenStabOmega@(d,q,sign,i,1:special:=special,
#                    general:=general,normaliser:=normaliser));
#                 fi;
#                 if d<>8 or i<>2 or all then
#                   #  conj to IsotropicStabOmega(8, q, 4, 1) when d=8, i=2
#                   #  under graph automorphism
#                   Add(asmax,NonDegenStabOmega@(d,q,sign,i,-1:special:=special,
#                    general:=general,normaliser:=normaliser));
#                 fi;
#               fi;
#             else
#               #  sign = -1
#               if i > 2 or q > 3 or (d=4 and q=2) then
#                 Add(asmax,NonDegenStabOmega@(d,q,sign,i,1:special:=special,
#                  general:=general,normaliser:=normaliser));
#               fi;
#               if i<>half then
#                 if d<>6 or q<>2 then
#                   Add(asmax,NonDegenStabOmega@(d,q,sign,d-i,
#                    1:special:=special,general:=general,normaliser:=normaliser)
#                    );
#                 fi;
#               fi;
#             fi;
#           else
#             #  i odd
#             if IsOddInt(q) and i<>half then
#               S:=NonDegenStabOmega@(d,q,sign,d-i,0:special:=special,
#                general:=general,normaliser:=normaliser);
#               Add(asmax,S);
#               if all then
#                 Add(asmax,S^CN);
#               fi;
#             fi;
#           fi;
#         od;
#       fi;
#       if IsEvenInt(d) and IsEvenInt(q) then
#         Add(asmax,NSPointStabOmega@(d,q,sign:special:=special,
#          normaliser:=normaliser));
#       fi;
      fi;
    elif cl=2 then
      if type="L" then
        if novelties then
          if (d=2 and q in Set([7,9,11])) then
            Add(asmax,ImprimsMeetSL@(d,q,d:general:=general));
          fi;
          if d=4 and q=3 then
            Add(asmax,ImprimsMeetSL@(d,q,2:general:=general));
          fi;
          if d=4 and q=5 then
            Add(asmax,ImprimsMeetSL@(d,q,4:general:=general));
          fi;
          continue;
        fi;
        divs:=DivisorsInt(d);
        RemoveSet(divs,1);
        for t in divs do
          if (t=d and q <= 4) or (t=QuoInt(d,2) and q <= 2) then
            continue;
            #  not maximal - in C1 or C8 group - KL
            #  For SL(3,3) - C2 group = C8 group
          fi;
          if (d=2 and q in Set([5,7,9,11])) or (d=3 and q in Set([2,4])) or 
             (d=4 and t=2 and q=3) or (d=4 and t=4 and q=5) then
            continue;
            #  small exceptions
          fi;
          Add(asmax,ImprimsMeetSL@(d,q,t:general:=general));
        od;
#     elif type="S" then
#       if d=4 and q mod 2=0 then
#         if novelties then
#           # =v= MULTIASSIGN =v=
#           S2:=NoveltyImprims@(q:normaliser:=normaliser);
#           S1:=S2.val1;
#           S2:=S2.val2;
#           # =^= MULTIASSIGN =^=
#           if q<>4 then
#             Add(asmax,S1);
#           fi;
#           Add(asmax,S2);
#         else
#           Add(asmax,GetSympImprimsD4@(q));
#         fi;
#       elif d=4 then
#         if novelties then
#           continue;
#         fi;
#         # =v= MULTIASSIGN =v=
#         S2:=GetSympImprimsD4@(q);
#         S1:=S2.val1;
#         S2:=S2.val2;
#         # =^= MULTIASSIGN =^=
#         Add(asmax,S1);
#         if q=3 then
#           continue;
#         fi;
#         #  small exception
#         Add(asmax,S2);
#       else
#         divs:=Filtered(DivisorsInt(d),x->x > 1 and IsEvenInt(QuoInt(d,x)));
#         for n in divs do
#           if q=2 and QuoInt(d,n)=2 then
#             #  otherwise orthogonal (KL)
#             continue;
#           fi;
#           Add(asmax,GetWreathProd@(d,q,n));
#         od;
#         if IsOddInt(q) then
#           #  Colva and KL have this - o.w. group is orthogonal
#           Add(asmax,GetStabOfHalf@(d,q));
#         fi;
#       fi;
#     elif type="U" then
#       if novelties then
#         if (d=4 and q=3) then
#           Add(asmax,StandardUnitImps@(d,q,1:general:=general,
#            normaliser:=normaliser));
#           Add(asmax,UnitImpHalfDim@(d,q));
#         elif (d=6 and q=2) or (d=3 and q=5) then
#           Add(asmax,StandardUnitImps@(d,q,1:general:=general,
#            normaliser:=normaliser));
#         fi;
#         continue;
#       fi;
#       divs:=DivisorsInt(d);
#       RemoveSet(divs,1);
#       for t in divs do
#         if t=QuoInt(d,2) and q=2 then
#           continue;
#           #  not maximal - in C2 group with t=d  - KL
#         fi;
#         if (d=3 and d=t and q=5) or (d=4 and d=t and q=3) or (d=6 and d=t and 
#            q=2) then
#           continue;
#           #  small exceptions
#         fi;
#         Add(asmax,StandardUnitImps@(d,q,QuoInt(d,t)
#          :general:=general,normaliser:=normaliser));
#       od;
#       if d mod 2=0 then
#         if (d=4 and q <= 3) then
#           continue;
#           #  small exception
#         fi;
#         Add(asmax,UnitImpHalfDim@(d,q:general:=general,normaliser:=normaliser)
#          );
#       fi;
#     elif type="O" then
#       if novelties then
#         if sign=(-1)^(QuoInt(d,2)) and q=3 then
#           Add(asmax,OrthImprim@(d,q,sign,2,-1:special:=special,
#            general:=general,normaliser:=normaliser));
#         elif sign=1 and q=5 then
#           Add(asmax,OrthImprim@(d,q,sign,2,1:special:=special,
#            general:=general,normaliser:=normaliser));
#         fi;
#         if sign=1 and d mod 4=2 then
#           Add(asmax,OrthStabOfHalfTS@(d,q:special:=special,general:=general,
#            normaliser:=normaliser));
#         fi;
#         if d=3 and p mod 5 in Set([1,4]) and p mod 8 in Set([3,5]) then
#           Add(asmax,OrthImprim@(d,q,0,1,0:special:=special,general:=general,
#            normaliser:=normaliser));
#         fi;
#         if sign=1 and d=8 then
#           if q=3 then
#             S:=OrthStabOfHalfTS@(d,q:special:=special,general:=general,
#              normaliser:=normaliser);
#             if all then
#               asmax:=Concatenation(asmax,[S,S^CG]);
#             else
#               Add(asmax,S);
#             fi;
#           fi;
#           if IsOddInt(q) and e=1 then
#             if p mod 8 in Set([3,5]) then
#               S:=OrthImprim@(d,q,sign,1,0:special:=special,general:=general,
#                normaliser:=normaliser);
#               if all then
#                 asmax:=Concatenation(asmax,[S,S^CN]);
#               else
#                 Add(asmax,S);
#               fi;
#             fi;
#             S:=KlLine51@(q:special:=special,general:=general,
#              normaliser:=normaliser);
#             if all then
#               asmax:=Concatenation(asmax,[S,S^CS,S^CN,S^(CS*CN)]);
#             else
#               Add(asmax,S);
#             fi;
#           fi;
#           Add(asmax,KlLine61@(q:special:=special,general:=general,
#            normaliser:=normaliser));
#         fi;
#         continue;
#       fi;
#       divs:=DivisorsInt(d);
#       RemoveSet(divs,1);
#       for t in divs do
#         k:=QuoInt(d,t);
#         if IsEvenInt(k) then
#           sign1:=1;
#           if sign=sign1^t then
#             if (k<>2 or q > 5) and (k<>4 or q<>2) then
#               #  KL
#               Add(asmax,OrthImprim@(d,q,sign,k,sign1:special:=special,
#                general:=general,normaliser:=normaliser));
#             fi;
#           fi;
#           sign1:=-1;
#           if sign=sign1^t then
#             if (k<>2 or q<>3) then
#               #  KL
#               Add(asmax,OrthImprim@(d,q,sign,k,sign1:special:=special,
#                general:=general,normaliser:=normaliser));
#             fi;
#           fi;
#         else
#           #  k odd
#           if IsEvenInt(q) then
#             continue;
#           fi;
#           if k=1 and (e<>1 or (d=3 and p mod 5 in Set([1,4]) and p mod 8 in 
#              Set([3,5]))) then
#             continue;
#           fi;
#           if q=3 and k=3 then
#             continue;
#           fi;
#           #  KL
#           if IsEvenInt(t) then
#             ex:=d mod 4=2 and q mod 4=3;
#             #  D non-square
#             if (ex and sign=-1) or (not ex and sign=1) then
#               S:=OrthImprim@(d,q,sign,k,0:special:=special,general:=general,
#                normaliser:=normaliser);
#               if not all then
#                 Add(asmax,S);
#               elif k=1 then
#                 if q mod 8 in Set([1,7]) then
#                   #  c=4
#                   asmax:=Concatenation(asmax,[S,S^CS,S^CN,S^(CS*CN)]);
#                 elif d<>8 then
#                   #  q =3,5 mod 8, c=2
#                   #  in O_8(2) when d=8
#                   asmax:=Concatenation(asmax,[S,S^CN]);
#                 fi;
#               else
#                 if IsEvenInt(t) then
#                   asmax:=Concatenation(asmax,[S,S^CN]);
#                 else
#                   Add(asmax,S);
#                 fi;
#               fi;
#             fi;
#           else
#             #  k, t odd
#             S:=OrthImprim@(d,q,sign,k,0:special:=special,general:=general,
#              normaliser:=normaliser);
#             Add(asmax,S);
#             if all and k=1 and q mod 8 in Set([1,7]) then
#               #  c=2
#               Add(asmax,S^CS);
#             fi;
#           fi;
#         fi;
#       od;
#       if IsEvenInt(d) then
#         if sign=1 and d mod 4=0 then
#           #  reducible if d mod 4 eq 2
#           S:=OrthStabOfHalfTS@(d,q:special:=special,general:=general,
#            normaliser:=normaliser);
#           #  c=2
#           Add(asmax,S);
#           if all then
#             if IsEvenInt(q) then
#               Add(asmax,S^CS);
#             else
#               Add(asmax,S^CG);
#             fi;
#           fi;
#         fi;
#         if IsOddInt(q) and d mod 4=2 then
#           if (q mod 4=1 and sign=-1) or (q mod 4=3 and sign=1) then
#             Add(asmax,OrthStabOfHalfND@(d,q:special:=special,general:=general,
#              normaliser:=normaliser));
#           fi;
#         fi;
#       fi;
      fi;
    elif cl=3 then
      if type="L" then
        if novelties then
          if (d=2 and q in Set([7,9])) or (d=3 and q=4) then
            if general then
              Add(asmax,GammaL@(d,q,d));
            else
              Add(asmax,GammaLMeetSL@(d,q,d));
            fi;
          fi;
          continue;
        fi;
        primes:=List(Collected(Factors(d)),f->f[1]);
        if (d=2 and q in Set([7,9])) or (d=3 and q=4) then
          continue;
          #  small exceptions
        fi;
        for s in primes do
          if general then
            Add(asmax,GammaL@(d,q,s));
          else
            Add(asmax,GammaLMeetSL@(d,q,s));
          fi;
        od;
#     elif type="S" then
#       if d=4 and q mod 2=0 and novelties then
#         Add(asmax,NoveltySemilin@(q:normaliser:=normaliser));
#       else
#         if novelties then
#           continue;
#         fi;
#         primes:=List(Collected(Factors(d)),f->f[1]);
#         for s in primes do
#           if IsEvenInt(QuoInt(d,s)) then
#             Add(asmax,GammaSp@(d,q,s:normaliser:=normaliser));
#           fi;
#         od;
#         if d=4 and q=3 then
#           continue;
#           #  small exceptions
#         fi;
#         #  KL has q odd here - o.w. group is orthogonal
#         if IsOddInt(q) then
#           Add(asmax,GammaUMeetSp@(d,q:normaliser:=normaliser));
#         fi;
#       fi;
#     elif type="U" then
#       if novelties then
#         if (d=6 and q=2) or (d=3 and q=5) then
#           Add(asmax,GammaSU@(d,q,3:general:=general,normaliser:=normaliser));
#         fi;
#         continue;
#       fi;
#       if (d=3 and q in Set([3,5])) or (d in Set([5,6]) and q=2) then
#         continue;
#         #  small exceptions
#       fi;
#       primes:=List(Collected(Factors(d)),f->f[1]);
#       for s in primes do
#         if s<>2 then
#           #  s=2 doesn't give subgroup
#           Add(asmax,GammaSU@(d,q,s:general:=general,normaliser:=normaliser));
#         fi;
#       od;
#     elif type="O" then
#       if novelties then
#         if d=4 and q=3 and sign=-1 then
#           Add(asmax,GammaOdimEven@(d,q,sign:special:=special,general:=general,
#            normaliser:=normaliser));
#         fi;
#         continue;
#       fi;
#       primes:=List(Collected(Factors(d)),f->f[1]);
#       for s in primes do
#         dim:=QuoInt(d,s);
#         if dim <= 2 and (d<>4 or sign<>-1 or q=3) then
#           continue;
#         fi;
#         if s=2 then
#           if IsEvenInt(dim) then
#             if d<>8 or sign<>1 or all then
#               #  if d=8, sign=1, then GammaOdimEven(d, q, sign) and
#               #  GammaUMeetOmega(d, q)
#               #  are conj to O-(4,q)wr2 and O-(2,q) x O-(6,q) under graph
#               #  automorphism
#               S:=GammaOdimEven@(d,q,sign:special:=special,general:=general,
#                normaliser:=normaliser);
#               Add(asmax,S);
#               if all and sign=1 then
#                 #  c=2
#                 if IsEvenInt(q) then
#                   Add(asmax,S^CS);
#                 else
#                   Add(asmax,S^CG);
#                 fi;
#               fi;
#               if sign=1 then
#                 S:=GammaUMeetOmega@(d,q:special:=special,general:=general,
#                  normaliser:=normaliser);
#                 Add(asmax,S);
#                 if all then
#                   #  c=2
#                   if IsEvenInt(q) then
#                     Add(asmax,S^CS);
#                   else
#                     Add(asmax,S^CG);
#                   fi;
#                 fi;
#               fi;
#             fi;
#           else
#             if IsOddInt(q) then
#               #  KL - qm odd r=2
#               S:=GammaOdimOdd@(d,q,sign:special:=special,general:=general,
#                normaliser:=normaliser);
#               Add(asmax,S);
#               if all then
#                 if (sign=1 and q mod 4=1) or (sign=-1 and q mod 4=3) then
#                   #  c=2
#                   Add(asmax,S^CG);
#                 fi;
#               fi;
#             fi;
#             if sign=-1 then
#               Add(asmax,GammaUMeetOmega@(d,q:special:=special,
#                general:=general,normaliser:=normaliser));
#             fi;
#           fi;
#         else
#           Add(asmax,GammaOsOdd@(d,q,s,sign:special:=special,general:=general,
#            normaliser:=normaliser));
#         fi;
#       od;
      fi;
#   elif cl=4 then
#     if type="L" then
#       if novelties then
#         continue;
#       fi;
#       #  t = d div t contained in C7
#       divs:=Filtered(DivisorsInt(d),t->t<>1 and t < QuoInt(d,t));
#       #  KL excludes d1=q=2. in GL_{n/2}(4)
#       if q=2 and Position(divs,2) > 0 then
#         Remove(divs,Position(divs,2));
#       fi;
#       if all then
#         for t in divs do
#           nconj:=Gcd([q-1,t,QuoInt(d,t)]);
#           S:=SLTensor@(t,QuoInt(d,t),q:general:=general);
#           asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#         od;
#       else
#         asmax:=Concatenation(asmax,List(divs,t->SLTensor@(t,QuoInt(d,t)
#          ,q:general:=general)));
#       fi;
#     elif type="S" and IsOddInt(q) then
#       #  q even doesn't seem to give a subgroup at all
#       if novelties then
#         continue;
#       fi;
#       divs:=Filtered(DivisorsInt(d),t->IsEvenInt(t) and QuoInt(d,t) > 2);
#       #  KL excludes d2=q=3 imprimitive? always non maximal
#       #  KL excludes d2=2 - imprimitive or semilinear?
#       if q=3 and d mod 3=0 and Position(divs,QuoInt(d,3)) > 0 then
#         Remove(divs,Position(divs,QuoInt(d,3)));
#       fi;
#       #  always c=1
#       for t in divs do
#         if IsEvenInt(QuoInt(d,t)) then
#           # =v= MULTIASSIGN =v=
#           S2:=SpTensors@(t,QuoInt(d,t),q:normaliser:=normaliser);
#           S1:=S2.val1;
#           S2:=S2.val2;
#           # =^= MULTIASSIGN =^=
#           #  for d=8 SO+(4,q)xSp(2,q) <= C7 group
#           if d=8 then
#             Add(asmax,S2);
#           else
#             asmax:=Concatenation(asmax,[S1,S2]);
#           fi;
#         else
#           Add(asmax,SpTensors@(t,QuoInt(d,t),q:normaliser:=normaliser));
#         fi;
#       od;
#     elif type="U" then
#       if novelties then
#         continue;
#       fi;
#       #  t = d div t contained in C7
#       divs:=Filtered(DivisorsInt(d),t->t<>1 and t < QuoInt(d,t));
#       if q=2 and Position(divs,2) > 0 then
#         #  KL- in C2 group
#         Remove(divs,Position(divs,2));
#       fi;
#       if all then
#         for t in divs do
#           nconj:=Gcd([q+1,t,QuoInt(d,t)]);
#           S:=SUTensor@(t,QuoInt(d,t)
#            ,q:general:=general,normaliser:=normaliser);
#           asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#         od;
#       else
#         asmax:=Concatenation(asmax,List(divs,t->SUTensor@(t,QuoInt(d,t)
#          ,q:general:=general,normaliser:=normaliser)));
#       fi;
#     elif type="O" then
#       if novelties then
#         if sign=1 and IsOddInt(q) and d mod 4=0 and d > 8 then
#           d1:=4;
#           d2:=QuoInt(d,4);
#           if IsOddInt(d2) then
#             if d2<>3 or q<>3 then
#               #  KL
#               Add(asmax,OrthTensorEvenOdd@(d1,d2,q,1:special:=special,
#                general:=general,normaliser:=normaliser));
#             fi;
#           else
#             #  c=2
#             if q mod 4=3 and d2 mod 4=2 then
#               S:=OrthTensorEvenEven@(d1,d2,q,1,1:special:=special,
#                general:=general,normaliser:=normaliser);
#             else
#               S:=OrthTensorEvenEven@(d1,d2,q,1,-1:special:=special,
#                general:=general,normaliser:=normaliser);
#             fi;
#             Add(asmax,S);
#             if all then
#               Add(asmax,S^CG);
#             fi;
#           fi;
#         fi;
#         continue;
#       fi;
#       divs:=Filtered(DivisorsInt(d),t->t<>1 and t <= QuoInt(d,t));
#       for t in divs do
#         d1:=t;
#         d2:=QuoInt(d,t);
#         if sign=1 and IsEvenInt(d1) and IsEvenInt(d2) and d1 < d2 then
#           if q=2 and d1=2 then
#             #  KL
#             continue;
#           fi;
#           if d1=2 and d2=4 and (not all or IsEvenInt(q)) then
#             #  if d=8, OrthSpTensor(2, 4, q) conjugate to O(3,q)xO(5,q) under
#             #  graph auto
#             #  if q even OrthSpTensor(2, 4, q) <= irrecucible Sp(6,q)
#             continue;
#           fi;
#           S:=OrthSpTensor@(d1,d2,q:special:=special,general:=general,
#            normaliser:=normaliser);
#           if not all then
#             Add(asmax,S);
#           elif IsOddInt(q) and d mod 8=0 then
#             #  c=4
#             asmax:=Concatenation(asmax,[S,S^CS,S^CG,S^(CS*CG)]);
#           else
#             #  c=2
#             if IsEvenInt(q) then
#               asmax:=Concatenation(asmax,[S,S^CS]);
#             else
#               asmax:=Concatenation(asmax,[S,S^CG]);
#             fi;
#           fi;
#         fi;
#         if IsEvenInt(q) or d1 <= 2 then
#           continue;
#         fi;
#         if IsOddInt(d1) and IsOddInt(d2) and d1 < d2 then
#           if d1=3 and q=3 then
#             continue;
#           fi;
#           #  KL
#           Add(asmax,OrthTensorOddOdd@(d1,d2,q:special:=special,
#            general:=general,normaliser:=normaliser));
#         elif IsOddInt(d1) and IsEvenInt(d2) then
#           if d1=3 and q=3 then
#             continue;
#           fi;
#           #  KL
#           if d2=4 and sign=1 then
#             continue;
#           fi;
#           #  KL
#           Add(asmax,OrthTensorEvenOdd@(d2,d1,q,sign:special:=special,
#            general:=general,normaliser:=normaliser));
#         elif IsEvenInt(d1) and IsOddInt(d2) then
#           if d1=4 and sign=1 then
#             continue;
#           fi;
#           #  KL
#           Add(asmax,OrthTensorEvenOdd@(d1,d2,q,sign:special:=special,
#            general:=general,normaliser:=normaliser));
#         elif sign=1 then
#           #  d1, d2 even, sign always 1
#           if d1 < d2 then
#             S:=OrthTensorEvenEven@(d1,d2,q,-1,-1:special:=special,
#              general:=general,normaliser:=normaliser);
#             #  c=2
#             Add(asmax,S);
#             if all then
#               Add(asmax,S^CG);
#             fi;
#             S:=OrthTensorEvenEven@(d1,d2,q,1,1:special:=special,
#              general:=general,normaliser:=normaliser);
#             if (q mod 4=3 and (d1 mod 4=2 or d2 mod 4=2)) or d mod 8=4 then
#               #  c=2
#               if d1 > 4 then
#                 #  KL
#                 if all then
#                   asmax:=Concatenation(asmax,[S,S^CG]);
#                 else
#                   Add(asmax,S);
#                 fi;
#               fi;
#             else
#               #  c=4
#               if all then
#                 asmax:=Concatenation(asmax,[S,S^CS,S^CG,S^(CS*CG)]);
#               else
#                 Add(asmax,S);
#               fi;
#             fi;
#           fi;
#           S:=OrthTensorEvenEven@(d1,d2,q,1,-1:special:=special,
#            general:=general,normaliser:=normaliser);
#           if q mod 4=3 and d1 mod 4=0 and d2 mod 4=2 then
#             #  c=4
#             if all then
#               asmax:=Concatenation(asmax,[S,S^CS,S^CG,S^(CS*CG)]);
#             else
#               Add(asmax,S);
#             fi;
#           else
#             #  c=2
#             if d1 > 4 then
#               #  KL
#               if all then
#                 asmax:=Concatenation(asmax,[S,S^CG]);
#               else
#                 Add(asmax,S);
#               fi;
#             fi;
#           fi;
#           if d1 <= d2 then
#             S:=OrthTensorEvenEven@(d2,d1,q,1,-1:special:=special,
#              general:=general,normaliser:=normaliser);
#             if q mod 4=3 and d2 mod 4=0 and d1 mod 4=2 then
#               #  c=4
#               if all then
#                 asmax:=Concatenation(asmax,[S,S^CS,S^CG,S^(CS*CG)]);
#               else
#                 Add(asmax,S);
#               fi;
#             else
#               #  c=2
#               if all then
#                 asmax:=Concatenation(asmax,[S,S^CG]);
#               else
#                 Add(asmax,S);
#               fi;
#             fi;
#           fi;
#         fi;
#         #   d1/d2 odd/even
#       od;
#       #  t in divs
#     fi;
#   elif cl=5 then
#     if novelties then
#       continue;
#     fi;
#     face:=Collected(Factors(ee));
#     #  recall q=p^e, ee=2e in type U, ee=e o.w.
#     for pf in List(face,f->f[1]) do
#       f:=QuoInt(e,pf);
#       if type="L" then
#         if d=2 and p=2 and f=1 then
#           continue;
#           #  small exception
#         fi;
#         S:=SubfieldSL@(d,p,e,f:general:=general);
#         if all then
#           nconj:=Gcd(d,QuoInt((q-1),(p^f-1)));
#           asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#         else
#           Add(asmax,S);
#         fi;
#       elif type="S" then
#         S:=SubfieldSp@(d,p,e,f:normaliser:=normaliser);
#         if all then
#           nconj:=Gcd(2,QuoInt((q-1),(p^f-1)));
#           asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#         else
#           Add(asmax,S);
#         fi;
#       elif type="U" then
#         if pf<>2 then
#           #  SU(d,q) is not a subgroup of SU(d,q^2)
#           S:=SubfieldSU@(d,p,e,f:general:=general,normaliser:=normaliser);
#           if all then
#             nconj:=Gcd(d,QuoInt((q+1),(p^f+1)));
#             asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#           else
#             Add(asmax,S);
#           fi;
#         fi;
#         if pf=2 then
#           if IsOddInt(d) then
#             if all then
#               nconj:=Gcd(d,q+1);
#             fi;
#             if IsOddInt(q) then
#               #  o.w. orthogonal group reducible!
#               if d=3 and q <= 5 then
#                 continue;
#                 #  small exceptions
#               fi;
#               S:=OrthsInSU@(d,q:general:=general,normaliser:=normaliser);
#               if all then
#                 asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#               else
#                 Add(asmax,S);
#               fi;
#             fi;
#           else
#             # =v= MULTIASSIGN =v=
#             S2:=OrthsInSU@(d,q:general:=general,normaliser:=normaliser);
#             S1:=S2.val1;
#             S2:=S2.val2;
#             # =^= MULTIASSIGN =^=
#             if IsOddInt(q) then
#               #  o.w. <= SpInSU(d, q)
#               if all then
#                 nconj:=QuoInt(Gcd(d,q+1),2);
#               fi;
#               if d=4 and q=3 then
#                 #  small exception - don't want S1
#                 if all then
#                   asmax:=Concatenation(asmax,GConjugates@(S2,C,nconj));
#                 else
#                   asmax:=Concatenation(asmax,[S2]);
#                 fi;
#               elif all then
#                 asmax:=Concatenation(asmax,GConjugates@(S1,C,nconj));
#                 asmax:=Concatenation(asmax,GConjugates@(S2,C,nconj));
#               else
#                 asmax:=Concatenation(asmax,[S1,S2]);
#               fi;
#             fi;
#             S:=SpInSU@(d,q:general:=general,normaliser:=normaliser);
#             if all then
#               nconj:=Gcd(QuoInt(d,2),q+1);
#               asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#             else
#               Add(asmax,S);
#             fi;
#           fi;
#           #  if IsOdd(d)
#         fi;
#         #  pf=2
#       elif type="O" then
#         if IsOddInt(d) then
#           S:=SubfieldOdimOdd@(d,p,e,f:special:=special,general:=general,
#            normaliser:=normaliser);
#           if all and pf=2 then
#             asmax:=Concatenation(asmax,[S,S^CS]);
#           else
#             Add(asmax,S);
#           fi;
#         else
#           if pf=2 then
#             if sign=-1 then
#               continue;
#             fi;
#             if p=2 then
#               Add(asmax,SubfieldOdimEven@(d,p,e,f,1:special:=special,
#                general:=general,normaliser:=normaliser));
#               Add(asmax,SubfieldOdimEven@(d,p,e,f,-1:special:=special,
#                general:=general,normaliser:=normaliser));
#             else
#               S:=SubfieldOdimEven@(d,p,e,f,1:special:=special,
#                general:=general,normaliser:=normaliser);
#               if not all then
#                 Add(asmax,S);
#               elif (d mod 4=2 and p^f mod 4=1) then
#                 #  c=2
#                 asmax:=Concatenation(asmax,[S,S^CN]);
#               else
#                 #  c=4
#                 asmax:=Concatenation(asmax,[S,S^CS,S^CN,S^(CS*CN)]);
#               fi;
#               S:=SubfieldOdimEven@(d,p,e,f,-1:special:=special,
#                general:=general,normaliser:=normaliser);
#               if not all then
#                 Add(asmax,S);
#               elif d mod 4=0 or (d mod 4=2 and p^f mod 4=3) then
#                 #  c=2
#                 asmax:=Concatenation(asmax,[S,S^CN]);
#               else
#                 #  c=4
#                 asmax:=Concatenation(asmax,[S,S^CS,S^CN,S^(CS*CN)]);
#               fi;
#             fi;
#             #  p eq 2
#           else
#             #  pf ne 2
#             Add(asmax,SubfieldOdimEven@(d,p,e,f,sign:special:=special,
#              general:=general,normaliser:=normaliser));
#           fi;
#           #  pf=2
#         fi;
#       fi;
#       #  types
#     od;
#     #   for pf in [f[1] : f in face] do
#   elif cl=6 then
#     fac:=Collected(Factors(d));
#     if Size(fac)<>1 then
#       continue;
#     fi;
#     r:=fac[1][1];
#     if (qq-1) mod r<>0 then
#       continue;
#     fi;
#     #  Let R be the extraspecial or symplectic group normalised.
#     #  Then these groups are contained in C5 groups and hence not maximal
#     #  unless qq = p^ee, where ee is minimal subject to |Z(R)| divides qq-1.
#     #  Note |Z(R)|= r for r odd and |Z(R)|=2 or 4 for r even.
#     if IsOddInt(r) and ee<>Order(p #CAST GF(r)
#       ) then
#       continue;
#     fi;
#     if type="L" then
#       if (d=2 and q mod 40 in Set([11,19,21,29]) and not novelties) or ((d<>2 
#          or not q mod 40 in Set([11,19,21,29])) and novelties) then
#         continue;
#         #  small exceptions
#       fi;
#       if IsOddInt(r) then
#         #  note that if minimal ee defined above is even, then the group
#         #  preserves a unitary form, so is not maximal
#         if IsEvenInt(ee) then
#           continue;
#         fi;
#         S:=NormaliserOfExtraSpecialGroup@(d,qq:general:=general);
#         if all then
#           nconj:=Gcd(d,q-1);
#           if d=3 and q mod 9 in Set([4,7]) then
#             nconj:=1;
#           fi;
#           asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#         else
#           Add(asmax,S);
#         fi;
#       else
#         #  note that if minimal ee is not equal to 1, then the group
#         #  preserves a unitary form, so is not maximal
#         if ee<>1 then
#           continue;
#         fi;
#         if (qq-1) mod 4=0 and d > 2 then
#           S:=NormaliserOfSymplecticGroup@(d,qq:general:=general);
#           if all then
#             nconj:=Gcd(d,q-1);
#             if d=4 and q mod 8=5 then
#               nconj:=2;
#             fi;
#             asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#           else
#             Add(asmax,S);
#           fi;
#         fi;
#         if d=2 then
#           #  whole group if qq=3.
#           #  In fact, we probably want this for larger d whenever q mod 4 eq
#           #  2.
#           S:=NormaliserOfExtraSpecialGroupMinus@(d,qq:general:=general);
#           if all and (qq mod 8=1 or qq mod 8=7) then
#             nconj:=2;
#             asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#           else
#             Add(asmax,S);
#           fi;
#         fi;
#       fi;
#     elif type="S" then
#       if ee<>1 then
#         continue;
#       fi;
#       if novelties then
#         continue;
#       fi;
#       if IsEvenInt(d) and IsOddInt(qq) then
#         S:=NormaliserOfExtraSpecialGroupMinus@(d,qq:symplectic:=true,
#          general:=general,normaliser:=normaliser);
#         if all and (qq mod 8=1 or qq mod 8=7) then
#           nconj:=2;
#           asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#         else
#           Add(asmax,S);
#         fi;
#       fi;
#     elif type="U" then
#       if (d=3 and q=5 and not novelties) or ((d<>3 or q<>5) and novelties) 
#          then
#         continue;
#         #  small exception
#       fi;
#       if IsOddInt(r) then
#         S:=NormaliserOfExtraSpecialGroup@(d,qq:unitary:=true,general:=general,
#          normaliser:=normaliser);
#         if all then
#           nconj:=Gcd(d,q+1);
#           if d=3 and q mod 9 in Set([2,5]) then
#             nconj:=1;
#           fi;
#           asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#         else
#           Add(asmax,S);
#         fi;
#       elif IsEvenInt(r) and p mod 4=3 and ee=2 then
#         S:=NormaliserOfSymplecticGroup@(d,qq:unitary:=true,general:=general,
#          normaliser:=normaliser);
#         if all then
#           nconj:=Gcd(d,q+1);
#           if d=4 and q mod 8=3 then
#             nconj:=2;
#           fi;
#           asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#         else
#           Add(asmax,S);
#         fi;
#       fi;
#     elif type="O" then
#       if sign=1 and r=2 and ee=1 then
#         ex:=d=8 and q mod 8 in Set([3,5]);
#         if (novelties and not ex) or (not novelties and ex) then
#           continue;
#         fi;
#         S:=NormaliserOfExtraSpecialGroup@(d,q:orthogonal:=true,
#          normaliser:=normaliser);
#         if not all then
#           Add(asmax,S);
#         elif q mod 8 in Set([3,5]) then
#           asmax:=Concatenation(asmax,[S,S^CS,S^CG,S^(CS*CG)]);
#         else
#           asmax:=Concatenation(asmax,[S,S^CS,S^CG,S^(CS*CG),S^CN,S^(CS*CN)
#            ,S^(CG*CN),S^(CS*CG*CN)]);
#         fi;
#       fi;
#     fi;
#   elif cl=7 then
#     if novelties then
#       continue;
#     fi;
#     t:=2;
#     while 2^t <= d do
#       # =v= MULTIASSIGN =v=
#       m:=IsPower(d,t);
#       isp:=m.val1;
#       m:=m.val2;
#       # =^= MULTIASSIGN =^=
#       if isp then
#         if type="L" then
#           #  KL excludes m=2 orthogonal?
#           if m=2 then
#             t:=t+1;
#             continue;
#           fi;
#           S:=SLTensorInd@(m,t,q:general:=false);
#           if all then
#             nconj:=Gcd(q-1,m^(t-1));
#             if (m mod 4=2) and t=2 and (q mod 4=3) then
#               #  in that case odd permutation from Sym(t) increases N_GL.
#               nconj:=QuoInt(nconj,2);
#             fi;
#             asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#           else
#             Add(asmax,S);
#           fi;
#         elif type="S" and IsEvenInt(m) then
#           #  group not symplectic for t even, q odd
#           #  KL insist on tq odd and (m,q) ne (2,3).
#           if IsEvenInt(t) or IsEvenInt(q) or (m=2 and q=3) then
#             t:=t+1;
#             continue;
#           fi;
#           S:=SpTensorInd@(m,t,q:normaliser:=normaliser);
#           #  always one conjugate here - yes!
#           Add(asmax,S);
#         elif type="U" then
#           #  KL exclude m=2 (subfield group) and (m,q) = (3,2).
#           if m=2 or (m=3 and q=2) then
#             t:=t+1;
#             continue;
#           fi;
#           S:=SUTensorInd@(m,t,q:general:=general,normaliser:=normaliser);
#           if all then
#             nconj:=Gcd(q+1,m^(t-1));
#             if (m mod 4=2) and t=2 and (q mod 4=1) then
#               #  in that case odd permutation from Sym(t) increases N_GL.
#               nconj:=QuoInt(nconj,2);
#             fi;
#             asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#           else
#             Add(asmax,S);
#           fi;
#         elif type="O" then
#           if sign=-1 or (m <= 3 and q <= 3) then
#             t:=t+1;
#             continue;
#           fi;
#           if IsEvenInt(q*t) and IsEvenInt(m) and (IsOddInt(q) or m > 4) then
#             #  last condition KL Table 3.5.I
#             S:=OrthogSpTensorInd@(m,t,q:special:=special,general:=general,
#              normaliser:=normaliser);
#             if not all or (t=2 and m mod 4=2) then
#               Add(asmax,S);
#             elif IsEvenInt(q) then
#               #  c=2
#               asmax:=Concatenation(asmax,[S,S^CS]);
#             else
#               #  c=4
#               asmax:=Concatenation(asmax,[S,S^CS,S^CG,S^(CS*CG)]);
#             fi;
#           fi;
#           if IsEvenInt(m) and m > 2 and IsOddInt(q) then
#             if t=2 and m mod 4=2 then
#               #  c=1
#               Add(asmax,OrthogTensorInd@(m,t,q,1:special:=special,
#                general:=general,normaliser:=normaliser));
#               Add(asmax,OrthogTensorInd@(m,t,q,-1:special:=special,
#                general:=general,normaliser:=normaliser));
#             else
#               S:=OrthogTensorInd@(m,t,q,1:special:=special,general:=general,
#                normaliser:=normaliser);
#               if not all then
#                 Add(asmax,S);
#               elif t=3 and m mod 4=2 and q mod 4=3 then
#                 #  c=2
#                 asmax:=Concatenation(asmax,[S,S^CG]);
#               else
#                 asmax:=Concatenation(asmax,[S,S^CS,S^CG,S^(CS*CG)]);
#               fi;
#               S:=OrthogTensorInd@(m,t,q,-1:special:=special,general:=general,
#                normaliser:=normaliser);
#               if not all then
#                 Add(asmax,S);
#               elif (t=3 and m mod 4=2 and q mod 4=1) or (t=2 and m mod 4=0) 
#                  then
#                 #  c=2
#                 asmax:=Concatenation(asmax,[S,S^CG]);
#               else
#                 asmax:=Concatenation(asmax,[S,S^CS,S^CG,S^(CS*CG)]);
#               fi;
#             fi;
#           fi;
#           if IsOddInt(m) and IsOddInt(q) then
#             Add(asmax,OrthogTensorInd@(m,t,q,0:special:=special,
#              general:=general,normaliser:=normaliser));
#           fi;
#         fi;
#       fi;
#       t:=t+1;
#     od;
#   elif cl=8 then
#     if novelties then
#       continue;
#     fi;
#     if type="L" then
#       if d=2 then
#         #  U(2,sqrt(q)) = L(2,sqrt(2)), subfield
#         #  Sp(2,q) = L(2,q)
#         #  O+(2,q) imprimitive, O-(2,q) semilinear
#         continue;
#       fi;
#       fac:=Collected(Factors(q));
#       p:=fac[1][1];
#       e:=fac[1][2];
#       if IsEvenInt(e) then
#         rq:=p^(QuoInt(e,2));
#         S:=NormOfSU@(d,rq:general:=general);
#         if all then
#           nconj:=Gcd(d,rq-1);
#           asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#         else
#           Add(asmax,S);
#         fi;
#       fi;
#       if IsEvenInt(d) then
#         S:=NormOfSp@(d,q:general:=general);
#         if all then
#           nconj:=Gcd(q-1,QuoInt(d,2));
#           asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#         else
#           Add(asmax,S);
#         fi;
#       fi;
#       if IsOddInt(q) then
#         if IsOddInt(d) then
#           S:=NormOfO@(d,q,0:general:=general);
#           if all then
#             nconj:=Gcd(q-1,d);
#             asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#           else
#             Add(asmax,S);
#           fi;
#         else
#           if all then
#             nconj:=QuoInt(Gcd(q-1,d),2);
#           fi;
#           S:=NormOfO@(d,q,1:general:=general);
#           if all then
#             asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#           else
#             Add(asmax,S);
#           fi;
#           S:=NormOfO@(d,q,-1:general:=general);
#           if all then
#             asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#           else
#             Add(asmax,S);
#           fi;
#         fi;
#       fi;
#     elif type="S" and IsEvenInt(q) and (d<>4 or all) then
#       varZ:=ScalarMat(d,PrimitiveElement(GF(q))) #CAST GL(d,q)
#         ;
#       if general then
#         Add(asmax,SubStructure(GL(d,q),GOPlus(d,q),#TODO CLOSURE
#           varZ));
#       else
#         Add(asmax,SOPlus(d,q));
#       fi;
#       # =v= MULTIASSIGN =v=
#       form:=SymplecticForm@(GOMinus(d,q));
#       isit:=form.val1;
#       form:=form.val2;
#       # =^= MULTIASSIGN =^=
#       Assert(1,isit);
#       trans:=CorrectForm(form,d,q,"symplectic") #CAST GL(d,q)
#         ;
#       if general then
#         Add(asmax,SubStructure(GL(d,q),GOMinus(d,q)^trans,#TODO CLOSURE
#           varZ));
#       else
#         Add(asmax,SOMinus(d,q)^trans);
#       fi;
#     fi;
#   elif cl=9 then
#     if d=2 then
#       #  must have type "L"
#       if novelties then
#         continue;
#       fi;
#       if (e=1 and p mod 5 in Set([1,4])) or (e=2 and p<>2 and p mod 5 in 
#          Set([2,3])) then
#         #  2.A5
#         _LRS:=Read(Concatenation(c9lib,"sl25d2"));
#         _LR:=#EVAL
#             _LRS;
#         S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#         if all then
#           nconj:=2;
#           asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#         else
#           Add(asmax,S[1]);
#         fi;
#       fi;
#     elif d=3 then
#       if type="L" then
#         if novelties then
#           continue;
#         fi;
#         if (e=1 and p<>2 and p mod 7 in Set([1,2,4])) then
#           #  L27
#           _LRS:=Read(Concatenation(c9lib,"l27d3"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             nconj:=Gcd(p-1,3);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if (e=1 and p mod 3=1 and p mod 5 in Set([1,4])) or (e=2 and p<>3 and 
#            p mod 5 in Set([2,3])) then
#           #  3.A6
#           _LRS:=Read(Concatenation(c9lib,"3a6d3"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             nconj:=3;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#       elif type="U" then
#         if (novelties and q=5) or (not novelties and e=1 and p<>5 and p mod 7 
#            in Set([3,5,6])) then
#           #  L27
#           _LRS:=Read(Concatenation(c9lib,"l27d3"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             nconj:=Gcd(p+1,3);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if novelties then
#           continue;
#         fi;
#         if (e=1 and p mod 3=2 and p mod 5 in Set([1,4])) then
#           #  3.A6
#           _LRS:=Read(Concatenation(c9lib,"3a6d3"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             nconj:=3;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if q=5 then
#           #  3.A7
#           _LRS:=Read(Concatenation(c9lib,"3a7d21b"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           S:=Filtered(S,s->Degree(s)=3);
#           if all then
#             nconj:=3;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#           #  3.M10
#           _LRS:=Read(Concatenation(c9lib,"3a6d3"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             nconj:=3;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#       elif type="O" then
#         if novelties then
#           continue;
#         fi;
#         if (e=1 and p mod 5 in Set([1,4])) or (e=2 and p<>2 and p mod 5 in 
#            Set([2,3])) then
#           #  A5
#           _LRS:=Read(Concatenation(c9lib,"a5d3"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:special:=special,general:=general,
#            normaliser:=normaliser);
#           if all then
#             asmax:=Concatenation(asmax,[S[1],S[1]^CS]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#       fi;
#     elif d=4 then
#       if type="L" then
#         if (e=1 and p<>2 and p mod 7 in Set([1,2,4])) then
#           if novelties then
#             #  2.L27
#             _LRS:=Read(Concatenation(c9lib,"sl27d4"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#             if all then
#               nconj:=Gcd(q-1,4);
#               asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#             else
#               Add(asmax,S[1]);
#             fi;
#           else
#             #  2.A7
#             _LRS:=Read(Concatenation(c9lib,"2a7d4"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#             if all then
#               nconj:=Gcd(q-1,4);
#               asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#         fi;
#         if novelties then
#           continue;
#         fi;
#         if (e=1 and p mod 6=1) then
#           #  2.U42
#           _LRS:=Read(Concatenation(c9lib,"2u42d4"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             nconj:=Gcd(q-1,4);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if q=2 then
#           #  A7
#           _LRS:=Read(Concatenation(c9lib,"2a7d4"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           Add(asmax,S[1]);
#         fi;
#       elif type="U" then
#         if (e=1 and p mod 7 in Set([3,5,6])) then
#           if novelties then
#             if p<>3 then
#               #  2.L27
#               _LRS:=Read(Concatenation(c9lib,"sl27d4"));
#               _LR:=#EVAL
#                   _LRS;
#               S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#                normaliser:=normaliser);
#               if all then
#                 nconj:=Gcd(q+1,4);
#                 asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#               else
#                 Add(asmax,S[1]);
#               fi;
#             fi;
#           else
#             #  2.A7
#             _LRS:=Read(Concatenation(c9lib,"2a7d4"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#              normaliser:=normaliser);
#             if all then
#               nconj:=Gcd(q+1,4);
#               asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#         fi;
#         if novelties then
#           continue;
#         fi;
#         if (e=1 and p mod 6=5) then
#           #  2.U42
#           _LRS:=Read(Concatenation(c9lib,"2u42d4"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             nconj:=Gcd(q+1,4);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if q=3 then
#           #  4_2.L34
#           _LRS:=Read(Concatenation(c9lib,"4bl34d20"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           S:=Filtered(S,s->Degree(s)=4);
#           if all then
#             nconj:=2;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#       elif type="S" then
#         if novelties then
#           if q=7 then
#             #  2.L2q
#             S:=SymplecticSL2@(4,q:normaliser:=normaliser);
#             Add(asmax,S);
#           fi;
#           continue;
#         fi;
#         if (e=1 and p<>7 and p mod 12 in Set([1,5,7,11])) then
#           #  2.A6 (p mod 12 in {5,7}), 2.S6 (p mod 12 in {1,11})
#           _LRS:=Read(Concatenation(c9lib,"2a6d4"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           if all and p mod 12 in Set([1,11]) then
#             asmax:=Concatenation(asmax,[S[1],S[1]^C]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if q=7 then
#           #  2.A7
#           _LRS:=Read(Concatenation(c9lib,"2a7d4"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           Add(asmax,S[1]);
#         fi;
#         if p >= 5 and q > 7 then
#           #  2.L2q
#           S:=SymplecticSL2@(4,q:normaliser:=normaliser);
#           Add(asmax,S);
#         fi;
#         if p=2 and IsOddInt(e) and e > 1 then
#           #  Szq
#           if normaliser then
#             Add(asmax,SubStructure(GL(d,q),Sz(q),#TODO CLOSURE
#               ScalarMat(d,z)));
#           else
#             Add(asmax,Sz(q));
#           fi;
#         fi;
#       elif type="O" then
#         #  must have sign -1
#         if novelties then
#           continue;
#         fi;
#         if e=1 and p<>2 and p mod 5 in Set([2,3]) then
#           #  A5
#           _LRS:=Read(Concatenation(c9lib,"a5d4"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:special:=special,general:=general,
#            normaliser:=normaliser);
#           if all then
#             asmax:=Concatenation(asmax,[S[1],S[1]^CS]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#       fi;
#     elif d=5 then
#       if type="L" then
#         if (novelties and q=3) or (not novelties and e=1 and p > 3 and p mod 
#            11 in Set([1,3,4,5,9])) then
#           #  L2_11
#           _LRS:=Read(Concatenation(c9lib,"l211d5"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             nconj:=Gcd(q-1,5);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if novelties then
#           continue;
#         fi;
#         if (e=1 and p mod 6=1) then
#           #  U42
#           _LRS:=Read(Concatenation(c9lib,"u42d5"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             nconj:=Gcd(q-1,5);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if q=3 then
#           #  M11
#           _LRS:=Read(Concatenation(c9lib,"m11d11"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           Add(asmax,S[1]);
#           if all then
#             Add(asmax,ActionGroup(Dual(GModule(S[1]))));
#           fi;
#         fi;
#       elif type="U" then
#         if novelties then
#           continue;
#         fi;
#         if (e=1 and p mod 11 in Set([2,6,7,8,10])) then
#           #  L2_11
#           _LRS:=Read(Concatenation(c9lib,"l211d5"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             nconj:=Gcd(q+1,5);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if (e=1 and p mod 6=5) then
#           #  U42
#           _LRS:=Read(Concatenation(c9lib,"u42d5"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             nconj:=Gcd(q+1,5);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#       elif type="O" then
#         if novelties then
#           if q=7 then
#             #  L2q
#             S:=OrthogSL2@(d,q:special:=special,general:=general,
#              normaliser:=normaliser);
#             Add(asmax,S);
#           fi;
#           continue;
#         fi;
#         if (e=1 and p<>7 and p mod 12 in Set([1,5,7,11])) then
#           #  A6 (p mod 12 in {5,7}) or S6 (p mod 12 in {1,11})
#           _LRS:=Read(Concatenation(c9lib,"a6d5"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:special:=special,general:=general,
#            normaliser:=normaliser);
#           if all and p mod 12 in Set([1,11]) then
#             asmax:=Concatenation(asmax,[S[1],S[1]^CS]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if q=7 then
#           #  A7
#           _LRS:=Read(Concatenation(c9lib,"a7d6"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:special:=special,general:=general,
#            normaliser:=normaliser);
#           Add(asmax,S[1]);
#         fi;
#         if p >= 5 and q > 7 then
#           #  L2q
#           S:=OrthogSL2@(d,q:special:=special,general:=general,
#            normaliser:=normaliser);
#           Add(asmax,S);
#         fi;
#       fi;
#     elif d=6 then
#       if type="L" then
#         if novelties then
#           if (e=1 and p mod 24 in Set([7,13])) then
#             #  6.L3_4
#             _LRS:=Read(Concatenation(c9lib,"6l34d6"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#             if all then
#               nconj:=3;
#               asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           if (e=1 and p mod 24 in Set([1,7])) or (e=2 and p mod 24 in 
#              Set([5,11,13,19])) then
#             #  6.A6
#             _LRS:=Read(Concatenation(c9lib,"6a6d6"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#             if all then
#               nconj:=6;
#               asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           if (e=1 and p mod 24 in Set([1,7,13,19])) then
#             #  3.A6
#             _LRS:=Read(Concatenation(c9lib,"3a6d6"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#             if all then
#               # rewritten select statement
#               if p mod 24 in Set([1,19]) then
#                 nconj:=6;
#               else
#                 nconj:=3;
#               fi;
#               asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           continue;
#         fi;
#         if (e=1 and p<>3 and p mod 11 in Set([1,3,4,5,9])) then
#           #  2.L2_11 in 2.M12 for p=3
#           _LRS:=Read(Concatenation(c9lib,"sl211d6"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             nconj:=Gcd(q-1,6);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         elif q=3 then
#           #  2.M12
#           _LRS:=Read(Concatenation(c9lib,"2m12d12"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             nconj:=2;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if (e=1 and p mod 12 in Set([1,7])) then
#           #  6_1.U4_3 (p mod 12 =7) or 6_1.U4_3.2_2 (p mod 12 = 1)
#           _LRS:=Read(Concatenation(c9lib,"6au43d6"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             # rewritten select statement
#             if p mod 12=1 then
#               nconj:=6;
#             else
#               nconj:=3;
#             fi;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if (e=1 and p mod 24 in Set([1,19])) then
#           #  6.L3_4.2_1
#           _LRS:=Read(Concatenation(c9lib,"6l34d6"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             nconj:=6;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if (e=1 and p mod 24 in Set([1,7])) or (e=2 and p mod 24 in 
#            Set([5,11,13,19])) then
#           #  6.A7
#           _LRS:=Read(Concatenation(c9lib,"6a7d6"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             nconj:=6;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#             asmax:=Concatenation(asmax,GConjugates@(S[2],C,nconj));
#           else
#             Add(asmax,S[1]);
#             Add(asmax,S[2]);
#           fi;
#         fi;
#         if IsOddInt(q) then
#           S:=l3qdim6@(q:general:=general);
#           if all then
#             nconj:=2;
#             asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#           else
#             Add(asmax,S);
#           fi;
#         fi;
#       elif type="U" then
#         if novelties then
#           if (e=1 and p mod 24 in Set([11,17])) then
#             #  6.L3_4
#             _LRS:=Read(Concatenation(c9lib,"6l34d6"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#              normaliser:=normaliser);
#             if all then
#               nconj:=3;
#               asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           if (e=1 and p mod 24 in Set([17,23])) then
#             #  6.A6
#             _LRS:=Read(Concatenation(c9lib,"6a6d6"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#              normaliser:=normaliser);
#             if all then
#               nconj:=6;
#               asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           if (e=1 and p mod 24 in Set([5,11,17,23]) and p<>5) then
#             #  3.A6
#             _LRS:=Read(Concatenation(c9lib,"3a6d6"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#              normaliser:=normaliser);
#             if all then
#               # rewritten select statement
#               if p mod 24 in Set([5,23]) then
#                 nconj:=6;
#               else
#                 nconj:=3;
#               fi;
#               asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           continue;
#         fi;
#         if (e=1 and p<>2 and p mod 11 in Set([2,6,7,8,10])) then
#           #  2.L2_11 in 3.M22 for p=2
#           _LRS:=Read(Concatenation(c9lib,"sl211d6"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             nconj:=Gcd(q+1,6);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         elif q=2 then
#           #  3.M22
#           _LRS:=Read(Concatenation(c9lib,"3m22d21"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             nconj:=3;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#           #  3.U4_3.2_2
#           _LRS:=Read(Concatenation(c9lib,"6au43d6"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             nconj:=3;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if (e=1 and p mod 12 in Set([5,11])) then
#           #  6_1.U4_3 (p mod 12 =5) or 6_1.U4_3.2_2 (p mod 12 = 11)
#           _LRS:=Read(Concatenation(c9lib,"6au43d6"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             # rewritten select statement
#             if p mod 12=11 then
#               nconj:=6;
#             else
#               nconj:=3;
#             fi;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if (e=1 and p mod 24 in Set([5,23])) then
#           #  6.L3_4.2_1
#           _LRS:=Read(Concatenation(c9lib,"6l34d6"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             nconj:=6;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if (e=1 and p mod 24 in Set([17,23])) then
#           #  6.A7
#           _LRS:=Read(Concatenation(c9lib,"6a7d6"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             nconj:=6;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#             asmax:=Concatenation(asmax,GConjugates@(S[2],C,nconj));
#           else
#             Add(asmax,S[1]);
#             Add(asmax,S[2]);
#           fi;
#         fi;
#         if IsOddInt(q) then
#           S:=u3qdim6@(q:general:=general,normaliser:=normaliser);
#           if all then
#             nconj:=2;
#             asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#           else
#             Add(asmax,S);
#           fi;
#         fi;
#       elif type="S" then
#         if novelties then
#           if e=1 and p mod 8 in Set([3,5]) and p mod 5 in Set([1,4]) then
#             #  2.A5
#             _LRS:=Read(Concatenation(c9lib,"sl25d6"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#             Add(asmax,S[1]);
#           fi;
#           if q=9 then
#             #  2.L_2(7)
#             _LRS:=Read(Concatenation(c9lib,"sl27d6"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#             if all then
#               asmax:=Concatenation(asmax,[S[1],S[1]^C]);
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           if e=1 and p mod 60 in Set([19,29,31,41]) then
#             #  2 x U_3(3)
#             _LRS:=Read(Concatenation(c9lib,"u33d6"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#             Add(asmax,S[1]);
#           fi;
#           continue;
#         fi;
#         if e=1 and (p mod 8 in Set([1,7]) or (p mod 8 in Set([3,5]) and p mod 
#            5 in Set([2,3]))) then
#           #  2.S5 (p mod 8 in {1,7}) of 2.A5 o.w.
#           _LRS:=Read(Concatenation(c9lib,"sl25d6"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           if all and p mod 8 in Set([1,7]) then
#             asmax:=Concatenation(asmax,[S[1],S[1]^C]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if (e=1 and p mod 16 in Set([1,15])) or (e=1 and p mod 16 in Set([7,9]
#            ) and p<>7) or (e=2 and p mod 16 in Set([3,5,11,13]) and p<>3) 
#            then
#           #  2.L2_7.2 (e eq 1 and p mod 16 in {1,15}) or 2.L2_7 o.w.
#           _LRS:=Read(Concatenation(c9lib,"sl27d6"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           if all and p mod 16 in Set([1,15]) then
#             asmax:=Concatenation(asmax,[S[1],S[1]^C,S[2],S[2]^C]);
#           else
#             Add(asmax,S[1]);
#             Add(asmax,S[2]);
#           fi;
#         fi;
#         if (e=1 and p mod 13 in Set([1,3,4,9,10,12])) or (e=2 and p mod 13 in 
#            Set([2,5,6,7,8,11]) and p<>2) then
#           #  2.L2_13
#           _LRS:=Read(Concatenation(c9lib,"sl213d6"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           if all then
#             asmax:=Concatenation(asmax,[S[1],S[1]^C]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if e=1 and (p mod 12 in Set([1,11]) or (p mod 12 in Set([5,7]) and p 
#            mod 5 in Set([2,3]))) then
#           #  U33.2 (p mod 12 in {1,11}) or U33 o.w.)
#           _LRS:=Read(Concatenation(c9lib,"u33d6"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           if all and p mod 12 in Set([1,11]) then
#             asmax:=Concatenation(asmax,[S[1],S[1]^C]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if (e=1 and p mod 5 in Set([0,1,4])) or (e=2 and p mod 5 in Set([2,3])
#             and p<>2) then
#           #  2.J2
#           _LRS:=Read(Concatenation(c9lib,"2j2d6"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           if all and p<>5 then
#             asmax:=Concatenation(asmax,[S[1],S[1]^C]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if q=9 then
#           #  2.A7
#           _LRS:=Read(Concatenation(c9lib,"2a7d6f9"));
#           S:=#EVAL
#               _LRS;
#           asmax:=Concatenation(asmax,[S,S^C]);
#         fi;
#         if p >= 7 then
#           #  2.L2q
#           S:=SymplecticSL2@(6,q:normaliser:=normaliser);
#           Add(asmax,S);
#         fi;
#         if p=2 then
#           #  G2q
#           C:=Constituents(GModule(G2(q)));
#           A:=ActionGroup(Filtered(C,c->DimensionOfMatrixGroup(c)=6)[1]);
#           A:=A^TransformForm(A);
#           if normaliser then
#             A:=SubStructure(GL(d,q),A,#TODO CLOSURE
#               ScalarMat(d,z));
#           fi;
#           Add(asmax,A);
#         fi;
#       elif type="O" then
#         if novelties then
#           if e=1 and ((sign=1 and p mod 7 in Set([1,2,4])) or (sign=-1 and p 
#              mod 7 in Set([3,5,6]))) then
#             #  L_2(7)
#             _LRS:=Read(Concatenation(c9lib,"l27d6"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all and q mod 4=1 then
#               if sign=-1 then
#                 asmax:=Concatenation(asmax,[S[1],S[1]^CN]);
#               else
#                 asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CN,S[1]^(CS*CN)]
#                  );
#               fi;
#             elif all and q mod 4=3 then
#               if sign=1 then
#                 asmax:=Concatenation(asmax,[S[1],S[1]^CN]);
#               else
#                 asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CN,S[1]^(CS*CN)]
#                  );
#               fi;
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           continue;
#         fi;
#         if sign=1 then
#           if e=1 and p mod 7 in Set([1,2,4]) then
#             #  A7
#             _LRS:=Read(Concatenation(c9lib,"a7d6"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all and q mod 4=1 then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CN,S[1]^(CS*CN)])
#                ;
#             elif all and q mod 4=3 then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CN]);
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           if e=1 and p mod 6=1 then
#             #  U42
#             _LRS:=Read(Concatenation(c9lib,"u42d6"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all and q mod 4=1 then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CN,S[1]^(CS*CN)])
#                ;
#             elif all and q mod 4=3 then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CN]);
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#         elif sign=-1 then
#           if e=1 and p mod 7 in Set([3,5,6]) then
#             #  A7
#             _LRS:=Read(Concatenation(c9lib,"a7d6"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all and q mod 4=3 then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CN,S[1]^(CS*CN)])
#                ;
#             elif all and q mod 4=1 then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CN]);
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           if e=1 and p mod 6=5 then
#             #  U42
#             _LRS:=Read(Concatenation(c9lib,"u42d6"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all and q mod 4=3 then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CN,S[1]^(CS*CN)])
#                ;
#             elif all and q mod 4=1 then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CN]);
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           if q=3 then
#             #  2.L34
#             _LRS:=Read(Concatenation(c9lib,"6l34d6"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CG]);
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#         fi;
#       fi;
#     elif d=7 then
#       if novelties then
#         continue;
#       fi;
#       if type="L" then
#         if e=1 and p mod 4=1 then
#           #  U33
#           _LRS:=Read(Concatenation(c9lib,"u33d7b"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             nconj:=Gcd(q-1,7);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#       elif type="U" then
#         if e=1 and p mod 4=3 and p<>3 then
#           #  U33
#           _LRS:=Read(Concatenation(c9lib,"u33d7b"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             nconj:=Gcd(q+1,7);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#       elif type="O" then
#         if e=1 then
#           #  Sp62
#           _LRS:=Read(Concatenation(c9lib,"s62d7"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:special:=special,general:=general,
#            normaliser:=normaliser);
#           if all then
#             asmax:=Concatenation(asmax,[S[1],S[1]^CS]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if q=3 then
#           #  S9
#           _LRS:=Read(Concatenation(c9lib,"a9d8"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:special:=special,general:=general,
#            normaliser:=normaliser);
#           if all then
#             asmax:=Concatenation(asmax,[S[1],S[1]^CS]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         S:=G2(q);
#         S:=S^TransformForm(S);
#         if normaliser then
#           S:=SubStructure(GL(d,q),S,#TODO CLOSURE
#             ScalarMat(d,z));
#         elif general then
#           S:=SubStructure(GL(d,q),S,#TODO CLOSURE
#             ScalarMat(d,-1));
#         fi;
#         if all then
#           asmax:=Concatenation(asmax,[S,S^CS]);
#         else
#           Add(asmax,S);
#         fi;
#       fi;
#     elif d=8 then
#       if type="L" then
#         if novelties then
#           continue;
#         fi;
#         if (e=1 and p mod 20 in Set([1,9])) or (e=2 and p mod 20 in 
#            Set([3,7,13,17])) then
#           #  4_1.L3_4 if q!=1 mod 16 or 4_1.L34.2_3 if q=1 mod 16
#           _LRS:=Read(Concatenation(c9lib,"4al34d8"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             # rewritten select statement
#             if q mod 16=1 then
#               nconj:=8;
#             else
#               nconj:=QuoInt(Gcd(q-1,8),2);
#             fi;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#             asmax:=Concatenation(asmax,GConjugates@(S[2],C,nconj));
#           else
#             Add(asmax,S[1]);
#             Add(asmax,S[2]);
#           fi;
#         fi;
#         if p=5 then
#           #  4_1.L3_4 once
#           _LRS:=Read(Concatenation(c9lib,"4al34d8"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             nconj:=2;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#       elif type="U" then
#         if novelties then
#           continue;
#         fi;
#         if (e=1 and p mod 20 in Set([11,19])) then
#           #  4_1.L3_4 if q!=-1 mod 16 or 4_1.L34.2_3 if q=-1 mod 16
#           _LRS:=Read(Concatenation(c9lib,"4al34d8"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             # rewritten select statement
#             if q mod 16=-1 then
#               nconj:=8;
#             else
#               nconj:=QuoInt(Gcd(q+1,8),2);
#             fi;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#             asmax:=Concatenation(asmax,GConjugates@(S[2],C,nconj));
#           else
#             Add(asmax,S[1]);
#             Add(asmax,S[2]);
#           fi;
#         fi;
#       elif type="S" then
#         if novelties then
#           continue;
#         fi;
#         if e=1 and p mod 12 in Set([1,5,7,11]) and p<>7 then
#           #  2.L27 if p mod 12 in {5,7}, 2.L27.2 if p mod 12 in {1,11}
#           _LRS:=Read(Concatenation(c9lib,"sl27d8"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           if all and p mod 12 in Set([1,11]) then
#             asmax:=Concatenation(asmax,[S[1],S[1]^C]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if (e=1 and p mod 20 in Set([1,9,11,19])) or (e=2 and p mod 5 in 
#            Set([2,3]) and p<>3) then
#           #  2.A6.2_2  if p mod 20 in {1,19}, 2.A6 o.w.
#           _LRS:=Read(Concatenation(c9lib,"2a6d8"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           if all and p mod 20 in Set([1,19]) then
#             asmax:=Concatenation(asmax,[S[1],S[1]^C]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if (e=1 and p mod 17 in Set([1,2,4,8,9,13,15,16])) or (e=2 and p mod 
#            17 in Set([3,5,6,7,10,11,12,14])) then
#           #  2.L2_17
#           _LRS:=Read(Concatenation(c9lib,"sl217d8"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           if all and p<>2 then
#             asmax:=Concatenation(asmax,[S[1],S[1]^C]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if q=2 then
#           #  S10
#           _LRS:=Read(Concatenation(c9lib,"a10d9"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           Add(asmax,S[1]);
#         fi;
#         if p >= 11 then
#           #  2.L2q
#           S:=SymplecticSL2@(8,q:normaliser:=normaliser);
#           Add(asmax,S);
#         fi;
#         if IsOddInt(q) then
#           Add(asmax,l2q3dim8@(q:normaliser:=normaliser));
#         fi;
#       elif type="O" then
#         if sign=1 then
#           if novelties then
#             continue;
#           fi;
#           if e=1 and p >= 3 then
#             #  2.Omega+(8,2)
#             _LRS:=Read(Concatenation(c9lib,"2o8+2d8"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CN,S[1]^(CS*CN)])
#                ;
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           if q=2 then
#             #  A9 x3 (all fused under triality)
#             _LRS:=Read(Concatenation(c9lib,"a9d8"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             Add(asmax,S[1]);
#             _LRS:=Read(Concatenation(c9lib,"2a9d8"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CS]);
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           if q=5 then
#             #  A10, 2.A10 (all fused under triality)
#             _LRS:=Read(Concatenation(c9lib,"a10d9"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CN,S[1]^(CS*CN)])
#                ;
#             else
#               Add(asmax,S[1]);
#             fi;
#             _LRS:=Read(Concatenation(c9lib,"2a10d16"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CG,S[1]^(CS*CG)
#                ,S[1]^CN,S[1]^(CS*CN),S[1]^(CG*CN),S[1]^(CS*CG*CN)]);
#             else
#               Add(asmax,S[1]);
#             fi;
#             #  2Sz8
#             _LRS:=Read(Concatenation(c9lib,"2sz8d8f5"));
#             S:=#EVAL
#                 _LRS;
#             if normaliser then
#               S:=SubStructure(GL(8,5),S,#TODO CLOSURE
#                 ScalarMat(8,z));
#             fi;
#             if all then
#               asmax:=Concatenation(asmax,[S,S^CS,S^CG,S^(CS*CG),S^CN,S^(CS*CN)
#                ,S^(CG*CN),S^(CS*CG*CN)]);
#             else
#               Add(asmax,S);
#             fi;
#           fi;
#           if q<>2 and p<>3 then
#             #  PSL(3,q).3 or PSU(3,q).3
#             # rewritten select statement
#             if q mod 3=1 then
#               S:=l3qdim8@(q:special:=special,general:=general,
#                normaliser:=normaliser);
#             else
#               S:=u3qdim8@(q:special:=special,general:=general,
#                normaliser:=normaliser);
#             fi;
#             if all and IsOddInt(q) then
#               asmax:=Concatenation(asmax,[S,S^CS,S^CN,S^(CS*CN)]);
#             else
#               Add(asmax,S);
#             fi;
#           fi;
#           if e mod 3=0 then
#             S:=SubStructure(GL(d,q),ChevalleyGroup("3D",4,GF(q)),#TODO 
#              CLOSURE
#               ScalarMat(8,-1));
#             S:=S^TransformForm(S);
#             if all then
#               if p=2 then
#                 asmax:=Concatenation(asmax,[S,S^CS]);
#               else
#                 asmax:=Concatenation(asmax,[S,S^CS,S^CG,S^(CS*CG)
#                  ,S^CN,S^(CS*CN),S^(CG*CN),S^(CS*CG*CN)]);
#               fi;
#             else
#               Add(asmax,S);
#             fi;
#           fi;
#           #  2.O(7,q)
#           # rewritten select statement
#           if normaliser and p<>2 then
#             S:=TwoO72@(q);
#           else
#             S:=TwoO7@(q);
#           fi;
#           if normaliser and p=2 then
#             S:=SubStructure(GL(8,q),S,#TODO CLOSURE
#               ScalarMat(8,z));
#           fi;
#           if all then
#             if p=2 then
#               asmax:=Concatenation(asmax,[S,S^CS]);
#             else
#               asmax:=Concatenation(asmax,[S,S^CS,S^CG,S^(CS*CG)]);
#             fi;
#           else
#             Add(asmax,S);
#           fi;
#           if IsEvenInt(e) then
#             #  2.O^-(8,q^(1/2))
#             # rewritten select statement
#             if normaliser and p<>2 then
#               S:=TwoOminus82@(p^(QuoInt(e,2)));
#             else
#               S:=TwoOminus8@(p^(QuoInt(e,2)));
#             fi;
#             if normaliser and p=2 then
#               S:=SubStructure(GL(8,q),S,#TODO CLOSURE
#                 ScalarMat(8,z));
#             fi;
#             if all then
#               if p=2 then
#                 asmax:=Concatenation(asmax,[S,S^CS]);
#               else
#                 asmax:=Concatenation(asmax,[S,S^CS,S^CG,S^(CS*CG)]);
#               fi;
#             else
#               Add(asmax,S);
#             fi;
#           fi;
#         elif sign=-1 then
#           if novelties then
#             continue;
#           fi;
#           if p<>3 then
#             #  PSL(3,q).3 or PSU(3,q).3
#             # rewritten select statement
#             if q mod 3=2 then
#               S:=l3qdim8@(q:special:=special,general:=general,
#                normaliser:=normaliser);
#             else
#               S:=u3qdim8@(q:special:=special,general:=general,
#                normaliser:=normaliser);
#             fi;
#             if all and IsOddInt(q) then
#               asmax:=Concatenation(asmax,[S,S^CN]);
#             else
#               Add(asmax,S);
#             fi;
#           fi;
#         fi;
#         #  signs for O8
#       fi;
#       #  types for d=8
#     elif d=9 then
#       if type="L" then
#         if novelties then
#           continue;
#         fi;
#         if (e=1 and p mod 19 in Set([1,4,5,6,7,9,11,16,17])) then
#           #  L2_19
#           _LRS:=Read(Concatenation(c9lib,"l219d9"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             nconj:=Gcd(q-1,9);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if (e=1 and p mod 3=1 and p mod 5 in Set([2,3])) then
#           #  3.A6.2_3
#           _LRS:=Read(Concatenation(c9lib,"3a6d9"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             nconj:=Gcd(q-1,9);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if q=7 then
#           #  3.A7
#           _LRS:=Read(Concatenation(c9lib,"3a7d15b"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           S:=Filtered(S,s->Degree(s)=9);
#           if all then
#             nconj:=3;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         #  (3.)L3_q^2(.3).2
#         S:=l3q2dim9l@(q:general:=general);
#         if all then
#           nconj:=Gcd(q-1,3);
#           asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#         else
#           Add(asmax,S);
#         fi;
#       elif type="U" then
#         if novelties then
#           if q=2 then
#             #  L2_19
#             _LRS:=Read(Concatenation(c9lib,"l219d9"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#              normaliser:=normaliser);
#             if all then
#               nconj:=Gcd(q+1,9);
#               asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           continue;
#         fi;
#         if (e=1 and p mod 19 in Set([2,3,8,10,12,13,14,15,18])) and p<>2 then
#           #  L2_19
#           _LRS:=Read(Concatenation(c9lib,"l219d9"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             nconj:=Gcd(q+1,9);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if (e=1 and p mod 3=2 and p mod 5 in Set([2,3]) and p > 2) then
#           #  3.A6.2_3
#           _LRS:=Read(Concatenation(c9lib,"3a6d9"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             nconj:=Gcd(q+1,9);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if q=2 then
#           #  3J3
#           _LRS:=Read(Concatenation(c9lib,"3j3d9f4"));
#           S:=#EVAL
#               _LRS;
#           if normaliser then
#             S:=SubStructure(GL(9,4),S,#TODO CLOSURE
#               ScalarMat(9,z));
#           fi;
#           if all then
#             nconj:=3;
#             asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#           else
#             Add(asmax,S);
#           fi;
#         fi;
#         #  (3.)L3_q^2(.3).2
#         S:=l3q2dim9u@(q:general:=general,normaliser:=normaliser);
#         if all then
#           nconj:=Gcd(q+1,3);
#           asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#         else
#           Add(asmax,S);
#         fi;
#       elif type="O" then
#         if novelties then
#           continue;
#         fi;
#         if (e=1 and p mod 7 in Set([1,6])) or (e=3 and p mod 7 in 
#            Set([2,3,4,5])) then
#           _LRS:=Read(Concatenation(c9lib,"l28d9"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:special:=special,general:=general,
#            normaliser:=normaliser);
#           if all then
#             asmax:=Concatenation(asmax,[S[1],S[1]^CS]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if (e=1 and p mod 17 in Set([1,2,4,8,9,13,15,16])) or (e=2 and p mod 
#            17 in Set([3,5,6,7,10,11,12,14])) then
#           _LRS:=Read(Concatenation(c9lib,"l217d9"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:special:=special,general:=general,
#            normaliser:=normaliser);
#           if all then
#             asmax:=Concatenation(asmax,[S[1],S[1]^CS]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if e=1 and p<>11 and p mod 5<>0 then
#           #  A10 (p mod 5 = 1,4) or A10.2 o.w.
#           _LRS:=Read(Concatenation(c9lib,"a10d9"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:special:=special,general:=general,
#            normaliser:=normaliser);
#           if all and p mod 5 in Set([1,4]) then
#             asmax:=Concatenation(asmax,[S[1],S[1]^CS]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if q=11 then
#           #  A11.2
#           _LRS:=Read(Concatenation(c9lib,"a11d10"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:special:=special,general:=general,
#            normaliser:=normaliser);
#           if all then
#             asmax:=Concatenation(asmax,[S[1],S[1]^CS]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if p >= 11 then
#           #  L2q
#           S:=OrthogSL2@(d,q:special:=special,general:=general,
#            normaliser:=normaliser);
#           if all then
#             asmax:=Concatenation(asmax,[S,S^CS]);
#           else
#             Add(asmax,S);
#           fi;
#         fi;
#         if q<>3 then
#           #  L2q^2
#           S:=l2q2dim9@(q:special:=special,general:=general,
#            normaliser:=normaliser);
#           Add(asmax,S);
#         fi;
#       fi;
#     elif d=10 then
#       if type="L" then
#         if novelties then
#           if e=1 and p<>2 and p mod 28 in Set([1,2,9,11,15,23,25]) then
#             #  2.l34 (p=11,15,23 mod 28) or 2.l34.2 o.w.
#             _LRS:=Read(Concatenation(c9lib,"2l34d10"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#             if all then
#               # rewritten select statement
#               if p mod 28 in Set([1,9,25]) then
#                 nconj:=Gcd(q-1,10);
#               else
#                 nconj:=QuoInt(Gcd(q-1,10),2);
#               fi;
#               asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#               #  asmax cat:= GConjugates(S[2],C,nconj);
#             else
#               Add(asmax,S[1]);
#               #  Append(~asmax, S[2]);
#             fi;
#           fi;
#           continue;
#         fi;
#         if (e=1 and p mod 19 in Set([1,4,5,6,7,9,11,16,17])) then
#           #  SL2_19
#           _LRS:=Read(Concatenation(c9lib,"sl219d10"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             nconj:=Gcd(q-1,10);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if e=1 and p mod 8 in Set([1,3]) then
#           #  2.M12 (p=3 mod 8) or 2.M12.2 (p=1 mod 8)
#           _LRS:=Read(Concatenation(c9lib,"2m12d10"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             # rewritten select statement
#             if p mod 8=1 then
#               nconj:=Gcd(q-1,10);
#             else
#               nconj:=QuoInt(Gcd(q-1,10),2);
#             fi;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#             asmax:=Concatenation(asmax,GConjugates@(S[2],C,nconj));
#           else
#             Add(asmax,S[1]);
#             Add(asmax,S[2]);
#           fi;
#         fi;
#         if e=1 and p mod 28 in Set([1,2,9,11,15,23,25]) then
#           #  2.M22 (p=11,15,23 mod 28) or 2.M22.2 o.w.
#           _LRS:=Read(Concatenation(c9lib,"2m22d10"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             # rewritten select statement
#             if p mod 28 in Set([1,2,9,25]) then
#               nconj:=Gcd(q-1,10);
#             else
#               nconj:=QuoInt(Gcd(q-1,10),2);
#             fi;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#             asmax:=Concatenation(asmax,GConjugates@(S[2],C,nconj));
#           else
#             Add(asmax,S[1]);
#             Add(asmax,S[2]);
#           fi;
#         fi;
#         if p >= 5 then
#           S:=l3qdim10@(q:general:=general);
#           if all then
#             nconj:=Gcd(q-1,d);
#             asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#           else
#             Add(asmax,S);
#           fi;
#         fi;
#         if p >= 3 then
#           S:=l4qdim10@(q:general:=general);
#           if all then
#             nconj:=Gcd(q-1,5);
#             asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#           else
#             Add(asmax,S);
#           fi;
#         fi;
#         S:=l5qdim10@(q:general:=general);
#         if all then
#           nconj:=Gcd(q-1,2);
#           asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#         else
#           Add(asmax,S);
#         fi;
#       elif type="U" then
#         if novelties then
#           if e=1 and p mod 28 in Set([3,5,13,17,19,27]) and p<>3 then
#             #  2.L34 (p=5,13,17 mod 28) or 2.L34.2 o.w.
#             _LRS:=Read(Concatenation(c9lib,"2l34d10"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#              normaliser:=normaliser);
#             if all then
#               # rewritten select statement
#               if p mod 28 in Set([3,19,27]) then
#                 nconj:=Gcd(q+1,10);
#               else
#                 nconj:=QuoInt(Gcd(q+1,10),2);
#               fi;
#               asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#               #  asmax cat:= GConjugates(S[2],C,nconj);
#             else
#               Add(asmax,S[1]);
#               #  Append(~asmax, S[2]);
#             fi;
#           fi;
#           continue;
#         fi;
#         if (e=1 and p mod 19 in Set([2,3,8,10,12,13,14,15,18]) and not p=2) 
#            then
#           #  SL2_19
#           _LRS:=Read(Concatenation(c9lib,"sl219d10"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             nconj:=Gcd(q+1,10);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if e=1 and p mod 8 in Set([5,7]) then
#           #  2.M12 (p=5 mod 8) or 2.M12.2 (p=7 mod 8)
#           _LRS:=Read(Concatenation(c9lib,"2m12d10"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             # rewritten select statement
#             if p mod 8=7 then
#               nconj:=Gcd(q+1,10);
#             else
#               nconj:=QuoInt(Gcd(q+1,10),2);
#             fi;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#             asmax:=Concatenation(asmax,GConjugates@(S[2],C,nconj));
#           else
#             Add(asmax,S[1]);
#             Add(asmax,S[2]);
#           fi;
#         fi;
#         if e=1 and p mod 28 in Set([3,5,13,17,19,27]) then
#           #  2.M22 (p=5,13,17 mod 28) or 2.M22.2 o.w.
#           _LRS:=Read(Concatenation(c9lib,"2m22d10"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             # rewritten select statement
#             if p mod 28 in Set([3,19,27]) then
#               nconj:=Gcd(q+1,10);
#             else
#               nconj:=QuoInt(Gcd(q+1,10),2);
#             fi;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#             asmax:=Concatenation(asmax,GConjugates@(S[2],C,nconj));
#           else
#             Add(asmax,S[1]);
#             Add(asmax,S[2]);
#           fi;
#         fi;
#         if p >= 5 then
#           S:=u3qdim10@(q:general:=general,normaliser:=normaliser);
#           if all then
#             nconj:=Gcd(q+1,d);
#             asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#           else
#             Add(asmax,S);
#           fi;
#         fi;
#         if p >= 3 then
#           S:=u4qdim10@(q:general:=general,normaliser:=normaliser);
#           if all then
#             nconj:=Gcd(q+1,5);
#             asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#           else
#             Add(asmax,S);
#           fi;
#         fi;
#         S:=u5qdim10@(q:general:=general,normaliser:=normaliser);
#         if all then
#           nconj:=Gcd(q+1,2);
#           asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#         else
#           Add(asmax,S);
#         fi;
#       elif type="S" then
#         if novelties then
#           continue;
#         fi;
#         if (e=1 and p mod 16 in Set([1,7,9,15])) or (e=2 and p mod 16 in 
#            Set([3,5,11,13]) and p<>3) then
#           #  2.A6.2_2 if p mod 16 in {1,15}, 2.A6 o.w.
#           _LRS:=Read(Concatenation(c9lib,"2a6d10"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           if all and p mod 16 in Set([1,15]) then
#             asmax:=Concatenation(asmax,[S[1],S[1]^C]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if (e=1 and p mod 8 in Set([1,3,5,7]) and p<>11) then
#           #  2.L2_11.2 if p mod 8 in {1,7}, 2.L2_11 o.w.
#           _LRS:=Read(Concatenation(c9lib,"sl211d10a"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           if all and p mod 8 in Set([1,7]) then
#             asmax:=Concatenation(asmax,[S[1],S[1]^C]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if (e=1 and p mod 24 in Set([1,11,13,23]) and p<>11) or (e=2 and p 
#            mod 24 in Set([5,7,17,19])) then
#           #  2.L2_11 if p mod 23 in {11,13}, 2.L2_11.2 o.w.
#           _LRS:=Read(Concatenation(c9lib,"sl211d10b"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           if all and p mod 24 in Set([1,5,7,17,19,23]) then
#             asmax:=Concatenation(asmax,[S[1],S[1]^C]);
#             asmax:=Concatenation(asmax,[S[2],S[2]^C]);
#           else
#             Add(asmax,S[1]);
#             Add(asmax,S[2]);
#           fi;
#         fi;
#         if (e=1 and p mod 8 in Set([1,3,5,7])) then
#           #  U52.2 if p mod 8 in {1,7}, U52 o.w.
#           _LRS:=Read(Concatenation(c9lib,"u52d10"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           if all and p mod 8 in Set([1,7]) then
#             asmax:=Concatenation(asmax,[S[1],S[1]^C]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if p >= 11 then
#           #  2.L2q
#           S:=SymplecticSL2@(10,q:normaliser:=normaliser);
#           Add(asmax,S);
#         fi;
#       elif type="O" then
#         if sign=1 then
#           if novelties then
#             if e=1 and p mod 12 in Set([1,5]) then
#               #  A6
#               _LRS:=Read(Concatenation(c9lib,"a6d10"));
#               _LR:=#EVAL
#                   _LRS;
#               S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#                general:=general,normaliser:=normaliser);
#               if all and p mod 12=1 then
#                 asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CN,S[1]^(CS*CN)]
#                  );
#               elif all and p mod 12=5 then
#                 asmax:=Concatenation(asmax,[S[1],S[1]^CN]);
#               else
#                 Add(asmax,S[1]);
#               fi;
#             fi;
#             if e=1 and p mod 11 in Set([1,3,4,5,9]) and p<>3 then
#               #  L211b
#               _LRS:=Read(Concatenation(c9lib,"l211d10b"));
#               _LR:=#EVAL
#                   _LRS;
#               S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#                general:=general,normaliser:=normaliser);
#               if all and p mod 4=1 then
#                 asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CN,S[1]^(CS*CN)]
#                  );
#               elif all and p mod 4=3 then
#                 asmax:=Concatenation(asmax,[S[1],S[1]^CN]);
#               else
#                 Add(asmax,S[1]);
#               fi;
#             fi;
#             continue;
#           fi;
#           if e=1 and p mod 11 in Set([1,3,4,5,9]) and p<>3 then
#             #  L2_11a
#             _LRS:=Read(Concatenation(c9lib,"l211d10a"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all and p mod 4=1 then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CN,S[1]^(CS*CN)])
#                ;
#             elif all and p mod 4=3 then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CN]);
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           if e=1 and p mod 11 in Set([1,3,4,5,9]) and p<>3 then
#             #  A11
#             _LRS:=Read(Concatenation(c9lib,"a11d10"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all and p mod 4=1 then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CN,S[1]^(CS*CN)])
#                ;
#             elif all and p mod 4=3 then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CN]);
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           if q=3 then
#             #  A12
#             _LRS:=Read(Concatenation(c9lib,"a12d11"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CN]);
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           if q mod 4=1 then
#             #  Sp4q
#             S:=sp4qdim10@(qq:special:=special,general:=general,
#              normaliser:=normaliser);
#             if all then
#               asmax:=Concatenation(asmax,[S,S^CG,S^CN,S^(CG*CN)]);
#             else
#               Add(asmax,S);
#             fi;
#           fi;
#         elif sign=-1 then
#           if novelties then
#             if e=1 and p mod 12 in Set([7,11]) then
#               #  A6
#               _LRS:=Read(Concatenation(c9lib,"a6d10"));
#               _LR:=#EVAL
#                   _LRS;
#               S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#                general:=general,normaliser:=normaliser);
#               if all and p mod 12=11 then
#                 asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CN,S[1]^(CS*CN)]
#                  );
#               elif all and p mod 12=7 then
#                 asmax:=Concatenation(asmax,[S[1],S[1]^CN]);
#               else
#                 Add(asmax,S[1]);
#               fi;
#             fi;
#             if e=1 and p mod 11 in Set([2,6,7,8,10]) then
#               #  L211b
#               _LRS:=Read(Concatenation(c9lib,"l211d10b"));
#               _LR:=#EVAL
#                   _LRS;
#               S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#                general:=general,normaliser:=normaliser);
#               if all and p mod 4=3 then
#                 asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CN,S[1]^(CS*CN)]
#                  );
#               elif all and p mod 4=1 then
#                 asmax:=Concatenation(asmax,[S[1],S[1]^CN]);
#               else
#                 Add(asmax,S[1]);
#               fi;
#             fi;
#             if q=2 then
#               #  M12
#               _LRS:=Read(Concatenation(c9lib,"m12d11"));
#               _LR:=#EVAL
#                   _LRS;
#               S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#                general:=general,normaliser:=normaliser);
#               Add(asmax,S[1]);
#             fi;
#             if q=7 then
#               #  2L34d10
#               _LRS:=Read(Concatenation(c9lib,"2l34d10"));
#               _LR:=#EVAL
#                   _LRS;
#               S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#                general:=general,normaliser:=normaliser);
#               if all then
#                 asmax:=Concatenation(asmax,[S[1],S[1]^CN]);
#               else
#                 Add(asmax,S[1]);
#               fi;
#             fi;
#             continue;
#           fi;
#           if e=1 and p mod 11 in Set([2,6,7,8,10]) and p<>2 then
#             #  L2_11
#             _LRS:=Read(Concatenation(c9lib,"l211d10a"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all and p mod 4=3 then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CN,S[1]^(CS*CN)])
#                ;
#             elif all and p mod 4=1 then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CN]);
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           if e=1 and p mod 11 in Set([2,6,7,8,10]) and p<>2 then
#             #  A11
#             _LRS:=Read(Concatenation(c9lib,"a11d10"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all and p mod 4=3 then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CN,S[1]^(CS*CN)])
#                ;
#             elif all and p mod 4=1 then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CN]);
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           if q=2 then
#             #  A12
#             _LRS:=Read(Concatenation(c9lib,"a12d11"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             Add(asmax,S[1]);
#           fi;
#           if q=7 then
#             #  2.M22
#             _LRS:=Read(Concatenation(c9lib,"2m22d10"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CN,S[1]^(CS*CN)])
#                ;
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           if q mod 4=3 then
#             #  Sp4q
#             S:=sp4qdim10@(qq:special:=special,general:=general,
#              normaliser:=normaliser);
#             if all then
#               asmax:=Concatenation(asmax,[S,S^CG,S^CN,S^(CG*CN)]);
#             else
#               Add(asmax,S);
#             fi;
#           fi;
#         fi;
#         #  sign=-1
#       fi;
#       #  type = "O"
#     elif d=11 then
#       if novelties then
#         if q=2 then
#           #  L2_23
#           _LRS:=Read(Concatenation(c9lib,"l223d11"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           Add(asmax,S[1]);
#         fi;
#         continue;
#       fi;
#       if type="L" then
#         if e=1 and p mod 3=1 then
#           #  U52
#           _LRS:=Read(Concatenation(c9lib,"u52d11"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             nconj:=Gcd(q-1,11);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if e=1 and p mod 23 in Set([1,2,3,4,6,8,9,12,13,16,18]) and p<>2 then
#           #  L2_23
#           _LRS:=Read(Concatenation(c9lib,"l223d11"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             nconj:=Gcd(q-1,11);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if q=2 then
#           #  M24
#           _LRS:=Read(Concatenation(c9lib,"m24d23"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           Add(asmax,S[1]);
#           Add(asmax,S[2]);
#         fi;
#       elif type="U" then
#         if e=1 and p mod 3=2 and p<>2 then
#           #  U52
#           _LRS:=Read(Concatenation(c9lib,"u52d11"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             nconj:=Gcd(q+1,11);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if e=1 and p mod 23 in Set([5,7,10,11,14,15,17,19,20,21,22]) then
#           #  L2_23
#           _LRS:=Read(Concatenation(c9lib,"l223d11"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             nconj:=Gcd(q+1,11);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#       elif type="O" then
#         if e=1 and Gcd(p,24)=1 and p<>13 then
#           #  A12 (p mod 24 = 7,11,13,17) or A12.2 p mod 24 =1,5,19,23
#           _LRS:=Read(Concatenation(c9lib,"a12d11"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:special:=special,general:=general,
#            normaliser:=normaliser);
#           if all and p mod 24 in Set([1,5,19,23]) then
#             asmax:=Concatenation(asmax,[S[1],S[1]^CS]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if q=13 then
#           #  A13
#           _LRS:=Read(Concatenation(c9lib,"a13d12"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:special:=special,general:=general,
#            normaliser:=normaliser);
#           Add(asmax,S[1]);
#           #  L33.2
#           _LRS:=Read(Concatenation(c9lib,"l33d12"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:special:=special,general:=general,
#            normaliser:=normaliser);
#           if all then
#             asmax:=Concatenation(asmax,[S[1],S[1]^CS]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if p >= 11 and q<>11 then
#           #  L2q
#           S:=OrthogSL2@(d,q:special:=special,general:=general,
#            normaliser:=normaliser);
#           Add(asmax,S);
#         fi;
#       fi;
#     elif d=12 then
#       if type="L" then
#         if novelties then
#           if (e=1 and p mod 3=1 and p mod 5 in Set([1,4])) or (e=2 and p mod 
#              5 in Set([2,3]) and p > 3) then
#             #  6A6
#             _LRS:=Read(Concatenation(c9lib,"6a6d12"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#             if all then
#               nconj:=Gcd(q-1,d);
#               asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           continue;
#         fi;
#         if e=1 and p mod 23 in Set([1,2,3,4,6,8,9,12,13,16,18]) and p<>2 then
#           #  2.L2_23
#           _LRS:=Read(Concatenation(c9lib,"sl223d12"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             nconj:=Gcd(q-1,d);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if e=1 and p mod 3=1 then
#           #  6.Suz
#           _LRS:=Read(Concatenation(c9lib,"6suzd12"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general);
#           if all then
#             nconj:=Gcd(q-1,d);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if q=49 then
#           #  12.L3_4
#           _LRS:=Read(Concatenation(c9lib,"12bl34d12f49"));
#           S:=#EVAL
#               _LRS;
#           if general then
#             S:=SubStructure(GL(d,q),S,#TODO CLOSURE
#               ScalarMat(d,z));
#           fi;
#           if all then
#             nconj:=12;
#             asmax:=Concatenation(asmax,GConjugates@(S,C,nconj));
#           else
#             Add(asmax,S);
#           fi;
#         fi;
#       elif type="U" then
#         if novelties then
#           if e=1 and p mod 3=2 and p mod 5 in Set([1,4]) then
#             #  6A6
#             _LRS:=Read(Concatenation(c9lib,"6a6d12"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#              normaliser:=normaliser);
#             if all then
#               nconj:=Gcd(q+1,d);
#               asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           continue;
#         fi;
#         if e=1 and p mod 23 in Set([5,7,10,11,14,15,17,19,20,21,22]) then
#           #  2.L2_23
#           _LRS:=Read(Concatenation(c9lib,"sl223d12"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             nconj:=Gcd(q+1,d);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if e=1 and p mod 3=2 then
#           #  6.Suz (or 3.Suz of p=2)
#           _LRS:=Read(Concatenation(c9lib,"6suzd12"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           if all then
#             nconj:=Gcd(q+1,d);
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if q=5 then
#           #  6A7
#           _LRS:=Read(Concatenation(c9lib,"6a7d24"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:general:=general,
#            normaliser:=normaliser);
#           S:=Filtered(S,s->Degree(s)=12);
#           if all then
#             nconj:=6;
#             asmax:=Concatenation(asmax,GConjugates@(S[1],C,nconj));
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#       elif type="S" then
#         if novelties then
#           continue;
#         fi;
#         if (e=1 and p mod 5 in Set([1,4])) or (e=2 and p mod 5 in Set([2,3]) 
#            and q<>4) then
#           #  2.L2_11.2 (q=1,19 mod 20), 2.L2_11 o.w.
#           _LRS:=Read(Concatenation(c9lib,"sl211d12"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           if all and p mod 20 in Set([1,19]) then
#             asmax:=Concatenation(asmax,[S[1],S[1]^C]);
#             asmax:=Concatenation(asmax,[S[2],S[2]^C]);
#           else
#             Add(asmax,S[1]);
#             Add(asmax,S[2]);
#           fi;
#         fi;
#         if (e=1 and p mod 7 in Set([1,6]) and p<>13) or (e=3 and p mod 7 in 
#            Set([2,3,4,5])) then
#           #  2.L2_13.2 (q=1,27 mod 28), 2.L2_13 o.w.
#           _LRS:=Read(Concatenation(c9lib,"sl213d12"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           if all and p mod 28 in Set([1,27]) then
#             asmax:=Concatenation(asmax,[S[1],S[1]^C]);
#             asmax:=Concatenation(asmax,[S[2],S[2]^C]);
#             asmax:=Concatenation(asmax,[S[3],S[3]^C]);
#           else
#             Add(asmax,S[1]);
#             Add(asmax,S[2]);
#             Add(asmax,S[3]);
#           fi;
#         fi;
#         if e=1 and p mod 5 in Set([2,3]) and p<>3 then
#           #  2.L2_25 (p!=2), L2_25.2 (p=2)
#           _LRS:=Read(Concatenation(c9lib,"sl225d12"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           Add(asmax,S[1]);
#         fi;
#         if (e=1 and p mod 5 in Set([0,1,4])) or (e=2 and p mod 5 in Set([2,3])
#            ) then
#           #  Sp4_5 (p!=2) or PSp4_5 (p=2)
#           _LRS:=Read(Concatenation(c9lib,"sp45d12"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           if all and p<>2 and p<>5 then
#             asmax:=Concatenation(asmax,[S[1],S[1]^C]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         #   U34 < G24
#         #  if e eq 1 and p ne 2 then
#         #  //U34.4 (p mod 8 = 1,7), U34.2 o.w.
#         #  _LRS := Read(c9lib cat "u34d12");
#         #  _LR := eval _LRS;
#         #  S := ReduceOverFiniteField(_LR,qq: normaliser:=normaliser);
#         #  if all and p mod 8 in {1,7} then
#         #  asmax cat:= [S[1], S[1]^C];
#         #  else Append(~asmax, S[1]);
#         #  end if;
#         #  end if;
#         
#         if e=1 and p<>2 and p<>3 then
#           #  2.G24.2 (p mod 8 = 1,7), 2.G24 o.w.
#           _LRS:=Read(Concatenation(c9lib,"2g24d12"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           if all and p mod 8 in Set([1,7]) then
#             asmax:=Concatenation(asmax,[S[1],S[1]^C]);
#           else
#             Add(asmax,S[1]);
#           fi;
#         fi;
#         if q=3 then
#           #  2.Suz
#           _LRS:=Read(Concatenation(c9lib,"6suzd12"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           Add(asmax,S[1]);
#         fi;
#         if q=2 then
#           #  S_14
#           _LRS:=Read(Concatenation(c9lib,"a14d13"));
#           _LR:=#EVAL
#               _LRS;
#           S:=ReduceOverFiniteField@(_LR,qq:normaliser:=normaliser);
#           Add(asmax,S[1]);
#         fi;
#         if p >= 13 then
#           #  2.L2q
#           S:=SymplecticSL2@(d,q:normaliser:=normaliser);
#           Add(asmax,S);
#         fi;
#       elif type="O" then
#         if sign=1 then
#           if novelties then
#             if e=1 and p mod 13 in Set([1,3,4,9,10,12]) and p<>3 then
#               #  L33
#               _LRS:=Read(Concatenation(c9lib,"l33d12"));
#               _LR:=#EVAL
#                   _LRS;
#               S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#                general:=general,normaliser:=normaliser);
#               if all and p mod 12 in Set([1,11]) then
#                 asmax:=Concatenation(asmax,[S[1],S[1]^CG,S[1]^CN,S[1]^(CG*CN)]
#                  );
#               elif all then
#                 asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CG,S[1]^(CS*CG)]
#                  );
#               else
#                 Add(asmax,S[1]);
#               fi;
#             fi;
#             if e=1 and p >= 5 and p mod 24 in Set([5,7,11,13,17,19]) then
#               #  2.M12
#               _LRS:=Read(Concatenation(c9lib,"2m12d12"));
#               _LR:=#EVAL
#                   _LRS;
#               S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#                general:=general,normaliser:=normaliser);
#               if all and p mod 24 in Set([11,13]) then
#                 asmax:=Concatenation(asmax,[S[1],S[1]^CG,S[1]^CN,S[1]^(CG*CN)]
#                  );
#               elif all then
#                 asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CG,S[1]^(CS*CG)]
#                  );
#               else
#                 Add(asmax,S[1]);
#               fi;
#             fi;
#             continue;
#           fi;
#           if e=1 and p mod 55 in Set([1,16,19,24,26,29,31,36,39,54]) then
#             #  L2_11
#             _LRS:=Read(Concatenation(c9lib,"l211d12"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CN,S[1]^(CS*CN)])
#                ;
#               asmax:=Concatenation(asmax,[S[2],S[2]^CS,S[2]^CN,S[2]^(CS*CN)])
#                ;
#             else
#               Add(asmax,S[1]);
#               Add(asmax,S[2]);
#             fi;
#           fi;
#           if p mod 13 in Set([1,3,4,9,10,12]) and ((e=1 and p mod 7 in 
#              Set([1,6])) or (e=3 and p mod 7 in Set([2,3,4,5]))) then
#             #  L2_13
#             _LRS:=Read(Concatenation(c9lib,"l213d12"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CN,S[1]^(CS*CN)])
#                ;
#               asmax:=Concatenation(asmax,[S[2],S[2]^CS,S[2]^CN,S[2]^(CS*CN)])
#                ;
#               asmax:=Concatenation(asmax,[S[3],S[3]^CS,S[3]^CN,S[3]^(CS*CN)])
#                ;
#             else
#               Add(asmax,S[1]);
#               Add(asmax,S[2]);
#               Add(asmax,S[3]);
#             fi;
#           fi;
#           if e=1 and p mod 13 in Set([1,3,4,9,10,12]) then
#             #  A13
#             _LRS:=Read(Concatenation(c9lib,"a13d12"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CN,S[1]^(CS*CN)])
#                ;
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           if e=1 and p >= 5 and p mod 24 in Set([1,23]) then
#             #  2.M12.2
#             _LRS:=Read(Concatenation(c9lib,"2m12d12"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CS,S[1]^CG,S[1]^(CS*CG)
#                ,S[1]^CN,S[1]^(CS*CN),S[1]^(CG*CN),S[1]^(CS*CG*CN)]);
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#         elif sign=-1 then
#           if novelties then
#             if e=1 and p mod 13 in Set([2,5,6,7,8,11]) and p mod 12 in 
#                Set([5,7]) then
#               #  L33
#               _LRS:=Read(Concatenation(c9lib,"l33d12"));
#               _LR:=#EVAL
#                   _LRS;
#               S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#                general:=general,normaliser:=normaliser);
#               if all then
#                 asmax:=Concatenation(asmax,[S[1],S[1]^CG]);
#               else
#                 Add(asmax,S[1]);
#               fi;
#             fi;
#             continue;
#           fi;
#           if (e=1 and p mod 55 in Set([4,6,9,14,21,34,41,46,49,51])) or (e=2 
#              and p mod 5 in Set([2,3])) then
#             #  L2_11
#             _LRS:=Read(Concatenation(c9lib,"l211d12"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all and p<>2 then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CN]);
#               asmax:=Concatenation(asmax,[S[2],S[2]^CN]);
#             else
#               Add(asmax,S[1]);
#               Add(asmax,S[2]);
#             fi;
#           fi;
#           if p mod 13 in Set([2,5,6,7,8,11]) and ((e=1 and p mod 7 in 
#              Set([1,6])) or (e=3 and p mod 7 in Set([2,3,4,5]))) then
#             #  L2_13
#             _LRS:=Read(Concatenation(c9lib,"l213d12"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all and p<>2 then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CN]);
#               asmax:=Concatenation(asmax,[S[2],S[2]^CN]);
#               asmax:=Concatenation(asmax,[S[3],S[3]^CN]);
#             else
#               Add(asmax,S[1]);
#               Add(asmax,S[2]);
#               Add(asmax,S[3]);
#             fi;
#           fi;
#           if e=1 and p mod 13 in Set([2,5,6,7,8,11]) and p mod 12 in 
#              Set([1,2,11]) then
#             #  L33.2
#             _LRS:=Read(Concatenation(c9lib,"l33d12"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all and p mod 12 in Set([1,11]) then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CG,S[1]^CN,S[1]^(CG*CN)])
#                ;
#             elif all and p=2 then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CS]);
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           if e=1 and p mod 13 in Set([2,5,6,7,8,11]) and p<>7 then
#             #  A13
#             _LRS:=Read(Concatenation(c9lib,"a13d12"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all and p<>2 then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CN]);
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#           if q=7 then
#             #  A14
#             _LRS:=Read(Concatenation(c9lib,"a14d13"));
#             _LR:=#EVAL
#                 _LRS;
#             S:=ReduceOverFiniteField@(_LR,qq:special:=special,
#              general:=general,normaliser:=normaliser);
#             if all then
#               asmax:=Concatenation(asmax,[S[1],S[1]^CN]);
#             else
#               Add(asmax,S[1]);
#             fi;
#           fi;
#         fi;
#         #  sign = 1,-1
#       fi;
#       #  type = "O"
#     fi;
#     #   if d eq ? loop
    fi;
    #   if cl eq d loop
  od;
  #  for cl in classes do
  return asmax;
end;
;

