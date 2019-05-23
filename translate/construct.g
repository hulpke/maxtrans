#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: ActionGroup, AllRoots, Append, ChangeMat,
#  ClassicalForms, Constituents, Degree, Determinant, Dimension, Eltseq,
#  ExtendedGreatestCommonDivisor, Factorisation, GCD, GF, GL, GModule,
#  IsAbsolutelyIrreducible, IsEven, IsIsomorphic, IsOdd, IsPower, ListMatToQ,
#  Log, Ngens, Orbits, Order, PrimitiveElement, ProjectiveOrder,
#  Representative, ScalarMatrix, Sym, TransformForm, Transpose, phi

#  Defines: ChangeMat, ListMatToQ, ReduceOverFiniteField

DeclareGlobalFunction("ReduceOverFiniteField@");

#  ***********************************************************************
#  * ChangeMat returns either Tranpose(Frobenius(mat)) or
#  * Transpose(mat), depending on whether we have a form s.t.
#  * g*form*Transpose(g) = form or g * form*(Transpose(Frobenius(g)))
#  * = form.

ListMatToQ@:=function(a,q)
#  /out: raise every element of matrix A to q-th power.
local i,list;
  list:=Eltseq(a);
  for i in [1..Size(list)] do
    list[i]:=list[i]^q;
  od;
  return list;
end;
;
ChangeMat@:=function(mat,type,d,p)
if type="unitary" then
    return TransposedMat(ListMatToQ@(mat,p) #CAST GL(d,p^2)
      );
  else
    return TransposedMat(mat);
  fi;
end;
;
InstallGlobalFunction(ReduceOverFiniteField@,
function(L,q)
#  /out: L should be "lattice record" with components:
#  * G: A finite irreducible quasisimple 2-generator matrix group over Z
#  * F: FreeGroup(2),
#  * AI: list of automorphisms of G described by generator images given as
#  *     words in F
#  * q = prime power, special = true/false
#  * Reduce G over GF(q) and find irreducible constituents of corresponding
#  * module. Work out action of automorphisms on these constituents,
#  * appending any new modules found to the list
#  * Choose orbit representatives of this action, and for each orbit
#  * append reduced group by any stabilizing automorphisms.
#  *
#  * By default, the subgroup of the relevant quasisimple group is returned.
#  * If special is true (case O only), normaliser in SO is returned.
#  * If general is true (cases L/U/O), normaliser in GL, GU, GO is returned.
#  * If normaliser is true (cases Sp/U/O) normaliser in GL is returned.
#  * Return list of resulting groups, one for each orbit.

local 
   AC,AG,AI,C,CC,F,G,M,M2,OAG,Q,_,a,c,co,d,det,dsq,f,ff,form,forms,g,general,
   gens,got,gps,i,isit,iso,j,lv,mat,modims,na,nc,new,normaliser,o,ox,perms,phi,
   po,quad,rq,rts,sAG,scal,sgens,sgn,special,stuff,tmat,u,v,w,ww,x;
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
  if normaliser then
    general:=true;
  fi;
  if general then
    special:=true;
  fi;
  G:=L.G;
  AI:=L.AI;
  F:=L.F;
  d:=DimensionOfMatrixGroup(G);
  Q:=SubStructure(GL(d,q),G.1,#TODO CLOSURE
    G.2);
  M:=GModule(Q);
  C:=Constituents(M);
  CC:=[];
  for c in C do
    if not IsAbsolutelyIrreducible(c) then
      Error("Constituents are not absolutely irreducible over finite field.");
    fi;
    #  if Dimension(c) eq 1 then
    #  "Module has a trivial constituent.";
    #  else Append(~CC,c);
    if DimensionOfMatrixGroup(c)<>1 then
      Add(CC,c);
    fi;
  od;
  C:=CC;
  AC:=List(C,c->ActionGroup(c));
  modims:=[];
  i:=1;
  while i <= Size(C) do
    modims[i]:=[];
    phi:=GroupHomomorphismByImages(F,AC[i],
      AC[i].1,AC[i].2);
    for a in AI do
      M2:=GModule(Q,[phi(a[1]),phi(a[2])]);
      new:=true;
      for j in [1..Size(C)] do
        if IsIsomorphic(C[j],M2) then
          Add(modims[i],j);
          new:=false;
          break;
        fi;
      od;
      if new then
        Add(C,M2);
        Add(AC,ActionGroup(M2));
        Add(modims[i],Size(C));
      fi;
    od;
    i:=i+1;
  od;
  nc:=Size(C);
  na:=Size(AI);
  perms:=List([1..na],j->List([1..nc],i->modims[i][j]));
  AG:=SubStructure(SymmetricGroup(nc),perms);
  OAG:=Orbits(AG);
  gps:=[];
  w:=PrimitiveElement(GF(q));
  for o in OAG do
    i:=Representative(o);
    d:=Degree(AC[i]);
    #  test if the group fixes a form, and act accordingly.
    forms:=ClassicalForms(AC[i]);
    if forms.formType="linear" then
      # rewritten select statement
      if general then
        ww:=w;
      else
        ww:=w^(QuoInt((q-1),Gcd(q-1,d)));
      fi;
      #  power of w s.t. ww I_d has det 1
      gens:=List([1..Ngens(AC[i])],j->AC[i].j);
      #  find generators of subgroup of automorphism group stabilizing this
      #  module
      sgens:=[];
      for j in [1..na] do
        if i^perms[j]=i then
          Add(sgens,j);
        fi;
      od;
      for j in sgens do
        #  Attempt to append this automorphism to AC[i];
        a:=AI[j];
        phi:=GroupHomomorphismByImages(F,AC[i],
          AC[i].1,AC[i].2);
        M2:=GModule(Q,[phi(a[1]),phi(a[2])]);
        # =v= MULTIASSIGN =v=
        iso:=IsIsomorphic(C[i],M2);
        isit:=iso.val1;
        iso:=iso.val2;
        # =^= MULTIASSIGN =^=
        if not isit then
          Error("Bug!");
        fi;
        det:=DeterminantMat(iso);
        # =v= MULTIASSIGN =v=
        v:=IsPower(det,d);
        isit:=v.val1;
        v:=v.val2;
        # =^= MULTIASSIGN =^=
        if isit then
          iso:=iso*ScalarMat(GF(q),d,v^-1);
        elif not general then
          continue;
        fi;
        #  We will try to make the order of iso as small as possible.
        #  if general is true, we will sacrifice determinant 1 if necessary
        # =v= MULTIASSIGN =v=
        x:=ProjectiveOrder(iso);
        po:=x.val1;
        x:=x.val2;
        # =^= MULTIASSIGN =^=
        ox:=Order(x);
        if ox > 1 then
          f:=CollectedFactors(ox);
          ff:=List(f,x->QuoInt(ox,x[1]^x[2]));
          #  e.g. ox=180, ff=[45, 20, 36].
          # =v= MULTIASSIGN =v=
          co:=ExtendedGreatestCommonDivisor(ff);
          _:=co.val1;
          co:=co.val2;
          # =^= MULTIASSIGN =^=
          for i in [1..Size(f)] do
            u:=x^(co[i]*ff[i]);
            #  factor of x with order f[i][1]^f[i][2]
            rts:=AllRoots(u,po);
            if rts<>[] then
              got:=false;
              for v in rts do
                if Log(v) mod (QuoInt((q-1),Gcd(q-1,d)))=0 then
                  #  v * I_d has det 1
                  iso:=iso*ScalarMat(GF(q),d,v^-1);
                  got:=true;
                  break;
                fi;
              od;
              if general and not got then
                iso:=iso*ScalarMat(GF(q),d,rts[1]^-1);
              fi;
            fi;
          od;
        fi;
        Add(gens,iso);
      od;
      #  finally adjoin scalars
      if (not general and Gcd(q-1,d)<>1) or (general and q > 2) then
        Add(gens,ScalarMat(GF(q),d,ww));
      fi;
      Add(gps,SubStructure(GL(d,q),gens));
    elif forms.formType="unitary" then
      form:=forms.sesquilinearForm;
      f:=CollectedFactors(q);
      rq:=f[1][1]^(QuoInt(f[1][2],2));
      # rewritten select statement
      if normaliser then
        ww:=w;
      else
        # rewritten select statement
        if general then
          ww:=w^(rq-1);
        else
          ww:=w^((rq-1)*(QuoInt((rq+1),Gcd(rq+1,d))));
        fi;
      fi;
      #  power of w^(rq-1) s.t. ww I_d has det 1
      gens:=List([1..Ngens(AC[i])],j->AC[i].j);
      #  find generators of subgroup of automorphism group stabilizing this
      #  module
      sgens:=[];
      for j in [1..na] do
        if i^perms[j]=i then
          Add(sgens,j);
        fi;
      od;
      for j in sgens do
        #  Attempt to append this automorphism to AC[i];
        a:=AI[j];
        phi:=GroupHomomorphismByImages(F,AC[i],
          AC[i].1,AC[i].2);
        M2:=GModule(Q,[phi(a[1]),phi(a[2])]);
        # =v= MULTIASSIGN =v=
        iso:=IsIsomorphic(C[i],M2);
        isit:=iso.val1;
        iso:=iso.val2;
        # =^= MULTIASSIGN =^=
        if not isit then
          Error("Bug!");
        fi;
        #  adjust by scalar to make iso fix form.
        scal:=(iso*form*ChangeMat@(iso,"unitary",d,rq)*form^-1)[1][1];
        # =v= MULTIASSIGN =v=
        v:=IsPower(scal #CAST GF(q)
          ,rq+1);
        isit:=v.val1;
        v:=v.val2;
        # =^= MULTIASSIGN =^=
        iso:=iso*ScalarMat(d,v^-1);
        #  try to make determinant 1
        det:=DeterminantMat(iso);
        rts:=AllRoots(det,d);
        got:=false;
        for v in rts do
          if Log(v) mod (rq-1)=0 then
            iso:=iso*ScalarMat(GF(q),d,v^-1);
            got:=true;
            break;
          fi;
        od;
        if not general and not got then
          continue;
        fi;
        #  We will try to make the order of iso as small as possible.
        #  if general is true, we will sacrifice determinant 1 if necessary
        #  if normaliser is true, we will sacrifice fixing form if necessary
        # =v= MULTIASSIGN =v=
        x:=ProjectiveOrder(iso);
        po:=x.val1;
        x:=x.val2;
        # =^= MULTIASSIGN =^=
        ox:=Order(x);
        if ox > 1 then
          f:=CollectedFactors(ox);
          ff:=List(f,x->QuoInt(ox,x[1]^x[2]));
          #  e.g. ox=180, ff=[45, 20, 36].
          # =v= MULTIASSIGN =v=
          co:=ExtendedGreatestCommonDivisor(ff);
          _:=co.val1;
          co:=co.val2;
          # =^= MULTIASSIGN =^=
          for i in [1..Size(f)] do
            u:=x^(co[i]*ff[i]);
            #  factor of x with order f[i][1]^f[i][2]
            rts:=AllRoots(u,po);
            got:=false;
            if rts<>[] then
              got:=false;
              for v in rts do
                if Log(v) mod ((rq-1)*(QuoInt((rq+1),Gcd(rq+1,d))))=0 then
                  #  v * I_d has det 1 and is in GU
                  iso:=iso*ScalarMat(GF(q),d,v^-1);
                  got:=true;
                  break;
                fi;
              od;
              if general and not got then
                for v in rts do
                  if Log(v) mod (rq-1)=0 then
                    #  v * I_d fixes form
                    iso:=iso*ScalarMat(GF(q),d,v^-1);
                    got:=true;
                    break;
                  fi;
                od;
                if normaliser and not got then
                  iso:=iso*ScalarMat(GF(q),d,rts[1]^-1);
                fi;
              fi;
            fi;
          od;
        fi;
        Add(gens,iso);
      od;
      #  finally adjoin scalars
      if general or Gcd(rq+1,d)<>1 then
        Add(gens,ScalarMat(GF(q),d,ww));
      fi;
      g:=TransformForm(form,forms.formType);
      Add(gps,SubStructure(GL(d,q),gens)^g);
    else
      form:=forms.bilinearForm;
      if IsEvenInt(q) and forms.quadraticForm<>false then
        quad:=true;
        form:=forms.quadraticForm;
      else
        quad:=false;
      fi;
      tmat:=TransformForm(form,forms.formType);
      gens:=List([1..Ngens(AC[i])],j->(AC[i].j)^tmat);
      #  find generators of subgroup of automorphism group stabilizing this
      #  module
      sgens:=[];
      for j in [1..na] do
        if i^perms[j]=i then
          Add(sgens,j);
        fi;
      od;
      if forms.formType="orthogonalplus" then
        dsq:=d mod 4=0 or (d mod 4=2 and q mod 4=1);
        sgn:=1;
      elif forms.formType="orthogonalminus" then
        dsq:=d mod 4=2 and q mod 4=3;
        sgn:=-1;
      else
        dsq:=false;
        sgn:=0;
      fi;
      for j in sgens do
        #  Attempt to append this automorphism to AC[i];
        a:=AI[j];
        phi:=GroupHomomorphismByImages(F,AC[i],
          AC[i].1,AC[i].2);
        M2:=GModule(Q,[phi(a[1]),phi(a[2])]);
        # =v= MULTIASSIGN =v=
        iso:=IsIsomorphic(C[i],M2);
        isit:=iso.val1;
        iso:=iso.val2;
        # =^= MULTIASSIGN =^=
        if not isit then
          Error("Bug!");
        fi;
        #  try to adjust by scalar to make iso fix form.
        if quad then
          got:=false;
          mat:=iso*form*TransposedMat(iso);
          for i in [2..d] do
            for j in [1..i-1] do
              mat[j][i]:=mat[j][i]+mat[i][j];
              if mat[j][i]<>0 #CAST GF(q)
                 and not got then
                scal:=mat[j][i]*form[j][i]^-1;
                got:=true;
              fi;
              mat[i][j]:=0*mat[i][j];
            od;
          od;
        else
          scal:=(iso*form*TransposedMat(iso)*form^-1)[1][1];
        fi;
        # =v= MULTIASSIGN =v=
        v:=IsPower(scal,2);
        isit:=v.val1;
        v:=v.val2;
        # =^= MULTIASSIGN =^=
        if isit then
          iso:=iso*ScalarMat(d,v^-1);
        elif not normaliser then
          continue;
        fi;
        det:=DeterminantMat(iso);
        if det=(-1) #CAST GF(q)
           and IsOddInt(d) then
          iso:=iso*ScalarMat(GF(q),d,(-1) #CAST GF(q)
            );
        elif not general and det<>1 #CAST GF(q)
           then
          continue;
        fi;
        iso:=tmat^-1*iso*tmat;
        if not special then
          if (forms.formType="orthogonalplus" and not InOmega@(iso,d,q,1)) or 
             (forms.formType="orthogonalminus" and not InOmega@(iso,d,q,-1)) 
             then
            if IsOddInt(q) and not dsq then
              iso:=-iso;
            else
              continue;
            fi;
          fi;
          if forms.formType="orthogonalcircle" and not InOmega@(iso,d,q,0) then
            continue;
          fi;
        fi;
        #  We will try to make the order of iso as small as possible.
        #  if normaliser is true, we will sacrifice fixing form if necessary
        # =v= MULTIASSIGN =v=
        x:=ProjectiveOrder(iso);
        po:=x.val1;
        x:=x.val2;
        # =^= MULTIASSIGN =^=
        ox:=Order(x);
        if special and ox > 1 then
          f:=CollectedFactors(ox);
          ff:=List(f,x->QuoInt(ox,x[1]^x[2]));
          #  e.g. ox=180, ff=[45, 20, 36].
          # =v= MULTIASSIGN =v=
          co:=ExtendedGreatestCommonDivisor(ff);
          _:=co.val1;
          co:=co.val2;
          # =^= MULTIASSIGN =^=
          for i in [1..Size(f)] do
            u:=x^(co[i]*ff[i]);
            #  factor of x with order f[i][1]^f[i][2]
            rts:=AllRoots(u,po);
            if rts<>[] then
              got:=false;
              for v in rts do
                if v=(-1) #CAST GF(q)
                   and IsEvenInt(d) and IsOddInt(q) then
                  #  v * I_d has det 1
                  iso:=iso*ScalarMat(GF(q),d,v^-1);
                  got:=true;
                  break;
                fi;
              od;
              if normaliser and not got then
                iso:=iso*ScalarMat(GF(q),d,rts[1]^-1);
              fi;
            fi;
          od;
        fi;
        Add(gens,iso);
      od;
      #  finally adjoin scalars
      if normaliser and q > 2 then
        Add(gens,ScalarMat(GF(q),d,w));
      elif (general and IsOddInt(q)) or (special and IsEvenInt(d) and 
         IsOddInt(q)) or (forms.formType="symplectic" or (IsEvenInt(d) and dsq))
          then
        Add(gens,ScalarMat(GF(q),d,(-1) #CAST GF(q)
          ));
      fi;
      Add(gps,SubStructure(GL(d,q),gens));
    fi;
  od;
  return gps;
end);


