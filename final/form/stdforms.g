#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.37, 12/20/15 by AH

# taken from `classical/standard.m'

Nonsquare@:=function(F)
#  -> ,FldFinElt  A nonsquare in F
local delta,i,q,r;
  q:=Size(F);
  if not IsOddInt(q)then
    Error("The field must have odd characteristic");
  fi;
  r:=Valuation(q-1,2);
  delta:=-One(F);
  for i in [2..r] do
    delta:=RootFFE(delta,2);
  od;
  return delta;
  
end;

#   test
#  pps := [ q : q in [2..100] | IsOdd(q) and IsPrimePower(q) ];
#  forall(q){ q : q in pps | not IsSquare(Nonsquare(GF(q))) };

#   F finite of even char, returns an element outside of
#   F^[2] := { a^2+a : a in F }

IsSquarish@:=
function(a)
local P,x,f;

  x:=X(DefaultRing(a),1);
  f:=x^2+x+a;
  if IsIrreducible(f) then
    return rec(val1:=false,
      val2:=fail);
  else
    return rec(val1:=true,
      val2:=RootsOfUPol(f)[1][1]);
  fi;
  
end;

Nonsquarish@:=
function(F)
local delta,new,sqr;
  new:=One(F);
  repeat
    delta:=new;
    # =v= MULTIASSIGN =v=
    new:=IsSquarish@(delta);
    sqr:=new.val1;
    new:=new.val2;
    # =^= MULTIASSIGN =^=
    
  until not sqr;
  return delta;
  
end;
#   test
#  pps := [ 2^i : i in [1..100] ];
#  forall(q){ q : q in pps | not IsSquarish(Nonsquarish(GF(q))) };

#   This is StandardQuadaticFormPlus(n,F : Variant := "Revised")
QuadraticFormPlus@:=function(n,F)
#  -> ,AlgMatElt  The matrix of the standard quadratic plus type form of even
#  degree n over F
local J,i,m;
  if not n >= 0 and IsEvenInt(n) then
    Error("the degree should be an even non-negative integer");
  fi;
  J:=ZeroMatrix(F,n,n);
  m:=QuoInt(n,2);
  for i in [1..m] do
    J[i][n-i+1]:=1;
  od;
  return J;
  
end;

#   This is StandardQuadaticFormMinus(n,F : Minus, Variant := "Revised")
QuadraticFormMinus@:=function(n,F)
#  -> ,AlgMatElt  The matrix of the standard orthogonal minus type form of
#  even degree n over F
local J,i,m;
  if not n > 0 and IsEvenInt(n)then
    Error("the degree should be an even positive integer");
  fi;
  if not IsFinite(F)then
    Error("The field must be finite");
  fi;
  J:=ZeroMatrix(F,n,n);
  m:=QuoInt(n,2);
  for i in [1..m-1] do
    J[i][n-i+1]:=1;
  od;
  if Characteristic(F)<>2 then
    J[m][m]:=1/2;
    J[m+1][m+1]:=-Nonsquare@(F)/2;
  else
    J[m][m]:=1;
    J[m+1][m+1]:=Nonsquarish@(F);
    J[m][m+1]:=1;
  fi;
  return J;
  
end;

QuadraticForm@:=function(t,n,F)
#  -> ,AlgMatElt  The matrix of the standard orthogonal form of degree n and
#  sign t over F
local Q,m;
  if not IsFinite(F)then
    Error("the field must be finite");
  fi;
  if IsEvenInt(n) then
    if not t in [1,-1]then
      Error("sign should be 1 or -1");
    fi;
    if (t=1) then
      return QuadraticFormPlus@(n,F);
    else
      return QuadraticFormMinus@(n,F);
    fi;
  else
    if not t in [1,0,-1]then
      Error("sign should be 1, 0 or -1");
    fi;
    Q:=QuadraticForm@(n,F);
    if t<>0 then
      if not Characteristic(F)<>2 then
        Error("invalid odd degree with characteristic 2");
      fi;
      m:=QuoInt(n,2);
      if t=1 then
	Q[m+1][m+1]:=One(F)/2;
      else
	Q[m+1][m+1]:=Nonsquare@(F)/2;
      fi;
    fi;
    return Q;
  fi;
  
end;

SymmetricBilinearFormPlus@:=function(n,F)
#  -> ,AlgMatElt  The matrix of the standard symmetric bilinear plus type
#  form of even degree n over F
local Q;
  Q:=QuadraticFormPlus@(n,F);
  return (Q+TransposedMat(Q));
end;

SymmetricBilinearFormMinus@:=function(n,F)
#  -> ,AlgMatElt  The matrix of the standard symmetric bilinear minus type
#  form of even degree n over F
local Q;
  Q:=QuadraticFormMinus@(n,F);
  return (Q+TransposedMat(Q));
end;



