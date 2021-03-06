#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.35, 12/15/15 by AH

#  Global Variables used: GF, GL, PrimitiveElement

#  Defines: Spin8Minus

DeclareGlobalFunction("Spin8Minus@");

#  
#  Construction of Spin_8^-(q) - by John Bray

#   Two visible submodules generated by V.i, i in {1,4,6,7,10,11,13,16} and
#  {2,3,5,8,9,12,14,15}.
#   x23o only required when q=3.
#   x1, x7, x8 to the same named elements in Spin_8^+(q) construction.
#   x4 vaguely correponds to element named x4 in Spin_8^+(q) construction,
#  but has order q+1 instead of q-1.
#   x23 corresponds to x2*x3^-1 in Spin_8^+(q) construction, and x23o is also
#  in <x2,x3>.
#   x26 and x46 correspond to the elements x2^x6 and x4^x6 in Spin_8^+(q)
#  construction.
InstallGlobalFunction(Spin8Minus@,
function(q)
local F,G,a,aa,b,bb,c,cc,x8,o;
  F:=GF(q^2);
  o:=One(F);
  b:=PrimitiveElement(F);
  bb:=1/b;
  c:=b^(q-1);
  cc:=1/c;
  a:=b^(q+1);
  aa:=1/a;
  G:=Group([
  [0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0]]*o
  ,[
  [1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,1,0,0,-1,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,1,0,0,-1,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,-1],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]]*o
  ,[
  [1,0,0,-c^q,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,1,c,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,1,0,0,-c^q,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,1,c,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,1,0,0,-c^q,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,1,c,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,-c^q],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,1,c,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]]*o
  ,[
  [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]]*o
  ,[
  [c,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,c^-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,c,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,c^-1,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,c,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,c^-1,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,c,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,c^-1,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,c,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,c^-1,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,c,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,c^-1,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,c,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,c^-1,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,c,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,c^-1]]*o
  ,[
  [a,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,a,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,a^-1,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,a^-1,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,a,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,a,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,a^-1,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,a^-1,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,a,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,a,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,a^-1,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,a^-1,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,a,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,a,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,a^-1,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,a^-1]]*o
  ,[
  [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
  [0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]]*o
  );
  x8:=[
  [0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1],
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0]]*o;
  x8:=ImmutableMatrix(F,x8);
  return rec(val1:=G,
      val2:=x8);

end);

