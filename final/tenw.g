DeclareGlobalFunction("TensorWreathProduct");

InstallGlobalFunction(TensorWreathProduct,function(M,P)
local d,e,f,s,dim,gens,mimgs,pimgs,tup,act,a;
  d:=Length(One(M));
  f:=DefaultFieldOfMatrixGroup(M);
  e:=LargestMovedPoint(P);
  s:=SymmetricGroup(e);
  dim:=d^e;
  gens:=[];
  mimgs:=[];
  for g in GeneratorsOfGroup(M) do
    a:=NullMat(dim,dim,f);
    for i in [1..dim/d] do
      tup:=[1..d]+(i-1)*d;
      a{tup}{tup}:=g;
    od;
    a:=ImmutableMatrix(f,a);
    Add(gens,a);
    Add(mimgs,a);
  od;
  tup:=List(Tuples([1..d],e),Reversed); # reverse to be consistent with Magma
  act:=ActionHomomorphism(s,tup,Permuted,"surjective");
  pimgs:=[];
  for g in GeneratorsOfGroup(P) do
    a:=PermutationMat(Image(act,g),dim,f);
    a:=ImmutableMatrix(f,a);
    Add(gens,a);
    Add(pimgs,a);
  od;
  return Group(gens);
end);
