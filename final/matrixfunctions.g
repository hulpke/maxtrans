#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.35, 12/15/15 by AH

#  Global Variables used: Append, GF, HorizontalJoin, IsSquare, Matrix,
#  Ncols, Nrows, VerticalJoin

#  Defines: BlockMatrix, SquareBlockMatrix

DeclareGlobalFunction("SquareBlockMatrix@");

# the following function seems to be not used, so no translation done

#  * The following function takes as input the 4 matrices A, B, C, D,
#  * defined over the same field, and returns the matrix
#  * A B
#  * C D

# BlockMatrix@:=function(A,B,C,D)
# local mat1,mat2;
#   mat1:=HorizontalJoin(A,B);
#   mat2:=HorizontalJoin(C,D);
#   return VerticalJoin(mat1,mat2);
#   
# end;

#  This function will accept entry 0 to mean the zero matrix, provided
#  that at least one entry in each row and column is not zero.
InstallGlobalFunction(SquareBlockMatrix@,
function(list,q)
local blocks,rows,new,hs,h,v,i,j,range,sel,bool;
  blocks:=Size(list);
  rows:=RootInt(blocks);
  bool:=blocks=rows^2;
  if not bool then
    return false;
  fi;
  q:=GF(q);
  new:=[];
  hs:=[];
  for i in [1..rows] do
    range:=[(i-1)*rows+1..i*rows];
    sel:=list{range};
    if ForAll(sel,x->x=0) then
      Info(InfoWarning,1,"each row must contain a nonzero entry");
      return 0;
    fi;
    v:=Length(First(sel,x->x<>0)); # vertical height
    # test for 0 blocks, replace
    for j in [1..rows] do
      if sel[j]=0 then
	# find horizontal width
	if not IsBound(hs[j]) then
	  h:=First(list{[j,j+rows..j+rows*(rows-1)]},x->x<>0);
	  if h=fail then
	    Info(InfoWarning,1,"each column must contain a nonzero entry");
	    return 0;
	  fi;
	  hs[j]:=h;
	else
	  h:=hs[j];
	fi;
	sel[j]:=NullMat(v,h,q);
      fi;
    od;
  od;
  for j in [1..v] do
    Add(new,Concatenation(List(sel,x->x[j])));
  od;
  return ImmutableMatrix(new,q);

end);

