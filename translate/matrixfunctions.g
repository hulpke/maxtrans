#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Append, GF, HorizontalJoin, IsSquare, Matrix, Ncols,
#  Nrows, VerticalJoin, ZeroMatrix

#  Defines: BlockMatrix, SquareBlockMatrix, ZeroMatrix

DeclareGlobalFunction("SquareBlockMatrix@");

DeclareGlobalFunction("ZeroMatrix@");

InstallGlobalFunction(ZeroMatrix@,
function(q,d_1,d_2)
return MatrixByEntries(GF(q),d_1,d_2,[]);
end);

#  
#  * The following function takes as input the 4 matrices A, B, C, D,
#  * defined over the same field, and returns the matrix
#  * A B
#  * C D

BlockMatrix@:=function(A,B,C,D)
local mat1,mat2;
  mat1:=HorizontalJoin(A,B);
  mat2:=HorizontalJoin(C,D);
  return VerticalJoin(mat1,mat2);
end;
;
#  This function will accept entry 0 to mean the zero matrix, provided
#  that at least one entry in each row and column is not zero.
InstallGlobalFunction(SquareBlockMatrix@,
function(input_list,q)
local 
   blocks,bool,colset,finalmat,i,list,ncols,nrows,range,rowmats,rows,temp,x,
   zeroset;
  blocks:=Size(input_list);
  list:=# [*-list:
  [];
  for x in input_list do
    Add(list,x);
  od;
  # =v= MULTIASSIGN =v=
  rows:=IsSquare(blocks);
  bool:=rows.val1;
  rows:=rows.val2;
  # =^= MULTIASSIGN =^=
  if not bool then
    return false;
  fi;
  rowmats:=# [*-list:
  [];
  for i in [1..rows] do
    range:=[(i-1)*rows+1..i*rows];
    zeroset:=Filtered(range,x->list[x]=0);
    if Size(zeroset) > 0 then
      for x in zeroset do
        if not rowmat:=ForAny(range,y->not list[y]=0) then
          Info(InfoWarning,1,"each row must contain a nonzero entry");
          return 0;
        fi;
        nrows:=Length(list[rowmat]);
        colset:=Filtered([1..blocks],j->(j mod rows)=(x mod rows));
        if not colmat:=ForAny(colset,z->not list[z]=0) then
          Info(InfoWarning,1,"each column must contain a nonzero entry");
          return 0;
        fi;
        ncols:=Ncols(list[colmat]);
        list[x]:=ZeroMatrix@(q,nrows,ncols);
      od;
    fi;
    temp:=MatrixByEntries(HorizontalJoin(List( # <-list:
      [1..rows],j->list[((i-1)*rows)+j])));
    Add(rowmats,temp);
  od;
  finalmat:=VerticalJoin(List( # <-list:
    [1..rows],i->rowmats[i]));
  return finalmat;
end);


