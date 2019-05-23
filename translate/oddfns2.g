#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: AddStrongGenerator, Append, AppendBasePoint, Base,
#  BasicOrbitLengths, Labelling, Random, RandomProcess, RandomSchreierCoding,
#  Strip, UpdateLevels

#  Defines: IncorporateCentralisingGenerators

DeclareGlobalFunction("IncorporateCentralisingGenerators@");

InstallGlobalFunction(IncorporateCentralisingGenerators@,
function(GQ,TILDEVAR~GQnew,C,TILDEVAR~prgens)
local GQnew,P1,P2,varX,c,flag,lev,res,x;
  varX:=RandomSchreierCoding(GQnew:Run:=5);
  if Product(BasicOrbitLengths(varX)=Size(GQ)) then
    return rec();
  fi;
  P1:=RandomProcess(GQnew);
  P2:=RandomProcess(C);
  repeat
    c:=Random(P2);
    x:=c*Random(P1);
    # =v= MULTIASSIGN =v=
    lev:=Strip(varX,x);
    flag:=lev.val1;
    res:=lev.val2;
    lev:=lev.val3;
    # =^= MULTIASSIGN =^=
    if flag then
      continue;
    fi;
    if lev > Size(Base(varX)) then
      Assert(1,lev=Size(Base(varX))+1);
      flag:=p:=ForAny(Labelling(GQ),p->p^res<>p);
      Assert(1,flag);
      AppendBasePoint(varX,p);
    fi;
    AddStrongGenerator(varX,res,n);
    UpdateLevels(varX,n,1,lev);
    GQnew:=SubStructure(GQ,GQnew,#TODO CLOSURE
      c);
    Add(prgens,1);
    
  until Product(BasicOrbitLengths(varX)=Size(GQ));
  GQnew.Order:=Size(GQ);
end);


