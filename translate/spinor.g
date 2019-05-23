#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: GF, GL, GO, GOMinus, GOPlus, IsSquare, Matrix,
#  PrimitiveElement, SpinorNorm, SymmetricBilinearForm

#  Defines: GetAandB, InOmega

DeclareGlobalFunction("InOmega@");

#   Most of this file has moved to Group/GrpMat/Classical
InstallGlobalFunction(InOmega@,
function(g,d,q,sign)
local form,isf;
  if sign=1 then
    if d=2 then
      form:=MatrixByEntries(GF(q),2,2,[0,1,1,0]);
    else
      # =v= MULTIASSIGN =v=
      form:=SymmetricBilinearForm(GOPlus(d,q));
      isf:=form.val1;
      form:=form.val2;
      # =^= MULTIASSIGN =^=
    fi;
  elif sign=-1 then
    # =v= MULTIASSIGN =v=
    form:=SymmetricBilinearForm(GOMinus(d,q));
    isf:=form.val1;
    form:=form.val2;
    # =^= MULTIASSIGN =^=
  else
    # =v= MULTIASSIGN =v=
    form:=SymmetricBilinearForm(GO(d,q));
    isf:=form.val1;
    form:=form.val2;
    # =^= MULTIASSIGN =^=
  fi;
  return SpinorNorm(g #CAST GL(d,q)
    ,form)=0;
end);

#  This function makes matrix entries that are needed for the
#  conformal orthogonal group = normaliser of GO in GL.
GetAandB@:=function(q)
local a,b,bool,z;
  z:=PrimitiveElement(GF(q));
  for a in GF(q) do
    # =v= MULTIASSIGN =v=
    b:=IsSquare(z-a^2);
    bool:=b.val1;
    b:=b.val2;
    # =^= MULTIASSIGN =^=
    if bool then
      return rec(val1:=a,
        val2:=b);
    fi;
  od;
end;
;

