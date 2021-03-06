#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.43, 4/04/16 by AH

#  Global Variables used: Degree, IsConjugate, Ngens, Order, Sym

#  Defines: ImageCopies, IsNormalised, SelectGroupFromSubset, 
 SelectGroupGeneral

DeclareGlobalFunction("ImageCopies@");

DeclareGlobalFunction("SelectGroupFromSubset@");

DeclareGlobalFunction("SelectGroupGeneral@");

#  
#  Function names:
#  IsNormalised(group, elt)
#  SelectGroup(subgroup, diag, norm_elt, factor)
#  ImageCopies(group, c, factor, homom, d,  p)

#  import "normconj.m": PartitionIsConjugate;
#  
#  * This file contains the functions which are needed to select
#  * 1 or more conjugates of a subgroup which extend under the action of
#  * some outer involution. The idea is to use this when one is trying to
#  * work out which copies of a group extend rather than fusing.
#  *
#  * It also contains functions to find group elements which do not lie
#  * in the socle.

#  ****************************************************
#  * This is just a handy function which takes a group  *
#  * and an element and returns true if the element     *
#  * normalises the group and false otherwise. ASSUMES *
#  * that the group is nontrivial.                      *
#  ****************************************************
IsNormalised@:=function(group,elt)
local i,ngens;
  ngens:=Ngens(group);
  for i in [1..ngens] do
    if not ((group.i)^elt in group) then
      return false;
    fi;
  od;
  return true;
end;
;
#  following function has been amended by dfh to check for conjugation
#  and to return only a single subgroup
InstallGlobalFunction(SelectGroupGeneral@,
function(group,subgroup,diag,norm_elt)
local conelt,i,isit,k,o,overgroup;
  overgroup:=SubStructure(SymmetricGroup(Degree(group)),group,#TODO CLOSURE
    diag);
  # =v= MULTIASSIGN =v=
  conelt:=IsConjugate(overgroup,subgroup,subgroup^norm_elt);
  isit:=conelt.val1;
  conelt:=conelt.val2;
  # =^= MULTIASSIGN =^=
  if not isit then
    Error("No normalized conjugate found (A)");
  fi;
  o:=Order(diag);
  for i in [0..(o-1)] do
    if conelt*diag^-i in group then
      #   Normalized conjugate is subgroup^(diag^k))
      #   where diag^(2k-i) in group
      for k in [0..(o-1)] do
        if diag^(2*k-i) in group then
          #  print "Found conjugate in SelectGroupGeneral";
          return subgroup^(diag^k);
        fi;
      od;
    fi;
  od;
  Error("No normalized conjugate found (B)");
end);

#  following function has been amended by dfh to check for conjugation
#  and to return only a single subgroup
#  has now been amended again by colva as if there's less conjugates of
#  the group than the order of diag, sometimes we were getting the "wrong"
#  conjugating element out of conelt, and was failing to find normalised
#  subgroup. c is the number of conjugacy classes under conelt.
#  This function assumes that diag and norm_elt generate a group (modulo input
#  group "group") which is isomorphic to a dihedral group of order 2*c. diag
#  has order c in its action on cosets, and norm_elt inverts it.
InstallGlobalFunction(SelectGroupFromSubset@,
function(group,subgroup,diag,norm_elt,c)
local conelt,i,isit,k,o,overgroup,s;
  overgroup:=SubStructure(SymmetricGroup(Degree(group)),group,#TODO CLOSURE
    diag);
  # =v= MULTIASSIGN =v=
  conelt:=IsConjugate(overgroup,subgroup,subgroup^norm_elt);
  isit:=conelt.val1;
  conelt:=conelt.val2;
  # =^= MULTIASSIGN =^=
  if not isit then
    Error("No normalized conjugate found (A)");
  fi;
  o:=Order(diag);
  Assert(1,(o mod c)=0);
  s:=QuoInt(o,c);
  for i in [0..(o-1)] do
    if conelt*diag^-i in group then
      #  "conelt*diag^-i in PSL for i =", i;
      #   Normalized conjugate is subgroup^(diag^k))
      #   where diag^(2k-i) in group
      for k in [0..(o-1)] do
        if ((2*k-i) mod c)=0 then
          #  "Found conjugate in SelectGroupGeneral. k =", k;
          return subgroup^(diag^k);
        fi;
      od;
    fi;
  od;
  Error("No normalized conjugate found (B)");
end);

#  
#  * This makes c copies of a group that are GL-conjugate and then
#  * returns their images in PSL

InstallGlobalFunction(ImageCopies@,
function(group,c,diag)
return List([0..c-1],i->group^(diag^i));
end);


