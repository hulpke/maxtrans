DeclareInfoClass("InfoClassmax");
SetInfoLevel(InfoClassmax,1);

Read("~/git/mgmconvert/util.g");

MyTest:=function(gp,recogfn)
local r,h;
  r:=recogfn(gp);
  Print("Testing 2\n");
  if Size(Group(GeneratorsOfGroup(r.val2)))<>Size(r.val2) then
    Error("err2");
  fi;
  Print("Testing 3\n");
  if ForAny(r.val3,x->Size(Group(GeneratorsOfGroup(x)))<>Size(x)) then
    Error("err3");
  fi;
  Print("Testing 1s\n");
  if Source(r.val1)<>gp then
    Error("err1s");
  fi;
  Print("Testing 1r\n");
  if not IsSubset(r.val2,Image(r.val1)) then
    Error("err1r");
  fi;
  if Size(Image(r.val1))<>Size(gp) then
    Error("err1rs");
  fi;
  Print("Testing 1\n");
  h:=MappingGeneratorsImages(r.val1);
  h:=GroupHomomorphismByImages(gp,r.val2,h[1],h[2]);
  if h=fail or not IsBijective(h) then
    Error("err1");
  fi;
  Print("Testing 5\n");
  h:=MappingGeneratorsImages(r.val5);
  h:=GroupHomomorphismByImages(r.val4,r.val2,h[1],h[2]);
  if h=fail then #or not IsBijective(h) then
    Error("err5");
  fi;
  return true;

end;

