theory Chapter3Defs
imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

end