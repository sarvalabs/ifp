def hello := "world"

def x  := 1
#eval x

#eval Nat.succ (Nat.succ x)

def myList := ["a","b"]
#eval "a" ∈ myList

class ByzQuorum (node : Type) (is_byz : outParam (node → Prop)) (nset : outParam Type) where
  member (a : node) (s : nset) : Prop
  supermajority (s : nset) : Prop       -- 2f + 1 nodes

  supermajorities_intersect_in_honest :
    ∀ (s1 s2 : nset), ∃ (a : node), member a s1 ∧ member a s2 ∧ ¬ is_byz a
