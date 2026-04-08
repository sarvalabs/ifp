namespace IFPTheory

variable {Node: Type}
variable {Participant: Type}
variable {Interaction: Type}
variable {Context : Type}
-- variable {View : Type}

def in_context (n: Node) (ixn: Interaction) (context: Participant → Node → Prop) (interactions: Interaction → Participant → Participant → Prop) : Prop :=
  ∃ p1 p2, interactions ixn p1 p2 ∧ (context p1 n ∨ context p2 n)

def lock_leq (ixn1 : Interaction) (s1 : Bool)  (ixn2 : Interaction) (s2 : Bool) (height : Interaction → Nat) : Prop :=
  -- (v1 : View) (v2 : View) (view_le : View → View → Prop)
  if height ixn1 < height ixn2 then
    True
  else if height ixn1 = height ixn2 ∧ s1 = true ∧ s2 = false then
    True
  -- else if height ixn1 = height ixn2 ∧ s1 = s2 ∧ view_le v1 v2 then
  --   True
  else
    False

set_option diagnostics true

end IFPTheory
