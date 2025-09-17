import Mathlib.Data.Set.Basic

namespace IFPTheory

variable {Node: Type}
variable {Participant: Type}
variable {Interaction: Type}

def in_context (n: Node) (ixn: Interaction) (context_rel: Participant → Node → Prop) (interactions: Interaction → Participant → Participant → Prop) : Prop :=
  ∃ p1 p2, interactions ixn p1 p2 ∧ (context_rel p1 n ∨ context_rel p2 n)

end IFPTheory
