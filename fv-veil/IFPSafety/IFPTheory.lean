namespace IFPTheory

variable {Node: Type}
variable {Participant: Type}
variable {Interaction: Type}

def in_context (n: Node) (ixn: Interaction) (context: Participant → Node → Prop) (interactions: Interaction → Participant → Participant → Prop) : Prop :=
  ∃ p1 p2, interactions ixn p1 p2 ∧ (context p1 n ∨ context p2 n)

end IFPTheory
