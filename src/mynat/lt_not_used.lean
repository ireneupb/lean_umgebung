import mynat.le

namespace N

def lt (a b : N) := a ≤ b ∧ ¬ (b ≤ a)

-- notation
instance : has_lt N := ⟨N.lt⟩

@[leakage] theorem lt_def' : N.lt = (<) := rfl

end N