import mynat.mul

-- this is one of *three* routes to
-- canonically_ordered_comm_semiring

namespace N

def le (a b : N) :=  ∃ (c : N), b = a + c

-- Another choice is to define it recursively: 
-- | le 0 _
-- | le (succ a) (succ b) = le ab 

-- notation
instance : has_le N := ⟨N.le⟩

@[leakage] theorem le_def' : N.le = (≤) := rfl

theorem le_iff_exists_add (a b : N) : a ≤ b ↔ ∃ (c : N), b = a + c := iff.rfl

end N