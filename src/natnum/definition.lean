@[derive decidable_eq]
inductive N
| zero : N
| succ (n : N) : N

namespace N

instance : has_zero N := ⟨N.zero⟩
theorem N_zero_eq_zero : N.zero = 0 := rfl

def one : N := succ 0

def two : N := succ(succ(0))

instance : has_one N := ⟨N.one⟩

theorem one_eq_succ_zero : one = succ zero := rfl

theorem two_eq_succ_one : two = succ(succ(zero)) := rfl

lemma zero_ne_succ (m : N) : (zero : N) ≠ succ m := λ h, by cases h

lemma succ_inj {m n : N} (h : succ m = succ n) : m = n := by cases h; refl

end N

attribute [symm] ne.symm