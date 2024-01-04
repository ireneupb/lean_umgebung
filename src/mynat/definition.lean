import tactic.nat_num_game
import tactic.structure_helper

/-

  mynat/definition.lean -- definition of mynat.
  
  Supplies:
  constants zero : mynat and one : mynat
  function S : mynat → mynat
  notation 0 for zero and 1 for one.

The below code will be *invisible to the player*
-/

-- definition of "the natural numbers"
@[derive decidable_eq]
inductive N
| zero : N
| succ (n : N) : N

namespace N

instance : has_zero N := ⟨N.zero⟩
@[leakage] theorem N_zero_eq_zero : N.zero = 0 := rfl

def one : N := succ 0

instance : has_one N := ⟨N.one⟩

theorem one_eq_succ_zero : 1 = succ 0 := rfl

lemma zero_ne_succ (m : N) : (0 : N) ≠ succ m := λ h, by cases h

lemma succ_inj {m n : N} (h : succ m = succ n) : m = n := by cases h; refl

end N

attribute [symm] ne.symm
