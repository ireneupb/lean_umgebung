/-
This file is intended for Lean beginners. The goal is to demonstrate what it feels like to prove
things using Lean and mathlib. Complicated definitions and theory building are not covered.
Everything is covered again more slowly and with exercises in the next files.
-/

-- We want real numbers and their basic properties
import data.nat.basic

-- We want to be able to use Lean's built-in "help" functionality
import tactic.suggest

-- We want to be able to define functions using the law of excluded middle
noncomputable theory
open_locale classical
namespace nat

theorem exist_divisor_rest_gr (m n : ℕ) (hm : m > 0) : ∃ q r : ℕ, n = m * q + r :=
begin
  induction n with d hd,
  { use [0, 0],
    simp [hm], },
  { by_cases hq : ∃ q, d.succ = m*q,
    { obtain ⟨q, hq⟩ := hq,
      use [q, 0],
      simp [hq],},
    { use [0, d.succ],
      simp, } }
end

theorem exist_divisor_rest (m n : ℕ) (hm : m > 0) : ∃ q r : ℕ, n = m * q + r ∧ r < m :=
begin
  induction n with d hd,
  { -- Induktionsanfang
    use [0, 0],
    split,
    { -- Zeige: 0=m*0+0
      simp, },
    { -- Zeige: 0 kleiner m
      exact hm, }, },
  { -- Induktionsschritt
    by_cases hq : ∃ q, d.succ = m*q,
    { -- Fall m teilt d+1
      obtain ⟨q, hq⟩ := hq,
      use [q, 0],
      split,
      { -- Zeige: d+1=m*q+0
        simp [hq],
        },
      { -- Zeige: r kleiner m
        exact hm, }, },
    { -- Fall m teilt d+1 nicht
      obtain ⟨q, r, ⟨hq, hr⟩⟩ := hd,
      use [q, r + 1],
      split,
      { -- Zeige: d+1 = m * q + (r + 1)
        rw hq,
        rw add_succ, },
      { -- Zeige r kleiner m
        by_contra h_contr,
        push_neg at h_contr,
        have hr_succ_le_m : r + 1 ≤ m,
        { exact nat.succ_le_of_lt hr, },
        have hr1_m : r+1=m,
        {exact le_antisymm hr_succ_le_m h_contr,}, 
        have d_mult_q : d.succ = m*(q+1),
        {rw succ_eq_add_one,
        rw hq,
        rw add_assoc,
        rw hr1_m,
        rw mul_add,
        simp,
        },
        have h_eq : ∃ (q : ℕ), d.succ = m * q := ⟨q+1, d_mult_q⟩,
        contradiction,
        },
    },
  },
end


end nat