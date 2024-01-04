-- Level name : Existenz Divisor und Rest

-- namespace nat -- hide 

import data.nat.basic -- hide
import tactic
import game.Division_mit_Rest.level_1 --hide
namespace nat -- hide 

/-
Text Text Text
-/

/- Hint : Hint Title?
Hint teeeext.
-/

/-
More teeeeext (8)
-/

/- Theorem
Für natürliche Zahlen m,n mit $m>0$ gilt: Es gibt natürliche Zahlen q, r mit $r < m$ und $n = m*q + r$
-/
theorem lemma_div (m d q r : ℕ) (hq' : ¬ ∃ (q':ℕ), d.succ=m*q') (hq : d = m*q+r) (hr : r < m): r+1<m :=
begin
  by_contra h_contr,
  push_neg at h_contr,
  have hr_succ_le_m : r + 1 ≤ m,
  { exact succ_le_of_lt hr, },
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
        
end

/- Tactic : rw
## Anleitung
Wenn `h` eine Aussage des Typs `X = Y` ist, dann wird
`rw h,` alle `X` in der zu beweisenden Aussage durch
`Y` austauschen.
Um alle `Y` durch `X` zu ersetzten verwendet man `rw ← h`.
## Beispiel
Bei folgendem Zustand:
```
x : N
⊢ succ (x + 0) = succ (x)
```
wird `rw add_zero,` das Ziel umändern zu `⊢ succ x = succ (x)`,
und damit den Beweis abschließen.
-/
end nat -- hide