-- Level name : Ungleichungen TBD

-- namespace nat -- hide 

import data.nat.basic -- hide
import tactic
namespace nat -- hide 

/-
Text, split
-/

/- Hint : Hint Title?
Hint teeeext.
-/

/-
More teeeeext (8)
-/

/- Theorem
TBD
-/

theorem no_small_mul_four : ¬∃ (n m : ℕ), m > 0 ∧ n<4 ∧ n = m*4 :=
begin
by_contra h_contr,
obtain ⟨n, m, hnm⟩ := h_contr,
cases hnm with hm hrest,
cases hrest with hn hnm,
have n_bigger_four : n ≥ 4,
{rw hnm,
linarith,},
linarith,
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