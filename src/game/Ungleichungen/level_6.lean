-- Level name : Ungleichungen TBD

-- namespace nat -- hide 

import data.nat.basic -- hide
import tactic
namespace nat -- hide 

/-
Goal: introduce contradiction!
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
theorem tobedet (n : ℕ) (hn : n ≥ 4) : ¬∃ (m : ℕ), m+n=3:=
begin
by_contra h_contr,
obtain ⟨m, hm⟩ := h_contr,
have h_2 : m + n ≥ 4,
{linarith,},
have h_3 : ¬ m + n ≥ 4,
{linarith,},
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