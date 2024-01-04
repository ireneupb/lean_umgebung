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
theorem gerades_quadrat : ∃ n m o : ℕ, n=m+m ∧ n=o*o :=
begin
  use [16, 8, 4],
  split,
  {linarith,},
  {linarith,},
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