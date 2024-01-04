-- Level name : Ungleichungen TBD

-- namespace nat -- hide 

import data.nat.basic -- hide
import tactic -- hide
namespace nat -- hide 

/-
Hier wird zum ersten Mal use benutzt!!
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
theorem kleiner_zwei : ∃ n : ℕ, n < 2 :=
begin
  use 1,
  simp,
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