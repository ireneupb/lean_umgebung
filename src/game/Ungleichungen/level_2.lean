-- Level name : Ungleichungen TBD

-- namespace nat -- hide 

import data.nat.basic -- hide
import tactic
namespace nat -- hide 

/-
Text, use mit mehreren Argumenten, linearith!
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
theorem Pythagoreisches_Tripel : ∃ n m o : ℕ, n*n+m*m=o*o :=
begin
  use [3, 4, 5],
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