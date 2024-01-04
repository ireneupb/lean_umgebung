-- Level name : TBD

-- namespace nat -- hide 

import data.nat.basic -- hide
import tactic
namespace nat -- hide

/-
Use needs to be introduced at latest here.
-/

/- Hint : Hint Title?
Hint teeeext.
-/

/-
More teeeeext (8)
-/

/- Theorem
Für natürliche Zahlen m,n mit $m>0$ gilt: Es gibt natürliche Zahlen q, r mit $n = m*q + r$
-/
theorem LGS_2 (n m : ℕ) (h : n+m+3=8 ∧ n=m+1) : n=3 ∧ m=2 :=
begin
cases h with h1 h2,
have umf : m+1+m+3=8,
{rw ← h2,
exact h1,},
have hm : m=2, linarith,
have hn : n=3, linarith,
split,
{exact hn,},
{exact hm,},
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