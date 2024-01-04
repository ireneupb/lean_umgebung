-- Level name : TBD

-- namespace nat -- hide 

import data.nat.basic -- hide
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
theorem mul_gerade (n m : ℕ) (hger : ∃ o : ℕ, n=2*o) : ∃ q : ℕ, n*m = 2*q :=
begin
  obtain ⟨o, hger⟩ := hger,
  use [o*m],
  rw hger,
  rw mul_assoc,
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