-- Level name : Existenz Divisor und Rest - unbeschränkt

-- namespace nat -- hide 

import data.nat.basic -- hide
import tactic -- hide
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