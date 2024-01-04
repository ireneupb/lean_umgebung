-- Level name : Existenz Divisor und Rest

-- namespace nat -- hide 

import data.nat.basic -- hide
import tactic
import game.Division_mit_Rest.level_2 --hide
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
    by_cases hq2 : ∃ q', d.succ = m*q',
    { -- Fall m teilt d+1
      obtain ⟨q, hq⟩ := hq2,
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
        apply lemma_div m d q r hq2 hq hr,
        },
    },
  },
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