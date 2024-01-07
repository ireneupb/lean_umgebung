-- Level name : Existenz Divisor und Rest - unbeschränktes $r$

import data.nat.basic -- hide
import tactic -- hide
namespace nat -- hide

/-
Wir möchten zuletzt noch zeigen, dass die Division mit Rest über den natürlichen
Zahlen funktioniert. Das heißt, dass es für natürliche Zahlen $n, m$ mit $m>0$ gilt: 
Es gibt natürliche Zahlen $q, r$ mit $n = m*q + r$ und $r < m$.

In diesem Level werden wir zuerst eine abgeschwächte Version zeigen, in der wir
nicht fordern, dass $r < m$ ist. 

Dazu werden wir lernen, wir mann in einem Beweis eine Fallunterscheidung macht. Wenn
man in LEAN `by_cases h: a>4,` verwendet, dann teilt LEAN den Beweiszustand in zwei
Teile. In beiden ist das Beweisziel das gleiche, in einem haben wir jedoch die
Aussage `h : a>4` und in dem anderen die Aussage `h : ¬ a>4`. Wie bei anderen Tactics
die den Beweis aufteilen kannst du auch hier Klammern verwenden und somit folgende
Struktur verwenden:
```
by_cases h: a>4,
{},
{},
```

Verwende für den Beweis in diesem Level folgendes Beweisgerüst und ergänze den
Induktionsanfang, und die Beweise für die beiden Fälle, je nachdem ob d.succ ein
Vielfaches von m ist oder nicht:
```
induction n with d hd,
{ sorry, },
{ by_cases hq : ∃ q, d.succ = m*q,
  { sorry, },
  { sorry, },
},
```
-/

/- Theorem
Seien $n,m ∈ \mathbb{N}$ mit $m>0$. Dann gilt: Es gibt $q,r\in \mathbb{N}$ mit $n = m*q + r$.
-/
theorem exist_divisor_rest_gr (n m : ℕ) (hm : m > 0) : ∃ q r : ℕ, n = m * q + r :=
begin
  induction n with d hd,
  { use [0, 0],
    simp [hm], },
  { by_cases hq' : ∃ q', d.succ = m*q',
    { obtain ⟨q', hq'⟩ := hq',
      use [q', 0],
      simp [hq'],},
    { use [0, d.succ],
      simp, } },




end

/- Tactic : by_cases
## Anleitung
`by_cases h : ha,` startet eine Fallunterscheidung. In einem Fall gilt `h : ha` und im
anderen gilt `h : ¬ha`. In beiden muss das ursprüngliche Beweisziel gezeigt werden.
## Beispiel
Wenn
man in LEAN `by_cases h: a>4,` verwendet, dann teilt LEAN den Beweiszustand in zwei
Teile. In beiden ist das Beweisziel das gleiche, in einem haben wir jedoch die
Aussage `h : a>4` und in dem anderen die Aussage `h : ¬ a>4`. Wie bei anderen Tactics
die den Beweis aufteilen kannst du auch hier Klammern verwenden und somit folgende
Struktur verwenden:
```
by_cases h: a>4,
{},
{},
```
-/

end nat -- hide