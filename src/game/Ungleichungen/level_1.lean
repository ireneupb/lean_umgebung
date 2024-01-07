-- Level name : Ungleichungen

import data.nat.basic -- hide
import tactic -- hide
namespace nat -- hide 

/-
Nun werden wir uns mit Ungleichungen auseinandersetzen. Dazu wird als erstes $≤$
definiert. Und zwar ist für natürliche Zahlen $a$ und $b$ $a≤b$ genau dann, wenn es
eine natürliche Zahl $c$ gibt, sodass $b=a+c$. Dieser Zusammenhang ist in LEAN
unter dem Satz `le_iff_exists_add` (`le` steht für "less or equal") gespeichert:

`le_iff_exists_add (a b : ℕ) : a ≤ b ↔ ∃ (c : ℕ), b = a + c`.

Du kannst diesen Satz mit `rw` verwenden. Oft ist es aber sehr aufwändig eine
Ungleichung über die Existenz eines `c` zu zeigen. Deswegen führen wir hier die
Tactic `simp` ein. `simp` verwendet Gleichungen und Ungleichungen im Beweiszustand 
um den Beweis zu vereinfachen oder zu beenden. Insbesondere kann `simp` ein
Beweisziel wie `2≤6` lösen.

In diesem Level ist zu zeigen, dass es eine natürliche Zahl kleiner gleich $2$
gibt. Beginne den Beweis, und sobal du ein Beweisziel der Form `a≤b` hast, verwende
`simp`.
-/

/- Hint: Nach dem du den Beweis gelöst hast: wie wäre der Beweis ohne `simp`?
```
use [1], -- Dieses use bezieht sich auf a
rw [le_iff_exists_add],
use [1], -- Dieses use bezieht such auf c
```
-/


/- Theorem
Es gibt ein $a \in \mathbb{N}$ mit $a\leq2$.
-/
theorem kleiner_zwei : ∃ a : ℕ, a ≤ 2 :=
begin
  use [1],
  simp,


  
end

/- Tactic : simp
## Anleitung
`simp` verwendet Gleichungen und Ungleichungen im Beweiszustand um den Beweis zu vereinfachen
oder zu beenden. Es kann entweder eine konkrete Aussage `h` übergeben werden, die vereinfacht
werden soll (`simp [h],`) oder einfach `simp,` verwendet werden.
## Beispiel
Bei folgendem Zustand:
```
⊢ 1 < 2
```
löst `simp,` den Beweis.
-/
end nat -- hide