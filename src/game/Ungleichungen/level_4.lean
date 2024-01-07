-- Level name : Aussagen negieren

import data.nat.basic -- hide
import tactic -- hide
namespace nat -- hide 

/-
In diesem Level werden wir lernen, wie wir ein Beweisziel, welches mit einem
Negationszeichen anfängt weiter vereinfachen. In deisem Level zum Beispiel ist
das Beweisziel `¬ a > 4`. Wir wissen, dass das equivalent zu `a ≤ 4` ist. Damit
LEAN diese Umformung macht verwenden wir die Tactic `push_neg,`. Probier es zu
Beginn dieses Beweises aus.
-/

/- Theorem
Sei $a \in \mathbb{N}$ mit $a\leq4$. Dann gilt nicht, dass $a>4$.
-/
theorem neg_gr_vier (a : ℕ) (h : a ≤ 4) : ¬ a > 4 :=
begin
push_neg,
exact h,



end

/- Wie schließ man nochmal ein Beweisziel das gleich zu einer der gegebenen Aussagen ist?
Schau dir dazu die Tactic `exact` an.
-/

/- Tactic : push_neg
## Anleitung
`push_neg` vereinfacht ein Beweisziel, welches mit einem Negationszeichen anfängt.
## Beispiel
Wenn `push_neg` angewandt wird, wird:
```
⊢ ¬a > 4
```
zu:
```
⊢ a ≤ 4
```
-/

end nat -- hide