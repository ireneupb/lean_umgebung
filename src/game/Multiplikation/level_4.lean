-- Level name : Das Distributivgesetz

import mynat.mul -- hide
import game.Multiplikation.level_3 -- hide
namespace N -- hide

/-
Das Distributivgesetz gibt uns an, wie wir mit Ausdrücken umgehen können, in denen
Addition und Multiplikation vorkommen. Wir werden hier die "Linksdistributivität"
zeigen, also $c⬝ $(a+b)=c⬝a+c⬝b$, daraus folgt aber nicht direkt $(a+b) ⬝ c=a⬝c+b⬝c$.

In diesem Level startest du den Beweis selber. Wenn du nicht weiterkommst sind
unter der Aufgabe Hinweise.
-/

/- Theorem
Seien $a, b, c \in \mathbb{N}$. Dann ist $c ⬝ (a + b) = c ⬝ a + c ⬝ b$.
-/
theorem left_distrib (a b c : N) : c * (a + b) = c * a + c * b :=
begin
induction b with d hd,
{rw [add_zero],
rw [mul_zero],
rw [add_zero],},
{rw [add_succ],
rw [mul_succ],
rw [hd],
rw [mul_succ],
rw [add_assoc],},



end

/- Hint :  Hinweis: Beweisstruktur
```
induction Induktionsvariable with d hd,
{sorry,},
{sorry,},
```
-/

/- Hint :  Induktionsvariable
Verwende `b` als Induktionsvariable.
-/

/- Hint :  Hinweis: Benötigte Tactics und Sätze
Du benötigst in diesem Beweis nur die `induction` und `rw` tactics. `rw` wendest du
auf die Induktionsvoraussetzung und folgende Sätze an: `add_zero`, `mul_zero`,
`add_succ`, `mul_succ`, `add_assoc`. 
-/

end N -- hide