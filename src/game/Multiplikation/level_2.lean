-- Level name : Multiplikation mit dem Nachfolger - von links

import mynat.mul -- hide
import game.Multiplikation.level_1 --hide
namespace N -- hide

/-
In diesem Level werden wir zeigen, dass $(a+1)*b=a*b+b$, ist, oder mit `succ`
ausgedrückt: `succ(a) * b = a * b + b`. Du kannst diesen Beweis wieder über
Induktion lösen.
-/

/- Hint : Ist die Induktion über `a` oder über `b` geschickter?
Bei `a` als Induktionsvariable hättest du im Induktionsschritt `succ(succ(a))*b=succ(a)*b+b`.
Hier wird es schwer sein so umzuformen, dass man die Induktionsvoraussetzung verwenden kann,
weil wir bis jetzt nur `mul_succ` verwenden können, welches angewandt werden kann
wenn im zweiten Faktor `succ` vorkommt. Dafür eignet sich `b` als Induktionsvariable,
weil genau dann beim Induktionsschritt `succ` im zweiten Faktor vorkommt.
-/

/-
Du kannst mit diesem Beweisgerüst starten. Zu ergänzen ist:
1. Die Induktionsvariable
2. Der Induktionsanfang
3. Die Umformungen zu Beginn des Induktionsschrittes, die gemacht werden müssen damit
die Induktionsvorraussetzung `hd` verwendet werden kann.

```
induction Induktionsvariable with d hd,
{sorry,},
{sorry,
rw [hd],
repeat {rw [add_succ],},
rw [add_right_comm],
},
```
-/

/- Theorem
Seien $a, b \in \mathbb{N}$. Dann ist `succ`$(a) * b = a * b + b$.
-/
theorem succ_mul (a b : N) : succ(a) * b = a * b + b :=
begin
induction b with d hd,
{repeat {rw [mul_zero],},
rw [add_zero],},
{repeat {rw [mul_succ],},
rw [hd],
repeat {rw [add_succ],},
rw [add_right_comm],
},



end

end N -- hide