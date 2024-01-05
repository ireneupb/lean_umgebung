-- Level name : Kommutativität der Multiplikation

import mynat.mul -- hide
import game.Multiplikation.level_2 -- hide
namespace N -- hide

/- 
Die Ergebnisse aus Level 1 und 2 sind genug, um die Kommutativität der Multiplikation
zu zeigen! Hier ist zur Erinnerung der Beweis der Kommutativität der Addition:
```
induction b with d hd,
{rw N_zero_eq_zero,
rw add_zero a,
rw zero_add a,},
{rw add_succ a,
rw hd,
rw succ_add d,},
```
-/

/- Hint :  Aufgabe nach dem Lösen des Lean-Beweises
Vielleicht ist dir aufgefallen, dass man in dem Beweis aus der Addition nur
überall `add` mit `mul` ersetzten musste. Wie sieht in normaler mathematischen 
Sprache aus? Formuliere dazu die Beweise add_comm und mul_comm schriftlich aus.
-/

/- Theorem
Seien $a, b \in \mathbb{N}$. Dann ist a * b = b * a
-/
theorem mul_comm (a b : N) : a * b = b * a :=
begin
induction b with d hd,
{rw N_zero_eq_zero,
rw mul_zero,
rw zero_mul,},
{rw mul_succ,
rw hd,
rw succ_mul,},



end

end N -- hide