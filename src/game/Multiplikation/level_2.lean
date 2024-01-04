-- Level name : Multiplikation mit dem Nachfolger - von links

import mynat.mul -- hide
import game.Multiplikation.level_1 --hide
namespace N -- hide

/- Tactic : repeat
## Anleitung
falls du in der zu beweisenden Aussage einen Befehl (z.B. `rw add_zero,`) mehrmals
anwenden kannst, dann wird `{repeat {⬝,},` den Befehl so oft ausführen, bis es
keine Instanz mehr gibt, an der der Befehl ausgeführt werden kann.
## Beispiel
Bei folgendem Zustand:
```
a b : N
⊢ a + zero + b = a + (b + zero)
```
wird `{repeat {rw add_zero,},` zweimal `add_zero` anwenden und
somit das Ziel zu `⊢ a + b = a + b ` umformen und damit
lösen.
-/

/-
Manchmal möchtest du einen Befehl mehrmals hintereinander ausführen. Wenn du dir
zum Beispiel den Induktionsanfang dieses Levels anschaust, musst du zeigen, dass
`a.succ * zero = a * zero + zero`, du könntest damit anfangen, überall wo mit
$0$ multipliziert wird `rw mul_zero,` anzuwenden. Anstatt den Befehl zweimal
auszuschreiben, kannst du `{repeat {rw mul_zero,},` anwenden. Dann wird LEAN den
Befehl `rw mul_zero,` so oft ausführen, bis es keine Instanz der Form `a+zero` gibt.
-/

/- Theorem
`succ`$(a) * b = a * b + b$
-/
theorem succ_mul (a b : N) : succ(a) * b = a * b + b :=
begin
induction b with d hd,
{rw N_zero_eq_zero,
repeat {rw mul_zero,},
rw add_zero,},
{rw mul_succ,
rw mul_succ,
rw hd,
rw add_succ,
rw add_succ,
rw add_right_comm,
},



end

end N -- hide