-- Level name : Kommutativität der Addition

import mynat.add -- hide
import game.Addition.level_6 --hide
namespace N -- hide

/-
Endlich können wir zeigen, dass die Addition kommutativ ist!

Auch hier können wir einen Induktionsbeweis führen. In diesem Level wirst du einen
fast richtigen Beweis korrigieren.

Kopiere dazu folgenden Beweis mit Fehler in die Aufgabe:
```
induction b with d hd,
{rw [add_zero(a)],
rw [zero_add(a),],},
{rw [add_succ(a)],
rw [hd],
rw [succ_add(b)],},
```
Klicke dich durch den Beweis und achte dabei auf den Beweiszustand und wie er sich
mit den unterschiedlichen Beweisschritten ändert. Zu korrigieren ist der Induktionsschritt. 

Finde den Fehler, indem du insbesondere auf die Fehlermeldung achtest. Kannst du den Beweis
korrigieren?
-/

/- Theorem
Seien $a, b \in \mathbb{N}$. Dann ist a+b=b+a.
-/
theorem add_comm (a b: N) : a + b = b + a :=
begin
  induction b with d hd,
  {rw [add_zero(a)],
  rw [zero_add(a)],},
  {rw [add_succ(a)],
  rw [hd],
  rw [succ_add(d)],},


  
end

/- Hint : Kommst du mit der Fehlersuche nicht weiter?
Der Fehler `unknown identifier 'b'` deutet darauf hin, dass LEAN die Variable `b` in diesem
Kontext nicht kennt. Denk daran, dass im Induktionschritt bewiesen wird, dass falls die
Aussage für ein `d` (also a+d=d+a) gilt, die Aussage auch für `d.succ` 
(also a+d.succ = d.succ+a) gilt. Hier kommt also kein `b` mehr vor.
-/

end N -- hide