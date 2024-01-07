-- Level name : Addition mit dem Nachfolger - von links

import mynat.add -- hide
import game.Addition.level_5 --hide
namespace N -- hide

/-
Genauso wie wir aus $a+0=a$ nicht direkt $0+a=a$ folgern könnten, können wir
aus $b + $`succ`$(a) =$ `succ`$(b+a)$ nicht `succ`$(a)+b =$ `succ`$(a+b)$
folgern. Wir haben nämlich noch nicht bewiesen, dass die Addition kommutativ ist.

Auch hier können wir einen Induktionsbeweis führen. In diesem Level wirst du einen
unvollständigen Beweis vervollständigen.

Kopiere dazu folgenden unvollständigen Beweis in die Aufgabe:
```
induction b with d hd,
  {rw [add_zero],
  rw [add_zero],},
  {sorry,},
```
Klicke dich durch den Beweis und achte dabei auf den Beweiszustand und wie er sich
mit den unterschiedlichen Beweisschritten ändert. Zu ergänzen ist der Induktionsschritt,
der zurzeit noch durch `sorry,` platzhaltend "gelöst" ist. 

Lösche dieses `sorry,` und ergänze den Induktionsschritt.
-/

/- Theorem
Seien $a, b \in \mathbb{N}$. Dann ist `succ`$(a)+b = $`succ`$(a+b)$.
-/
theorem succ_add (a b: N) : succ(a) + b = succ(a + b) :=
begin
  induction b with d hd,
  {rw [add_zero],
  rw [add_zero],},
  {rw [add_succ],
  rw [hd],
  rw [add_succ],},


  
end

/- Hint : Kommst du mit dem Induktionsschritt nicht weiter?
Der Induktionschritt kann wiefolgt geführt werden:
```
rw [add_succ],
rw [hd],
rw [add_succ],
```
Kopiere diesen Code und versuche ihn Schritt für Schritt nachzuvollziehen.
-/

end N -- hide