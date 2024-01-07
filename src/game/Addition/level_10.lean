-- Level name : Lösung einer Linearen Gleichung

-- namespace nat -- hide 

import data.nat.basic -- hide
import tactic -- hide
namespace nat -- hide

/-
In diesem Level wirst du Beweisen, dass $a=5$ die lineare Gleichung
$a+3=8$ löst. Dazu braucht man die Rechenregeln der Addition, die du
ja bereits bewiesen hast. Wir wollen diese aber nicht mehr Schritt 
für Schritt anwenden, sondern lineare Umformungen direkt LEAN überlassen.

Dazu gibt es die Tactic `linarith`, die automatisch den Beweiszustand mithilfe
der gegebenen Aussagen und linearen arithmetischen Operationen vereinfacht.
Du kannst diesen Beweis lösen, indem du einfach `linarith,` schreibst.
-/

/- Hint : Ohne `linarith` wäre der Beweis aufwändig.
Wir würden folgende Umformungen an `h` machen:
```
a+3=8
a+succ(2)=8
succ(a+2)=8
succ(a+succ(1))=8
succ(succ(a+1))=8
succ(succ(a+succ(0)))=8
succ(succ(succ(a+0)))=8
succ(succ(succ(a)))=8
succ(succ(succ(a)))=succ(7)
succ(succ(succ(a)))=succ(succ(6))
succ(succ(succ(a)))=succ(succ(succ(5)))
a = 5
```
-/

/- Theorem
Sei $a \in \mathbb{N}$ mit $a+3=5$. Dann ist a=5.
-/
theorem lineare_gleichung (a : ℕ) (h : a+3=8) : a=5 :=
begin
linarith,




end

/- Tactic : linarith
## Anleitung
Die Taktik `linarith` in LEAN führt linear-arithmetische Operationen aus,
um automatisch Ungleichungen und Gleichungen in natürlichen Zahlen zu lösen
## Beispiel
Bei folgendem Zustand:
```
a: ℕ
h: a + 3 = 8
⊢ a = 5
```
löst `linarith,` durch arithmetische Umformunge den Beweis.
-/
end nat -- hide