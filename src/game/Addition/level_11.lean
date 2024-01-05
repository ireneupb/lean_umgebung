-- Level name : Lösung einer linearen Gleichung mit Zwischenschritt

import data.nat.basic -- hide
import tactic -- hide
namespace nat -- hide

/-
Hier hast du eine weitere lineare Gleichung $a+2=4$. Als Beweisziel ist aber
nicht der Wert von $a$ gesucht, sonder von $a+3$. Das schafft zwar `linarith`
auch direkt (probier es gerne aus!), wir wollen aber die Gelegenheit nutzen
um zu erklären, wie man sich in Beweisen Zwischenziele setzen kann.

In diesem Beweis könnte es zum Beispiel sinnvoll sein, die Hypothese `ha : a=2`
zu beweisen und diese zu verwenden, `a` mit `rw ha,` in den Beweiszustand einzusetzen.
Um sich eine Hypothese als Zwischenziel vorzunehmen verwendet man die Tactic `have`.
Dazu schreibt man:
```
have ha : a = 2,
{...},
```
Man führt die Hypothese ha ein, die im weiterem Verlauf verwendet werden kann. Dazu muss
sie aber in den Klammern bewiesen werden.

In diesem Level könnte der Beweis dann so aussehen:
```
have ha : a = 2,
{sorry,}, -- Beweise ha, du kannst dazu linarith verwenden
sorry,    -- Beweise nun mithilfe von ha den Beweiszustand
```
Kopiere diesen Code und ergänze die beiden sorry.
-/

/- Theorem
Sei $a \in \mathbb{N}$ mit $a+2=4$. Dann ist $a + 3=5$.
-/
theorem lin_gl_zwischenschritt (a : ℕ) (h : a + 2 = 4): a + 3=5 :=
begin
have ha : a = 2,
{linarith,},
rw ha,


end

/- Tactic : have
## Anleitung
Die Taktik have in Lean erlaubt es, einen Zwischenschritt während eines Beweises 
zu definieren, welches bewiesen werden soll um im restlichem Beweis verwendet
zu werden.
## Beispiel
Bei folgendem Zustand:
```
a: ℕ
h: a + 2 = 4
⊢ a + 3 = 5
```
wird 
```
have ha : a = 2,
{...},
```
das Ziel ha einführen, welches in den Klammern bewiesen werden soll und dann
im Verlauf des Beweises verwendet werden darf.
-/

end nat -- hide