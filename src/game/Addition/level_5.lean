-- Level name : Assoziativität der Addition

import mynat.add -- hide
import game.Addition.level_4 --hide
namespace N -- hide

/-
Nun werden wir die Assoziativität der Addition der natürlichen
Zahlen zeigen. Das bedeutet $(a + b) + c = a + (b + c)$. Dies ist wieder
über einen Induktionsbeweis möglich. In diesem Level werden wir uns 
einen fertigen Beweis anschauen und dann mit der neuen Tactic "repeat" verkürzen.

Als erstes kannst du dazu folgenden Beweis als Lösung reikopieren und ihn
Schritt für Schritt nachvollziehen.
```
induction c with d hd,
  {rw [add_zero],
  rw [add_zero],},
  {rw [add_succ(a+b)(d)],
  rw [add_succ],
  rw [add_succ],
  rw [hd],},
```
Bemerkung: In der Zeile `rw [add_succ(a+b)(d),` siehst du, wie man in LEAN
die Stelle spezifiziert, an der ein `rw` ausgeführt werden soll, wenn man
mehrere Argumente übergeben muss. Die Argumente werden in getrennten Klammern
übergeben. 

Wie du siehst muss man in diesem Beweis sowohl im Induktionsanfang wie im
Induktionschritt den gleichen Beweisschritt mehrmals hintereinander ausführen.
Das kann man in LEAN mit der Tactic "repeat" verkürzen, die einen gegebenen
Beweisschritt so oft wiederholt, wie es möglich ist. Bei dem Zustand:
```
a : N, 
⊢ a + 0 + 0 + 0 = a
```
wird der Befehl `repeat{rw [add_zero],},` dreimal den Befehl `rw [add_zero]` anwenden
und somit das Beweisziel zu `a=a` umformen und den Beweis schließen. Achte
auf das Komma innehalb wie auch außerhalb der Klammer.

Verwende nun `repeat` um den vorhandenen Beweis zu verkürzen.
-/

/-
Noch eine Bemerkung: LEAN ist linksassoziativ. Das bedeutet, dass für LEAN
$a+b+b$ das gleiche wie $(a+b)+c$ ist.
-/

/- Theorem
Seien $a, b, c \in \mathbb{N}$. Dann ist $(a + b) + c = a + (b + c)$.
-/
theorem add_assoc (a b c : N) : (a + b) + c = a + (b + c) :=
begin
  induction c with d hd,
  {repeat{rw [add_zero],},},
  {repeat{rw [add_succ],},
  rw [hd],},


  
end

/- Tactic : repeat
## Anleitung
für einen Beweisschritt `step,`, führt `repeat {step,},` so oft den
Beweisschritt aus wie es möglich ist.
## Beispiel
Bei folgendem Zustand:
```
a : N, 
⊢ a + 0 + 0 + 0 = a
```
wird `repeat{rw [add_zero],},` dreimal den Befehl `rw [add_zero]` anwenden
und somit den Beweiszustand zu `a=a` umformen und den Beweis schließen.
-/

end N -- hide