-- Level name : Die natürliche Zahl 1

import mynat.add -- hide
import game.Addition.level_2 --hide
namespace N -- hide

/- Axiom : one_eq_succ_zero (a : N) :
one = succ(zero)
-/

/-
Aus praktischen Gründen möchten wir nun dem Nachfolger von $0$ einen Namen
geben. Diese Zahl nennen wir $1$. Die Aussage `one = succ(zero)` heißt in
LEAN `one_eq_succ_zero`.
-/


/- 
Nun können wir zeigen, dass der Nachfolger von $a$ gleich $a+1$ ist. Löse
den Beweis mit `rw` und den verfügbaren Axiomen `one_eq_succ_zero`,
`add_succ` und `add_zero`. 
-/

/- Hint : Aufgabe nach dem Lösen des LEAN-Beweises
Schau dir den Beweiszustand nach der ersten Zeile `rw [one_eq_succ_zero],` an. Betrachte nun in der linken Spalte die Sätze, die
wir zur Addition bereits bewiesen haben. Kannst du an dieser Stelle einen davon verwenden?
-/

/- Theorem
Sei $a \in \mathbb{N}$. Dann ist `succ`$(a) = a + 1$.
-/
theorem succ_eq_add_one (a : N) : succ(a) = a + 1 :=
begin
rw [one_eq_succ_zero],
rw [add_succ],
rw [add_zero],



end

end N -- hide