-- Level name : Addition mit dem Nachfolger von 0

import mynat.add -- hide
import game.Addition.level_1 --hide
namespace N -- hide

/-
In diesem Level werden wir zeigen, dass Addition mit dem Nachfolger von $0$ (den
wir noch nicht formal als $1$ eingeführt haben), gleich dem Nachfolger der Zahl ist.
Löse den Beweis mit `rw` und den verfügbaren Axiomen.
-/

/- Theorem
Sei $a \in \mathbb{N}$. Dann ist $a+$`succ`$(0)=$`succ`$(a)$
-/
theorem add_succ_zero (a : N) : a + succ(0) = succ(a) :=
begin
  rw [add_succ],
  rw [add_zero],


  
end

end N -- hide