-- Level name : Assoziativität der Addition

import mynat.add -- hide
import game.Addition.level_4 --hide
namespace N -- hide

/-
Nun werden wir die Assoziativität der Addition der natürlichen
Zahlen zeigen. Das bedeutet $(a + b) + c = a + (b + c)$. 
-/

/- Hint : Über welcher der drei Variablen ist ein Induktionsbeweis am sinnvollsten?
Wir haben die Addition mit Rekursion auf die rechte Variable definiert,
es ist also sinnvoll bei dem Induktionsbeweis über die Variable
$c$ zu induzieren.
-/

/-
Noch eine Bemerkung: LEAN ist linksassoziativ. Das bedeutet, dass für LEAN
$a+b+b$ das gleiche wie $(a+b)+c$ ist.

Zu diesem Beweis gibt es <a href="https://go.upb.de/lean_2_4" target="blank">hier</a> ein Aufgabenblatt.
-/

/- Theorem
$(a + b) + c = a + (b + c)$
-/
theorem add_assoc (a b c : N) : (a + b) + c = a + (b + c) :=
begin
  induction c with d hd,
  {rw N_zero_eq_zero,
  rw add_zero,
  rw add_zero,},
  {rw add_succ (a+b) d,
  rw add_succ,
  rw add_succ,
  rw hd,},


  
end

end N -- hide