-- Level name : Kommutativität der Addition

import mynat.add -- hide
import game.Addition.level_6 --hide
namespace N -- hide

/-
Endlich können wir zeigen, dass die Addition kommutativ ist!

Zu diesem Beweis gibt es <a href="https://go.upb.de/lean_2_6" target="blank">hier</a> ein Aufgabenblatt.
-/

/- Theorem
a+b=b+a
-/
theorem add_comm (a b: N) : a + b = b + a :=
begin
  induction b with d hd,
  {/- Induktionsanfang -/
  rw N_zero_eq_zero,
  rw add_zero,
  rw zero_add,},
  {/- Induktionsschritt -/
  rw add_succ,
  rw hd,
  rw succ_add,},


  
end

end N -- hide