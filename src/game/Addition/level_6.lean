-- Level name : Addition mit dem Nachfolger - von links

import mynat.add -- hide
import game.Addition.level_5 --hide
import tactic
namespace N -- hide

/-
Genauso wie wir aus $a+0=a$ nicht direkt $0+a=a$ folgern könnten, können wir
aus $b + $`succ`$(a) =$ `succ`$(b+a)$ nicht `succ`$(a)+b =$ `succ`$(a+b)$
folgern. Wir haben nämlich noch nicht bewiesen, dass die Addition kommutativ ist.
-/

/- Theorem
`succ`$(a)+b = $`succ`$(a+b)$
-/
theorem succ_add (a b: N) : succ(a) + b = succ(a + b) :=
begin
  induction b with d hd,
  {rw N_zero_eq_zero,
  rw add_zero,
  rw add_zero,},
  {rw add_succ,
  rw hd,
  rw add_succ,},


  
end

end N -- hide