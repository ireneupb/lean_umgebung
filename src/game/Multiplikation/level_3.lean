-- Level name : Kommutativität der Multiplikation

import mynat.mul -- hide
import game.Multiplikation.level_2 -- hide
namespace N -- hide

/- 
Die Ergebnisse aus Level 1 und 2 sind genug, um die Kommutativität zu zeigen!
-/

/- Theorem
a * b = b * a
-/
theorem mul_comm (a b : N) : a * b = b * a :=
begin
induction b with d hd,
{rw N_zero_eq_zero,
rw mul_zero,
rw zero_mul,},
{rw mul_succ,
rw hd,
rw succ_mul,},



end

end N -- hide

/- Hint :  Kommen dir die Schritte in diesem Beweis bekannt vor?
Wenn du dir den Beweis der Kommutativität der Addition anschaust und dort
das überall "add" mit "mul" ersetzt, hast du einen gültigen Beweis für
die Kommutativität der Multiplikation!
-/