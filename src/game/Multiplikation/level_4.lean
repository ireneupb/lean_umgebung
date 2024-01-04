-- Level name : Das Distributivgesetz

import mynat.mul -- hide
import game.Multiplikation.level_3 -- hide
namespace N -- hide

/-
Das Distributivgesetz gibt uns an, wie wir mit Ausdrücken umgehen können, in denen
Addition und Multiplikation vorkommen.
-/

/- Theorem
$c * (a + b) = c * a + c * b$
-/
theorem left_distrib (a b c : N) : c * (a + b) = c * a + c * b :=
begin
induction b with d hd,
{rw N_zero_eq_zero,
rw add_zero,
rw mul_zero,
rw add_zero,},
{rw add_succ,
rw mul_succ,
rw hd,
rw mul_succ,
rw add_assoc,},



end

end N -- hide