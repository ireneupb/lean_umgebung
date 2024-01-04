-- Level name : Assoziativität der Multiplikation

import mynat.mul -- hide
import game.Multiplikation.level_4 -- hide
namespace N -- hide

/-



-/

/- Theorem
$(a * b) * c = a * (b * c)$
-/
theorem mul_assoc (a b c : N) : (a * b) * c = a * (b * c) :=
begin
induction c with d hd,
{rw N_zero_eq_zero,
  repeat {rw mul_zero,},},
{repeat{rw mul_succ},
rw left_distrib,
rw hd,},



end

end N -- hide

/- Hint :  Kannst du auch bei der Assoziativität den Beweis aus der Addition einfach übernehmen?
Nein, für diesen Beweis brauchst du nämlich das Distributivgesetz. Das kommt daher, dass die 
Definition der Multiplikation von der Addition abhängt (`a*succ(d)=a*d+a`).
-/