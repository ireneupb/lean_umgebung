-- Level name : Gerade Quadratzahl

import data.nat.basic -- hide
import tactic -- hide
namespace nat -- hide 

/-
In diesem Level möchten wir zeigen, dass es eine gerade Quadratzahl gibt. Eine
natürliche Zahl $a$ heiß Quadratzahl, genau dann wenn es eine natürliche Zahl
$b$ gibt, sodass $a=c^2$. In diesem Level werden wir das als `a=c⬝c` schreiben.
-/

/- Theorem
Es gibt $a, b, c \in \mathbb{N}$ mit $a=2⬝b$ und $a=c⬝c$.
-/
theorem gerades_quadrat : ∃ a b c : ℕ, a=2*b ∧ a=c*c :=
begin
  use [16, 8, 4],
  split,
  {linarith,},
  {linarith,},


  
end

/- Hint : Wie war das nochmal mit Beweiszielen die `∧` beinhalten?
Schau dir dazu die Tactic `split` an.
-/

end nat -- hide