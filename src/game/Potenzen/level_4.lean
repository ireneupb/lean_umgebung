-- Level name : Die Potenzen von 1

import mynat.pow -- hide
import game.Potenzen.level_3 -- hide
namespace N -- hide

/-
Ebenso haben wir noch nicht bewiesen, dass $1^a=1$ ist. Für dieses Level hat du einen gegebenen
Beweis, denn du nachvollziehen sollst. Kopiere dazu diesen Beweis in das Feld:
```
induction a with d hd,
{rw [pow_zero],},
{rw [pow_succ],
rw [one_eq_succ_zero],
rw [mul_succ],
rw [mul_zero],
rw [zero_add],
rw [← one_eq_succ_zero],
rw [hd],
},
```
Wie würdest du diesen Beweis auf Papier schreiben?
-/

/- Theorem
Sei $a \in \mathbb{N}$. Dann ist $1^a=1$.
-/
theorem one_pow (a : N) : (one) ^ (a) = one :=
begin
induction a with d hd,
{rw pow_zero,},
{rw pow_succ,
rw one_eq_succ_zero,
rw mul_succ,
rw mul_zero,
rw zero_add,
rw ← one_eq_succ_zero,
rw hd,
},



end

end N -- hide