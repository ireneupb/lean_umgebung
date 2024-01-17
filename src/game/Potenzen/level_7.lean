-- Level name : Potenz einer Potenz

import data.nat.basic -- hide
import mynat.one_eq
import tactic -- hide
namespace nat -- hide

/-
Zuletzt wollen wir noch folgendes Potenzgesetz beweisen: $(a^b)^c=a^{b*c}$. Dazu kannst
du folgendes Beweisgerüst verwenden.

```
induction c with d hd,
{sorry,},
{sorry, -- so weit umformen, bis die Induktionshypothese angewandt werden kann
rw hd,
repeat{rw pow_mul,},
rw pow_succ,},
```
-/

/- Theorem
Seien $a,b,c \in \mathbb{N}$. Dann ist $(a^b)^c = a^{b * c}$.
-/
theorem pow_pow (a b c : ℕ) : (a ^ b) ^ c = a ^ (b * c) :=
begin
induction c with d hd,
{rw mul_zero,
repeat {rw pow_zero},},
{rw pow_succ,
rw hd,
repeat{rw pow_mul,},
rw pow_succ,},



end

end nat -- hide