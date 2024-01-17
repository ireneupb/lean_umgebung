-- Level name : Potenzieren als Homomorphismus $a∧⬝: (\mathbb{N}, +) → (\mathbb{N}, *)$

import data.nat.basic -- hide
import mynat.one_eq
import tactic -- hide
namespace nat -- hide

/-
Wenn wir das Potenzieren als Abbildung $a∧⬝: (\mathbb{N}, +) → (\mathbb{N}, *)$
auffassen, dann ist $∧$ ein Homomorphismus, da $a^{b + c} = a^b * a^c$. Dies 
ist eines der Potenzgesetze.

Du kannst dieses Gesetz mit einem Induktionsbeweis zeigen. Dazu kannst du vollgendes Gerüst verwenden:
```
induction Induktionsvariable with d hd,
{sorry, -- so weit umformen bis linarith das Ziel lösen kann
linarith,},
{sorry, -- so weit umformen, bis die Induktionshypothese angewandt werden kann
rw [hd],
linarith,
},
```
-/

/- Theorem
Seien $a,b,c \in \mathbb{N}$. Dann ist $a^{b + c} = a^b * a^c$.
-/
theorem pow_add (a b c : ℕ) : a ^ (b + c) = a ^ b * a ^ c :=
begin
induction c with d hd,
{rw add_zero,
rw pow_zero,
linarith,},
{rw add_succ,
repeat{rw pow_succ},
rw hd,
linarith,
},



end

end nat -- hide