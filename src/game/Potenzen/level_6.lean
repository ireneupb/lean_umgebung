-- Level name : Potenzieren als Homomorphismus $⬝∧c: (\mathbb{N}, *) → (\mathbb{N}, *)$

import data.nat.basic -- hide
import mynat.one_eq -- hide
import tactic -- hide
namespace nat -- hide

/-
Wenn wir das Potenzieren als Abbildung $⬝∧c: (\mathbb{N}, *) → (\mathbb{N}, *)$
auffassen, dann ist $∧$ ebenfalls ein Homomorphismus, da $(a * b)^c = a^c * b^c$. 
Dies ist ein weiteres der Potenzgesetze.

Das Potenzieren ist also sowohl im ersten als auch im zweiten Argument ein
Homomorphismus, aber jeweils bezüglich einer anderen Verknüpfung in der Urbildmenge.

Führe diesen Beweis selbstständig. Du kannst Induktion verwenden und an gegebenen Stellen
linarith.
-/

/- Theorem
Seien $a,b,c \in \mathbb{N}$. Dann ist $(a * b)^c = a^c * b^c$.
-/
theorem mul_pow (a b c : ℕ) : (a * b) ^ c = a ^ c * b ^ c :=
begin
induction c with d hd,
{linarith,},
{repeat {rw pow_succ},
rw hd,
linarith, 
},



end

end nat -- hide