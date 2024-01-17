-- Level name : Die Potenzierung mit 1

import mynat.pow -- hide
import game.Potenzen.level_2 -- hide
namespace N -- hide

/-
Da wir die Potenz nur für $0$ explizit definiert haben, und ansonsten nur über Induktion,
ist noch nicht bewisen, dass $a^1=a$ gilt. Du kannst in diesem Level mit der rw Tactic arbeiten.
Dazu kannst du dich an folgender Abfolge von Beweiszuständen orientieren. Welche Sätze musst
du jeweils anwenden um diese Zustände nachzubauen?

```
⊢ a ^ one = a
⊢ a ^ zero.succ = a
⊢ a ^ zero * a = a
⊢ one * a = a
⊢ zero.succ * a = a
⊢ zero * a + a = a
⊢ zero + a = a
⊢ a = a -- goals accomplished
```
-/

/- Theorem
Sei $a \in \mathbb{N}$. Dann ist $a^1 = a$.
-/
theorem pow_one (a : N) : (a) ^ (one) = a :=
begin
rw one_eq_succ_zero,
rw pow_succ,
rw pow_zero,
rw one_eq_succ_zero,
rw succ_mul,
rw zero_mul,
rw zero_add,



end

end N -- hide