-- Level name : Die Potenzen von 0

import mynat.pow -- hide
import game.Potenzen.level_1 -- hide
namespace N -- hide

/-

In diesem Level zeigen wir, dass $0$ hoch jedem Nachfolger einer natürlichen Zahl
$0$ ergibt. Verwende dazu die rw Tactic.

-/

/- Hint :  Wieso folgt daraus nicht $0^0=0$, was ein Widerspruch zu Level 1 ist?
In den Peano-Axiomen steht, dass $0$ nicht der Nachfolger einer Zahl ist. Deswegen
zeigen wir hier $0^{(succ(a))}=0$ und nicht $0^a=0$. Wir schließen so die $0$ aus.
-/

/- Theorem
Sei $a \in \mathbb{N}$. Dann ist $0^{(succ(a))}=0$.
-/
theorem zero_pow_succ (a : N) : (zero) ^ (succ(a)) = zero :=
begin
rw pow_succ,
rw mul_zero,



end

end N -- hide