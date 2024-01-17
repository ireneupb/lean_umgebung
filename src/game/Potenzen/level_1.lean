-- Level name : Die Potenzierung

import mynat.pow -- hide
import game.Multiplikation.level_5 -- hide
namespace N -- hide

/- Axiom : pow_zero (a : N) :
a ^ 0 = 1
-/

/- Axiom : pow_succ (a b : N) :
a ^ succ(b) = a^b*a
-/

/-
Man kann auch die Potenzierung einer natürlichen Zahl mit einer anderen 
rekursiv anhand der Peano-Axiome definieren.
- Für $m \in \mathbb{N}$ sei $m^0=1$
- Für $m,n \in \mathbb{N}$ sei $m^{(succ(n))} = m^n*m$

Nach dem Prinzip der Induktion ist dann die Potenzierung für alle Paare von
natürlichen Zahlen definiert.

Die beiden Aussagen, die die Potenzierung definieren, sind in LEAN implementiert und 
haben jeweils den Namen `pow_zero` und `pow_succ`.
-/

/-
In diesem Level werden wir zeigen, dass nach Definition gilt, dass $0^0=1$.
-/

/- Theorem
Es gilt, dass $0^0=1$.
-/
theorem zero_pow_zero : zero ^ zero = one :=
begin
rw pow_zero,



end

end N -- hide