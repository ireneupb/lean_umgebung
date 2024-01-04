-- Level name : Die Multiplikation

import mynat.mul -- hide
import game.Addition.level_8 --hide
namespace N -- hide

/- Axiom : mul_zero (a : N) :
a * 0 = 0
-/

/- Axiom : mul_succ (a b : N) :
a * succ(b) = a*d+a
-/

/-
Man kann auch die Multiplikation zweier natürlichen Zahlen rekursiv anhand der 
Peano-Axiome definieren.
- Für $a \in \mathbb{N}$ sei $a*0=0$
- Für $a,d \in \mathbb{N}$ sei $a* $`succ`$(d) = a*d+a$

Nach dem Prinzip der Induktion ist dann die Multiplikation für alle Paare von
natürlichen Zahlen definiert.

Die beiden Aussagen, die die Multiplikation definieren, sind in LEAN implementiert und 
haben jeweils den Namen `mul_zero` und `mul_succ`.
-/

/- Hint : Klicke hier, um die Definition der Multiplikation der natürlichen Zahlen in LEAN zu sehen. Du musst diesen Code nicht zu 100% verstehen.
Definition: <br>
`def mul : N → N → N` <br>
`| a zero := zero` <br>
`| a (succ d) := mul a d + a` <br>

Den beiden definierenden Eigenschaften wird ein Namen gegeben: <br>
`lemma mul_zero (a : N) : a * zero = zero := rfl` <br>
`lemma mul_succ (a d : N) : a * (succ d) = a * d + a := rfl`
-/

/-
In diesem Level werden wir zeigen, dass auch die Multiplikation mit $0$ von links $0$ ergibt.
Wir haben die Kommutativität der Multiplikation noch nicht gezeigt.
-/

/- Theorem
$0*a=0$
-/
theorem zero_mul (a: N) : 0*a = 0 :=
begin
induction a with d hd,
{rw N_zero_eq_zero,
rw mul_zero,},
{rw mul_succ,
rw hd,
rw add_zero,},



end

end N -- hide