-- Level name : Die Addition

import mynat.add -- hide
import game.Addition.level_1 --hide
namespace N -- hide

/- Axiom : add_zero (a : N) :
a + 0 = a
-/

/- Axiom : add_succ (a b : N) :
a + succ(b) = succ(a + b)
-/


/-
Man kann die Addition zweier natürlichen Zahlen rekursiv anhand der Peano-Axiome 
definieren.
- Für $a \in \mathbb{N}$ sei $a+0=a$
- Für $a,d \in \mathbb{N}$ sei $a+$`succ`$(d) = $`succ`$(a+d)$

Nach dem Prinzip der Induktion ist dann die Addition für alle Paare von natürlichen
Zahlen definiert.

Die beiden Aussagen, die die Addition definieren, sind in LEAN implementiert und 
haben jeweils den Namen `add_zero` und `add_succ`. Auch diese Aussagen können mit
dem Befehl `rw` verwendet werden. `rw add_zero,` wandelt die Aussage `b+zero` in `b`
um.
-/

/- Hint : Klicke hier, um die Definition der Addition der natürlichen Zahlen in LEAN zu sehen. Du musst diesen Code nicht zu 100% verstehen.
Definition: <br>
`def add : N → N → N` <br>
`| m 0 := m` <br>
`| m (succ n) := succ (add m n)` <br>

Den beiden definierenden Eigenschaften wird ein Namen gegeben: <br>
`lemma add_zero (m : N) : m + zero = m := rfl` <br>
`lemma add_succ (m n : N) : m + succ n = succ (m + n) := rfl`
-/

/-
In diesem Level werden wir zeigen, dass Addition mit dem Nachfolger von $0$ (den
wir noch nicht formal als $1$ eingeführt haben), gleich dem Nachfolger der Zahl ist.
-/

/- Theorem
$a+$`succ`$(0)=$`succ`$(a)$
-/
theorem add_succ_zero (a : N) : a + succ(0) = succ(a) :=
begin
  rw add_succ,
  rw add_zero,


  
end

end N -- hide