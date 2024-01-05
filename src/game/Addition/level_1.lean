-- Level name : Die Addition

-- namespace nat -- hide 
import mynat.add -- hide
import game.Peano.level_3 -- hide
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
In diesem Level werden wir eine Aussage beweisen, in der die Addition der
natürlichen Zahlen vorkommt. Die Aussage ist: Sei $a \in \mathbb{N}$. 
Dann ist `succ`$(a)+0=$`succ`$(a+0)$. Wir können diese Aussage beweisen,
indem wir die Aussage `add_zero` mit `rw` auf den Beweiszustand anwenden.

In dieser Aussage kommen zwei Ausrücke der Form $n+0$ vor. Man kann bei der
Tactic rw konkretisieren, auf welche der beiden Stellen rw angewandt werden
soll. Probiere in dem Beweis erst `rw add_zero a,` aus. Lösche diese Zeile
und schreibe stattdessen `rw add_zero a.succ,`. Siehts du den unterschied im
Beweiszustand?
-/

/- Theorem
Sei $a \in \mathbb{N}$. Dann ist `succ`$(a)+0=$`succ`$(a+0)$.
-/

theorem succ_add_zero (a : N) : succ(a)+0=succ(a+0) :=
begin
rw add_zero a,
rw add_zero a.succ,
end

end N -- hide