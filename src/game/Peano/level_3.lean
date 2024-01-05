-- Level name : Die Peano Axiome - Teil 3

import mynat.definition -- hide
import game.Peano.level_2 --hide
namespace N -- hide

/-
In diesem Level werden wir wieder einen ähnlichen Satz wie im vorherigem Level
lösen. Wir möchten aber dazu eine neue Eingeschaft der Tactic `rw` benutzen und
eine weitere Tactic kennenlernen.

Man kann rw auch auf gegebene Hypothesen anwenden statt auf den Beweiszustand. Man
gibt dazu mit `at hypothese` and, auf welche hypothese rw angewandt werden soll.
Bei folgendem Zustand, den wir aus dem vorherigem Level kennen:
```
x : N
h : succ(a) = b
g : succ(b) = c
⊢ succ(succ(a)) = c
```
wird `rw ← h at g,` den Beweiszustand nicht ändern, dafür aber `g` umformen zu 
`g : succ(succ(a))=c`. In diesem Beispiel hätten wir dann eine Hypothese, die
exakt gleich zu dem Beweiszustand ist. Um diese Hypothese zu verwenden um den
Beweiszustand zu lösen, können wir die `exact` tactic verwenden und den Beweis
mit `exact g` schließen.

Den Beweis in diesem Level kannst du ebenfalls mit `rw ... at ...,` und `exact...,`
lösen.
-/

/- Theorem
Seien $a, b, c \in \mathbb{N}$. Falls `succ`$(a) = b$ und `succ`$($`succ`$(a)) = c$, dann `succ`$(b)= c$.
-/
theorem succ_succ_zw2 (a b c : N) (h : succ(a) = b) (g : succ(succ(a)) = c): succ(b) = c :=
begin
rw [h] at g,
exact g,



end

/- Tactic : exact
## Anleitung
Wenn `h` eine Aussage ist, die exakt gleich zu dem Beweiszustand
ist, dann löst `exact h` den Beweis.
## Beispiel
Bei folgendem Zustand:
```
x y : N
h : x + 1 = y
⊢ x + 1 = y
```
löst `exact h` den Beweis.
-/

end N -- hide

/- Hint : Brauchst du Hilfe, um einen zweiten Weg zu finden?
In der zu zeigenden Aussage kommt der Term `c` vor, der auch Teil der Aussage
`g` ist. Du kannst also mit `rw ← g,` das `c` in der Aussage ersetzen.
-/