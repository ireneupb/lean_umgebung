-- Level name : Lineares Gleichungssystem - Teil 2

-- namespace nat -- hide 

import data.nat.basic -- hide
import tactic -- hide
namespace nat -- hide

/-
In diesem Level möchten wir ein letztes Gleichungssystem lösen.
```
a+b+3=8
a=b+1
```
Es soll gezeigt werden, dass die Lösung
```
a=3
b=2
```
ist. In diesem Fall können wir nicht linarith direkt anwenden, weil in
unserem Beweisziel ein "und" (`∧`) ist. Man kann aber ein Ziel, welches
ein "und" (`∧`) enthält mit der Tactic `split` in zwei Unterziele einteilen.
In unserem Fall wird mit `split,` das Ziel `a=3 ∧ b=2` zu den Zielen
`a=3` und `b=2`. Wie beim Induktionsbeweis kannst du die beiden Ziele
in getrennten Umgebungen mit Klammern {} einteilen. Das Gerüst für diesen
Beweis ist also 
```
split,
{sorry,},
{sorry,},
```
Kopiere dieses Gerüst, schau dir an was der erste Schritt bewirkt und
ersetze dann die beiden `sorry` mit Beweisen.
-/

/- Theorem
Seien $a, b \in \mathbb{N}$ mit $a+b+3=8$ und $a=b+1$. Dann ist $a=3$ und $b=2$.
-/
theorem LGS_2 (a b : ℕ) (h : a+b+3=8 ∧ a=b+1) : a=3 ∧ b=2 :=
begin
split,
{linarith,},
{linarith,},



end

/- Hint : Du weißt nicht wie du die Beweise an der Stelle der `sorry` führen sollst?
Jetzt wo die Ziele jeweils nur einzelne Gleichungen sind kannst du `linarith` verwenden.
-/

/- Tactic : split
## Anleitung
Man kann ein Ziel, welches
ein "und" (`∧`) enthält mit der Tactic `split` in zwei Unterziele einteilen.
## Beispiel
Folgendem Zustand:
```
ab: ℕ
h: a + b + 3 = 8 ∧ a = b + 1
⊢ a = 3 ∧ b = 2
```
wird durch `split,` zu:
```
ab: ℕ
h: a + b + 3 = 8 ∧ a = b + 1
⊢ a = 3
ab: ℕ
h: a + b + 3 = 8 ∧ a = b + 1
⊢ b = 2
```
-/
end nat -- hide