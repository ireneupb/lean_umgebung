-- Level name : Multiplikation mit einer geraden Zahl ergibt eine gerade Zahl

-- namespace nat -- hide 

import data.nat.basic -- hide
import tactic -- hide
namespace nat -- hide

/-
Nun haben wir alle grundlegenden Eigenschaften der Addition und Multiplikation gezeigt.
Du darfst also insbesondere `linarith` wieder verwenden. 

In diesem Level werden wir zeigen, dass die Multiplikation mit einer geraden Zahl
eine gerade Zahl ergibt. Also: Seien $a, b$ natürliche Zahlen. Falls es eine natürliche
Zahl $c$ gibt, sodass $a=2*c$ ,
dann gibt es eine matürliche Zahl $d$, sodass $a*b=2*d$.

Da die Existenz von dem $d$ gezeigt wird, wirst du wieder die Tactic `use` brauchen,
die wir bereits in anderen Existenzbeweisen gesehen haben. Nun hast du aber auch
eine Existenzaussage in den Voraussetzungen. Du wirst in deinem Beweis das konkrete
$c$ für das $a=2*c$ gilt brauchen. Dazu kannst du die Tactic `obatin` verwenden. Diese
verwendet die Existenzaussage um eine Variable $c$ einzuführen und die Aussage, dass
für dieses c $a=2*c$ gilt. Konkret:

Für die Aussage `(hger : ∃ c : ℕ, a=2*c)`, wird `obtain ⟨c, ager⟩ := hger,` folgendendes
im Zustand ergänzen:
```
c : N
ager : a=2*c
```
Dabei sind die Argumente in den Klammern die Namen, die jeweil die Variable und die
Aussage bekommen sollen und das Argument nach dem `:=` die Existenzaussage.

Du kannst den folgenden Beweis mit dieser Zeile starten.
-/

/- Theorem
Seien $a, b \in \mathbb{N}$. Falls es ein $c \in \mathbb{N}$ gibt, sodass $a=2*c$ ,
dann gibt es ein $d \in \mathbb{N}$, sodass $a*b=2*d$.
-/
theorem mul_gerade (a b : ℕ) (hger : ∃ c : ℕ, a=2*c) : ∃ d : ℕ, a*b = 2*d :=
begin
  obtain ⟨c, ager⟩ := hger,
  use [c*b],
  rw ager,
  rw mul_assoc,
end

/- Tactic : obtain
## Anleitung
Obtain (`obtain ⟨c, hc⟩ := h,`) verwendet die Existenzaussage `h : ∃ c : ℕ, hc` um eine 
Variable `c` und die entsprechende Aussage `hc` (h im konkretem Fall von `c`) einzuführen.
## Beispiel
Bei folgendem Zustand:
```
a b: ℕ
hger: ∃ (c : ℕ), a = 2 * c
⊢ ∃ (d : ℕ), a * b = 2 * d
```
führt `obtain ⟨c, ager⟩ := hger,` zu:
```
a b c: ℕ
ager: a = 2 * c
⊢ ∃ (d : ℕ), a * b = 2 * d
```
-/

end nat -- hide