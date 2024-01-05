-- Level name : Ein Existenzbeweis

import data.nat.basic -- hide
import tactic -- hide
namespace nat -- hide

/-
Nun hast du alle grundlegenden Eigenschaften der Addition gezeigt. In den
verbleibenden Levels der "Addition" möchten wir nun ein bisschen "rechnen".

In diesem Level geht es konkret darum zu zeigen, dass es natürliche Zahlen
$a$ und $b$ gibt, sodass a+b=10. Um das zu Beweisen muss man nur ein solches
Paar an Zahlen angeben, zum Beispiel $4$ und $6$. In diesem Level werden wir
die Tactic `use` kennenlernen, mit der man bei Existenzaussagen im Beweiszustand
konkrete Objekte übergeben kann. Wir führen `use` am Beispiel dieses Levels ein:
Der Zustand ist:
```
⊢ ∃ (a b : ℕ), a + b = 10
```
Mit `use [4,6],` wird der Beweiszustand ersetzt durch `⊢ 4 + 6 = 10`, was den
Beweis direkt löst. 
Probier diesen Schritt direkt im Beweis aus. Du kannst $4$ und $6$ nun auch durch
andere Zahlenpaare ersetzen, die $10$ ergeben. Probiere zuletzt noch aus, den
Schritt einzuteilen in:
```
use [4],
use [6],
```
dann kannst du im Zwischenschritt nachvollziehen, was `use` verändert hat.
-/

/- Für welches $a \in \mathbb{N}$ kann der Beweis mit `repeat{use a,},` gelöst werden?
Das funktioniert nur mit $a=5$. In diesem Fall wird dann zweimal `use 5,` ausgeführt,
was analog zu `use [5,5],` ist. Probier es doch mal aus!
-/

/- Theorem
Es existieren $a, b, \in \mathbb{N}$, sodass a+b=10.
-/
theorem ex_add_10 : (∃ a b : ℕ, a+b=10) :=
begin
use [4,6],
end

/- Tactic : use
## Anleitung
für einen Beweiszustand `⊢ ∃ (a : ℕ), Aussage(a)` setzt `use [b],` `b` ein,
sodass der Beweiszustand zu `⊢ Aussage(b)` wird. `b` muss nicht eine konkrete
Zahl sein, sonder kann eine Variable sein, zum Beispiel eine Induktionsvariable.
Es können mehrer Werte übergeben werden (`[b,c]`), wenn die Existenzaussage mehrere
Variablen enthält. 
## Beispiel
Bei folgendem Zustand:
```
⊢ ∃ (a b : ℕ), a + b = 10
```
setzt `use [4,6],` jeweils $4$ und $6$ für `a` und `b` ein und löst den Beweis.
-/

end nat -- hide