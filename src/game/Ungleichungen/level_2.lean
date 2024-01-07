-- Level name : Pythagoreisches Tripel

-- namespace nat -- hide 

import data.nat.basic -- hide
import tactic -- hide
namespace nat -- hide 

/-
Ein pythagoreisches Tripel besteht aus drei positiven natürlichen Zahlen $a$, $b$
und $c$, die die Gleichung $a^2 + b^2 = c^2$ erfüllen. Diese Tripel sind besonders
bekannt im Zusammenhang mit dem Satz des Pythagoras, der besagt, dass in einem 
rechtwinkligen Dreieck das Quadrat der Länge der Hypotenuse $c$ gleich der Summe der Quadrate
der Längen der beiden Katheten $a$ und $b$ ist.

In diesem Level möchten wir zeigen, dass ein solches Tripel existiert. Da wir keine
Potenzen eingeführt haben schreiben wir $a^2$ als $a⬝a$.
-/



/- Theorem
Es gibt $a, b, c \in \mathbb{N}$ mit $a⬝a+b⬝b+c⬝c$.
-/
theorem Pythagoreisches_Tripel : ∃ a b c : ℕ, a*a+b*b=c*c :=
begin
  use [3, 4, 5],
  linarith,


  
end

/- Hint: Kommst du nicht weiter?
Bei Existenzbeweisen brauchst du die Tactic `use`. Denk auch daran, dass du die Tactic
`linarith` verwenden darfst um Ausdrücke zu vereinfachen.
-/

end nat -- hide