-- Level name : Kommutativität der rechten Summanden

import mynat.add -- hide
import game.Addition.level_7 --hide
namespace N -- hide

/-
Das Ziel dieses Levels ist $a+b+c=a+c+b$. Das sieht vielleicht erstmal danach aus,
dass du nur `add_comm,` anwenden muss. Aber LEAN ist links-assoziativ. Das bedeutet,
dass diese Aussage mit Klammern so geschrieben werden kann: $(a+b)+c=(a+c)+b$. Um
dieses Lemma zu zeigen, wirst du also auch die Assoziativität verwenden. Dieses
Lemma wird dir in zukünftigen Beweisen etwas Schreibarbeit sparen.

Noch eine Bemerkung: manchmal gibt es mehr als eine Stelle, an der `rw` etwas
anstellen kann. Wenn du nichts Weiteres spezifizierst, wird LEAN die erste dieser
Stellen heraussuchen. Wenn du zum Beispiel in diesem Level damit anfangen möchtest,
dass du auf der rechten Seite $a+c+b$ zu $a+(c+b)$ umschreibst, wird das nicht mit
dem Befehl `rw add_assoc,` klappen. Dies wird nämlich in der linken Seite der Gleichung
die Assoziativität ausnutzen. Du kannst LEAN konkret angeben an welcher Stelle du die
Änderung möchtest, in diesem Fall: `rw add_assoc a c b,`.
-/

/- Theorem
$a+b+c=a+c+b$
-/
theorem add_right_comm (a b c: N) : a + b + c = a + c + b :=
begin
rw add_assoc a b c,
rw add_comm b c,
rw ← add_assoc a c b,



end

end N -- hide