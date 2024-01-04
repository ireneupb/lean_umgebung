-- Level name : Die Peano Axiome - Teil 2

-- namespace nat -- hide 

import mynat.definition -- hide
import game.Peano.level_1 --hide
namespace N -- hide

/-
In diesem Level passiert nicht viel. Es dient eher zur Übung von dem Gelernten in
Level 1.

Vielleicht hast du gemerkt, dass es eine linke Spalte gibt. Hier kannst du alle
Tools finden, die du zum Beweisen brauchst. Das sind einerseits die Befehle (wie
z.B. `rw`), die in LEAN Tactics heißen. Andererseits sind das die Axiome und Aussagen,
die wir bereits eingeführt/bewiesen haben. Diese sind in der Kategorie Theorem
statements. Umso weiter du bist, umso mehr Inhalt wirst du hier finden.

Wir werden aber auch die Gelegenheit nutzen, um uns den `rw` Befehl nochmal
anzuschauen. Wir haben gesehen, dass für die Aussage `h: a = b` der Befehl
`rw h,` in der zu zeigenden Aussage jedes `a` durch ein `b` ersetzt. Aber wie
kann man jedes `b` durch ein `a` ersetzen? Dazu verwendet man den Befehl
`rw ← h,`. Der Pfeil steht sozusagen dafür, dass LEAN die Aussage h von rechts
nach links lesen soll. Du kannst den Pfeil mit \ l (backslash + klein L)
schreiben.

Du kannst das untenstehende Lemma ähnlich wie Level 1 lösen, aber erkennst du
auch einen weiteren Weg?
-/

/- Theorem
Falls `succ`$(a) = b$ und `succ`$(b)= c$, dann `succ`$($`succ`$(a)) = c$
-/
theorem succ_succ_c (a b c : N) (h : succ(a) = b) (g : succ(b) = c): succ(succ(a)) = c :=
begin
rw h,
rw g,



end

end N -- hide

/- Hint : Brauchst du Hilfe, um einen zweiten Weg zu finden?
In der zu zeigenden Aussage kommt der Term `c` vor, der auch Teil der Aussage
`g` ist. Du kannst also mit `rw ← g,` das `c` in der Aussage ersetzen.
-/