-- Level name : Addition mit 0 - von links

import mynat.add -- hide
import game.Addition.level_3 --hide
namespace N -- hide

/- Tactic : induction
## Anleitung
falls `n : N` gegeben ist, dann startet `induction n with d hd`
einen Induktionsbeweis über `n` der zu beweisenden Aussage. `d` wird 
der Name der Variable im Induktionsschritt sein, und `hd` ist die Aussage
der Induktionsvoraussetzung.
## Beispiel
Bei folgendem Zustand:
```
n : N
⊢ 2 * n = n + n
```
dann wird `induction n with d hd` zwei neue Ziele öffnen:
```
⊢ 2 * 0 = 0 + 0
```
und
```
d : mynat,
hd : 2 * d = d + d
⊢ 2 * succ d = succ d + succ d
```
-/

/-
Nach Definition der Addition gilt: $a+0=a$. Wir haben aber noch nicht bewiesen,
dass die Addition kommutativ ist. Es ist also noch nicht bewiesen, dass auch
$0+a=a$ gilt.

Dies werden wir über Induktion zeigen. Dazu lernen wir den `induction` Befehl in
LEAN. Um einen Induktionsbeweis zu starten, müssen wir `induction a with d hd,`
aufrufen. Dabei ist das $a$ die Variable, über die induziert werden soll, $d$
wird der Name der Variable im Induktionsschritt sein, und `hd` ist die Aussage
der Induktionsvoraussetzung.

Nachdem du den Befehl `induction a with d hd,` eingibst, wirst du in der rechten
Spalte sehen, dass du zwei Beweisziele hast: den Induktionsanfang und die 
Induktionsvoraussetzung. Um den Beweis übersichtlicher zu führen, kannst du
die zwei Teile mit geschweiften Klammern umgeben. Dein Beweis hat dann die Form: <br>
`begin` <br>
  `induction a with d hd,` <br>
  `{},` <br>
  `{},` <br>
`end` <br>
Innerhalb der geschweiften Klammern kannst du dann jeweils den Induktionsanfang und
den Induktionsschritt zeigen.

Zu diesem Beweis gibt es <a href="https://go.upb.de/lean_2_3" target="blank">hier</a> ein Aufgabenblatt.
-/

/- Theorem
$0+a=a$
-/
theorem zero_add (a : N) : 0 + a = a :=
begin
  induction a with d hd,
  {rw N_zero_eq_zero,
   rw add_zero,},
  {rw add_succ,
  rw hd,},



end

end N -- hide