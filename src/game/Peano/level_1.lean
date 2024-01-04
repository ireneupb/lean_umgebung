-- Level name : Die Peano Axiome

-- namespace nat -- hide 

import mynat.definition -- hide
namespace N -- hide

/-
Die natürlichen Zahlen können mit Peanos Axiomen eindeutig definiert werden. Die
Axiome lauten wie folgt:
- $A_1$: $0$ (in LEAN: `zero`) ist eine natürliche Zahl 
- $A_2$: Es gibt eine injektive Abbildung `succ`$: \mathbb{N} \to \mathbb{N}$, die für jede natürliche Zahl ihren Nachfolger angibt.
- $A_3$: $0$ ist nicht der Nachfolger einer natürlichen Zahl.
- $A_4$: Das Prinzip der Induktion: Enthält eine Menge die $0$ und für jede enthaltene natürliche Zahl $n$ auch ihren Nachfolger `succ`$(n)$, so enthält sie alle natürlichen Zahlen.

In LEAN kann man die Anwendung der Abbildung `succ` auf `a` sowohl als `succ(a)` als auch 
als `a.succ` schreiben.
-/

/- Hint : Wieso brauchen wir hier die Abbildung `succ`, um den Nachfolger einer Zahl $n$ zu beschreiben, anstatt den Ausdruck n+1 zu verwenden?
Wir haben die Addition noch nicht definiert. Außerdem ist `succ`$(n)=n+1$ mit $1=$`succ`$(0)$ dann noch zu beweisen.
-/

/-
Aus diesen Axiomen werden wir alles herleiten und beweisen, was wir in dieser Einheit
vorhaben. In diesem Level werden wir folgende Aussage zur Funktion `succ` zeigen: Für die natürlichen Zahlen a und b gilt: falls `succ(a)=b` dann `succ(succ(a))=succ(b)`.

Diese Aussage kann man direkt zeigen, indem man die gegebene Hypothese `succ(a)=b` in die
zu zeigende Aussage `succ(succ(a))=succ(b)` einsetzt und somit `succ(b)=succ(b)` erhält.

Wir schauen uns nun an, wie das in LEAN funktioniert. Wir werden mit der Klasse
N arbeiten, die genau nach den Axiomen von Peano definiert ist.
-/

/- Hint : Klicke hier, um die Definition der natürlichen Zahlen in LEAN zu sehen. Du musst diesen Code nicht zu 100% verstehen.
`inductive N` → $A_4$ <br>
`| zero : N` → $A_1$ <br>
`| succ (n : N) : N` → $A_2$ <br>
`lemma succ_inj {m n : N} (h : succ m = succ n) : m = n := by cases h; refl` → $A_2$ <br>
`lemma zero_ne_succ (m : N) : (zero : N) ≠ succ m := λ h, by cases h` → $A_3$
-/

/-
Als Erstes muss man das Lemma definieren, das man beweisen möchte. Dies besteht aus drei 
Teilen.
- Name: Der Name kann beliebig gewählt werden, ist im besten Fall aber eine gute 
Beschreibung des Lemmas. Hier kann man zum Beispiel “succ_succ” wählen, um anzudeuten, 
dass es um die Zweifachanwendung der Abbildung `succ` geht.
- Voraussetzungen: Diese stehen zwischen dem Namen und dem Doppelpunkt. In diesem Fall
sind das, dass a und b natürliche Zahlen sind und die Aussage h, dass `succ(a)=b`.
- Folgerung: Diese steht zwischen dem Doppelpunkt und dem Definitionszeichen. In diesem
Fall also, `succ(succ(a))=b`.

Der Beweis folgt zwischen dem `begin` und dem `end`. Zu Beginn der Bearbeitung steht im
Beweis immer `sorry`. Dies ist ein Keyword, was so viel bedeutet wie: "Hier fehlt ein
Teil des Beweises". Du kannst dieses Keyword verwenden, wenn ein Beweis überprüft werden
soll, bei dem dir noch ein Teil fehlt. LEAN wird bestätigen, dass der Beweis stimmt, aber
mit dem warning "uses `sorry`" darauf hinweisen, dass noch etwas zu tun ist. Lösche als
Erstes das `sorry`, um mit dem Beweis zu starten.

Wir haben oben bereits beschrieben, wie der Beweis mathematisch funktioniert. Wie 
übertragen wir die Idee in LEAN? Dazu gibt es den `rw` (rewrite) Befehl. Wenn `h` eine
Aussage ist (z.B. $a=b$), dann bewirkt `rw h,`, dass LEAN die Aussage `h` in der zu 
zeigenden Aussage einsetzt (im Beispiel würde also in der zu zeigenden Aussage jedes $a$
mit einem $b$ ersetzt werden). Probiere also den Befehl `rw h,` aus. Das Komma am Ende 
jedes LEAN-Befehls ist sehr wichtig. Wenn du Fehlermeldungen bekommst, die du nicht
verstehst, überprüfe deinen Code auf fehlende Kommata.

Die rechte Spalte:
Hier gibt LEAN dynamisches Feedback. Bis auf die letzte Zeile steht hier immer was 
gegeben ist, in diesem Fall zum Beispiel, dass a und b natürliche Zahlen sind und die
Aussage `h`. In der letzten Zeile, nach dem `⊢` Symbol, steht immer das aktuelle Ziel, 
also das, was gerade zu  zeigen ist. Wenn man am Anfang des Beweises steht, ist das 
noch die ganze Aussage des Lemmas. Nachdem man `rw h,` eingibt, sieht man, dass sich 
der Zustand ändert. In diesem Fall kommt die Nachricht `Proof complete!`, die uns 
angibt, dass wir fertig sind. In längeren Aufgaben würde hier das neue Ziel stehen.
-/

/- Theorem
Falls `succ`$(a) = b$, dann `succ`$($`succ`$(a)) = $`succ`$(b)$
-/
theorem succ_succ (a b : N) (h : succ(a) = b): succ(succ(a)) = succ(b) :=
begin
rw h,



end

/- Tactic : rw
## Anleitung
Wenn `h` eine Aussage des Typs `X = Y` ist, dann wird
`rw h,` alle `X` in der zu beweisenden Aussage durch
`Y` austauschen.
Um alle `Y` durch `X` zu ersetzten verwendet man `rw ← h`.
## Beispiel
Bei folgendem Zustand:
```
x : N
⊢ succ (x + 0) = succ (x)
```
wird `rw add_zero,` das Ziel umändern zu `⊢ succ x = succ (x)`,
und damit den Beweis abschließen.
-/

end N -- hide