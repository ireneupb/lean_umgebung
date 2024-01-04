-- Level name : intro

/-
# Die natürlichen Zahlen
## Worum geht es in diesem Spiel?
### Mathematisch 
In der Schule lernen wir die natürlichen Zahlen kennen und wir lernen, wie 
wir mit ihnen elementare Rechenoperationen durchführen. Dabei wird aber nicht 
auf die formale Definition eingegangen.

In dieser Einheit möchten wir die Definition der natürlichen Zahlen nach Peano
betrachten. Grob gesagt entstehen damit die natürlichen Zahlen aus der 0 zusammen 
mit Rekursion. Über die Rekursion kann dann die Addition, Multiplikation und 
Potenzierung definiert werden. Für diese Rechenoperationen werden wir dann die 
grundlegenden Eigenschaften wie Kommutativität und Assoziativität zeigen.

### Technologisch
Wir werden die Programmiersprache 
<a href="https://leanprover-community.github.io/" target="blank">LEAN</a> kennenlernen.
LEAN ist ein interaktiver Theorembeweiser. In einem Theorembeweiser kann man
einen Beweis Schritt für Schritt (in Computersprache) eingeben. Dieser überprüft
dann, ob der Beweis korrekt ist und kann an jeder Stelle des Beweises Feedback zum
aktuellen Stand des Beweises geben.


## Eine kurze Anleitung.
Mit diesem Tool kannst du an dieser Einheit arbeiten. Die Einheit ist in die Kapitel
Peano, Addition, Multiplikation und Potenzen eingeteilt. Bei der Addition und der 
Multiplikation gibt es zusätzliche Kapitel mit Extra-Aufgaben. Jedes Kapitel hat 
mehrere Level. Am besten ist es, wenn du die Kapitel und Level der Reihe nach 
bearbeitest. Eine Ausnahme sind die Extra-Kapitel, die nicht erforderlich sind,
um mit dem nächsten Kapitel weiterzumachen.

In jedem Level gibt es als Erstes einen Text, der den mathematischen Inhalt und die 
nötigen LEAN-Anleitungen des Levels einführt. Darunter ist die zu lösende Aufgabe:
der Beweis eines Satzes, der in LEAN ausgeführt werden soll.

Dein Fortschritt wird nicht automatisch gespeichert. Um beim nächsten Mal dort
weiterzumachen, wo du aufgehört hast, solltest du vor dem Schließen dieses Fensters
den 💾 Button über dem Spielbaum klicken. Damit wird dein Spielstand in einer json-Datei gespeichert.
Diese kannst du beim nächsten Mal hochladen, indem du den 📝 Button klickst. 

Viel Spaß beim Coden!

## Du bist mit dem Tool fertig - was nun?

Dieses Tool ist eine Anpassung der ersten Levels in dem 
<a href="https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/" target="blank">Natural Number Game</a>
von Kevin Buzzard. Du kannst dort noch mehr Levels lösen und viele andere Befehle
kennenlernen (In unserem Modul haben wir nur `rw` und `induction` verwendet). Die LEAN Version dort
ist etwas älter und einige Dinge funktionieren leicht anders, am besten solltest
du also die ersten paar Levels wieder lösen.
-/