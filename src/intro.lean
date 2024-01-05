-- Level name : intro

/-
# Einführung in den Theorembeweiser LEAN
## Worum geht es in dieser Lernumgebung?
### Mathematisch 
In der Schule lernen wir die natürlichen Zahlen kennen und wir lernen, wie 
wir mit ihnen elementare Rechenoperationen durchführen. Dabei wird aber nicht 
auf die formale Definition eingegangen.

In dieser Einheit möchten wir die Definition der natürlichen Zahlen nach Peano
betrachten. Grob gesagt entstehen damit die natürlichen Zahlen aus der 0 zusammen 
mit Rekursion. Über die Rekursion kann dann die Addition und Multiplikation definiert 
werden. Für diese Rechenoperationen werden wir dann die grundlegenden Eigenschaften 
wie Kommutativität und Assoziativität zeigen. Danach führen wir das Konzept der 
Ungleichungen ein, indem wir definieren, dass $a \leq b$ genau dann, wenn ein 
$k \in \mathbb{N}$ existiert, sodass $a+k=b$. Diese Resultate verwenden wir um am Ende
der Lernumgebung den Satz der Divion mit Rest zu zeigen, also:

Für alle $n,m \in \mathbb{N}$ mit $m>0$ gibt es $q,r \in \mathbb{N}$ mit $q < m$ und
$n=q*m+r$.

### Technologisch
Wir werden die Programmiersprache 
<a href="https://leanprover-community.github.io/" target="blank">LEAN</a> kennenlernen.
LEAN ist ein interaktiver Theorembeweiser. In einem Theorembeweiser kann man
einen Beweis Schritt für Schritt (in Computersprache) eingeben. Dieser überprüft
dann, ob der Beweis korrekt ist und kann an jeder Stelle des Beweises Feedback zum
aktuellen Stand des Beweises geben.


## Eine kurze Anleitung.
Mit diesem Tool kannst du an dieser Einheit arbeiten. Die Einheit ist in die Kapitel
Peano, Addition, Multiplikation, Ungleichungen und Division mit Rest eingeteilt. Jedes
Kapitel hat mehrere Level. Am besten ist es, wenn du die Kapitel und Level der Reihe nach 
bearbeitest.

In jedem Level gibt es als Erstes einen Text, der den mathematischen Inhalt und die 
nötigen LEAN-Anleitungen des Levels einführt. Darunter ist die zu lösende Aufgabe:
der Beweis eines Satzes, der in LEAN ausgeführt werden soll. Oft musst du den Beweis
nicht vollständig selber machen, weil ein Ausgangs-Code ist in der Einführung gegeben
ist.

Dein Fortschritt wird im normalfall automatisch im Browser gespeichert. Wenn du 
vorsichtshalber deinen Stand speichern möchtest klicke in diesem Fensters den 💾 Button 
über dem Spielbaum. Damit wird dein Spielstand in einer json-Datei gespeichert. Diese 
kannst du beim nächsten Mal hochladen, indem du den 📝 Button klickst. 

Viel Spaß beim Coden!

## Du bist mit dem Tool fertig - was nun?

Dieses Tool ist inspiriert durch das 
<a href="https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/" target="blank">Natural Number Game</a>
von Kevin Buzzard. Du kannst dort andere Levels lösen. Die LEAN Version dort
ist etwas älter und einige Dinge funktionieren leicht anders, am besten solltest
du also die ersten paar Levels wieder lösen, obwohl sie sehr ähnlich sind.
-/