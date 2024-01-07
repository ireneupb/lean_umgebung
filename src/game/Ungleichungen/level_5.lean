-- Level name : Der Widerspruchsbeweis

-- namespace nat -- hide 

import data.nat.basic -- hide
import tactic
namespace nat -- hide 

/-
In LEAN wird für einen Widerspruchsbeweis die Tactic `by_contra` verwendet.
Angenommen, du möchtest die Aussage P mit einem Widerspruchsbeweis beweisen, 
Du verwendest als erstes `by_contra` um den Widerspruchsbeweis zu starten.
Du wirst sehen, dass nun `¬P` unter den gegebenen Aussagen ist, und das neue
Beweisziel `⊢ false` ist. Das bedeutet, dass das Ziel ist, einen Widespruch zu
erzeugen.

Ein Widerspruchsbeweis sieht also zum Beispiel so aus:

```
theorem no_n_succ_eq_zero : ¬∃ (n : ℕ), n+1=0 :=
begin
by_contra hex,
obtain ⟨n, hn⟩ := hex,
linarith,
end
```
Dabei kann man nach `by_contra` einen Namen (hier `hex`) für die Widerspruchsannahme geben.

In diesem Level werden wir mit einem Widerspruchsbeweis zeigen, dass es keine natürliche
Zahl $a<4$ gibt, die ein echtes Vielfaches von $4$ ist.

Um den LEAN beweis zu schreiben, kannst du diesen Beweis verwenden:
1. Widerspruchsannahme: Angenommen es gibt $a, b \in \mathbb{N}$ mit $b>0$, $a<4$ und $a=b*4$.
2. Seien nun $a, b \in \mathbb{N}$ sodass $b>0$, $a<4$ und $a=b*4$.
3. Wir geben der Aussage $b>0$ den Namen hb, der Aussage $a<4$ den Namen ha und der Aussage
$a=b*4$ den Namen hab.
4. Wir zeigen nun zuerst, dass $a\geq0$, indem wir die Aussage hnm und arithmetische
Operationen verwenden.
5. Mit dieser neuen Aussage und arithmentischen Operationen lässt sich ein Widerspruch
zur Aussage hn herleiten.
-/

/- Theorem
Es gibt kein $a, b \in \mathbb{N}$ mit $b>0$, $a<4$ und $a=b*4$.
-/
theorem no_small_mul_four : ¬∃ (a b : ℕ), b > 0 ∧ a<4 ∧ a = b*4 :=
begin
by_contra h_contr,
obtain ⟨n, m, hnm⟩ := h_contr,
cases hnm with hm hrest,
cases hrest with hn hnm,
have n_bigger_four : n ≥ 4,
{rw [hnm],
linarith,},
linarith,




end


/- Tactic : by_contra
## Anleitung
Wenn eine Aussage `P` zu beweisen ist, startet `by_contra` einen Widerspruchsbeweis
indem `¬P` zu den gegebenen Aussagen hinzugefügt wird und das Beweisziel zu `⊢ false` wird.
## Beispiel
Folgender Zustand:
```
⊢ ¬∃ (n : ℕ), n + 1 = 0
```
wird durch `by_contra hex,` zu 
```
hex: ∃ (n : ℕ), n + 1 = 0
⊢ false
```
-/
end nat -- hide