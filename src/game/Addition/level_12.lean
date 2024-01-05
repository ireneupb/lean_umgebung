-- Level name : Lineares Gleichungssystem

-- namespace nat -- hide 

import data.nat.basic -- hide
import tactic -- hide
import mynat.one_eq -- hide
namespace nat -- hide

/-
Wir schauen uns nun ein lineares Gleichungssystem an. Gegeben ist:
```
a + b = 8
b = 3
```
Und zu zeigen ist, dass `a=5`. Auch hier könnte man direkt `linarith` anwenden
und wäre fertig. Wir wollen uns aber die Frage stellen, wie wir eine hypothese
wie `h`, die ein "und" (`∧`) enthält in zwei hypothesen einteilen kann, damit man
sie einzeln verwenden kann.

Dazu gibt es die Tactic `cases`. Für eine hypothese `h : h1 ∧ h2` teilt `cases h with f g,`
die hypothese auf, sodass man die hypothesen `f : h1` und `g : h2` erhält. Die Namen der
neuen Hypothesen können wir hier (`f g`) explizit angegeben werden oder werden ansonsten
von LEAN vergeben.

Wir werden in diesem Level so vorgehen, dass wir die hypothese aufteilen um `b=3` in 
`a+b=8` einzusetzten. Dafür kannst du folgenden Schritte in deinem Beweis machen:
1. Teile `h` auf. Du kannst die neuen hypothesen `hab` und `ha` nennen, um anzudeuten,
dass `hab` die Gleichung ist die sowohl `a` wie auch `b` enthält und `ha` nur `a`.
2. Setzte mithilfe von `rw` die Gleichung `hb` in `hab` ein.
3. Nutze `linarith` um mit Umformungen den Beweis zu beenden.
-/


/- Theorem
Seien $a, b \in \mathbb{N}$ mit $a+b=8$ und $b=3$. Dann ist $a=5$.
-/
theorem LGS_1 (a b : ℕ) (h : a+b=8 ∧ b=3) : a=5 :=
begin
cases h with hab hb,
rw hb at hab,
linarith,
end

/- Tactic : cases
## Anleitung
Für eine hypothese `h : h1 ∧ h2` teilt `cases h with f g,`
die hypothese auf, sodass man die hypothesen `f : h1` und `g : h2` erhält.
## Beispiel
Bei folgendem Zustand:
```
ab: ℕ
h: a + b = 8 ∧ b = 3
⊢ a = 5
```
führt `cases h with hab hb,` zu:
```
ab: ℕ
hab: a + b = 8
hb: b = 3
⊢ a = 5
```
.
-/

end nat -- hide