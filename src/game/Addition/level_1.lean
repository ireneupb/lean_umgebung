-- Level name : TBD

-- namespace nat -- hide 
import mynat.add -- hide
import game.Peano.level_3 -- hide
namespace N -- hide

/-
Hier: SPEZIFIZIERUNG!
-/

/- Hint : Hint Title?
Hint teeeext.
-/

/-
More teeeeext (8)
-/

/- Theorem
TBD
-/

theorem succ_add_zero (a : N) : succ(a)+0=succ(a+0) :=
begin
rw add_zero a,
rw add_zero a.succ,
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