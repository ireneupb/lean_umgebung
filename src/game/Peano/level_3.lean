-- Level name : Die Peano Axiome - Teil 2

-- namespace nat -- hide 

import mynat.definition -- hide
import game.Peano.level_2 --hide
namespace N -- hide

/-

-/

/- Theorem
Falls `succ`$(a) = b$ und `succ`$(b)= c$, dann `succ`$($`succ`$(a)) = c$
-/
theorem succ_succ_c_anders (a b c : N) (h : succ(a) = b) (g : succ(b) = c): succ(succ(a)) = c :=
begin
rw [←h] at g,
exact g,



end

end N -- hide

/- Hint : Brauchst du Hilfe, um einen zweiten Weg zu finden?
In der zu zeigenden Aussage kommt der Term `c` vor, der auch Teil der Aussage
`g` ist. Du kannst also mit `rw ← g,` das `c` in der Aussage ersetzen.
-/