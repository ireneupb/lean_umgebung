-- Level name : Kommutativität der rechten Summanden

import data.nat.basic -- hide
import tactic
namespace nat -- hide

/-

-/

/- Theorem
$a+b+c=a+c+b$
-/
theorem no_name_yet (a : ℕ) (h : a + 2 = 4): a + 3=5 :=
begin
have ha : a = 2,
{linarith,},
rw ha,


end

end nat -- hide