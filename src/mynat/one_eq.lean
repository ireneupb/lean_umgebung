-- This file should help import the theoremes that are "lost" when reading in nat instead of
-- mynat (to be completed)

import data.nat.basic -- hide
import tactic -- hide
namespace nat -- hide

theorem one_eq_succ_zero : 1=succ(0) :=
begin
linarith,
end

end nat -- hide