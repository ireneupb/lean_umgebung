import natnum.add

namespace N

def mul : N → N → N
| m zero := zero
| m (succ n) := mul m n + m

instance : has_mul N := ⟨mul⟩
-- notation a * b := mul a b

lemma mul_zero (m : N) : m * zero = zero := rfl

lemma mul_succ (m n : N) : m * (succ n) = m * n + m := rfl

end N