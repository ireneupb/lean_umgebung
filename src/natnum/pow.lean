import natnum.mul

namespace N

def pow : N → N → N
| m zero := one
| m (succ n) := pow m n * m

instance : has_pow N N := ⟨pow⟩
-- notation a ^ b := pow a b

lemma pow_zero (m : N) : m ^ (zero : N) = one := rfl

lemma pow_succ (m n : N) : m ^ (succ n) = m ^ n * m := rfl

end N