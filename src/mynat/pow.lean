import mynat.mul

namespace N

def pow : N → N → N
| m zero := one
| m (succ n) := pow m n * m

instance : has_pow N N := ⟨pow⟩
-- notation a ^ b := pow a b

example : (1 : N) ^ (1 : N) = 1 := 
begin
refl
end

lemma pow_zero (m : N) : m ^ (0 : N) = 1 := rfl

lemma pow_succ (m n : N) : m ^ (succ n) = m ^ n * m := rfl

end N