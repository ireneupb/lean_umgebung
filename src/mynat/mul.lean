import mynat.add

namespace N

def mul : N → N → N
| m zero := zero
| m (succ n) := mul m n + m

instance : has_mul N := ⟨mul⟩
-- notation a * b := mul a b

example : (1 : N) * 1 = 1 := 
begin
refl
end


lemma mul_zero (m : N) : m * zero = zero := rfl

lemma mul_succ (m n : N) : m * (succ n) = m * n + m := rfl

end N