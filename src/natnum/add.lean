import natnum.definition

namespace N

def add : N → N → N
| m 0 := m
| m (succ n) := succ (add m n)

instance : has_add N := ⟨N.add⟩

lemma add_zero (m : N) : m + zero = m := rfl

lemma add_succ (m n : N) : m + succ n = succ (m + n) := rfl

end N