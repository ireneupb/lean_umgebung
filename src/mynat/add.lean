import mynat.definition

/- 
  mynat/add.lean
  
-/
namespace N

-- definition of "addition on the natural numbers"
def add : N → N → N
| m 0 := m
| m (succ n) := succ (add m n)

instance : has_add N := ⟨N.add⟩

-- numerals now work
example : N := 37

lemma add_zero (m : N) : m + 0 = m := rfl

lemma add_succ (m n : N) : m + succ n = succ (m + n) := rfl

-- end of definition of "addition on the natural numbers"

end N
