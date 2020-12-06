lemma ne_succ_self (n : mynat) : n ≠ succ n :=
begin
cases n with k,
exact zero_ne_succ 0,
intro x,
have h := succ_eq_succ_iff k (succ k),
rw h at x,
symmetry at x,
rw succ_eq_add_one at x,
have h2 := eq_zero_of_add_right_eq_self x,
rw one_eq_succ_zero at h2,
symmetry at h2, 
apply zero_ne_succ 0,
exact h2,



end