lemma le_zero (a : mynat) (h : a ≤ 0) : a = 0 :=
begin
cases h with b hd,
symmetry at hd,
exact add_right_eq_zero hd,
end