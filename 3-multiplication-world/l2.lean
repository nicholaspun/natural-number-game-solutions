lemma mul_one (m : mynat) : m * 1 = m :=
begin
rw one_eq_succ_zero,
rw mul_succ,
rw mul_zero,
rw zero_add,
refl,
end