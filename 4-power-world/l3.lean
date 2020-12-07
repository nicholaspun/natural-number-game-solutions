lemma pow_one (a : mynat) : a ^ (1 : mynat) = a :=
begin
rw one_eq_succ_zero,
rw pow_succ,
rw pow_zero,
exact one_mul a,
end