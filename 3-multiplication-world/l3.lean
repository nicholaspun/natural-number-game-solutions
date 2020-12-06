lemma one_mul (m : mynat) : 1 * m = m :=
begin
induction m with k Pk,
rw mul_zero, refl,
rw mul_succ,
rw Pk,
symmetry,
exact succ_eq_add_one _,
end