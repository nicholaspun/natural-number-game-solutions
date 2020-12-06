lemma zero_mul (m : mynat) : 0 * m = 0 :=
begin
induction m with k Pk,
apply mul_zero,
rw mul_succ,
rw add_zero,
exact Pk,
end