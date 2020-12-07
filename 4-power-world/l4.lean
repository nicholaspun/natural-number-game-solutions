lemma one_pow (m : mynat) : (1 : mynat) ^ m = 1 :=
begin
induction m with k Pk,
exact pow_zero 1,
rw pow_succ,
rw Pk,
exact one_mul 1,
end