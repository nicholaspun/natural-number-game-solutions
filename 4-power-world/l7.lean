lemma pow_pow (a m n : mynat) : (a ^ m) ^ n = a ^ (m * n) :=
begin
induction n with k Pk,
rw mul_zero,
rw pow_zero a,
exact pow_zero (a^m),

rw pow_succ,
rw Pk,
rw ← pow_add,
rw mul_succ,
refl,
end