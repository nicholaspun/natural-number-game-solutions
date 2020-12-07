lemma mul_pow (a b n : mynat) : (a * b) ^ n = a ^ n * b ^ n :=
begin
induction n with k Pk,
repeat { rw pow_zero },
rw one_mul,
refl,

rw pow_succ a,
rw mul_assoc (a^k) _ _,
rw mul_left_comm,
rw pow_succ b,
rw ← mul_assoc (a^k) _ _,
rw ← Pk,
rw ← mul_left_comm,
exact pow_succ (a * b) k,

end