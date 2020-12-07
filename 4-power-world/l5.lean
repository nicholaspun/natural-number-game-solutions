lemma pow_add (a m n : mynat) : a ^ (m + n) = a ^ m * a ^ n :=
begin
induction n with k Pk,
rw add_zero,
rw pow_zero,
rw mul_one,
refl,

rw pow_succ,
rw ← mul_assoc,
rw ← Pk,
rw ← pow_succ,
rw add_succ,
refl,
end