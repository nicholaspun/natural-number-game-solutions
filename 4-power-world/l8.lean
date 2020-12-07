lemma add_squared (a b : mynat) :
  (a + b) ^ (2 : mynat) = a ^ (2 : mynat) + b ^ (2 : mynat) + 2 * a * b :=
begin
rw two_eq_succ_one,
rw one_eq_succ_zero,
repeat { rw pow_succ },
repeat { rw pow_zero },
repeat { rw one_mul },

rw mul_add,
repeat { rw add_mul },
rw mul_comm b a,
rw add_assoc,
rw ← add_assoc (a * b) _ _,
rw ← one_mul (a * b),
rw ← add_mul,
rw ← one_eq_succ_zero,
rw ← succ_eq_add_one,
rw add_comm _ (b * b),
rw ← add_assoc,
rw ← mul_assoc,
refl,
end