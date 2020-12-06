lemma mul_add (t a b : mynat) : t * (a + b) = t * a + t * b :=
begin
induction b with k Pk,
rw mul_zero,
repeat { rw add_zero },
rw mul_succ,
rw ← add_assoc,
rw ← Pk,
rw ← mul_succ,
rw add_succ,
refl,
end