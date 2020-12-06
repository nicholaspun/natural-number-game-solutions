lemma mul_comm (a b : mynat) : a * b = b * a :=
begin
induction b with k Pk,
rw zero_mul, rw mul_zero, refl, 
rw mul_succ, rw succ_mul, rw Pk, refl,
end