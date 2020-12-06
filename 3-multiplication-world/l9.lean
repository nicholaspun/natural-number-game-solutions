lemma mul_left_comm (a b c : mynat) : a * (b * c) = b * (a * c) :=
begin
induction b with k Pk,
repeat { rw zero_mul },
rw mul_zero,
refl,
repeat { rw succ_mul },
rw mul_add,
rw Pk,
refl,

end