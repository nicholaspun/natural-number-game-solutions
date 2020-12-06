lemma succ_mul (a b : mynat) : succ a * b = a * b + b :=
begin
induction b with k Pk,
repeat { rw mul_zero },
rw add_zero,
refl,
repeat { rw mul_succ },
rw Pk,
repeat { rw add_succ },
rw add_right_comm,
refl,


end