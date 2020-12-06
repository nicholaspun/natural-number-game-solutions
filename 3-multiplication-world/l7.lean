lemma add_mul (a b t : mynat) : (a + b) * t = a * t + b * t :=
begin
induction t with k Pk,
repeat { rw mul_zero },
rw add_zero,
refl,

repeat { rw mul_succ },
rw Pk,
simp,
end