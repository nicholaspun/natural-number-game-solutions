lemma mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c) :=
begin
induction c with k Pk,
repeat { rw mul_zero },
repeat { rw mul_succ },
rw mul_add,
rw Pk,
refl,
end