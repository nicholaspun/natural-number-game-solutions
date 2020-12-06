lemma zero_add (n : mynat) : 0 + n = n :=
begin
induction n with k Pk,
rw add_zero, refl,
rw add_succ, rw Pk, refl, 
end