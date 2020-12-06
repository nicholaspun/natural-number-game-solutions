lemma add_assoc (a b c : mynat) : (a + b) + c = a + (b + c) :=
begin
induction c with k Pk,
rw add_zero b, rw add_zero, refl,
rw add_succ, rw Pk, rw ← add_succ, rw ← add_succ, refl,
end