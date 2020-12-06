lemma add_succ_zero (a : mynat) : a + succ(0) = succ(a) :=
begin
rw add_succ, rw add_zero, refl,
end