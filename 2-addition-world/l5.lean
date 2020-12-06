theorem succ_eq_add_one (n : mynat) : succ n = n + 1 :=
begin
rw one_eq_succ_zero, rw add_succ, rw add_zero, refl,
end