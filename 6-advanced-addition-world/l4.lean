theorem succ_eq_succ_iff (a b : mynat) : succ a = succ b ↔ a = b :=
begin
split,
exact succ_inj,
exact succ_eq_succ_of_eq,
end