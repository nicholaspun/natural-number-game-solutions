theorem not_succ_le_self (a : mynat) : ¬ (succ a ≤ a) :=
begin
intro h,
have h2 := (le_antisymm a (succ a)) (le_succ_self a) h,
exact (ne_succ_self a) h2,
end