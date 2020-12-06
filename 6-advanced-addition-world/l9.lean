theorem succ_ne_zero (a : mynat) : succ a ≠ 0 := 
begin
symmetry,
exact zero_ne_succ a,
end