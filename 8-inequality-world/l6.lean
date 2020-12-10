theorem le_antisymm (a b : mynat) (hab : a ≤ b) (hba : b ≤ a) : a = b :=
begin
cases hab with c hc,
cases hba with d hd,
rw hd at hc,
rw add_assoc at hc,
symmetry at hc,
have h := eq_zero_of_add_right_eq_self hc,
have h2 := add_right_eq_zero h,
rw h2 at hd,
rw add_zero at hd,
exact hd,
end