theorem mul_eq_zero_iff (a b : mynat): a * b = 0 ↔ a = 0 ∨ b = 0 :=
begin
split,
exact eq_zero_or_eq_zero_of_mul_eq_zero a b,
intro h,
cases h,
rw h,
exact zero_mul b,
rw h,
exact mul_zero a,

end