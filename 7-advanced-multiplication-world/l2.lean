theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : mynat) (h : a * b = 0) :
  a = 0 ∨ b = 0 :=
begin
cases b with n,
right, refl,
rw mul_succ at h,
rw add_comm at h,
left,
exact add_right_eq_zero h,
end