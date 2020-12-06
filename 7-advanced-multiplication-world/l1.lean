theorem mul_pos (a b : mynat) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 :=
begin
intros aH bH abH,
cases b with n,
apply bH,
refl,

apply aH,
rw mul_succ at abH,
rw add_comm at abH,
exact add_right_eq_zero abH,

end