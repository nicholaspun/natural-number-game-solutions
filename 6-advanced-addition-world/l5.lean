theorem add_right_cancel (a t b : mynat) : a + t = b + t → a = b :=
begin
induction t with k Pk,
intro h,
repeat { rw add_zero at h },
exact h,

intro h_2,
repeat { rw add_succ at h_2 },
have q := succ_inj h_2,
exact Pk(q),
end