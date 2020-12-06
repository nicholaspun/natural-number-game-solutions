theorem add_right_cancel_iff (t a b : mynat) :  a + t = b + t ↔ a = b :=
begin
split,
exact add_right_cancel a t b,
induction t with k Pk,
rw add_zero,
rw add_zero,
intro x, exact x,
intro f,
rw add_succ, rw add_succ,
have g := Pk(f),
rw g,
refl,
end