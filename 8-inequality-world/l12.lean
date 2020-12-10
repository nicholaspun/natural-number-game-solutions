theorem le_of_succ_le_succ (a b : mynat) : succ a ≤ succ b → a ≤ b :=
begin
intro h,
repeat { rw succ_eq_add_one at h },
cases h with c hc,
rw add_assoc a 1 c at hc,
rw add_comm 1 c at hc,
rw ← add_assoc a c 1 at hc,
rw add_right_cancel_iff at hc,
rw hc,
use c, 
refl,
end