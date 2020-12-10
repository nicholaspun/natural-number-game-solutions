theorem le_total (a b : mynat) : a ≤ b ∨ b ≤ a :=
begin
induction a with k Pk,
left,
exact zero_le b,

cases Pk,
cases Pk with c hc,
cases c,
rw add_zero at hc,
right,
rw hc,
use 1,
refl,

left,
rw hc,
repeat { rw ← add_one_eq_succ },
rw add_comm c 1,
rw ← add_assoc k 1 c,
use c,
refl, 

right,
rw add_one_eq_succ,
exact (le_succ b k) Pk,



end