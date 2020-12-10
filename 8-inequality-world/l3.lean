theorem le_succ (a b : mynat) : a ≤ b → a ≤ (succ b) :=
begin
intro h,
cases h with c hc,
use c + 1,
rw add_one_eq_succ,
rw add_succ,
rw hc,
refl,
end