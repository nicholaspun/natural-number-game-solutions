lemma succ_le_succ (a b : mynat) (h : a ≤ b) : succ a ≤ succ b :=
begin
cases h with c hc,
rw hc,
use c,
rw succ_add,
refl,
end