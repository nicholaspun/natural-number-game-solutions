lemma lt_aux_two (a b : mynat) : succ a ≤ b → a ≤ b ∧ ¬ (b ≤ a) :=
begin
intro h,
split,
cases h with c hc,
rw succ_eq_add_one at hc,
use (1 + c),
rw ← add_assoc,
rw hc,
refl,

intro h2,
have h3 := (le_trans (succ a) b a) h h2,
exact (not_succ_le_self a) h3,
end