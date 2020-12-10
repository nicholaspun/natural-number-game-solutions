theorem add_le_add_right {a b : mynat} : a ≤ b → ∀ t, (a + t) ≤ (b + t) :=
begin
intros h t,
cases h with c hc,
rw hc,
use c,
rw add_right_comm,
refl,
end