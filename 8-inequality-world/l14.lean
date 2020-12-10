theorem add_le_add_left {a b : mynat} (h : a ≤ b) (t : mynat) :
  t + a ≤ t + b :=
begin
cases h with c hc,
rw hc,
use c,
rw add_assoc,
refl,
end