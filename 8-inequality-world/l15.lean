lemma lt_aux_one (a b : mynat) : a ≤ b ∧ ¬ (b ≤ a) → succ a ≤ b :=
begin
intro h,
cases h,
cases h_left,
cases h_left_w,

rw add_zero at h_left_h,
rw h_left_h at h_right,
exfalso,
exact h_right (le_refl a),

rw add_succ at h_left_h,
rw h_left_h,
use h_left_w,
rw succ_add,
refl,
end