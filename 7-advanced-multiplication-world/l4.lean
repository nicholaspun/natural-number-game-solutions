/-
induction a with k Pk,
exfalso,
apply ha,
refl,

cases k,
repeat { rw ← one_eq_succ_zero },
repeat { rw one_mul },
intro h, exact h,

intro h,
have h2 := Pk (succ_ne_zero k),
rw succ_mul at h,

Don't think this works, fun attempt tho
-/

induction c with k Pk generalizing b,
rw mul_zero,
rw mul_eq_zero_iff,
intro h,
cases h,
exfalso,
exact ha h,

exact h,

intro h,
cases b,
rw mul_zero at h,
symmetry at h,
have h2 := eq_zero_or_eq_zero_of_mul_eq_zero a (succ k),
have h3 := h2 h,
cases h3,
exfalso,
exact ha h3,

symmetry at h3,
exact h3,

repeat { rw mul_succ at h },
rw add_right_cancel_iff at h,
have h4 := Pk b,
have h5 := h4 h,
rw ← succ_eq_succ_iff at h5,
exact h5,