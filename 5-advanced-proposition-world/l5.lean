lemma iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
intros g h,
cases h with hpr hrp,
cases g with gpq gqp,
split,
intro p,
exact hpr(gpq(p)),
intro r,
exact gqp(hrp(r)),
end