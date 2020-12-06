lemma contra (P Q : Prop) : (P ∧ ¬ P) → Q :=
begin
intro h,
cases h with p notp,
rw not_iff_imp_false at notp,
exfalso,
apply notp,
exact p,
end