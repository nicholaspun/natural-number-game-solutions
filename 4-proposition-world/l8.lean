lemma contrapositive (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) :=
begin
repeat {rw not_iff_imp_false},
intros f g p,
apply g,
exact f p,
end