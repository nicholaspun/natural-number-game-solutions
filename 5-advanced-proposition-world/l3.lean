lemma and_symm (P Q : Prop) : P ∧ Q → Q ∧ P :=
begin
intro h,
cases h with p q,
split,
exact q,
exact p,
end