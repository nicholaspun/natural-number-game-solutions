lemma or_symm (P Q : Prop) : P ∨ Q → Q ∨ P :=
begin
intro h,
cases h with p q,
right,
exact p,
left,
exact q,
end