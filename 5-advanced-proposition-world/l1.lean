example (P Q : Prop) (p : P) (q : Q) : P ∧ Q :=
begin
split,
exact p,
exact q,
end