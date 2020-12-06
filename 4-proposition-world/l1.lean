example (P Q : Prop) (p : P) (h : P → Q) : Q :=
begin
exact h p,
end