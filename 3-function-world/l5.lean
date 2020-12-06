example (P Q : Type) : P → (Q → P) :=
begin
intro p,
intro q,
exact p,
end