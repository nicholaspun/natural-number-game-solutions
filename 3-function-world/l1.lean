example (P Q : Type) (p : P) (h : P → Q) : Q :=
begin
exact h(p),
end