example (P Q : Prop) : P → (Q → P) :=
begin
intros p q,
exact p,
end