example (P Q : Type) : (P → Q) → ((Q → empty) → (P → empty)) :=
begin
intros f g p,
exact g(f(p)),
end