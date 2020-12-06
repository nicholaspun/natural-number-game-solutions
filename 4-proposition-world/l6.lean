example (P Q R : Prop) : (P → (Q → R)) → ((P → Q) → (P → R)) :=
begin
intros f g p,
apply f,
exact p,
exact g(p),
end