example (P Q R : Type) : (P → (Q → R)) → ((P → Q) → (P → R)) :=
begin
intros f g p,
have h : Q -> R := f p,
apply h,
exact g p,
end