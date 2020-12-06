example (P Q F : Type) : (P → Q) → ((Q → F) → (P → F)) :=
begin
intros f g p,
have q : Q := f p,
exact g q,
end