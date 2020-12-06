lemma and_or_distrib_left (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
begin
split,
intro paqor,
cases paqor with p qor,
cases qor with q r,
left,
split,
exact p,
exact q,
right,
split,
exact p,
exact r,

intro long,
split,
cases long with paq par,
exact paq.left,
exact par.left,
cases long with paq par,
left,
exact paq.right,
right, 
exact par.right,

end