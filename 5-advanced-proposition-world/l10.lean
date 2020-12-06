lemma contrapositive2 (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) :=
begin
by_cases p : P; by_cases q : Q,
intros h p2,
exact q,
repeat { tauto! },
end