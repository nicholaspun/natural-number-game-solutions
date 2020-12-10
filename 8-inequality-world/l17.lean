lemma lt_iff_succ_le (a b : mynat) : a < b ↔ succ a ≤ b :=
begin
split,
exact lt_aux_one a b,
exact lt_aux_two a b,
end