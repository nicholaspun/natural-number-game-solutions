lemma eq_zero_of_add_right_eq_self {a b : mynat} : a + b = a → b = 0 :=
begin
intro s,
rw ← add_zero a at s,
rw add_assoc a 0 b at s,
rw zero_add at s,
have f := add_left_cancel a b 0,
exact f(s),
end