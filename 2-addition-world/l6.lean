lemma add_right_comm (a b c : mynat) : a + b + c = a + c + b :=
begin
rw add_assoc a b c, rw add_comm b c, rw add_assoc a c b, refl,
end