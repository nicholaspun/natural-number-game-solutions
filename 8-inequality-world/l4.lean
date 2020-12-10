lemma zero_le (a : mynat) : 0 ≤ a :=
begin
use a,
rw zero_add,
refl,
end