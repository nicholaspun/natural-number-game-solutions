lemma le_refl (x : mynat) : x ≤ x :=
begin
use 0,
symmetry,
exact add_zero x,
end