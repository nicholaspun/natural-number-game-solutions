lemma example2 (x y : mynat) (h : y = x + 7) : 2 * y = 2 * (x + 7) :=
begin
rw ← h,
refl,
end