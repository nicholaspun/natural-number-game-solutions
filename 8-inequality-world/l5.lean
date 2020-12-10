theorem le_trans (a b c : mynat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
begin
cases hab with d hd, 
cases hbc with e he,
use (d + e),
rw he,
rw hd,
rw add_assoc,
refl,
end