lemma zero_pow_succ (m : mynat) : (0 : mynat) ^ (succ m) = 0 :=
begin
rw pow_succ,
exact mul_zero (0 ^ m),
end