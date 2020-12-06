lemma imp_self (P : Prop) : P → P :=
begin
intro p, exact p,
end