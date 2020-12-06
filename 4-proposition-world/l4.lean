lemma maze (P Q R S T U: Prop)
(p : P)
(h : P → Q)
(i : Q → R)
(j : Q → T)
(k : S → T)
(l : T → U)
: U :=
begin
have q : Q := h p,
have t : T := j q,
have u : U := l t,
exact u,
end