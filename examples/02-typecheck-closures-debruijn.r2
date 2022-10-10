-- Dependent types

let Nat : U = (N : U) -> (N -> N) -> N -> N;
let three : Nat = \N s z. s (s (s z));
let add : Nat -> Nat -> Nat = \a b N s z. a N s (b N s z);
let mul : Nat -> Nat -> Nat = \a b N s z. a N (b N s) z;
let result : Nat = mul three three;
result