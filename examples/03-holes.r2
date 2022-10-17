-- Dependent type with holes

let id : (A : _) -> A -> A
  = \A x. x;

let List : U -> U
  = \A. (L : _) -> (A -> L -> L) -> L -> L;

let nil : (A : _) -> List A
  = \A L cons nil. nil;

let cons : (A : _) -> A -> List A -> List A
  = \A x xs L cons nil. cons x (xs _ cons nil);

let Bool : U
  = (B : _) -> B -> B -> B;

let true : Bool
  = \B t f. t;

let false : Bool
  = \B t f. f;

let not : Bool -> Bool
  = \b B t f. b B f t;

let list1 : List Bool
  = cons _ (id _ true) (nil _);

let Eq : (A : _) -> A -> A -> U
  = \A x y. (P : A -> U) -> P x -> P y;

let refl : (A : _)(x : A) -> Eq A x x
  = \A x P px. px;

let list1 : List Bool
  = cons _ true (cons _ false (nil _));

let Nat   : U = (N : U) -> (N -> N) -> N -> N;
let three : Nat = \N s z. s (s (s z));
let add   : Nat -> Nat -> Nat = \a b N s z. a N s (b N s z);
let mul   : Nat -> Nat -> Nat = \a b N s z. a N (b N s) z;

let nine : Nat = mul three three;

let eqTest : Eq _ nine nine = refl _ _;

U