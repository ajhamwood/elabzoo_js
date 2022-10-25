-- Dependent type with implicit arguments

let id : {A : U} -> A -> A = \x. x;
let const : {A B} -> A -> B -> A = \x y. x;

let group1 : {A B : U}(x y z : A) -> B -> B = \x y z b. b;
let group2 : {A B}(x y z : A) -> B -> B = \x y z b. b;

let the : (A : _) -> A -> A = \_ x. x;

let argTest1 = const {U}{U} U;
let argTest2 = const {B = U} U;
let id2 : {A} -> A -> A = \{A} x. x;

let namedLam  : {A B C} -> A -> B -> C -> A = \{B = B} a b c. a;
let namedLam2 : {A B C} -> A -> B -> C -> A = \{B = X} a b c. a;
let namedLam2 : {A B C} -> A -> B -> C -> A = \{C = X} a b c. a;

let insert : {A} -> A -> A = id;
let noinsert = \{A} x. the A x;
let insert2 = (\{A} x. the A x) U;

--------------------------------------------------------------------------------

-- bool
let Bool : U
    = (B : _) -> B -> B -> B;
let true : Bool
    = \B t f. t;
let false : Bool
    = \B t f. f;
let not : Bool -> Bool
    = \b B t f. b B f t;

-- lists
let List : U -> U
    = \A. (L : _) -> (A -> L -> L) -> L -> L;
let nil : {A} -> List A
    = \L cons nil. nil;
let cons : {A} -> A -> List A -> List A
    = \x xs L cons nil. cons x (xs L cons nil);
let map : {A B} -> (A -> B) -> List A -> List B
    = \{A}{B} f xs L c n. xs L (\a. c (f a)) n;
let list1 : List Bool
    = cons true (cons false (cons true nil));

-- dependent function composition
let comp : {A}{B : A -> U}{C : {a} -> B a -> U}
           (f : {a}(b : B a) -> C b)
           (g : (a : A) -> B a)
           (a : A)
           -> C (g a)
    = \f g a. f (g a);

let compExample = comp (cons true) (cons false) nil;

-- nat
let Nat : U
    = {N : U} -> (N -> N) -> N -> N;
let mul : Nat -> Nat -> Nat
    = \a b s z. a (b s) z;
let three : Nat
    = \s z. s (s (s z));
let nine = mul three three;

-- Leibniz equality
let Eq : {A} -> A -> A -> U
    = \{A} x y. (P : A -> U) -> P x -> P y;
let refl : {A}{x : A} -> Eq x x
    = \_ px. px;

let sym : {A x y} -> Eq {A} x y -> Eq y x
  = \{A}{x}{y} p. p (\y. Eq y x) refl;

the (Eq (mul three three) nine) refl
