-- Examples for elaborating first-class polymorphism
-- Preliminary defs
------------------------------------------------------------

let List   : U -> U                       = \A. (L : U) -> L -> (A -> L -> L) -> L;
let nil    : {A} -> List A                = \L n c. n;
let cons   : {A} -> A -> List A -> List A = \a as L n c. c a (as L n c);
let Bool   : U                            = (B : U) -> B -> B -> B;
let true   : Bool                         = \b t f. t;
let Pair   : U -> U -> U                  = \A B. (P : U) -> (A -> B -> P) -> P;
let pair   : {A B} -> A -> B -> Pair A B  = \a b P p. p a b;
let Nat    : U                            = (N : U) -> (N -> N) -> N -> N;
let zero   : Nat                          = \N s z. z;
let suc    : Nat -> Nat                   = \n N s z. s (n N s z);
let append : {A} -> List A -> List A -> List A = \xs ys L n c. xs L (ys L n c) c;
let length : {A} -> List A -> Nat         = \as N s z. as N z (\x. s);
let map    : {A B} -> (A -> B) -> List A -> List B = \f as L n c. as L n (\a. c (f a));
let ST     : U -> U -> U                  = \S A. S -> A;
let runST  : {A} -> ({S} -> ST S A) -> A  = \f. f {Bool} true;
let argST  : {S} -> ST S Nat              = \_. zero;
let Id     : U -> U                       = \A. (I : U) -> (A -> I) -> I;
let mkId   : {A} -> A -> Id A             = \a I f. f a;
let unId   : {A} -> Id A -> A             = \i. i _ (\x. x);
let the    : (A : U) -> A -> A            = \A a. a;
let const  : {A B} -> A -> B -> A         = \x y. x;
let IdTy   : U                            = {A} -> A -> A;
let single : {A} -> A -> List A           = \a. cons a nil;
let id     : {A} -> A -> A                = \a. a;
let ids    : List IdTy                    = nil;
let oneId  : Id IdTy                      = mkId id;
let app    : {A B} -> (A -> B) -> A -> B  = id;
let revapp : {A B} -> A -> (A -> B) -> B  = \x f. f x;
let poly   : IdTy -> Pair Nat Bool        = \f. pair (f zero) (f true);
let choose : {A} -> A -> A -> A           = const;
let auto   : IdTy -> IdTy                 = id;
let auto2  : {B} -> IdTy -> B -> B        = \_ b. b;


-- A: polymorphic instantiation
--------------------------------------------------------------------------------

let A1 = \x y. y;
let A2 : IdTy -> IdTy = choose id;
let A3 = choose nil ids;
let A4 : IdTy -> IdTy = \(x : IdTy). x x;
let A5 = id auto;
let A6 : {B} -> IdTy -> B -> B = id auto2;
let A7 = choose id auto;

-- let A8 = choose id auto2 in -- FAILS the reason is simply that the types are
--   definitionally different, the orders of implicit args do not match. We
--   do *not* reorder or float out implicit args, intentionally, since we
--   support mixing implicit and explicit args in arbitrary order.

let A9 : ({A} -> (A -> A) -> List A -> A) -> IdTy
    = \f. f (choose id) ids;
let A10 = poly id;
let A11 = poly (\x. x);
let A12 = id poly (\x. x);

-- B: inference of polymorphic arguments
--------------------------------------------------------------------------------

-- FAILS
-- let B1 = \f. pair (f zero) (f true);

-- FAILS
-- let B2 = \x. poly (unId x);

-- C: functions on polymorphic lists
--------------------------------------------------------------------------------

let C1 = length ids;
let C2 = id ids;
let C3 : IdTy = unId oneId;
let C4 : List IdTy = single id;
let C5 = cons id ids;
let C6 = cons (\x. x) ids;
let C7 = append (single suc) (single id);
let C8 : _ -> IdTy = \(g : {A} -> List A -> List A -> A). g (single id) ids;
let C9 = map poly (single id);
let C10 = map unId (single oneId);

-- D: application functions
--------------------------------------------------------------------------------

let D1 = app poly id;
let D2 = revapp id poly;
let D3 = runST argST;
let D4 = app runST argST;
let D5 = revapp argST runST;

-- -- E: η-expansion
-- --------------------------------------------------------------------------------

-- let E1 =   -- FAILS
--   \(h : Nat -> {A} -> A -> A)(k : {A} -> A -> List A -> A)(lst : List ({A} -> Nat -> A -> A)).
--   k h lst;
--   -- fails again because of mismatched implicit/explicit arguments

let E2 =
  \(h : Nat -> {A} -> A -> A)(k : {A} -> A -> List A -> A)(lst : List ({A} -> Nat -> A -> A)).
  k (\x. h x) lst;
let E3 =
  \(r : ({A} -> A -> {B} -> B -> B) -> Nat). r (\x y. y);

U