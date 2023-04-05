{-# OPTIONS --allow-unsolved-meta #-}

open import Agda.Primitive

-- data Nat = Zero | Succ Nat
data ℕ : Set where  -- \bN ℕ
  zero : ℕ
  succ : ℕ → ℕ

double : ℕ → ℕ
double zero     = zero
double (succ n) = succ (succ (double n))

-- Set is the type of all (small) types.
-- Set itself is a type, but not a small type.
-- Set₁ is the type of all large types.
-- Set₂ is the type of all very large types.
-- zero : ℕ : Set : Set₁ : Set₂ : ... : Setω : Setω+1
id : {A : Set} → (A → A)
id x = x

ex : ℕ
ex = id {ℕ} zero

data Vector (A : Set) : ℕ → Set where
  []  : Vector A zero
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

two : ℕ
two = succ (succ zero)

ex₂ : Vector ℕ two
ex₂ = two ∷ (zero ∷ [])

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)

data Bool : Set where
  false true : Bool

-- "The boolean way"
is-even? : ℕ → Bool
is-even? zero            = true
is-even? (succ zero)     = false
is-even? (succ (succ n)) = is-even? n

is-eq? : ℕ → ℕ → Bool
is-eq? zero zero = true
is-eq? zero (succ b) = false
is-eq? (succ a) zero = false
is-eq? (succ a) (succ b) = is-eq? a b

is-eq?? : (ℕ → ℕ) → (ℕ → ℕ) → Bool
is-eq?? f g = {!!}

-- Haskell just has types depending on types,
-- like [Int] or IO Int; Agda also has types
-- depending on values; and in fact, types also
-- are just values (namely values of type Set
-- (or Set₁ (or Set₂ (...)))).
replicate : {X : Set} → (n : ℕ) → X → Vector X n
replicate zero     x = []
replicate (succ n) x = x ∷ replicate n x

-- "The witness way"
-- "Even n" is the type of witnesses that n is even.
-- For instance, Even (succ zero) should be an empty type.
-- But Even zero and Even (succ (succ zero)) should contain
-- something.
data Even : ℕ → Set where
  base : Even zero
  step : {n : ℕ} → Even n → Even (succ (succ n))

postulate
  whatever : Even (succ zero)

-- de Bruijn factor

four-is-even : Even (succ (succ (succ (succ zero))))
four-is-even = step (step base)

even-numbers-are-even : {n : ℕ} → Even n → Even n
even-numbers-are-even p = p

double-x-is-even : (n : ℕ) → Even (double n)
double-x-is-even zero     = base
double-x-is-even (succ n) = step (double-x-is-even n)
-- double (succ n) is succ (succ (double n))

thm : Even (succ (succ zero))
thm = double-x-is-even (succ zero)

-- For every type X, and for every values a and b of X,
-- there should be a type "a ≡ b" of witnesses that a equals b.
-- For instance, if a and b are NOT equal, then this type should
-- be empty.
data _≡_ {ℓ : Level} {X : Set ℓ} : X → X → Set where
  refl : {x : X} → x ≡ x
  -- bailout : {x y : X} → x ≡ y

lemma₀ : (zero + zero) ≡ zero
lemma₀ = refl

lemma₁ : (b : ℕ) → (zero + b) ≡ b
lemma₁ b = refl

cong
  : {ℓ : Level} {X Y : Set ℓ} {a b : X}
  → (f : X → Y) → a ≡ b → f a ≡ f b
cong f refl = refl

lemma₂ : (a : ℕ) → (a + zero) ≡ a
lemma₂ zero     = refl
lemma₂ (succ a) = cong succ (lemma₂ a)

foo : ℕ → (b : ℕ) → ℕ → is-even? b ≡ true → Vector ℕ b
foo a b c p = {!!}

foo' : ℕ → (b : ℕ) → ℕ → Even b → Vector ℕ b
foo' a b c p = {!!}

data List (X : Set) : Set where
  []  : List X
  _∷_ : X → List X → List X

length : {X : Set} → List X → ℕ
length []       = zero
length (x ∷ xs) = succ (length xs)

fib : ℕ → ℕ
fib zero            = zero
fib (succ zero)     = succ zero
fib (succ (succ n)) = fib n + fib (succ n)
-- This implemention requires O(fib(n)) time for computing fib n.

data IsFibonacci : ℕ → Set where
  bar : (a : ℕ) → IsFibonacci (fib a)

foo'' : {X : Set} → (xs : List X) → IsFibonacci (length xs) → {!!}
foo'' = {!!}

open import Data.Product

foo''' : {X : Set} → (xs : List X) → Σ[ a ∈ ℕ ] (length xs ≡ fib a) → {!!}
foo''' = {!!}
