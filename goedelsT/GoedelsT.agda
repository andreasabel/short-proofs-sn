-- Following Joachimski/Matthes, AML 2003, Short proofs of normalization...

{-# OPTIONS --rewriting #-}

open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)

{-# BUILTIN REWRITE _≡_ #-}

data Ty : Set where
  Nat : Ty
  _⇒_ : (A B : Ty) → Ty

infixr 6 _⇒_ _∷_ _++_
infixl 5 _∙_ _◇_

data Cxt : Set where
  ε : Cxt
  _∙_ : (Γ : Cxt) (A : Ty) → Cxt

data Var : (Γ : Cxt) (A : Ty) → Set where
  vz : ∀{Γ A} → Var (Γ ∙ A) A
  vs : ∀{Γ A B} (x : Var Γ A) → Var (Γ ∙ B) A

-- Terms in spine notation

-- data Flag : Set where
--   app : Flag  -- only app eliminations
--   rec : Flag  -- both eliminations

mutual

  -- data Tm (Γ : Cxt) (C : Ty) : Set where
  --   _∙_ : ∀{A} (h : Head Γ A) (es : Elims Γ A C) → Tm Γ C

  record Tm (Γ : Cxt) (C : Ty) : Set where
    no-eta-equality; inductive; constructor _∙_; field
      {A} : Ty
      h   : Head Γ A
      es  : Elims Γ A C

  data Head (Γ : Cxt) : (C : Ty) → Set where
    zero : Head Γ Nat
    suc  : (t : Tm Γ Nat) → Head Γ Nat
    abs  : ∀{A B} (t : Tm (Γ ∙ A) B) → Head Γ (A ⇒ B)
    var  : ∀{A} (x : Var Γ A) → Head Γ A

  data Elim (Γ : Cxt) : (A C : Ty) → Set where
    app : ∀{A B} (u : Tm Γ A) → Elim Γ (A ⇒ B) B
    rec : ∀{C} (u : Tm Γ C) (v : Tm Γ (Nat ⇒ C ⇒ C)) → Elim Γ Nat C

  data Elims (Γ : Cxt) (A : Ty) : (C : Ty) → Set where
    [] : Elims Γ A A
    _∷_ : ∀{B C} (e : Elim Γ A B) (es : Elims Γ B C) → Elims Γ A C

pattern var! x = var x ∙ []
pattern zero!  = zero  ∙ []
pattern suc! t = suc t ∙ []
pattern abs! t = abs t ∙ []

-- Numerals

num : ∀{Γ} (n : ℕ) → Tm Γ Nat
num 0       = zero!
num (suc n) = suc! (num n)

data Num {Γ : Cxt} : Tm Γ Nat → Set where
  zero : Num zero!
  suc  : ∀{t} (n : Num t) → Num (suc! t)

-- Elimination concatenation

_++_ : ∀{Γ A B C} (es : Elims Γ A B) (es' : Elims Γ B C) → Elims Γ A C
[]       ++ es' = es'
(e ∷ es) ++ es' = e ∷ (es ++ es')

++-assoc : ∀{Γ A B C D} (es₁ : Elims Γ A B) {es₂ : Elims Γ B C} {es₃ : Elims Γ C D} →
  (es₁ ++ es₂) ++ es₃ ≡ es₁ ++ (es₂ ++ es₃)
++-assoc [] = refl
++-assoc (e ∷ es) = cong (e ∷_) (++-assoc es)

++-[] : ∀{Γ A B} (es : Elims Γ A B) → es ++ [] ≡ es
++-[] [] = refl
++-[] (e ∷ es) = cong (e ∷_) (++-[] es)

{-# REWRITE ++-assoc ++-[] #-}

_◇_ : ∀{Γ A C} (t : Tm Γ A) (es : Elims Γ A C) → Tm Γ C
_◇_ (h ∙ es) es' = h ∙ es ++ es'

◇-[] : ∀{Γ A} (t : Tm Γ A) → t ◇ [] ≡ t
◇-[] (h ∙ es) = refl

◇-++ : ∀ {Γ A B C} (t : Tm Γ A) {es : Elims Γ A B} {es' : Elims Γ B C} → t ◇ es ◇ es' ≡ t ◇ (es ++ es')
◇-++ (h ∙ es) = refl

{-# REWRITE ◇-[] ◇-++ #-}


-- Weakening

infix 2 _≤_

data _≤_ : (Γ Δ : Cxt) → Set where
  id≤ : ∀{Γ} → Γ ≤ Γ
  weak : ∀{A Γ Δ} (τ : Γ ≤ Δ) → Γ ∙ A ≤ Δ
  lift : ∀{A Γ Δ} (τ : Γ ≤ Δ) → Γ ∙ A ≤ Δ ∙ A

wkVar : ∀ {C Γ Δ} (τ : Γ ≤ Δ) (x : Var Δ C) → Var Γ C
wkVar id≤      x      = x
wkVar (weak τ) x      = vs (wkVar τ x)
wkVar (lift τ) vz     = vz
wkVar (lift τ) (vs x) = vs (wkVar τ x)

wkWk : ∀{Γ Γ' Δ} (τ : Γ' ≤ Γ) (ρ : Γ ≤ Δ) → Γ' ≤ Δ
wkWk id≤ ρ = ρ
wkWk (weak τ) ρ = weak (wkWk τ ρ)
wkWk (lift τ) id≤ = lift τ
wkWk (lift τ) (weak ρ) = weak (wkWk τ ρ)
wkWk (lift τ) (lift ρ) = lift (wkWk τ ρ)

mutual
  wkTm : ∀{Γ Δ C} (τ : Γ ≤ Δ) (t : Tm Δ C) → Tm Γ C
  wkTm τ (h ∙ es) = wkHead τ h ∙ wkElims τ es

  wkHead : ∀{Γ Δ C} (τ : Γ ≤ Δ) (h : Head Δ C) → Head Γ C
  wkHead τ zero    = zero
  wkHead τ (suc t) = suc (wkTm τ t)
  wkHead τ (abs t) = abs (wkTm (lift τ) t)
  wkHead τ (var x) = var (wkVar τ x)

  wkElim : ∀{Γ Δ A C} (τ : Γ ≤ Δ) (e : Elim Δ A C) → Elim Γ A C
  wkElim τ (app u)   = app (wkTm τ u)
  wkElim τ (rec u v) = rec (wkTm τ u) (wkTm τ v)

  wkElims : ∀{Γ Δ A C} (τ : Γ ≤ Δ) (es : Elims Δ A C) → Elims Γ A C
  wkElims τ []       = []
  wkElims τ (e ∷ es) = wkElim τ e ∷ wkElims τ es

-- Substitution

data Sub (Γ : Cxt) : (Δ : Cxt) → Set where
  wk : ∀{Δ} (τ : Γ ≤ Δ) → Sub Γ Δ
  _∙_ : ∀{Δ A} (σ : Sub Γ Δ) (u : Tm Γ A) → Sub Γ (Δ ∙ A)

wkSub : ∀{Γ Γ' Δ} (τ : Γ' ≤ Γ) (σ : Sub Γ Δ) → Sub Γ' Δ
wkSub τ (wk ρ) = wk (wkWk τ ρ)
wkSub τ (σ ∙ u) = wkSub τ σ ∙ wkTm τ u

sgSub : ∀{Γ A} (u : Tm Γ A) → Sub Γ (Γ ∙ A)
sgSub u = wk id≤ ∙ u

liftSub : ∀{A Γ Δ} (σ : Sub Γ Δ) → Sub (Γ ∙ A) (Δ ∙ A)
liftSub σ = wkSub (weak id≤) σ ∙ var! vz

subVar : ∀ {C Γ Δ} (σ : Sub Γ Δ) (x : Var Δ C) → Tm Γ C
subVar (wk τ) x       = var (wkVar τ x) ∙ []
subVar (σ ∙ u) vz     = u
subVar (σ ∙ u) (vs x) = subVar σ x

mutual
  subTm : ∀{Γ Δ C} (σ : Sub Γ Δ) (t : Tm Δ C) → Tm Γ C
  subTm σ (h ∙ es) = subHead σ h ◇ subElims σ es

  subHead : ∀{Γ Δ A} (σ : Sub Γ Δ) (h : Head Δ A) → Tm Γ A
  subHead σ zero    = zero!
  subHead σ (suc t) = suc! (subTm σ t)
  subHead σ (abs t) = abs! (subTm (liftSub σ) t)
  subHead σ (var x) = subVar σ x

  -- subHead : ∀{Γ Δ A C} (σ : Sub Γ Δ) (h : Head Δ A) (es : Elims Γ A C) → Tm Γ C
  -- subHead σ zero    es = zero ∙ es
  -- subHead σ (suc t) es = suc (subTm σ t) ∙ es
  -- subHead σ (abs t) es = abs (subTm (liftSub σ) t) ∙ es
  -- subHead σ (var x) es = subVar σ x ◇ es

  subElim : ∀{Γ Δ A C} (σ : Sub Γ Δ) (e : Elim Δ A C) → Elim Γ A C
  subElim σ (app u)   = app (subTm σ u)
  subElim σ (rec u v) = rec (subTm σ u) (subTm σ v)

  subElims : ∀{Γ Δ A C} (σ : Sub Γ Δ) (es : Elims Δ A C) → Elims Γ A C
  subElims σ []       = []
  subElims σ (e ∷ es) = subElim σ e ∷ subElims σ es

_[_] : ∀{Γ A B} (t : Tm (Γ ∙ A) B) (u : Tm Γ A) → Tm Γ B
t [ u ] = subTm (sgSub u) t

subElims-++ : ∀{Γ Δ} {σ : Sub Γ Δ} {A B C} (es : Elims Δ A B) {es' : Elims Δ B C}
  → subElims σ (es ++ es') ≡ subElims σ es ++ subElims σ es'
subElims-++ [] = refl
subElims-++ (e ∷ es) = cong (_ ∷_) (subElims-++ es)

{-# REWRITE subElims-++ #-}

sub-◇ : ∀{Γ Δ} {σ : Sub Γ Δ} {A B} (t : Tm Δ A) {es : Elims Δ A B} →
  subTm σ (t ◇ es) ≡ subTm σ t ◇ subElims σ es
sub-◇ (h ∙ es) = refl

{-# REWRITE sub-◇ #-}

subNum : ∀ {Δ} {t : Tm Δ Nat} {Γ} (σ : Sub Γ Δ) (n : Num t) → Num (subTm σ t)
subNum σ zero    = zero
subNum σ (suc n) = suc (subNum σ n)

sub-num : ∀ {Γ Δ} {σ : Sub Γ Δ} (n : ℕ) → subTm σ (num n) ≡ num n
sub-num zero = refl
sub-num (suc n) = cong suc! (sub-num n)

{-# REWRITE sub-num #-}

-- The Ω set

mutual

  data Oks {Γ : Cxt} : {A C : Ty} (es : Elims Γ A C) → Set where
    []  : ∀{A} → Oks {Γ} {A} {A} []
    _∷_ : ∀{A B C} {u : Tm Γ A} (o : Ok u) {es : Elims Γ B C} (os : Oks es) → Oks (app u ∷ es)

  data Ok {Γ : Cxt} : {C : Ty} (t : Tm Γ C) → Set where
    zero   : Ok zero!
    suc    : ∀{t} (o : Ok t) → Ok (suc! t)
    abs    : ∀{A B} {t : Tm (Γ ∙ A) B} (o : Ok t) → Ok (abs! t)
    ne     : ∀{A C} (x : Var Γ A) {es : Elims Γ A C} (os : Oks es) → Ok (var x ∙ es)

    zerec  : ∀{A C} {u : Tm Γ A} {v} {es : Elims Γ A C} (o : Ok (u ◇ es)) → Ok (zero ∙ rec u v ∷ es)
    surec  : ∀{A C} {t : Tm Γ Nat} (n : Num t) {u : Tm Γ A} {v} {es : Elims Γ A C}
             (o : Ok (v ◇ app t ∷ app (t ◇ rec u v ∷ []) ∷ es)) → Ok (suc t ∙ rec u v ∷ es)

    beta   : ∀{A B C} {t : Tm (Γ ∙ A) B} {u} {es : Elims Γ B C}
             (o : Ok (t [ u ] ◇ es)) → Ok (abs t ∙ app u ∷ es)

    omega  : ∀{A C}{t : Tm Γ Nat} {u : Tm Γ A} {v} {es : Elims Γ A C}
             (o : Ok t) (f : ∀ n → Ok (num n ◇ rec u v ∷ es)) → Ok (t ◇ rec u v ∷ es)

  --   omega  : ∀{A C}{t : Tm Γ Nat} {u : Tm Γ A} {v} {es : Elims Γ A C}
  --            (o : Ok t) (f : ∀ n → OkRec u v es n) → Ok (t ◇ rec u v ∷ es)

  -- data OkRec {Γ : Cxt} {A C : Ty} (u : Tm Γ A) (v : Tm Γ (Nat ⇒ A ⇒ A)) (es : Elims Γ A C) : (n : ℕ) → Set where
  --   zerec : (o : Ok (u ◇ es)) → OkRec u v es zero
  --   surec : ∀{n} (let t = num n) (o : Ok (v ◇ app t ∷ app (t ◇ rec u v ∷ []) ∷ es)) → OkRec u v es (suc n)

oks-snoc : ∀ {Γ A B C} {es : Elims Γ A (B ⇒ C)} {u : Tm Γ B} →
           (os : Oks es) (o : Ok u) → Oks (es ++ app u ∷ [])
oks-snoc []       ou = ou ∷ []
oks-snoc (o ∷ os) ou = o ∷ oks-snoc os ou

data Res A {Γ} : ∀{B} (t : Tm Γ B) → Set where
  rtm  : {t : Tm Γ A} (o : Ok t) → Res A t
  rvar : ∀{B} (x : Var Γ B) → Res A (var! x)

data OkSub A {Γ} : ∀{Δ} (σ : Sub Γ Δ) → Set where
  wk : ∀{Δ} (τ : Γ ≤ Δ) → OkSub A (wk τ)
  _∙_ : ∀{Δ B} {σ : Sub Γ Δ} (oσ : OkSub A σ) {t : Tm Γ B} (r : Res A t) → OkSub A (σ ∙ t)

wkOk : ∀ {B Γ} {t : Tm Γ B} {Γ'} (τ : Γ' ≤ Γ) (o : Ok t) → Ok (wkTm τ t)
wkOk = {!!}

wkRes : ∀ {B Γ} {t : Tm Γ B} {A Γ'} (τ : Γ' ≤ Γ) (r : Res A t) → Res A (wkTm τ t)
wkRes τ (rtm o)  = rtm (wkOk τ o)
wkRes τ (rvar x) = rvar (wkVar τ x)

wkOkSub : ∀ {A Γ Γ' Δ} {σ : Sub Γ Δ} (τ : Γ' ≤ Γ) (oσ : OkSub A σ) → OkSub A (wkSub τ σ)
wkOkSub τ (wk τ₁) = wk (wkWk τ τ₁)
wkOkSub τ (oσ ∙ r) = wkOkSub τ oσ ∙ wkRes τ r

sgOk : ∀ {A Γ} {u : Tm Γ A} → Ok u → OkSub A (wk id≤ ∙ u)
sgOk o = wk id≤ ∙ rtm o

liftOk : ∀ {B A Γ Δ} {σ : Sub Γ Δ} (oσ : OkSub A σ) → OkSub A (liftSub {B} σ)
liftOk oσ = wkOkSub (weak id≤) oσ ∙ rvar vz

-- Show that Ω is closed under application and substitution

mutual

  apply : ∀ A {Γ B} {t : Tm Γ (A ⇒ B)} {u : Tm Γ A} (ot : Ok t) (ou : Ok u) → Ok (t ◇ app u ∷ [])
  apply A (abs ot) ou = beta (sub A ot ou)
  apply A (ne x os) ou = ne x (oks-snoc os ou)
  apply A (zerec ot) ou = zerec (apply A ot ou)
  apply A (surec n ot) ou = surec n (apply A ot ou)
  apply A (beta ot) ou = beta (apply A ot ou)
  apply A (omega ot f) ou = omega ot λ n → apply A (f n) ou

  applys : ∀ {Γ A B} {t : Tm Γ A} (ot : Ok t) {es : Elims Γ A B} (os : Oks es) → Ok (t ◇ es)
  applys ot []       = ot
  applys ot (o ∷ os) = applys (apply _ ot o) os

  subs : ∀ A {Γ Δ} {σ : Sub Γ Δ} (oσ : OkSub A σ) {C} {t : Tm Δ C} (o : Ok t) → Ok (subTm σ t)
  subs A oσ zero = zero
  subs A oσ (suc o) = suc (subs A oσ o)
  subs A oσ (abs o) = abs (subs A (liftOk oσ) o)
  subs A oσ (ne x os) = {!applys ? !}
  subs A oσ (zerec o) = zerec (subs A oσ o)
  subs A oσ (surec n o) = surec (subNum _ n) (subs A oσ o)
  subs A oσ (beta o) = beta {!(subs A oσ o)!}  -- need substitution composition
  subs A oσ (omega o f) = omega (subs A oσ o) (λ n → {!subs A oσ (f n)!})

  sub : ∀ A {Γ B} {t : Tm (Γ ∙ A) B} {u : Tm Γ A} (ot : Ok t) (ou : Ok u) → Ok (t [ u ])
  sub A ot ou = subs A (sgOk ou) ot

-- Show that every term is in Ω

-- Extract a normal form from Ω

-- -}
-- -}
