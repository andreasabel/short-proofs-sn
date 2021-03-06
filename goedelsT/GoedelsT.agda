-- Following Joachimski/Matthes, AML 2003, Short proofs of normalization...

{-# OPTIONS --rewriting #-}

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (∃; _,_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂)

{-# BUILTIN REWRITE _≡_ #-}

Absurd : ∀ ℓ → Set _
Absurd ℓ = ∀{X : Set ℓ} → X

-- Absurd = ∀{ℓ}{X : Set ℓ} → X  -- Setω

data Ty : Set where
  Nat : Ty
  _⇒_ : (A B : Ty) → Ty

infixr 6 _⇒_ _∷_ _++_ _++s_ _++sn_
infixl 5 _∙_ _◇_ _∙′_ _◇s_

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

numNum : ∀ n {Γ} → Num {Γ} (num n)
numNum zero    = zero
numNum (suc n) = suc (numNum n)

numNotVar : ∀ (n : ℕ) {Γ A} {x : Var Γ A} {es : Elims Γ A Nat} (eq : num n ≡ var x ∙ es) → ∀{ℓ} → Absurd ℓ
numNotVar zero ()
numNotVar (suc n) ()

numNotElim : ∀ (n : ℕ) {Γ A B} {h : Head Γ A} {e : Elim Γ A B} {es : Elims Γ B Nat} (eq : num n ≡ h ∙ e ∷ es) → ∀{ℓ} → Absurd ℓ
numNotElim zero ()
numNotElim (suc n) ()

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

-- Appending eliminations

-- data Append {Γ} : ∀{A} (t : Tm Γ A) {B} (es : Elims Γ A B) (t' : Tm Γ B) → Set where
--   append : ∀{A B C} {h : Head Γ A} {es : Elims Γ A B}
--            → Append (h ∙ es) [] (h ∙ es)
--   append : ∀{A B C} {h : Head Γ A} {es : Elims Γ A B} {es' : Elims Γ B C}
--            → Append (h ∙ es ++ e ∷ []) es'
--            → Append (h ∙ es) (e ∷ es') (h ∙ es ++ es')

data Append {Γ} : ∀{A} (t : Tm Γ A) {B} (es : Elims Γ A B) (t' : Tm Γ B) → Set where
  append : ∀{A B C} {h : Head Γ A} {es : Elims Γ A B} {es' : Elims Γ B C}
           → Append (h ∙ es) es' (h ∙ es ++ es')

headIsNotAppend : ∀{Γ A B C} (t : Tm Γ A) {e : Elim Γ A B} {es : Elims Γ B C} {h : Head Γ C}
  (apd : Append t (e ∷ es) (h ∙ [])) → ∀{ℓ} → Absurd ℓ
headIsNotAppend (h ∙ []) ()
headIsNotAppend (h ∙ e ∷ es) ()


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

wkElims-++ : ∀{Γ Δ} {σ : Γ ≤ Δ} {A B C} (es : Elims Δ A B) {es' : Elims Δ B C}
  → wkElims σ (es ++ es') ≡ wkElims σ es ++ wkElims σ es'
wkElims-++ [] = refl
wkElims-++ (e ∷ es) = cong (_ ∷_) (wkElims-++ es)

{-# REWRITE wkElims-++ #-}

wk-◇ : ∀{Γ Δ} {σ : Γ ≤ Δ} {A B} (t : Tm Δ A) {es : Elims Δ A B} →
  wkTm σ (t ◇ es) ≡ wkTm σ t ◇ wkElims σ es
wk-◇ (h ∙ es) = refl

{-# REWRITE wk-◇ #-}

wkNum : ∀ {Δ} {t : Tm Δ Nat} {Γ} (σ : Γ ≤ Δ) (n : Num t) → Num (wkTm σ t)
wkNum σ zero    = zero
wkNum σ (suc n) = suc (wkNum σ n)

wk-num : ∀ {Γ Δ} {σ : Γ ≤ Δ} (n : ℕ) → wkTm σ (num n) ≡ num n
wk-num zero = refl
wk-num (suc n) = cong suc! (wk-num n)

{-# REWRITE wk-num #-}

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
subVar (wk τ) x       = var! (wkVar τ x)
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
sub-num zero    = refl
sub-num (suc n) = cong suc! (sub-num n)

{-# REWRITE sub-num #-}

-- Goal: Ok ((subTm (liftSub .σ) .t [ subTm .σ .u ]) ◇ subElims .σ .es)
-- Have: Ok (subTm .σ (subTm (sgSub .u) .t) ◇ subElims .σ .es)

-- Relational definition of substitution

-- data WkVar : ∀ {Γ Δ} (σ : Γ ≤ Δ) {C} (x : Var Δ C) (x' : Var Γ C) → Set where

data SubstVar : ∀ {Γ Δ} (σ : Sub Γ Δ) {C} (x : Var Δ C) (t' : Tm Γ C) → Set where
  suwk : ∀{Γ Δ C} {τ : Γ ≤ Δ} {x : Var Δ C} {x'} (wx : wkVar τ x ≡ x') → SubstVar (wk τ) x (var! x')
  suvz : ∀{Γ Δ C} {σ : Sub Γ Δ} {u t' : Tm Γ C} (eq : u ≡ t') → SubstVar (σ ∙ u) vz t'
  suvs : ∀{Γ Δ A C} {σ : Sub Γ Δ} {u : Tm Γ A} {x : Var Δ C} {t'} (sx : SubstVar σ x t') → SubstVar (σ ∙ u) (vs x) t'

pattern suvz! = suvz refl

mutual
  data SubstTm    {Γ Δ} (σ : Sub Γ Δ) : ∀{C} (t : Tm   Δ C) (t' : Tm Γ C) → Set where
    _∙_∣_ : ∀{A C} {h : Head Δ A} {t'} (sh : SubstHead σ h t')
         {es : Elims Δ A C} {es'} (ses : SubstElims σ es es') {t'' : Tm Γ C}
         (apd : Append t' es' t'') → SubstTm σ (h ∙ es) t'' -- (t' ◇ es')

  data SubstHead  {Γ Δ} (σ : Sub Γ Δ) : ∀{C} (h : Head Δ C) (t' : Tm Γ C) → Set where
    zero : SubstHead σ zero zero!
    suc  : ∀ {t t'} (st : SubstTm σ t t') → SubstHead σ (suc t) (suc! t')
    abs  : ∀{A B} {t : Tm (Δ ∙ A) B} {t'} (st : SubstTm (liftSub σ) t t') → SubstHead σ (abs t) (abs! t')
    var  : ∀{C} {x : Var Δ C} {t'} (sx : SubstVar σ x t') → SubstHead σ (var x) t'

  data SubstElim  {Γ Δ} (σ : Sub Γ Δ) : ∀{A C} (e : Elim Δ A C) (e' : Elim Γ A C) → Set where
    app : ∀{A B} {u : Tm Δ A} {u'} (su : SubstTm σ u u') → SubstElim σ {A ⇒ B} (app u) (app u')
    rec : ∀{C} {u : Tm Δ C} {u'} (su : SubstTm σ u u')
          {v : Tm Δ (Nat ⇒ C ⇒ C)} {v'} (sv : SubstTm σ v v') → SubstElim σ (rec u v) (rec u' v')

  data SubstElims {Γ Δ} (σ : Sub Γ Δ) {A} : ∀{C} (es : Elims Δ A C) (es' : Elims Γ A C) → Set where
    [] : SubstElims σ [] []
    _∷_ : ∀{B C}
          {e : Elim Δ A B} {e'} (se : SubstElim σ e e')
          {es : Elims Δ B C} {es'} (ses : SubstElims σ es es') → SubstElims σ (e ∷ es) (e' ∷ es')


pattern _∙′_ sh ses = sh ∙ ses ∣ append

_++s_ : ∀ {Γ Δ} {σ : Sub Γ Δ} {A B C} {es₁ : Elims Δ A B} {es₁' : Elims Γ A B}
          {es₂ : Elims Δ B C} {es₂' : Elims Γ B C} →
        (ses₁ : SubstElims σ es₁ es₁')
        (ses₂ : SubstElims σ es₂ es₂') → SubstElims σ (es₁ ++ es₂) (es₁' ++ es₂')
[] ++s ses₂ = ses₂
(se ∷ ses₁) ++s ses₂ = se ∷ (ses₁ ++s ses₂)

_◇s_ : ∀{Γ Δ} {σ : Sub Γ Δ} {A C} {t : Tm Δ A} {t'} (sh : SubstTm σ t t')
         {es : Elims Δ A C} {es'} (ses : SubstElims σ es es') → SubstTm σ (t ◇ es) (t' ◇ es')
sh ∙′ ses ◇s ses' = sh ∙′ (ses ++s ses')


-- The Ω set

mutual

  -- Applicative eliminations only:

  data Oks {Γ : Cxt} : {A C : Ty} (es : Elims Γ A C) → Set where
    []  : ∀{A} → Oks {Γ} {A} {A} []
    cons : ∀ A B {C} {u : Tm Γ A} (o : Ok u) {es : Elims Γ B C} (os : Oks es) → Oks (app u ∷ es)

  data Ok {Γ : Cxt} : {C : Ty} (t : Tm Γ C) → Set where
    zero   : Ok zero!
    suc    : ∀{t} (o : Ok t) → Ok (suc! t)
    abs    : ∀{A B} {t : Tm (Γ ∙ A) B} (o : Ok t) → Ok (abs! t)
    ne     : ∀{A C} (x : Var Γ A) {es : Elims Γ A C} (os : Oks es) → Ok (var x ∙ es)

    zerec  : ∀{A C} {u : Tm Γ A} {v} (ov : Ok v) {es : Elims Γ A C} (o : Ok (u ◇ es)) → Ok (zero ∙ rec u v ∷ es)
    surec  : ∀{A C} {t : Tm Γ Nat} (n : Num t) {u : Tm Γ A} {v} {es : Elims Γ A C}
             (o : Ok (v ◇ app t ∷ app (t ◇ rec u v ∷ []) ∷ es)) → Ok (suc t ∙ rec u v ∷ es)

    beta   : ∀{A B C} {t : Tm (Γ ∙ A) B} {u} (ou : Ok u) {es : Elims Γ B C}
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
oks-snoc []       ou = cons _ _ ou []
oks-snoc (cons A B o os) ou = cons A B o (oks-snoc os ou)

data OkElim {Γ : Cxt} : {A C : Ty} (e : Elim Γ A C) → Set where
  app : ∀{A B} {u : Tm Γ A} (o : Ok u) → OkElim {Γ} {A ⇒ B} (app u)
  rec : ∀{C} {u : Tm Γ C} (ou : Ok u) {v : Tm Γ (Nat ⇒ C ⇒ C)} (ov : Ok v) → OkElim (rec u v)

data OkElims {Γ : Cxt} {A} : {C : Ty} (es : Elims Γ A C) → Set where
  []  : OkElims []
  _∷_ : ∀{B C} {e : Elim Γ A B} (o : OkElim e) {es : Elims Γ B C} (os : OkElims es) → OkElims (e ∷ es)

mutual
  wkOk : ∀ {B Γ} {t : Tm Γ B} {Γ'} (τ : Γ' ≤ Γ) (o : Ok t) → Ok (wkTm τ t)
  wkOk τ zero        = zero
  wkOk τ (suc o)     = suc (wkOk τ o)
  wkOk τ (abs o)     = abs (wkOk (lift τ) o)
  wkOk τ (ne x os)   = ne (wkVar τ x) (wkOks τ os)
  wkOk τ (zerec ov o)= zerec (wkOk τ ov) (wkOk τ o)
  wkOk τ (surec n o) = surec (wkNum τ n) (wkOk τ o)
  wkOk τ (beta ou o) = beta (wkOk τ ou) {!(wkOk τ o)!}  -- need weakening composition
  wkOk τ (omega o f) = omega (wkOk τ o) (λ n → wkOk τ (f n))

  wkOks : ∀ {B Γ A} {es : Elims Γ A B} {Γ'} (τ : Γ' ≤ Γ) →
          (os : Oks es) → Oks (wkElims τ es)
  wkOks τ [] = []
  wkOks τ (cons A B o os) = cons A B (wkOk τ o) (wkOks τ os)

data Res A {Γ} : ∀{B} (t : Tm Γ B) → Set where
  rtm  : {t : Tm Γ A} (o : Ok t) → Res A t
  rvar : ∀{B} (x : Var Γ B) → Res A (var! x)

data OkSub A {Γ} : ∀{Δ} (σ : Sub Γ Δ) → Set where
  wk : ∀{Δ} (τ : Γ ≤ Δ) → OkSub A (wk τ)
  _∙_ : ∀{Δ B} {σ : Sub Γ Δ} (oσ : OkSub A σ) {t : Tm Γ B} (r : Res A t) → OkSub A (σ ∙ t)

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

subOkVar : ∀ A {Γ Δ} {σ : Sub Γ Δ} (oσ : OkSub A σ) {C} (x : Var Δ C) → Res A (subVar σ x)
subOkVar A (wk τ) x = rvar (wkVar τ x)
subOkVar A (oσ ∙ r) vz = r
subOkVar A (oσ ∙ r) (vs x) = subOkVar A oσ x

mutual

  appOk : ∀ A {Γ B} {t : Tm Γ (A ⇒ B)} {u : Tm Γ A} (ot : Ok t) (ou : Ok u) → Ok (t ◇ app u ∷ [])
  appOk A (abs ot) ou = beta ou (subOk1 A ot ou)
  appOk A (ne x os) ou = ne x (oks-snoc os ou)
  appOk A (zerec ov ot) ou = zerec ov (appOk A ot ou)
  appOk A (surec n ot) ou = surec n (appOk A ot ou)
  appOk A (beta o ot) ou = beta o (appOk A ot ou)
  appOk A (omega ot f) ou = omega ot λ n → appOk A (f n) ou

  appOks : ∀ A {Γ B} {t : Tm Γ A} (ot : Ok t) {es : Elims Γ A B} (os : Oks es) → Ok (t ◇ es)
  appOks _         ot []             = ot
  appOks .(A ⇒ B) ot (cons A B o os) = appOks B (appOk A ot o) os

  appRes : ∀ A {Γ B C} {t : Tm Γ B} (ot : Res A t) {es : Elims Γ B C} (os : Oks es) → Ok (t ◇ es)
  appRes A (rtm o) os = appOks A o os
  appRes A (rvar x) os = ne x os

  subOks : ∀ A {Γ Δ} {σ : Sub Γ Δ} (oσ : OkSub A σ) {B C} {es : Elims Δ B C} (os : Oks es) → Oks (subElims σ es)
  subOks A oσ [] = []
  subOks A oσ (cons B C o os) = cons B C (subOk A oσ o) (subOks A oσ os)

  subOk : ∀ A {Γ Δ} {σ : Sub Γ Δ} (oσ : OkSub A σ) {C} {t : Tm Δ C} (o : Ok t) → Ok (subTm σ t)
  subOk A oσ zero = zero
  subOk A oσ (suc o) = suc (subOk A oσ o)
  subOk A oσ (abs o) = abs (subOk A (liftOk oσ) o)
  subOk A oσ (ne x os) = appRes A (subOkVar A oσ x) (subOks A oσ os)
  subOk A oσ (zerec ou o) = zerec (subOk A oσ ou) (subOk A oσ o)
  subOk A oσ (surec n o) = surec (subNum _ n) (subOk A oσ o)
  subOk A oσ (beta ou o) = beta (subOk A oσ ou) {!(subOk A oσ o)!}  -- need substitution composition
  subOk A oσ (omega o f) = omega (subOk A oσ o) (λ n → subOk A oσ (f n))

  subOk1 : ∀ A {Γ B} {t : Tm (Γ ∙ A) B} {u : Tm Γ A} (ot : Ok t) (ou : Ok u) → Ok (t [ u ])
  subOk1 A ot ou = subOk A (sgOk ou) ot

-- Ω is closed under eliminations (not just applications)

numOk : ∀ n {Γ} → Ok {Γ} (num n)
numOk zero = zero
numOk (suc n) = suc (numOk n)

recOk : ∀ {B Γ} {u : Tm Γ B} {v : Tm Γ (Nat ⇒ B ⇒ B)} (ou : Ok u) (ov : Ok v) (n : ℕ) → Ok (num n ◇ rec u v ∷ [])
recOk ou ov zero = zerec ov ou
recOk ou ov (suc n) = surec (numNum n) (appOk _ (appOk _ ov (numOk n)) (recOk ou ov n))

elimOk : ∀{Γ A B} {t : Tm Γ A} (ot : Ok t) {e : Elim Γ A B} (oe : OkElim e) → Ok (t ◇ e ∷ [])
elimOk ot (app o)     = appOk _ ot o
elimOk ot (rec ou ov) = omega ot (recOk ou ov)

elimsOk : ∀{Γ A B} {t : Tm Γ A} (ot : Ok t) {es : Elims Γ A B} (os : OkElims es) → Ok (t ◇ es)
elimsOk ot [] = ot
elimsOk ot (o ∷ os) = elimsOk (elimOk ot o) os

-- Show that every term is in Ω

mutual
  ok : ∀{Γ A} (t : Tm Γ A) → Ok t
  ok (h ∙ es) = elimsOk (okHead h) (okElims es)

  okHead : ∀ {Γ A} (h : Head Γ A) → Ok (h ∙ [])
  okHead zero = zero
  okHead (suc t) = suc (ok t)
  okHead (abs t) = abs (ok t)
  okHead (var x) = ne x []

  okElim : ∀ {Γ A B} (e : Elim Γ A B) → OkElim e
  okElim (app u) = app (ok u)
  okElim (rec u v) = rec (ok u) (ok v)

  okElims : ∀ {Γ A B} (es : Elims Γ A B) → OkElims es
  okElims [] = []
  okElims (e ∷ es) = okElim e ∷ okElims es

-- Strong normalization

mutual

  data SN {Γ : Cxt} : {C : Ty} (t : Tm Γ C) → Set where
    zero   : SN zero!
    suc    : ∀{t} (sn : SN t) → SN (suc! t)
    abs    : ∀{A B} {t : Tm (Γ ∙ A) B} (sn : SN t) → SN (abs! t)
    ne     : ∀{A C} (x : Var Γ A) {es : Elims Γ A C} (sns : SNElims es) → SN (var x ∙ es)

    zerec  : ∀{A C} {u : Tm Γ A} {v} (snv : SN v) {es : Elims Γ A C} (sn : SN (u ◇ es)) → SN (zero ∙ rec u v ∷ es)
    surec  : ∀{A C} {t : Tm Γ Nat} (snt : SN t) {u : Tm Γ A} {v} {es : Elims Γ A C}
             (sn : SN (v ◇ app t ∷ app (t ◇ rec u v ∷ []) ∷ es)) → SN (suc t ∙ rec u v ∷ es)

    beta   : ∀{A B C} {t : Tm (Γ ∙ A) B} {u} (snu : SN u) {es : Elims Γ B C}
             (sn : SN (t [ u ] ◇ es)) → SN (abs t ∙ app u ∷ es)

  data SNElim {Γ : Cxt} : {A C : Ty} (e : Elim Γ A C) → Set where
    app : ∀{A B} {u : Tm Γ A} (sn : SN u) → SNElim {Γ} {A ⇒ B} (app u)
    rec : ∀{C} {u : Tm Γ C} (snu : SN u) {v : Tm Γ (Nat ⇒ C ⇒ C)} (snv : SN v) → SNElim (rec u v)

  data SNElims {Γ : Cxt} {A} : {C : Ty} (es : Elims Γ A C) → Set where
    []  : SNElims []
    _∷_ : ∀{B C} {e : Elim Γ A B} (sn : SNElim e) {es : Elims Γ B C} (sns : SNElims es) → SNElims (e ∷ es)

_++sn_ : ∀{Γ A B C} {es : Elims Γ A B} (sns : SNElims es) {es' : Elims Γ B C} (sns' : SNElims es') → SNElims (es ++ es')
[] ++sn sns = sns
(sn ∷ sns) ++sn sns' = sn ∷ (sns ++sn sns')

mutual
  wkSN : ∀{Γ Δ} (τ : Γ ≤ Δ) {C} {t : Tm Δ C} (sn : SN t) → SN (wkTm τ t)
  wkSN τ zero = zero
  wkSN τ (suc sn) = suc (wkSN τ sn)
  wkSN τ (abs sn) = abs (wkSN (lift τ) sn)
  wkSN τ (ne x sns) = ne (wkVar τ x) (wkSNElims τ sns)
  wkSN τ (zerec snv sn) = zerec (wkSN τ snv) (wkSN τ sn)
  wkSN τ (surec snt sn) = surec (wkSN τ snt) (wkSN τ sn)
  wkSN τ (beta snu sn) = beta (wkSN τ snu) {! (wkSN τ sn) !}  -- need substitution lemma

  wkSNElim : ∀{Γ Δ} (τ : Γ ≤ Δ) {A B} {e : Elim Δ A B} (sn : SNElim e) → SNElim (wkElim τ e)
  wkSNElim τ (app sn) = app (wkSN τ sn)
  wkSNElim τ (rec snu snv) = rec (wkSN τ snu) (wkSN τ snv)

  wkSNElims : ∀{Γ Δ} (τ : Γ ≤ Δ) {A B} {es : Elims Δ A B} (sn : SNElims es) → SNElims (wkElims τ es)
  wkSNElims τ [] = []
  wkSNElims τ (sn ∷ sns) = wkSNElim τ sn ∷ wkSNElims τ sns

-- From Ω to SN

-- Extract a numeral from SN terms of type Nat

val : ∀{Γ} {t : Tm Γ Nat} (sn : SN t) → ℕ
val zero = zero
val (suc sn) = suc (val sn)
val (ne x os) = zero
val (zerec _ sn) = val sn
val (surec _ sn) = val sn
val (beta _ sn) = val sn


wkVal : ∀{Γ Δ} (τ : Γ ≤ Δ) {t : Tm Δ Nat} (sn : SN t) → val (wkSN τ sn) ≡ val sn
wkVal τ zero = refl
wkVal τ (suc sn) = cong suc (wkVal τ sn)
wkVal τ (ne x sns) = refl
wkVal τ (zerec _ sn) = wkVal τ sn
wkVal τ (surec _ sn) = wkVal τ sn
wkVal τ (beta  _ sn) = wkVal τ sn

{-# REWRITE wkVal #-}

-- Nat substitutions and their numeral value extraction

data SNRes A {Γ} : ∀{B} (t : Tm Γ B) → Set where
  rtm  : {t : Tm Γ A} (sn : SN t) → SNRes A t
  rvar : ∀{B} (x : Var Γ B) → SNRes A (var! x)

data SNSub A {Γ} : ∀{Δ} (σ : Sub Γ Δ) → Set where
  wk : ∀{Δ} (τ : Γ ≤ Δ) → SNSub A (wk τ)
  _∙_ : ∀{Δ B} {σ : Sub Γ Δ} (oσ : SNSub A σ) {t : Tm Γ B} (r : SNRes A t) → SNSub A (σ ∙ t)

snSubVar : ∀{Γ Δ A} {σ : Sub Γ Δ} (sσ : SNSub A σ) {C} (x : Var Δ C) → SN (subVar σ x)
snSubVar (wk τ)        x      = ne (wkVar τ x) []
snSubVar (sσ ∙ rtm sn) vz     = sn
snSubVar (sσ ∙ rvar x) vz     = ne x []
snSubVar (sσ ∙ r)      (vs x) = snSubVar sσ x

wkSNRes : ∀{Γ Δ} (τ : Γ ≤ Δ) {A B} {t : Tm Δ B} (r : SNRes A t) → SNRes A (wkTm τ t)
wkSNRes τ (rtm sn) = rtm (wkSN τ sn)
wkSNRes τ (rvar x) = rvar (wkVar τ x)

wkSNSub : ∀{Γ Δ} (τ : Γ ≤ Δ) {Δ' A} {σ : Sub Δ Δ'} (sσ : SNSub A σ) → SNSub A (wkSub τ σ)
wkSNSub τ (wk ρ) = wk (wkWk τ ρ)
wkSNSub τ (sσ ∙ r) = wkSNSub τ sσ ∙ wkSNRes τ r

liftSNSub : ∀ {Γ Δ} {σ : Sub Γ Δ} {A B} (sσ : SNSub A σ) →
            SNSub A (wkSub (weak {B} id≤) σ ∙ var! vz)
liftSNSub sσ = wkSNSub (weak id≤) sσ ∙ rvar vz


valr : ∀ {B Γ} {t : Tm Γ B} → SNRes Nat t → Tm Γ B
valr (rtm sn) = num (val sn)
valr (rvar x) = var! x

vals : ∀{Γ Δ} {σ : Sub Γ Δ} (sσ : SNSub Nat σ) → Sub Γ Δ
vals (wk τ) = wk τ
vals (sσ ∙ r) = vals sσ ∙ valr r

wkValr : ∀{Γ Δ} (τ : Γ ≤ Δ) {A} {t : Tm Δ A} (r : SNRes Nat t) → valr (wkSNRes τ r) ≡ wkTm τ (valr r)
wkValr τ (rtm sn) = refl
wkValr τ (rvar x) = refl

wkVals : ∀{Γ Δ} (τ : Γ ≤ Δ) {Δ'} {σ : Sub Δ Δ'} (sσ : SNSub Nat σ) → vals (wkSNSub τ sσ) ≡ wkSub τ (vals sσ)
wkVals τ (wk τ₁) = refl
wkVals τ (sσ ∙ r) = cong₂  _∙_ (wkVals τ sσ) (wkValr τ r)

{-# REWRITE wkValr wkVals #-}

-- Value expansion lemma

-- Need an inductive (relational) definition of substitution

mutual
  SNElims' : ∀ {Γ A B C} (es₀ : Elims Γ A B) (es : Elims Γ B C) → Set
  SNElims' {Γ} {A} {B} es₀ es = (eqT : B ≡ A) (eq : subst (Elims Γ A) eqT es₀ ≡ []) → SNElims es

  valexpElims' : ∀ {Γ Δ} {σ : Sub Γ Δ} (sσ : SNSub Nat σ)
            {A B C} {es₀ : Elims Γ A B} {es' : Elims Γ B C} {es : Elims Δ B C}
            (ses : SubstElims (vals sσ) es es') →
            (sns : SNElims (es₀ ++ es')) → SNElims' es₀ (subElims σ es)
            -- (eqT : B ≡ A)
            -- (eq : subst (Elims Γ A) eqT es₀ ≡ []) → SNElims (subElims σ es)
  valexpElims' sσ ses sns refl refl = valexpElims sσ ses sns

  valexpVar : ∀ {A Γ B C} {es₀ : Elims Γ A B}
              {Δ} {x : Var Δ B} {es : Elims Γ B C} {σ : Sub Γ Δ}
              (sσ : SNSub Nat σ) (x' : Var Γ A) →
            (sx  : SubstVar (vals sσ) x (var x' ∙ es₀)) →
            (sns : SNElims' es₀ es) → SN (subVar σ x ◇ es)
  valexpVar (wk τ) x' (suwk wx) sns = ne (wkVar τ _) (sns refl refl)
  valexpVar (sσ ∙ rtm sn) x' (suvz eq) sns = numNotVar _ eq  -- refute eq : num _ = var _ ∙ _
  valexpVar (sσ ∙ rtm sn) x' (suvs sx) sns = valexpVar sσ x' sx sns
  valexpVar (sσ ∙ rvar x) .x suvz! sns = ne x (sns refl refl)
  valexpVar (sσ ∙ rvar x) x' (suvs sx) sns = valexpVar sσ x' sx sns


  -- valexpVar : ∀ {A Γ B C} {es₀ : Elims Γ A B} {es' : Elims Γ B C}
  --             {Δ} {x : Var Δ B} {es : Elims Δ B C} {σ : Sub Γ Δ}
  --             (sσ : SNSub Nat σ) (x' : Var Γ A) →
  --           (sx  : SubstVar (vals sσ) x (var x' ∙ es₀)) →
  --           (ses : SubstElims (vals sσ) es es') →
  --           (sns : SNElims (es₀ ++ es')) → SN (subVar σ x ◇ subElims σ es)
  -- valexpVar (wk τ) x' (suwk wx) ses sns = ne (wkVar τ _) (valexpElims (wk τ) ses sns)
  -- valexpVar (sσ ∙ rtm sn) x' (suvz eq) ses sns = {!!}  -- refute eq : num _ = var _ ∙ _
  -- valexpVar (sσ ∙ rtm sn) x' (suvs sx) ses sns = {!valexpVar sσ x' sx ses sns!}
  -- valexpVar (sσ ∙ rvar x) .x suvz! ses sns = ne x (valexpElims (sσ ∙ rvar x) ses sns)
  -- valexpVar (sσ ∙ rvar x) x' (suvs sx) ses sns = {!valexpVar sσ x' sx ses sns!}


  valexp : ∀{Γ Δ} {σ : Sub Γ Δ} (sσ : SNSub Nat σ) {A} {t : Tm Δ A} {t' : Tm Γ A} (st : SubstTm (vals sσ) t t') (sn : SN t') → SN (subTm σ t)
  -- Cases on SN t'
  -- Case zero:
  valexp sσ (zero ∙′ []) zero = zero
  valexp sσ (var sx ∙ [] ∣ apd) zero = snSubVar sσ _
  -- Impossible subcases
  valexp sσ (var sx ∙ se ∷ ses ∣ apd) zero = headIsNotAppend _ apd
  valexp sσ (zero ∙ se ∷ ses ∣ ()) zero
  valexp sσ (suc st ∙ ses ∣ ()) zero
  valexp sσ (abs st ∙ ses ∣ ()) zero

  -- Case suc:
  valexp sσ (suc st ∙′ []) (suc sn) = suc (valexp sσ st sn)
  valexp sσ (var sx ∙ [] ∣ apd) (suc sn) = snSubVar sσ _
  -- Impossible subcases
  valexp sσ (var sx ∙ se ∷ ses ∣ apd) (suc sn) = headIsNotAppend _ apd
  valexp sσ (zero ∙ ses ∣ ()) (suc sn)
  valexp sσ (suc st ∙ se ∷ ses ∣ ()) (suc sn)
  valexp sσ (abs st ∙ ses ∣ ()) (suc sn)

  -- Case var
  valexp sσ (var sx ∙′ ses) (ne x sns) = valexpVar sσ x sx (valexpElims' sσ ses sns)
  -- Impossible subcases
  valexp sσ (zero ∙ ses ∣ ()) (ne x sns)
  valexp sσ (suc st ∙ ses ∣ ()) (ne x sns)
  valexp sσ (abs st ∙ ses ∣ ()) (ne x sns)

  -- Case abs
  valexp sσ (abs st ∙′ []) (abs sn) = abs (valexp (liftSNSub sσ) st sn)  -- REWRITE wkVals
  -- Impossible cases
  valexp sσ (var sx ∙ ses ∣ apd) (abs sn) = valexpAbs sσ sx _ apd
  valexp sσ (zero ∙ ses ∣ ()) (abs sn)
  valexp sσ (suc st ∙ ses ∣ ()) (abs sn)

  valexp sσ (zero ∙′ rec su sv ∷ ses) (zerec snv sn) = zerec (valexp sσ sv snv) (valexp sσ (su ◇s ses) sn)
  valexp sσ (suc st ∙ ses ∣ ()) (zerec snv sn)
  valexp sσ (abs st ∙ ses ∣ ()) (zerec snv sn)
  valexp sσ (var sx ∙ ses ∣ apd) (zerec snv sn) = {!valExpZeRec sσ sx ses apd snv sn!}  -- by induction on sx

  -- valexp sσ (var sx ∙′ []) (zerec snv sn) = snSubVar sσ _
  -- valexp sσ (var sx ∙ app su ∷ ses ∣ apd) (zerec snv sn) = {!!}  -- should be impossible by induction on sx
  -- valexp sσ (_∙_∣_ {t' = zero ∙ es} (var sx) (rec su sv ∷ ses) apd) (zerec snv sn) = {!apd!}
  -- valexp sσ (_∙_∣_ {t' = suc t ∙ es} (var sx) (rec su sv ∷ ses) ()) (zerec snv sn)
  -- valexp sσ (_∙_∣_ {t' = abs t ∙ es} (var sx) (rec su sv ∷ ses) ()) (zerec snv sn)
  -- valexp sσ (_∙_∣_ {t' = var x ∙ es} (var sx) (rec su sv ∷ ses) ()) (zerec snv sn)

  valexp sσ st (surec snt sn) = {!!}
  valexp sσ st (beta snu sn) = {!!}

  valexpAbs : ∀ {A B Γ} {t : Tm (Γ ∙ A) B} {C Δ} {x : Var Δ C}
              {t' : Tm Γ C} {σ : Sub Γ Δ}
            (sσ : SNSub Nat σ) →
            (sx : SubstVar (vals sσ) x t') →
            (es : Elims Γ C (A ⇒ B)) →
            (apd : Append t' es (abs! t)) → ∀{ℓ} → Absurd ℓ
  valexpAbs (wk τ) (suwk wx) es ()
  valexpAbs (sσ ∙ rtm sn) suvz! (e ∷ es) apd = headIsNotAppend _ apd
  valexpAbs (sσ ∙ rvar x) suvz! es ()
  valexpAbs (sσ ∙ r) (suvs sx) es apd = valexpAbs sσ sx es apd

  valExpZeRec : ∀ {Γ Δ A C D} {σ : Sub Γ Δ}
                {x : Var Δ A} {t' : Tm Γ A}
                {es : Elims Δ A D} {es' : Elims Γ A D}
                (sσ : SNSub Nat σ)
              (sx : SubstVar (vals sσ) x t')
              (ses : SubstElims (vals sσ) es es')
              {u : Tm Γ C} {v : Tm Γ (Nat ⇒ C ⇒ C)} {esᵣ : Elims Γ C D}
              (apd : Append t' es' (zero ∙ rec u v ∷ esᵣ))
              (snv : SN v) (snus : SN (u ◇ esᵣ)) →
              SN (subVar σ x ◇ subElims σ es)
  valExpZeRec (wk τ) (suwk wx) ses () snv snus
  valExpZeRec (sσ ∙ rtm sn) (suvz eq) [] append snv snus = numNotElim _ eq
  valExpZeRec {Γ} {t' = zero!} (_∙_ {σ = σ} sσ (rtm sn)) (suvz eq) (_∷_ (rec {u = u} su {v} sv) {es} {es'} ses) {u'} {v'} append snv snus = aux _ sn eq su sv ses
    -- aux sn eq su sv ses    -- induction on sn
    where
    snv' : SN (subTm (σ ∙ _) v)
    snv' = valexp (sσ ∙ rtm sn) sv snv
    snu' : SN (subTm (σ ∙ _) u)
    snu' = valexp (sσ ∙ rtm sn) su {!!}  -- snu from (snus : SN (u ◇ esᵣ)
    aux : ∀ (t : Tm Γ Nat) (sn : SN t) →
      (eq : num (val sn) ≡ zero!) →
      (su : SubstTm (vals sσ ∙ num (val sn)) u u') →
      (sv : SubstTm (vals sσ ∙ num (val sn)) v v') →
      (ses : SubstElims (vals sσ ∙ num (val sn)) es es') →  -- es es'
      SN (t ◇ rec (subTm (σ ∙ t) u) (subTm (σ ∙ t) v) ∷ subElims (σ ∙ t) es)
    aux t1 zero eq su sv ses = zerec (valexp (sσ ∙ rtm zero) sv snv) (valexp (sσ ∙ rtm zero) (su ◇s ses) snus)
    aux t1 (suc sn) () su sv ses
    aux t1 (ne x {es₀} sns) eq su sv ses = ne x (sns ++sn rec snu {!!} ∷ valexpElims (sσ ∙ {!!}) {! ses !} {!(valexp (sσ ∙ rtm zero) (su ◇s ses) snus)!})
      where
      snus' : SN (subTm (σ ∙ (var x ∙ es₀)) u ◇ subElims (σ ∙ (var x ∙ es₀)) es)
      snus' = (valexp (sσ ∙ rtm (ne x sns)) (su ◇s ses) snus)
      snu   : SN (subTm (σ ∙ (var x ∙ es₀)) u)
      snu   = {!!}
      snes' : SNElims (subElims (σ ∙ (var x ∙ es₀)) es)
      snes' = {!!}
      -- snus' : SN (subTm (σ ∙ zero!) u ◇ subElims (σ ∙ zero!) es)
      -- snus' = (valexp (sσ ∙ rtm zero) (su ◇s ses) snus)
      -- snu   : SN (subTm (σ ∙ zero!) u)
      -- snu   = {!!}
      -- snes' : SNElims (subElims (σ ∙ zero!) es)
      -- snes' = {!!}
    aux t1 (zerec snv sn) eq su sv ses = {!zerec snv (aux sn eq su sv ses)!}
    aux t1 (surec snt sn) eq su sv ses = surec snt {!aux sn eq su sv!}
    aux .(abs t ∙ app _ ∷ _) (beta {t = t} snu sn) eq su sv ses = {!!}
    -- aux : ∀ {B Γ} {u' : Tm Γ B} {v' : Tm Γ (Nat ⇒ B ⇒ B)} {D}
    --     {es' : Elims Γ B D} {Δ} {u : Tm (Δ ∙ Nat) B}
    --     {v : Tm (Δ ∙ Nat) (Nat ⇒ B ⇒ B)} {es : Elims (Δ ∙ Nat) B D}
    --     {σ : Sub Γ Δ} {sσ : SNSub Nat σ} {t : Tm Γ Nat} (sn : SN t) →
    --   (eq : num (val sn) ≡ zero!) →
    --   (su : SubstTm (vals sσ ∙ num (val sn)) u u') →
    --   (sv : SubstTm (vals sσ ∙ num (val sn)) v v') →
    --   (ses : SubstElims (vals sσ ∙ num (val sn)) es es') →
    --   SN (t ◇ rec (subTm (σ ∙ t) u) (subTm (σ ∙ t) v) ∷ subElims (σ ∙ t) es)
    -- aux = {!!}
  valExpZeRec {t' = zero ∙ .(rec _ _) ∷ es} (sσ ∙ rtm sn) (suvz eq) (rec su sv ∷ ses) append snv snus = numNotElim _ eq
  valExpZeRec {t' = suc t ∙ es} (sσ ∙ rtm sn) (suvz eq) (rec su sv ∷ ses) () snv snus
  valExpZeRec {t' = abs t ∙ es} (sσ ∙ rtm sn) (suvz eq) (rec su sv ∷ ses) () snv snus
  valExpZeRec {t' = var x ∙ es} (sσ ∙ rtm sn) (suvz eq) (rec su sv ∷ ses) () snv snus
  valExpZeRec (sσ ∙ rvar x) suvz! ses () snv snus
  valExpZeRec (sσ ∙ r) (suvs sx) ses apd snv snus = {!valExpZeRec sσ sx ses apd snv snus!} -- Need generalization!

  -- valexpAbs : ∀ {A B Γ} {t : Tm (Γ ∙ A) B} {A₁ Δ} {x : Var Δ A₁}
  --             {t' : Tm Γ A₁} {es : Elims Δ A₁ (A ⇒ B)} {σ : Sub Γ Δ}
  --             {es' : Elims Γ A₁ (A ⇒ B)} (sσ : SNSub Nat σ) →
  --           (sx : SubstVar (vals sσ) x t') →
  --           (ses : SubstElims (vals sσ) es es') →
  --           (apd : Append t' es' (abs! t)) → SN (subVar σ x ◇ subElims σ es)
  -- valexpAbs (wk τ) (suwk wx) ses ()
  -- valexpAbs (sσ ∙ rtm sn) suvz! (se ∷ ses) apd = headIsNotAppend _ apd
  -- valexpAbs (sσ ∙ rvar x) suvz! ses ()
  -- valexpAbs (sσ ∙ r) (suvs sx) ses apd = valexpAbs sσ sx {!!} apd

{-
  valexp sσ (zero ∙′ []) zero = zero
  valexp sσ (zero ∙′ rec su sv ∷ ses) (zerec snv sn) = zerec (valexp sσ sv snv) (valexp sσ (su ◇s ses) sn) -- {!valexp sσ su!}
  valexp sσ (suc st ∙′ []) (suc sn) = suc (valexp sσ st sn)
  valexp sσ (suc st ∙′ rec su sv ∷ ses) (surec snt sn) =
    surec (valexp sσ st snt) (valexp sσ ( sv ◇s (app st ∷ app (st ◇s (rec su sv ∷ [])) ∷ ses)) sn)
  valexp sσ (abs st ∙′ []) (abs sn) = abs {!valexp ? st sn!}  -- Substitution lemma
  valexp sσ (abs st ∙′ app su ∷ ses) (beta snu sn) = beta (valexp sσ su snu) {!valexp ? ? sn!}
  valexp (wk τ) (var (suwk refl) ∙′ ses) (ne .(wkVar τ _) sns) = ne (wkVar τ _) (valexpElims (wk τ) ses sns)
  valexp sσ (var _ ∙′ []) _ = snSubVar sσ _
  valexp (sσ ∙ rtm snt) (var suvz ∙ se ∷ ses ∣ apd) sn = {!!}
  -- valexp (sσ ∙ rvar x) (var suvz ∙′ []) (ne .x sns) = ne x []
  valexp (sσ ∙ rvar x) (var suvz ∙′ ses) (ne .x sns) = ne x (valexpElims (sσ ∙ rvar x) ses sns)
  valexp (sσ ∙ rtm snt) (var (suvs sx) ∙′ se ∷ ses) sn = {!!}
  valexp (sσ ∙ rvar x) (var (suvs sx) ∙′ ses) sn = {!sn!}

  valexpVar : ∀{Γ Δ} {σ : Sub Γ Δ} (sσ : SNSub Nat σ) {A} {x : Var Δ A} {t' : Tm Γ A} (st : SubstVar (vals sσ) x t') (sn : SN t') → SN (subVar σ x)
  valexpVar = {!!}
-}
  valexpElim : ∀{Γ Δ} {σ : Sub Γ Δ} (sσ : SNSub Nat σ) {A B} {e : Elim Δ A B} {e' : Elim Γ A B} (se : SubstElim (vals sσ) e e') (sn : SNElim e') → SNElim (subElim σ e)
  valexpElim sσ (app su) (app sn) = app (valexp sσ su sn)
  valexpElim sσ (rec su sv) (rec snu snv) = rec (valexp sσ su snu) (valexp sσ sv snv)

  valexpElims : ∀{Γ Δ} {σ : Sub Γ Δ} (sσ : SNSub Nat σ) {A B} {es : Elims Δ A B} {es' : Elims Γ A B} (ses : SubstElims (vals sσ) es es') (sns : SNElims es') → SNElims (subElims σ es)
  valexpElims sσ [] [] = []
  valexpElims sσ (se ∷ ses) (sn ∷ sns) = valexpElim sσ se sn ∷ valexpElims sσ ses sns

{-
-- Extract a normal form from SN

mutual

  data Nf {Γ : Cxt} : {C : Ty} (t : Tm Γ C) → Set where
    zero   : Nf zero!
    suc    : ∀{t} (o : Nf t) → Nf (suc! t)
    abs    : ∀{A B} {t : Tm (Γ ∙ A) B} (o : Nf t) → Nf (abs! t)
    ne     : ∀{A C} (x : Var Γ A) {es : Elims Γ A C} (os : NfElims es) → Nf (var x ∙ es)

  data NfElim {Γ : Cxt} : {A C : Ty} (e : Elim Γ A C) → Set where
    app : ∀{A B} {u : Tm Γ A} (o : Nf u) → NfElim {Γ} {A ⇒ B} (app u)
    rec : ∀{C} {u : Tm Γ C} (ou : Nf u) {v : Tm Γ (Nat ⇒ C ⇒ C)} (ov : Nf v) → NfElim (rec u v)

  data NfElims {Γ : Cxt} {A} : {C : Ty} (es : Elims Γ A C) → Set where
    []  : NfElims []
    _∷_ : ∀{B C} {e : Elim Γ A B} (o : NfElim e) {es : Elims Γ B C} (os : NfElims es) → NfElims (e ∷ es)

-- Existence of a normal form

record NF Γ A : Set where
  constructor norm; field
    {t} : Tm Γ A
    nf : Nf t

record NFElim Γ A B : Set where
  constructor normE; field
    {e} : Elim Γ A B
    nf  : NfElim e

record NFElims Γ A B : Set where
  constructor normEs; field
    {es} : Elims Γ A B
    nf  : NfElims es

appNf : ∀{Γ A B} → NF Γ A → NFElim Γ (A ⇒ B) B
appNf (norm u) = normE (app u)

recNf : ∀ {B Γ} → NF Γ B → NF Γ (Nat ⇒ B ⇒ B) → NFElim Γ Nat B
recNf (norm u) (norm v) = normE (rec u v)

consNF : ∀ {B Γ A C} → NFElim Γ A B → NFElims Γ B C → NFElims Γ A C
consNF (normE e) (normEs es) = normEs (e ∷ es)

sucNf : ∀ {Γ} → NF Γ Nat → NF Γ Nat
sucNf (norm t) = norm (suc t)

absNf : ∀ {A B Γ} → NF (Γ ∙ A) B → NF Γ (A ⇒ B)
absNf (norm t) = norm (abs t)

neNf : ∀ {A Γ B} → Var Γ A → NFElims Γ A B → NF Γ B
neNf x (normEs es) = norm (ne x es)

mutual
  nf : ∀{Γ A} {t : Tm Γ A} (sn : SN t) → NF Γ A
  nf zero = norm zero
  nf (suc sn) = sucNf (nf sn)
  nf (abs sn) = absNf (nf sn)
  nf (ne x os) = neNf x (nfElims os)
  nf (zerec _ sn) = nf sn
  nf (surec _ sn) = nf sn
  nf (beta _ sn) = nf sn

  nfElim : ∀ {Γ A B} {e : Elim Γ A B} (sn : SNElim e) → NFElim Γ A B
  nfElim (app u)   = appNf (nf u)
  nfElim (rec u v) = recNf (nf u) (nf v)

  nfElims : ∀ {Γ A B} {es : Elims Γ A B} (sn : SNElims es) → NFElims Γ A B
  nfElims []       = normEs []
  nfElims (e ∷ es) =  consNF (nfElim e) (nfElims es)

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
