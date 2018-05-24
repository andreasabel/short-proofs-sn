-- Following Joachimski/Matthes, AML 2003, Short proofs of normalization...

data Ty : Set where
  Nat : Ty
  _⇒_ : (A B : Ty) → Ty

infixr 6 _⇒_ _∷_ _++_
infixl 4 _∙_

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

  data Tm (Γ : Cxt) (C : Ty) : Set where
    _∙_ : ∀{A} (h : Head Γ A) (es : Elims Γ A C) → Tm Γ C

  data Head (Γ : Cxt) : (C : Ty) → Set where
    zero : Head Γ Nat
    suc  : (t : Tm Γ Nat) → Head Γ Nat
    abs  : ∀{A B} (t : Tm (Γ ∙ A) B) → Head Γ (A ⇒ B)
    var  : ∀{A} (x : Var Γ A) → Head Γ A

  data Elim (Γ : Cxt) : (A C : Ty) → Set where
    app : ∀{A B} (u : Tm Γ A) → Elim Γ (A ⇒ B) B
    rec : ∀{C} (u : Tm Γ C) (v : Tm (Γ ∙ Nat ∙ C) C) → Elim Γ Nat C

  data Elims (Γ : Cxt) (A : Ty) : (C : Ty) → Set where
    [] : Elims Γ A A
    _∷_ : ∀{B C} (e : Elim Γ A B) (es : Elims Γ B C) → Elims Γ A C

_++_ : ∀{Γ A B C} (es : Elims Γ A B) (es' : Elims Γ B C) → Elims Γ A C
[]       ++ es' = es'
(e ∷ es) ++ es' = e ∷ (es ++ es')

_·_ : ∀{Γ A C} (t : Tm Γ A) (es : Elims Γ A C) → Tm Γ C
_·_ (h ∙ es) es' = h ∙ es ++ es'

pattern zero!  = zero  ∙ []
pattern suc! t = suc t ∙ []
pattern abs! t = abs t ∙ []

-- Numerals

data Num {Γ : Cxt} : Tm Γ Nat → Set where
  zero : Num zero!
  suc  : ∀{t} (n : Num t) → Num (suc! t)

-- The Ω set

mutual
  data Ok {Γ : Cxt} : {C : Ty} (t : Tm Γ C) → Set where
    zero   : Ok zero!
    suc    : ∀{t} (o : Ok t) → Ok (suc! t)
    abs    : ∀{A B} {t : Tm (Γ ∙ A) B} (o : Ok t) → Ok (abs! t)
    ne     : ∀{A C} (x : Var Γ A) {es : Elims Γ A C} (os : Oks es) → Ok (var x ∙ es)
    zerec  : ∀{A C} {u : Tm Γ A} {v} {es : Elims Γ A C} (o : Ok (u ·es)) → Ok (zero ∙ rec u v ∷ es)
    surec  : ∀{A C} {t : Tm Γ Nat} (n : Num t) {u : Tm Γ A} {v} {es : Elims Γ A C} (o : Ok (v t (t · rec u v ∷ [])) es)) → Ok (suc t ∙ rec u v ∷ es)

  data Oks {Γ : Cxt} : {A C : Ty} (es : Elims Γ A C) → Set where
    []  : ∀{A} → Oks {Γ} {A} {A} []
    _∷_ : ∀{A B C} {u : Tm Γ A} (o : Ok u) {es : Elims Γ B C} (os : Oks es) → Oks (app u ∷ es)
