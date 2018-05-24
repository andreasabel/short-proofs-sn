-- Following Joachimski/Matthes, AML 2003, Short proofs of normalization...

data Ty : Set where
  Nat : Ty
  _⇒_ : (A B : Ty) → Ty

infixr 6 _⇒_ _∷_
infixl 4 _∙_

data Cxt : Set where
  ε : Cxt
  _∙_ : (Γ : Cxt) (A : Ty) → Cxt

data Var : (Γ : Cxt) (A : Ty) → Set where
  vz : ∀{Γ A} → Var (Γ ∙ A) A
  vs : ∀{Γ A B} (x : Var Γ A) → Var (Γ ∙ B) A

-- Terms in spine notation

data Flag : Set where
  app : Flag  -- only app eliminations
  rec : Flag  -- both eliminations

mutual

  data Tm (Γ : Cxt) (C : Ty) : Set where
    _⟨_⟩_ : ∀{A} (h : Head Γ A) f (es : Elims Γ f A C) → Tm Γ C

  data Head (Γ : Cxt) : (C : Ty) → Set where
    zero : Head Γ Nat
    suc  : (t : Tm Γ Nat) → Head Γ Nat
    abs  : ∀{A B} (t : Tm (Γ ∙ A) B) → Head Γ (A ⇒ B)
    var  : ∀{A} (x : Var Γ A) → Head Γ A

  data Elim (Γ : Cxt) : (f : Flag) (A C : Ty) → Set where
    app : ∀{A B f} (u : Tm Γ A) → Elim Γ f (A ⇒ B) B
    rec : ∀{C} (u : Tm Γ C) (v : Tm (Γ ∙ Nat ∙ C) C) → Elim Γ rec Nat C

  data Elims (Γ : Cxt) (f : Flag) (A : Ty) : (C : Ty) → Set where
    [] : Elims Γ f A A
    _∷_ : ∀{B C} (e : Elim Γ f A B) (es : Elims Γ f B C) → Elims Γ f A C

pattern zero!  = zero  ⟨ app ⟩ []
pattern suc! t = suc t ⟨ app ⟩ []
pattern abs! t = abs t ⟨ app ⟩ []

-- Numerals

data Num {Γ : Cxt} : Tm Γ Nat → Set where
  zero : Num zero!
  suc  : ∀{t} (n : Num t) → Num (suc! t)

-- The Ω set

data Ok {Γ : Cxt} : {C : Ty} (t : Tm Γ C) → Set where
  zero : Ok zero!
  suc  : ∀{t} (ot : Ok t) → Ok (suc! t)
  abs  : ∀{A B} {t : Tm (Γ ∙ A) B} (ot : Ok t) → Ok (abs! t)
  ne   : ∀{A C} (x : Var Γ A) {es : Elim Γ A C} (os : OkEs es) → Ok (var x ∙ es)
