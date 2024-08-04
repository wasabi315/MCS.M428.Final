open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Maybe using ( Maybe; just; nothing )
open import Data.Nat using ( ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s )
open import Function using ( _∘′_ )
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using ( Star; _◅_ ) renaming ( ε to [] )
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties using ( module StarReasoning )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; cong )
open import Relation.Nullary using ( ¬_ )
open import Relation.Nullary.Decidable using ( True; toWitness )

infixr 8 ↑_ ↑Val_ ↑PEC_
infixr 7 _⇒_!_
infixl 7 _·_
infixl 6 _[_] _⟨_⟩
infixl 5 _,_
infix  5 ƛ_ μ_
infix  4 _∋_
infix  2 _⟶_ _⟶*_

--------------------------------------------------------------------------------
-- Syntax

data Ty : Set
data Eff : Set

data Ty where
  `ℕ : Ty
  _⇒_!_ : Ty → Ty → Eff → Ty

data Eff where
  ι : Eff
  _➡_ : Ty → Ty → Eff

data Ctx : Set where
  ∙ : Ctx
  _,_ : Ctx → Ty → Ctx

variable
  Γ Δ : Ctx
  α β γ αₕ : Ty
  ε ε' εₕ : Eff

data _∋_ : Ctx → Ty → Set where
  zero : Γ , α ∋ α
  suc : Γ ∋ α → Γ , β ∋ α

data Tm : Ctx → Eff → Ty → Set where
  var : Γ ∋ α → Tm Γ ε α
  ƛ_ : Tm (Γ , α) ε β → Tm Γ ε' (α ⇒ β ! ε)
  _·_ : Tm Γ ε (α ⇒ β ! ε) → Tm Γ ε α → Tm Γ ε β
  zero : Tm Γ ε `ℕ
  suc : Tm Γ ε `ℕ → Tm Γ ε `ℕ
  case : Tm Γ ε `ℕ → Tm Γ ε α → Tm (Γ , `ℕ) ε α → Tm Γ ε α
  μ_ : Tm (Γ , α ⇒ β ! ε) ε (α ⇒ β ! ε) → Tm Γ ε (α ⇒ β ! ε)
  send : Tm Γ (α ➡ β) α → Tm Γ (α ➡ β) β
  run : Tm Γ (α ➡ β) γ → Tm (Γ , α , β ⇒ γ ! ε) ε γ → Tm Γ ε γ

length : Ctx → ℕ
length ∙ = 0
length (Γ , _) = suc (length Γ)

lookup : ∀ {n} → n < length Γ → Ty
lookup {_ , α} {zero} (s≤s z≤n) = α
lookup {Γ , _} {suc n} (s≤s p) = lookup p

count : ∀ {n} (p : n < length Γ) → Γ ∋ lookup p
count {_ , _} {zero} (s≤s z≤n) = zero
count {Γ , _} {suc n} (s≤s p) = suc (count p)

var# : ∀ n {n∈Γ : True (suc n ≤? length Γ)} → Tm Γ ε (lookup (toWitness n∈Γ))
var# n {n∈Γ} = var (count (toWitness n∈Γ))

--------------------------------------------------------------------------------
-- Renaming and Substitution

Ren : Ctx → Ctx → Set
Ren Γ Δ = ∀ {α} → Γ ∋ α → Δ ∋ α

ext : Ren Γ Δ → Ren (Γ , α) (Δ , α)
ext ρ zero = zero
ext ρ (suc i) = suc (ρ i)

ren : Ren Γ Δ → Tm Γ ε α → Tm Δ ε α
ren ρ (var i) = var (ρ i)
ren ρ (ƛ t) = ƛ ren (ext ρ) t
ren ρ (t · u) = ren ρ t · ren ρ u
ren ρ zero = zero
ren ρ (suc t) = suc (ren ρ t)
ren ρ (case n z s) = case (ren ρ n) (ren ρ z) (ren (ext ρ) s)
ren ρ (μ t) = μ (ren (ext ρ) t)
ren ρ (send t) = send (ren ρ t)
ren ρ (run t u) = run (ren ρ t) (ren (ext (ext ρ)) u)

↑_ : Tm Γ ε α → Tm (Γ , β) ε α
↑_ = ren suc

Sub : Ctx → Ctx → Set
Sub Γ Δ = ∀ {α} → Γ ∋ α → (∀ {ε} → Tm Δ ε α)

exts : Sub Γ Δ → Sub (Γ , α) (Δ , α)
exts σ zero = var zero
exts σ (suc i) = ↑ (σ i)

sub : Sub Γ Δ → Tm Γ ε α → Tm Δ ε α
sub σ (var i) = σ i
sub σ (ƛ t) = ƛ sub (exts σ) t
sub σ (t · u) = sub σ t · sub σ u
sub σ zero = zero
sub σ (suc t) = suc (sub σ t)
sub σ (case n z s) = case (sub σ n) (sub σ z) (sub (exts σ) s)
sub σ (μ t) = μ (sub (exts σ) t)
sub σ (send t) = send (sub σ t)
sub σ (run t u) = run (sub σ t) (sub (exts (exts σ)) u)

_[_] : Tm (Γ , α) ε β → (∀ {ε'} → Tm Γ ε' α) → Tm Γ ε β
t [ u ] = sub (λ { zero → u; (suc i) → var i }) t

--------------------------------------------------------------------------------
-- Values

data Val : Tm Γ ε α → Set where
  ƛ_ : (t : Tm (Γ , α) ε β) → Val {Γ} {ε'} (ƛ t)
  zero : Val {Γ} {ε} zero
  suc : {t : Tm Γ ε `ℕ} → Val t → Val (suc t)

renVal : (ρ : Ren Γ Δ) {t : Tm Γ ε α} → Val t → Val (ren ρ t)
renVal ρ (ƛ t) = ƛ ren (ext ρ) t
renVal ρ zero = zero
renVal ρ (suc v) = suc (renVal ρ v)

↑Val_ : {t : Tm Γ ε α} → Val t → Val {Γ , β} (↑ t)
↑Val_ = renVal suc

coe : {t : Tm Γ ε α} → Val t → Tm Γ ε' α
coe (ƛ t) = ƛ t
coe zero = zero
coe (suc v) = suc (coe v)

--------------------------------------------------------------------------------
-- Pure Evaluation Contexts

data _InPEC_ (h : Tm Γ εₕ αₕ) : Tm Γ ε α → Set where
  ⟨⟩ : h InPEC h
  _·₁_ : ∀ {t : Tm Γ ε (α ⇒ β ! ε)} (c : h InPEC t) u → h InPEC (t · u)
  _·₂_ : ∀ {t : Tm Γ ε (α ⇒ β ! ε)} {u} → Val t → h InPEC u → h InPEC (t · u)
  suc : ∀ {t : Tm Γ ε `ℕ} → h InPEC t → h InPEC (suc t)
  case : ∀ {n} (c : h InPEC n) (z : Tm Γ ε α) s → h InPEC case n z s
  send : ∀ {t : Tm Γ (α ➡ β) α} → h InPEC t → h InPEC send t

_⟨_⟩ : {h : Tm Γ εₕ αₕ} {t : Tm Γ ε α} → h InPEC t → Tm Γ εₕ αₕ → Tm Γ ε α
⟨⟩ ⟨ h' ⟩ = h'
(c ·₁ t) ⟨ h' ⟩ = (c ⟨ h' ⟩) · t
(_·₂_ {t = t} _ c) ⟨ h' ⟩ = t · (c ⟨ h' ⟩)
suc c ⟨ h' ⟩ = suc (c ⟨ h' ⟩)
case c z s ⟨ h' ⟩ = case (c ⟨ h' ⟩) z s
send c ⟨ h' ⟩ = send (c ⟨ h' ⟩)

⟨⟩-correct : {h : Tm Γ εₕ αₕ} {t : Tm Γ ε α} (c : h InPEC t)
  → t ≡ c ⟨ h ⟩
⟨⟩-correct ⟨⟩ = refl
⟨⟩-correct (c ·₁ u) = cong (_· u) (⟨⟩-correct c)
⟨⟩-correct (v ·₂ c) = cong (_ ·_) (⟨⟩-correct c)
⟨⟩-correct (suc c) = cong suc (⟨⟩-correct c)
⟨⟩-correct (case c z s) = cong (λ n → case n z s) (⟨⟩-correct c)
⟨⟩-correct (send c) = cong send (⟨⟩-correct c)

renPEC : (ρ : Ren Γ Δ) {h : Tm Γ εₕ αₕ} {t : Tm Γ ε α}
  → h InPEC t
  → ren ρ h InPEC ren ρ t
renPEC ρ ⟨⟩ = ⟨⟩
renPEC ρ (c ·₁ u) = renPEC ρ c ·₁ ren ρ u
renPEC ρ (v ·₂ c) = renVal ρ v ·₂ renPEC ρ c
renPEC ρ (suc c) = suc (renPEC ρ c)
renPEC ρ (case c z s) = case (renPEC ρ c) (ren ρ z) (ren (ext ρ) s)
renPEC ρ (send c) = send (renPEC ρ c)

↑PEC_ : {h : Tm Γ εₕ αₕ} {t : Tm Γ ε α} → h InPEC t → (↑_ {β = β} h) InPEC (↑ t)
↑PEC_ = renPEC suc

--------------------------------------------------------------------------------
-- Reduction rules

-- Preservation holds by construction
data _⟶_ : Tm Γ ε α → Tm Γ ε α → Set where
  app : ∀ {t : Tm (Γ , α) ε β} {u}
    → (v : Val u)
    → (ƛ t) · u ⟶ t [ coe v ]

  run-value : ∀ {t} (v : Val t) {u : Tm (Γ , α , β ⇒ γ ! ε) ε γ}
    → run t u ⟶ coe v

  run-send : ∀ {t} {u} {h : Tm (Γ , α , β ⇒ γ ! ε) ε γ}
    → (c : send u InPEC t)
    → (v : Val u)
    → run t h ⟶ h [ ƛ run (↑PEC ↑PEC c ⟨ var# 0 ⟩) (ren (ext (ext (suc ∘′ suc))) h) ] [ coe v ]

  case-zero : ∀ {z : Tm Γ ε α} {s}
    → case zero z s ⟶ z

  case-suc : ∀ {n} (v : Val n) {z : Tm Γ ε α} {s}
    → case (suc n) z s ⟶ s [ coe v ]

  unroll : {t : Tm (Γ , α ⇒ β ! ε) ε (α ⇒ β ! ε)}
    → μ t ⟶ t [ ƛ (↑ (μ t)) · var zero ]

  cong-·₁ : {t t' : Tm Γ ε (α ⇒ β ! ε)}
    → t ⟶ t'
    → ∀ {u} → t · u ⟶ t' · u

  cong-·₂ : ∀ {t : Tm Γ ε (α ⇒ β ! ε)} (v : Val t) {u u'}
    → u ⟶ u'
    → t · u ⟶ t · u'

  cong-send : {t t' : Tm Γ (α ➡ β) α}
    → t ⟶ t'
    → send t ⟶ send t'

  cong-run : ∀ {t t'}
    → t ⟶ t'
    → {h : Tm (Γ , α , β ⇒ γ ! ε) ε γ} → run t h ⟶ run t' h

  cong-suc : {t t' : Tm Γ ε `ℕ}
    → t ⟶ t'
    → suc t ⟶ suc t'

  cong-case : ∀ {n n'}
    → n ⟶ n'
    → ∀ {z : Tm Γ ε α} {s} → case n z s ⟶ case n' z s

_⟶*_ : Tm Γ ε α → Tm Γ ε α → Set
_⟶*_ = Star _⟶_

module ⟶*-Reasoning {Γ ε α} where
  open StarReasoning (_⟶_ {Γ} {ε} {α}) public

--------------------------------------------------------------------------------
-- Progress

data Progress : Tm ∙ ε α → Set where
  done : {t : Tm ∙ ε α} → Val t → Progress t
  step : {t t' : Tm ∙ ε α} → t ⟶ t' → Progress t
  bare-send : {u : Tm ∙ (α ➡ β) α} {t : Tm ∙ (α ➡ β) γ}
    → send u InPEC t
    → Val u
    → Progress t

progress : (t : Tm ∙ ε α) → Progress t
progress (ƛ t) = done (ƛ t)
progress (t · u) with progress t
... | step t⟶t' = step (cong-·₁ t⟶t')
... | bare-send c v = bare-send (c ·₁ u) v
... | done (ƛ t') with progress u
...   | step u⟶u' = step (cong-·₂ (ƛ t') u⟶u')
...   | bare-send c v = bare-send ((ƛ t') ·₂ c) v
...   | done vu = step (app vu)
progress (send t) with progress t
... | step t⟶t' = step (cong-send t⟶t')
... | done vt = bare-send ⟨⟩ vt
... | bare-send c v = bare-send (send c) v
progress (run t u) with progress t
... | step t⟶t' = step (cong-run t⟶t')
... | done vt = step (run-value vt)
... | bare-send c v = step (run-send c v)
progress zero = done zero
progress (suc t) with progress t
... | step t⟶t' = step (cong-suc t⟶t')
... | done vt = done (suc vt)
... | bare-send c v = bare-send (suc c) v
progress (case n z s) with progress n
... | step n⟶n' = step (cong-case n⟶n')
... | done zero = step case-zero
... | done (suc vn) = step (case-suc vn)
... | bare-send c v = bare-send (case c z s) v
progress (μ t) = step unroll

--------------------------------------------------------------------------------
-- Other properties

V¬⟶ : {v v' : Tm Γ ε α} → Val v → ¬ (v ⟶ v')
V¬⟶ (suc v) (cong-suc v⟶v') = V¬⟶ v v⟶v'

V-unique : {t : Tm Γ ε α} (v v' : Val t) → v ≡ v'
V-unique (ƛ t) (ƛ .t) = refl
V-unique zero zero = refl
V-unique (suc v) (suc v') = cong suc (V-unique v v')

-- V¬⟨send⟩ : {t : Tm Γ ε α} {u : Tm Γ (β ➡ γ) β}
--   → Val t
--   → ¬ InCtx (send u) t
-- V¬⟨send⟩ (suc v) (suc c) = V¬⟨send⟩ v c

-- ⟨send⟩¬⟶ : {u : Tm Γ (α ➡ β) α} {t t' : Tm Γ ε γ}
--   → Val u
--   → InCtx (send u) t
--   → ¬ (t ⟶ t')
-- ⟨send⟩¬⟶ v ⟨⟩ (cong-send t⟶t') = V¬⟶ v t⟶t'
-- ⟨send⟩¬⟶ v (c ·₁ u) (cong-·₁ t⟶t') = ⟨send⟩¬⟶ v c t⟶t'
-- ⟨send⟩¬⟶ v (c ·₁ u) (cong-·₂ v' t⟶t') = ⊥-elim (V¬⟨send⟩ v' c)
-- ⟨send⟩¬⟶ v (v' ·₂ c) (app v'') = ⊥-elim (V¬⟨send⟩ v'' c)
-- ⟨send⟩¬⟶ v (v' ·₂ c) (cong-·₁ t⟶t') = ⊥-elim (V¬⟶ v' t⟶t')
-- ⟨send⟩¬⟶ v (v' ·₂ c) (cong-·₂ v'' t⟶t') = ⟨send⟩¬⟶ v c t⟶t'
-- ⟨send⟩¬⟶ v (send c) (cong-send t⟶t') = ⟨send⟩¬⟶ v c t⟶t'
-- ⟨send⟩¬⟶ v (suc c) (cong-suc t⟶t') = ⟨send⟩¬⟶ v c t⟶t'
-- ⟨send⟩¬⟶ v (case s t c) (β-suc v') = ⊥-elim (V¬⟨send⟩ (suc v') c)
-- ⟨send⟩¬⟶ v (case s t c) (cong-case t⟶t') = ⟨send⟩¬⟶ v c t⟶t'

-- ⟶-deterministic : {t s u : Tm Γ ε α} → t ⟶ s → t ⟶ u → s ≡ u
-- ⟶-deterministic (app {t = t} v) (app v') = cong (λ u → t [ coe u ]) (V-unique v v')
-- ⟶-deterministic (β-run₁ v) (β-run₁ v') = cong coe (V-unique v v')
-- ⟶-deterministic (β-run₂ c v) (β-run₂ c' v') = {!   !}
-- ⟶-deterministic β-zero β-zero = refl
-- ⟶-deterministic (β-suc {u = t} v) (β-suc v') = cong (λ u → t [ coe u ]) (V-unique v v')
-- ⟶-deterministic (cong-·₁ t⟶s) (cong-·₁ t⟶u) = cong (_· _) (⟶-deterministic t⟶s t⟶u)
-- ⟶-deterministic (cong-·₂ _ t⟶s) (cong-·₂ _ t⟶u) = cong (_ ·_) (⟶-deterministic t⟶s t⟶u)
-- ⟶-deterministic (cong-send t⟶s) (cong-send t⟶u) = cong send (⟶-deterministic t⟶s t⟶u)
-- ⟶-deterministic (cong-run {u = u} t⟶s) (cong-run t⟶u) = cong (flip run u) (⟶-deterministic t⟶s t⟶u)
-- ⟶-deterministic (cong-suc t⟶s) (cong-suc t⟶u) = cong suc (⟶-deterministic t⟶s t⟶u)
-- ⟶-deterministic (cong-case t⟶s) (cong-case t⟶u) = cong (case _ _) (⟶-deterministic t⟶s t⟶u)
-- ⟶-deterministic (app v) (cong-·₂ _ t⟶u) = ⊥-elim (V¬⟶ v t⟶u)
-- ⟶-deterministic (cong-·₂ _ t⟶s) (app v) = ⊥-elim (V¬⟶ v t⟶s)
-- ⟶-deterministic (β-run₁ v) (β-run₂ c _) = ⊥-elim (V¬⟨send⟩ v c)
-- ⟶-deterministic (β-run₂ c _) (β-run₁ v) = ⊥-elim (V¬⟨send⟩ v c)
-- ⟶-deterministic (β-run₁ v) (cong-run t⟶u) = ⊥-elim (V¬⟶ v t⟶u)
-- ⟶-deterministic (cong-run t⟶s) (β-run₁ v) = ⊥-elim (V¬⟶ v t⟶s)
-- ⟶-deterministic (β-run₂ c v) (cong-run t⟶u) = ⊥-elim (⟨send⟩¬⟶ v c t⟶u)
-- ⟶-deterministic (cong-run t⟶s) (β-run₂ c v) = ⊥-elim (⟨send⟩¬⟶ v c t⟶s)
-- ⟶-deterministic (β-suc v) (cong-case t⟶u) = ⊥-elim (V¬⟶ (suc v) t⟶u)
-- ⟶-deterministic (cong-case t⟶s) (β-suc v) = ⊥-elim (V¬⟶ (suc v) t⟶s)
-- ⟶-deterministic (cong-·₁ t⟶s) (cong-·₂ v t⟶u) = ⊥-elim (V¬⟶ v t⟶s)
-- ⟶-deterministic (cong-·₂ v t⟶s) (cong-·₁ t⟶u) = ⊥-elim (V¬⟶ v t⟶u)

--------------------------------------------------------------------------------
-- Evaluation

data Steps (t : Tm ∙ ι α) : Set where
  steps : ∀ {t'} → t ⟶* t' → Maybe (Val t') → Steps t

eval : ℕ → (t : Tm ∙ ι α) → Steps t
eval zero t = steps [] nothing
eval (suc gas) t with progress t
... | done v = steps [] (just v)
... | step {t' = t'} t⟶t' with eval gas t'
...   | steps t'⟶*t'' v = steps (t⟶t' ◅ t'⟶*t'') v

--------------------------------------------------------------------------------
-- Examples

-- run (suc (send 0)) (x k. k (k x))
ex : Tm ∙ ι `ℕ
ex = run (suc (send zero)) (var# 0 · (var# 0 · var# 1))

_ : let open ⟶*-Reasoning in
    eval 10 ex ≡ steps
      (begin
        run (suc (send zero)) (var# 0 · (var# 0 · var# 1))
      ⟶⟨ run-send (suc ⟨⟩) zero ⟩
        (var# 0 · (var# 0 · var# 1))
          [ ƛ run (suc (var# 0)) (var# 0 · (var# 0 · var# 1)) ]
          [ zero ]
      ≡⟨⟩
        (ƛ run (suc (var# 0)) (var# 0 · (var# 0 · var# 1))) ·
          ((ƛ run (suc (var# 0)) (var# 0 · (var# 0 · var# 1))) · zero)
      ⟶⟨ cong-·₂ (ƛ run (suc (var# 0)) (var# 0 · (var# 0 · var# 1))) (app zero) ⟩
        (ƛ run (suc (var# 0)) (var# 0 · (var# 0 · var# 1))) ·
          (run (suc zero) (var# 0 · (var# 0 · var# 1)))
      ⟶⟨ cong-·₂ (ƛ run (suc (var# 0)) (var# 0 · (var# 0 · var# 1))) (run-value (suc zero)) ⟩
        (ƛ run (suc (var# 0)) (var# 0 · (var# 0 · var# 1))) · suc zero
      ⟶⟨ app (suc zero) ⟩
        run (suc (suc zero)) (var# 0 · (var# 0 · var# 1))
      ⟶⟨ run-value (suc (suc zero)) ⟩
        suc (suc zero)
      ∎)
      (just (suc (suc zero)))
_ = refl

plus : Tm ∙ ι (`ℕ ⇒ `ℕ ⇒ `ℕ ! ι ! ι)
plus = μ ƛ ƛ case (var# 1) (var# 0) (suc (var# 3 · var# 0 · var# 1))

_ : let open ⟶*-Reasoning in
    eval 10 (plus · suc zero · suc zero) ≡ steps
      (begin
        plus · suc zero · suc zero
      ⟶⟨ cong-·₁ (cong-·₁ unroll) ⟩
        (ƛ ƛ case (var# 1) (var# 0) (suc ((ƛ (↑ ↑ ↑ ↑ plus) · var# 0) · var# 0 · var# 1)))
          · suc zero
          · suc zero
      ⟶⟨ cong-·₁ (app (suc zero)) ⟩
        (ƛ case (suc zero) (var# 0) (suc ((ƛ (↑ ↑ ↑ plus) · var# 0) · var# 0 · var# 1)))
          · suc zero
      ⟶⟨ app (suc zero) ⟩
        case (suc zero) (suc zero) (suc ((ƛ ↑ ↑ plus · var# 0) · var# 0 · suc zero))
      ⟶⟨ case-suc zero ⟩
        suc ((ƛ ↑ plus · var# 0) · zero · suc zero)
      ⟶⟨ cong-suc (cong-·₁ (app zero)) ⟩
        suc (plus · zero · suc zero)
      ⟶⟨ cong-suc (cong-·₁ (cong-·₁ unroll)) ⟩
        suc (
          (ƛ ƛ case (var# 1) (var# 0) (suc ((ƛ (↑ ↑ ↑ ↑ plus) · var# 0) · var# 0 · var# 1)))
          · zero
          · suc zero)
      ⟶⟨ cong-suc (cong-·₁ (app zero)) ⟩
        suc ((ƛ case zero (var# 0) (suc ((ƛ (↑ ↑ ↑ plus) · var# 0) · var# 0 · var# 1))) · suc zero)
      ⟶⟨ cong-suc (app (suc zero)) ⟩
        suc (case zero (suc zero) (suc ((ƛ ↑ ↑ plus · var# 0) · var# 0 · suc zero)))
      ⟶⟨ cong-suc case-zero ⟩
        suc (suc zero)
      ∎)
      (just (suc (suc zero)))
_ = refl
