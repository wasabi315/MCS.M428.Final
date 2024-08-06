open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Maybe using ( Maybe; just; nothing )
open import Data.Nat using ( ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s )
open import Function using ( _∘′_ )
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using ( Star; _◅_ ) renaming ( ε to [] )
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties using ( module StarReasoning )
open import Relation.Binary.HeterogeneousEquality using ( _≅_ ) renaming ( refl to hrefl )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; cong )
open import Relation.Nullary using ( ¬_ )
open import Relation.Nullary.Decidable using ( True; toWitness )

infixr 8 ↑_ ↑Val_ ↑PEC_
infixr 7 _⇒_!_
infixl 7 _·_ _⇾_
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
  _⇾_ : Ty → Ty → Eff

data Ctx : Set where
  ∙ : Ctx
  _,_ : Ctx → Ty → Ctx

variable
  Γ Δ : Ctx
  α β γ δ αₕ : Ty
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
  send : Tm Γ (α ⇾ β) α → Tm Γ (α ⇾ β) β
  run : Tm Γ (α ⇾ β) γ → Tm (Γ , α , β ⇒ γ ! ε) ε γ → Tm Γ ε γ

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
  send : ∀ {t : Tm Γ (α ⇾ β) α} → h InPEC t → h InPEC send t

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

  run-value : ∀ {t} (v : Val t) {h : Tm (Γ , α , β ⇒ γ ! ε) ε γ}
    → run t h ⟶ coe v

  run-send : ∀ {t u}
    → (c : send u InPEC t)
    → (v : Val u)
    → {h : Tm (Γ , α , β ⇒ γ ! ε) ε γ}
    → run t h ⟶ h [ ƛ run (↑PEC ↑PEC c ⟨ var zero ⟩) (ren (ext (ext (suc ∘′ suc))) h) ] [ coe v ]

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

  cong-send : {t t' : Tm Γ (α ⇾ β) α}
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
  bare-send : {u : Tm ∙ (α ⇾ β) α} {t : Tm ∙ (α ⇾ β) γ}
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

V¬sendInPEC : {u : Tm Γ (α ⇾ β) α} {t : Tm Γ ε γ}
  → Val t
  → ¬ (send u InPEC t)
V¬sendInPEC (suc v) (suc c) = V¬sendInPEC v c

sendInPEC¬⟶ : {u : Tm Γ (α ⇾ β) α} {t t' : Tm Γ ε γ}
  → Val u
  → send u InPEC t
  → ¬ (t ⟶ t')
sendInPEC¬⟶ v ⟨⟩ (cong-send t⟶t') = V¬⟶ v t⟶t'
sendInPEC¬⟶ v (c ·₁ u) (cong-·₁ t⟶t') = sendInPEC¬⟶ v c t⟶t'
sendInPEC¬⟶ v (c ·₁ u) (cong-·₂ v' t⟶t') = ⊥-elim (V¬sendInPEC v' c)
sendInPEC¬⟶ v (v' ·₂ c) (app v'') = ⊥-elim (V¬sendInPEC v'' c)
sendInPEC¬⟶ v (v' ·₂ c) (cong-·₁ t⟶t') = ⊥-elim (V¬⟶ v' t⟶t')
sendInPEC¬⟶ v (v' ·₂ c) (cong-·₂ v'' t⟶t') = sendInPEC¬⟶ v c t⟶t'
sendInPEC¬⟶ v (suc c) (cong-suc t⟶t') = sendInPEC¬⟶ v c t⟶t'
sendInPEC¬⟶ v (case c z s) (case-suc v') = ⊥-elim (V¬sendInPEC (suc v') c)
sendInPEC¬⟶ v (case c z s) (cong-case t⟶t') = sendInPEC¬⟶ v c t⟶t'
sendInPEC¬⟶ v (send c) (cong-send t⟶t') = sendInPEC¬⟶ v c t⟶t'

sendInPEC-unique-ty : {t : Tm Γ ε α}
  → {u : Tm Γ (γ ⇾ β) γ} (c : send u InPEC t) (v : Val u)
  → {u' : Tm Γ (δ ⇾ β) δ} (c' : send u' InPEC t) (v' : Val u')
  → γ ≡ δ
sendInPEC-unique-ty ⟨⟩ vu ⟨⟩ vu' = refl
sendInPEC-unique-ty ⟨⟩ vu (send c') vu' = ⊥-elim (V¬sendInPEC vu c')
sendInPEC-unique-ty (c ·₁ u) vu (c' ·₁ .u) vu' rewrite sendInPEC-unique-ty c vu c' vu' = refl
sendInPEC-unique-ty (c ·₁ u) vu (v ·₂ c') vu' = ⊥-elim (V¬sendInPEC v c)
sendInPEC-unique-ty (v ·₂ c) vu (c' ·₁ _) vu' = ⊥-elim (V¬sendInPEC v c')
sendInPEC-unique-ty (v ·₂ c) vu (v' ·₂ c') vu' rewrite sendInPEC-unique-ty c vu c' vu' = refl
sendInPEC-unique-ty (suc c) vu (suc c') vu' rewrite sendInPEC-unique-ty c vu c' vu' = refl
sendInPEC-unique-ty (case c z s) vu (case c' .z .s) vu' rewrite sendInPEC-unique-ty c vu c' vu' = refl
sendInPEC-unique-ty (send c) vu ⟨⟩ vu' = ⊥-elim (V¬sendInPEC vu' c)
sendInPEC-unique-ty (send c) vu (send c') vu' rewrite sendInPEC-unique-ty c vu c' vu' = refl

sendInPEC-unique-tm : {t : Tm Γ ε α}
  → {u : Tm Γ (γ ⇾ β) γ} (c : send u InPEC t) (v : Val u)
  → {u' : Tm Γ (γ ⇾ β) γ} (c' : send u' InPEC t) (v' : Val u')
  → u ≡ u'
sendInPEC-unique-tm ⟨⟩ vu ⟨⟩ vu' = refl
sendInPEC-unique-tm ⟨⟩ vu (send c') vu' = ⊥-elim (V¬sendInPEC vu c')
sendInPEC-unique-tm (c ·₁ u) vu (c' ·₁ .u) vu' rewrite sendInPEC-unique-tm c vu c' vu' = refl
sendInPEC-unique-tm (c ·₁ u) vu (v ·₂ c') vu' = ⊥-elim (V¬sendInPEC v c)
sendInPEC-unique-tm (v ·₂ c) vu (c' ·₁ _) vu' = ⊥-elim (V¬sendInPEC v c')
sendInPEC-unique-tm (v ·₂ c) vu (v' ·₂ c') vu' rewrite sendInPEC-unique-tm c vu c' vu' = refl
sendInPEC-unique-tm (suc c) vu (suc c') vu' rewrite sendInPEC-unique-tm c vu c' vu' = refl
sendInPEC-unique-tm (case c z s) vu (case c' .z .s) vu' rewrite sendInPEC-unique-tm c vu c' vu' = refl
sendInPEC-unique-tm (send c) vu ⟨⟩ vu' = ⊥-elim (V¬sendInPEC vu' c)
sendInPEC-unique-tm (send c) vu (send c') vu' rewrite sendInPEC-unique-tm c vu c' vu' = refl

sendInPEC-unique' : {t : Tm Γ ε α} {u : Tm Γ (γ ⇾ β) γ}
  → (c c' : send u InPEC t) (v : Val u)
  → c ≡ c'
sendInPEC-unique' ⟨⟩ ⟨⟩ vu = refl
sendInPEC-unique' ⟨⟩ (send c') vu = ⊥-elim (V¬sendInPEC vu c')
sendInPEC-unique' (c ·₁ u) (c' ·₁ .u) vu rewrite sendInPEC-unique' c c' vu = refl
sendInPEC-unique' (c ·₁ u) (v ·₂ c') vu = ⊥-elim (V¬sendInPEC v c)
sendInPEC-unique' (v ·₂ c) (c' ·₁ _) vu = ⊥-elim (V¬sendInPEC v c')
sendInPEC-unique' (v ·₂ c) (v' ·₂ c') vu rewrite V-unique v v' | sendInPEC-unique' c c' vu = refl
sendInPEC-unique' (suc c) (suc c') vu rewrite sendInPEC-unique' c c' vu = refl
sendInPEC-unique' (case c z s) (case c' .z .s) vu rewrite sendInPEC-unique' c c' vu = refl
sendInPEC-unique' (send c) ⟨⟩ vu = ⊥-elim (V¬sendInPEC vu c)
sendInPEC-unique' (send c) (send c') vu rewrite sendInPEC-unique' c c' vu = refl

sendInPEC-unique : {t : Tm Γ ε α}
  → {u : Tm Γ (γ ⇾ β) γ} (c : send u InPEC t) (v : Val u)
  → {u' : Tm Γ (δ ⇾ β) δ} (c' : send u' InPEC t) (v' : Val u')
  → c ≅ c'
sendInPEC-unique c v c' v'
  with refl ← sendInPEC-unique-ty c v c' v'
  with refl ← sendInPEC-unique-tm c v c' v'
  with refl ← V-unique v v'
  with refl ← sendInPEC-unique' c c' v
  = hrefl

⟶-deterministic : {t s u : Tm Γ ε α} → t ⟶ s → t ⟶ u → s ≡ u
⟶-deterministic (app v) (app v') rewrite V-unique v v' = refl
⟶-deterministic (run-value v) (run-value v') rewrite V-unique v v' = refl
⟶-deterministic (run-send c v) (run-send c' v')
  with refl ← sendInPEC-unique-ty c v c' v'
  with refl ← sendInPEC-unique-tm c v c' v'
  with refl ← V-unique v v'
  with refl ← sendInPEC-unique' c c' v
  = refl
⟶-deterministic case-zero case-zero = refl
⟶-deterministic (case-suc v) (case-suc v') rewrite V-unique v v' = refl
⟶-deterministic unroll unroll = refl
⟶-deterministic (cong-·₁ t⟶s) (cong-·₁ t⟶u) rewrite ⟶-deterministic t⟶s t⟶u = refl
⟶-deterministic (cong-·₂ _ t⟶s) (cong-·₂ _ t⟶u) rewrite ⟶-deterministic t⟶s t⟶u = refl
⟶-deterministic (cong-send t⟶s) (cong-send t⟶u) rewrite ⟶-deterministic t⟶s t⟶u = refl
⟶-deterministic (cong-run t⟶s) (cong-run t⟶u) rewrite ⟶-deterministic t⟶s t⟶u = refl
⟶-deterministic (cong-suc t⟶s) (cong-suc t⟶u) rewrite ⟶-deterministic t⟶s t⟶u = refl
⟶-deterministic (cong-case t⟶s) (cong-case t⟶u) rewrite ⟶-deterministic t⟶s t⟶u = refl
⟶-deterministic (app v) (cong-·₂ _ t⟶u) = ⊥-elim (V¬⟶ v t⟶u)
⟶-deterministic (cong-·₂ _ t⟶s) (app v) = ⊥-elim (V¬⟶ v t⟶s)
⟶-deterministic (run-value v) (run-send c _) = ⊥-elim (V¬sendInPEC v c)
⟶-deterministic (run-send c _) (run-value v) = ⊥-elim (V¬sendInPEC v c)
⟶-deterministic (run-value v) (cong-run t⟶u) = ⊥-elim (V¬⟶ v t⟶u)
⟶-deterministic (cong-run t⟶s) (run-value v) = ⊥-elim (V¬⟶ v t⟶s)
⟶-deterministic (run-send c v) (cong-run t⟶u) = ⊥-elim (sendInPEC¬⟶ v c t⟶u)
⟶-deterministic (cong-run t⟶s) (run-send c v) = ⊥-elim (sendInPEC¬⟶ v c t⟶s)
⟶-deterministic (case-suc v) (cong-case t⟶u) = ⊥-elim (V¬⟶ (suc v) t⟶u)
⟶-deterministic (cong-case t⟶s) (case-suc v) = ⊥-elim (V¬⟶ (suc v) t⟶s)
⟶-deterministic (cong-·₁ t⟶s) (cong-·₂ v t⟶u) = ⊥-elim (V¬⟶ v t⟶s)
⟶-deterministic (cong-·₂ v t⟶s) (cong-·₁ t⟶u) = ⊥-elim (V¬⟶ v t⟶u)

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
