open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Maybe using ( Maybe; just; nothing )
open import Data.Nat using ( ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; cong )
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using ( Star; _◅_ ) renaming ( ε to [] )
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties using ( module StarReasoning )
open import Relation.Nullary using ( ¬_ )
open import Relation.Nullary.Decidable using ( True; toWitness )

infixr 8 ↑_ ↑Val_ ↑PEC_
infixr 7 _⇒_!_
infixl 7 _·_
infixl 5 _,_
infix  5 ƛ_ μ_
infixl 6 _[_] _⟨_⟩
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
  _,_ : Eff → Ty → Eff

data Ctx : Set where
  ∙ : Ctx
  _,_ : Ctx → Ty → Ctx

variable
  Γ Δ : Ctx
  α β γ δ αₕ βₕ : Ty
  ε ε' ε'' εₕ : Eff

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
  delimit : Tm Γ (ε , α) α → Tm Γ ε α
  grab : Tm (Γ , α ⇒ β ! ε) ε β → Tm Γ (ε , β) α

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
ren ρ (μ t) = μ ren (ext ρ) t
ren ρ (delimit t) = delimit (ren ρ t)
ren ρ (grab t) = grab (ren (ext ρ) t)

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
sub σ (μ t) = μ sub (exts σ) t
sub σ (delimit t) = delimit (sub σ t)
sub σ (grab t) = grab (sub (exts σ) t)

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

↑Val_ : {t : Tm Γ ε α} → Val t → Val {Γ = Γ , β} (↑ t)
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
  case : ∀ {n} (c : h InPEC n) (z : Tm Γ ε α) s → h InPEC (case n z s)

_⟨_⟩ : {h : Tm Γ εₕ αₕ} {t : Tm Γ ε α} → h InPEC t → Tm Γ εₕ αₕ → Tm Γ ε α
⟨⟩ ⟨ h' ⟩ = h'
(c ·₁ t) ⟨ h' ⟩ = (c ⟨ h' ⟩) · t
(_·₂_ {t = t} _ c) ⟨ h' ⟩ = t · (c ⟨ h' ⟩)
suc c ⟨ h' ⟩ = suc (c ⟨ h' ⟩)
case c z s ⟨ h' ⟩ = case (c ⟨ h' ⟩) z s

⟨⟩-correct : {h : Tm Γ εₕ αₕ} {t : Tm Γ ε α} (c : h InPEC t)
  → t ≡ c ⟨ h ⟩
⟨⟩-correct ⟨⟩ = refl
⟨⟩-correct (c ·₁ u) = cong (_· u) (⟨⟩-correct c)
⟨⟩-correct (v ·₂ c) = cong (_ ·_) (⟨⟩-correct c)
⟨⟩-correct (suc c) = cong suc (⟨⟩-correct c)
⟨⟩-correct (case c z s) = cong (λ n → case n z s) (⟨⟩-correct c)

renPEC : (ρ : Ren Γ Δ) {h : Tm Γ εₕ αₕ} {t : Tm Γ ε α}
  → h InPEC t
  → ren ρ h InPEC ren ρ t
renPEC ρ ⟨⟩ = ⟨⟩
renPEC ρ (c ·₁ u) = renPEC ρ c ·₁ ren ρ u
renPEC ρ (v ·₂ c) = renVal ρ v ·₂ renPEC ρ c
renPEC ρ (suc c) = suc (renPEC ρ c)
renPEC ρ (case c z s) = case (renPEC ρ c) (ren ρ z) (ren (ext ρ) s)

↑PEC_ : {h : Tm Γ εₕ αₕ} {t : Tm Γ ε α} → h InPEC t → (↑_ {β = β} h) InPEC (↑ t)
↑PEC_ = renPEC suc

--------------------------------------------------------------------------------
-- Reduction rules

-- Preservation holds by construction
data _⟶_ : Tm Γ ε α → Tm Γ ε α → Set where
  app : ∀ {t : Tm (Γ , α) ε β} {u}
    → (v : Val u)
    → (ƛ t) · u ⟶ t [ coe v ]

  case-zero : ∀ {z : Tm Γ ε α} {s}
    → case zero z s ⟶ z

  case-suc : ∀ {n} (v : Val n) {z : Tm Γ ε α} {s}
    → case (suc n) z s ⟶ s [ coe v ]

  delimit-val : {t : Tm Γ (ε , α) α} (v : Val t)
    → delimit t ⟶ coe v

  delimit-grab : ∀ {u : Tm (Γ , α ⇒ β ! ε) ε β} {t} (c : grab u InPEC t)
    → delimit t ⟶ u [ ƛ delimit (↑PEC c ⟨ var zero ⟩) ]

  unroll : {t : Tm (Γ , α ⇒ β ! ε) ε (α ⇒ β ! ε)}
    → μ t ⟶ t [ ƛ (↑ (μ t)) · var zero ]

  cong-·₁ : {t t' : Tm Γ ε (α ⇒ β ! ε)}
    → t ⟶ t'
    → ∀ {u} → t · u ⟶ t' · u

  cong-·₂ : ∀ {t : Tm Γ ε (α ⇒ β ! ε)} (v : Val t) {u u'}
    → u ⟶ u'
    → t · u ⟶ t · u'

  cong-delimit : {t t' : Tm Γ (ε , α) α}
    → t ⟶ t'
    → delimit t ⟶ delimit t'

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
  bare-grab : {u : Tm (∙ , α ⇒ β ! ε) ε β} {t : Tm ∙ (ε , β) γ}
    → grab u InPEC t
    → Progress t

progress : (t : Tm ∙ ε α) → Progress t
progress (ƛ t) = done (ƛ t)
progress (t · u) with progress t
... | step t⟶t' = step (cong-·₁ t⟶t')
... | bare-grab c = bare-grab (c ·₁ u)
... | done (ƛ t') with progress u
...   | step u⟶u' = step (cong-·₂ (ƛ t') u⟶u')
...   | done vu = step (app vu)
...   | bare-grab c = bare-grab ((ƛ t') ·₂ c)
progress (delimit t) with progress t
... | done vt = step (delimit-val vt)
... | step t⟶t' = step (cong-delimit t⟶t')
... | bare-grab c = step (delimit-grab c)
progress (grab t) = bare-grab ⟨⟩
progress zero = done zero
progress (suc t) with progress t
... | done vt = done (suc vt)
... | step t⟶t' = step (cong-suc t⟶t')
... | bare-grab c = bare-grab (suc c)
progress (case n z s) with progress n
... | done zero = step case-zero
... | done (suc vn) = step (case-suc vn)
... | step n⟶n' = step (cong-case n⟶n')
... | bare-grab c = bare-grab (case c z s)
progress (μ t) = step unroll

--------------------------------------------------------------------------------
-- Other properties

V¬⟶ : {v v' : Tm Γ ε α} → Val v → ¬ (v ⟶ v')
V¬⟶ (suc v) (cong-suc v⟶v') = V¬⟶ v v⟶v'

V-unique : {t : Tm Γ ε α} (v v' : Val t) → v ≡ v'
V-unique (ƛ t) (ƛ .t) = refl
V-unique zero zero = refl
V-unique (suc v) (suc v') = cong suc (V-unique v v')

V¬grabInPEC : {u : Tm (Γ , α ⇒ β ! ε) ε β} {v : Tm Γ (ε , β) γ}
  → Val v
  → ¬ (grab u InPEC v)
V¬grabInPEC (suc v) (suc c) = V¬grabInPEC v c

grabInPEC¬⟶ : {u : Tm (Γ , α ⇒ β ! ε) ε β} {t t' : Tm Γ (ε , β) γ}
  → grab u InPEC t
  → ¬ (t ⟶ t')
grabInPEC¬⟶ (c ·₁ u) (cong-·₁ t⟶t') = grabInPEC¬⟶ c t⟶t'
grabInPEC¬⟶ (c ·₁ u) (cong-·₂ v t⟶t') = V¬grabInPEC v c
grabInPEC¬⟶ (v ·₂ c) (app v') = V¬grabInPEC v' c
grabInPEC¬⟶ (v ·₂ c) (cong-·₁ t⟶t') = V¬⟶ v t⟶t'
grabInPEC¬⟶ (v ·₂ c) (cong-·₂ v' t⟶t') = grabInPEC¬⟶ c t⟶t'
grabInPEC¬⟶ (suc c) (cong-suc t⟶t') = grabInPEC¬⟶ c t⟶t'
grabInPEC¬⟶ (case c z s) (case-suc v) = V¬grabInPEC (suc v) c
grabInPEC¬⟶ (case c z s) (cong-case t⟶t') = grabInPEC¬⟶ c t⟶t'

grabInPEC-unique-ty : {t : Tm Γ (ε , α) β}
  → {u : Tm (Γ , γ ⇒ α ! ε) ε α} (c : grab u InPEC t)
  → {u' : Tm (Γ , δ ⇒ α ! ε) ε α} (c' : grab u' InPEC t)
  → γ ≡ δ
grabInPEC-unique-ty ⟨⟩ ⟨⟩ = refl
grabInPEC-unique-ty (c ·₁ u) (c' ·₁ .u) rewrite grabInPEC-unique-ty c c' = refl
grabInPEC-unique-ty (c ·₁ u) (v ·₂ c') = ⊥-elim (V¬grabInPEC v c)
grabInPEC-unique-ty (v ·₂ c) (c' ·₁ _) = ⊥-elim (V¬grabInPEC v c')
grabInPEC-unique-ty (v ·₂ c) (v' ·₂ c') rewrite grabInPEC-unique-ty c c' = refl
grabInPEC-unique-ty (suc c) (suc c') rewrite grabInPEC-unique-ty c c' = refl
grabInPEC-unique-ty (case c z s) (case c' .z .s) rewrite grabInPEC-unique-ty c c' = refl

grabInPEC-unique-tm : {t : Tm Γ (ε , α) β}
  → {u : Tm (Γ , γ ⇒ α ! ε) ε α} (c : grab u InPEC t)
  → {u' : Tm (Γ , γ ⇒ α ! ε) ε α} (c' : grab u' InPEC t)
  → u ≡ u'
grabInPEC-unique-tm ⟨⟩ ⟨⟩ = refl
grabInPEC-unique-tm (c ·₁ u) (c' ·₁ .u) rewrite grabInPEC-unique-tm c c' = refl
grabInPEC-unique-tm (c ·₁ u) (v ·₂ c') = ⊥-elim (V¬grabInPEC v c)
grabInPEC-unique-tm (v ·₂ c) (c' ·₁ _) = ⊥-elim (V¬grabInPEC v c')
grabInPEC-unique-tm (v ·₂ c) (v' ·₂ c') rewrite grabInPEC-unique-tm c c' = refl
grabInPEC-unique-tm (suc c) (suc c') rewrite grabInPEC-unique-tm c c' = refl
grabInPEC-unique-tm (case c z s) (case c' .z .s) rewrite grabInPEC-unique-tm c c' = refl

grabInPEC-unique : {t : Tm Γ (ε , α) β} {u : Tm (Γ , γ ⇒ α ! ε) ε α}
  → (c c' : grab u InPEC t)
  → c ≡ c'
grabInPEC-unique ⟨⟩ ⟨⟩ = refl
grabInPEC-unique (c ·₁ u) (c' ·₁ .u) rewrite grabInPEC-unique c c' = refl
grabInPEC-unique (c ·₁ u) (v ·₂ c') = ⊥-elim (V¬grabInPEC v c)
grabInPEC-unique (v ·₂ c) (c' ·₁ _) = ⊥-elim (V¬grabInPEC v c')
grabInPEC-unique (v ·₂ c) (v' ·₂ c') rewrite grabInPEC-unique c c' | V-unique v v' = refl
grabInPEC-unique (suc c) (suc c') rewrite grabInPEC-unique c c' = refl
grabInPEC-unique (case c z s) (case c' .z .s) rewrite grabInPEC-unique c c' = refl

⟶-deterministic : {t s u : Tm Γ ε α} → t ⟶ s → t ⟶ u → s ≡ u
⟶-deterministic (app {t = t} v) (app v') rewrite V-unique v v' = refl
⟶-deterministic (delimit-val v) (delimit-val v') rewrite V-unique v v' = refl
-- Is there a better way to do this?
⟶-deterministic (delimit-grab c) (delimit-grab c')
  with refl ← grabInPEC-unique-ty c c'
  with refl ← grabInPEC-unique-tm c c'
  with refl ← grabInPEC-unique c c'
  = refl
⟶-deterministic case-zero case-zero = refl
⟶-deterministic (case-suc v) (case-suc v') rewrite V-unique v v' = refl
⟶-deterministic unroll unroll = refl
⟶-deterministic (cong-suc t⟶s) (cong-suc t⟶u) rewrite ⟶-deterministic t⟶s t⟶u = refl
⟶-deterministic (cong-·₁ t⟶s) (cong-·₁ t⟶u) rewrite ⟶-deterministic t⟶s t⟶u = refl
⟶-deterministic (cong-·₂ _ t⟶s) (cong-·₂ _ t⟶u) rewrite ⟶-deterministic t⟶s t⟶u = refl
⟶-deterministic (cong-delimit t⟶s) (cong-delimit t⟶u) = cong delimit (⟶-deterministic t⟶s t⟶u)
⟶-deterministic (cong-case t⟶s) (cong-case t⟶u) rewrite ⟶-deterministic t⟶s t⟶u = refl
⟶-deterministic (app v) (cong-·₂ _ t⟶u) = ⊥-elim (V¬⟶ v t⟶u)
⟶-deterministic (cong-·₂ _ t⟶s) (app v) = ⊥-elim (V¬⟶ v t⟶s)
⟶-deterministic (delimit-val v) (cong-delimit t⟶u) = ⊥-elim (V¬⟶ v t⟶u)
⟶-deterministic (cong-delimit t⟶s) (delimit-val v) = ⊥-elim (V¬⟶ v t⟶s)
⟶-deterministic (delimit-val v) (delimit-grab c) = ⊥-elim (V¬grabInPEC v c)
⟶-deterministic (delimit-grab c) (delimit-val v) = ⊥-elim (V¬grabInPEC v c)
⟶-deterministic (delimit-grab c) (cong-delimit t⟶u) = ⊥-elim (grabInPEC¬⟶ c t⟶u)
⟶-deterministic (cong-delimit t⟶s) (delimit-grab c) = ⊥-elim (grabInPEC¬⟶ c t⟶s)
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

-- delimit (suc (grab k. k (k 0)))
ex : Tm ∙ ι `ℕ
ex = delimit (suc (grab (var# 0 · (var# 0 · zero))))

_ : let open ⟶*-Reasoning in
    eval 10 ex ≡ steps
      (begin
        ex
      ≡⟨⟩
        delimit (suc (grab (var# 0 · (var# 0 · zero))))
      ⟶⟨ delimit-grab (suc ⟨⟩) ⟩
        (var# 0 · (var# 0 · zero)) [ ƛ delimit (suc (var# 0)) ]
      ≡⟨⟩
        (ƛ delimit (suc (var# 0))) · ((ƛ delimit (suc (var# 0))) · zero)
      ⟶⟨ cong-·₂ (ƛ delimit (suc (var# 0))) (app zero) ⟩
        (ƛ delimit (suc (var# 0))) · delimit (suc zero)
      ⟶⟨ cong-·₂ (ƛ delimit (suc (var# 0))) (delimit-val (suc zero)) ⟩
        (ƛ delimit (suc (var# 0))) · suc zero
      ⟶⟨ app (suc zero) ⟩
        delimit (suc (suc zero))
      ⟶⟨ delimit-val (suc (suc (zero))) ⟩
        suc (suc zero)
      ∎)
      (just (suc (suc zero)))
_ = refl

plus : Tm ∙ ι (`ℕ ⇒ `ℕ ⇒ `ℕ ! ι ! ι)
plus = μ ƛ ƛ case (var# 1) (var# 0) (suc (var# 3 · var# 0 · var# 1))

-- Heavy!
-- _ : let open ⟶*-Reasoning in
--     eval 10 (plus · suc zero · suc zero) ≡ steps
--       (begin
--         plus · suc zero · suc zero
--       ⟶⟨ cong-·₁ (cong-·₁ unroll) ⟩
--         (ƛ ƛ case (var# 1) (var# 0) (suc ((ƛ (↑ ↑ ↑ ↑ plus) · var# 0) · var# 0 · var# 1)))
--           · suc zero
--           · suc zero
--       ⟶⟨ cong-·₁ (app (suc zero)) ⟩
--         (ƛ case (suc zero) (var# 0) (suc ((ƛ (↑ ↑ ↑ plus) · var# 0) · var# 0 · var# 1)))
--           · suc zero
--       ⟶⟨ app (suc zero) ⟩
--         case (suc zero) (suc zero) (suc ((ƛ ↑ ↑ plus · var# 0) · var# 0 · suc zero))
--       ⟶⟨ case-suc zero ⟩
--         suc ((ƛ ↑ plus · var# 0) · zero · suc zero)
--       ⟶⟨ cong-suc (cong-·₁ (app zero)) ⟩
--         suc (plus · zero · suc zero)
--       ⟶⟨ cong-suc (cong-·₁ (cong-·₁ unroll)) ⟩
--         suc (
--           (ƛ ƛ case (var# 1) (var# 0) (suc ((ƛ (↑ ↑ ↑ ↑ plus) · var# 0) · var# 0 · var# 1)))
--           · zero
--           · suc zero)
--       ⟶⟨ cong-suc (cong-·₁ (app zero)) ⟩
--         suc ((ƛ case zero (var# 0) (suc ((ƛ (↑ ↑ ↑ plus) · var# 0) · var# 0 · var# 1))) · suc zero)
--       ⟶⟨ cong-suc (app (suc zero)) ⟩
--         suc (case zero (suc zero) (suc ((ƛ ↑ ↑ plus · var# 0) · var# 0 · suc zero)))
--       ⟶⟨ cong-suc case-zero ⟩
--         suc (suc zero)
--       ∎)
--       (just (suc (suc zero)))
-- _ = refl
