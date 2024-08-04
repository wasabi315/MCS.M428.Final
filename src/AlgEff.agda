open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Maybe using ( Maybe; just; nothing )
open import Data.Nat using ( ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s )
open import Data.Product using ( _×_ )
open import Data.Sum using ( inj₁; inj₂ )
open import Data.Unit using ( ⊤ )
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using ( Star; _◅_ ) renaming ( ε to [] )
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties using ( module StarReasoning )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; cong )
open import Relation.Nullary using ( ¬_ )
open import Relation.Nullary.Decidable using ( True; toWitness; Dec; yes; no; ¬?; _⊎-dec_ ) renaming ( map′ to mapDec )

--------------------------------------------------------------------------------
-- Signatures

data PTy : Set where
  `ℕ : PTy

record Sig : Set₁ where
  field
    Op : Set
    decEq : (x y : Op) → Dec (x ≡ y)
    Dom : Op → PTy
    Cod : Op → PTy

-- Fix a signature
module M (Σ : Sig) where
  open Sig Σ

--------------------------------------------------------------------------------
-- Syntax

  infixr 8 ↑_ ↑H_ ↑Val_ ↑PEC_
  infixr 7 _⇒_!_
  infixl 7 _·_ _!_
  infixl 6 _[_] _⟨_⟩
  infixl 5 _,_
  infix  5 ƛ_ μ_
  infix  4 _∋_
  infix  2 _⟶_ _⟶*_

  data Ty : Set
  data Eff : Set
  Distinct : Op → Eff → Set

  data Ty where
    `ℕ : Ty
    _⇒_!_ : Ty → Ty → Eff → Ty

  data Eff where
    ι : Eff
    cons : (ε : Eff) (op : Op) → Distinct op ε → Eff

  pattern _,#_ ε op = cons ε op _

  Distinct op ι = ⊤
  Distinct op (ε ,# op') = True (¬? (decEq op op')) × Distinct op ε

  data Ctx : Set where
    ∙ : Ctx
    _,_ : Ctx → Ty → Ctx

  pure : PTy → Ty
  pure `ℕ = `ℕ

  Dom' Cod' : Op → Ty
  Dom' op = pure (Dom op)
  Cod' op = pure (Cod op)

  variable
    op op' : Op
    Γ Δ : Ctx
    α β γ αₕ : Ty
    ε ε' εₕ : Eff

  data _∋_ : Ctx → Ty → Set where
    zero : Γ , α ∋ α
    suc : Γ ∋ α → Γ , β ∋ α

  data _∋ₑ_ : Eff → Op → Set where
    zero : ∀ {p} → cons ε op p ∋ₑ op
    suc : ∀ {p} → ε ∋ₑ op → cons ε op' p ∋ₑ op

  data Tm : Ctx → Eff → Ty → Set
  record Handler (Γ : Ctx) (ε ε' : Eff) (α β : Ty) : Set

  data Tm where
    var : Γ ∋ α → Tm Γ ε α
    ƛ_ : Tm (Γ , α) ε β → Tm Γ ε' (α ⇒ β ! ε)
    _·_ : Tm Γ ε (α ⇒ β ! ε) → Tm Γ ε α → Tm Γ ε β
    zero : Tm Γ ε `ℕ
    suc : Tm Γ ε `ℕ → Tm Γ ε `ℕ
    case : Tm Γ ε `ℕ → Tm Γ ε α → Tm (Γ , `ℕ) ε α → Tm Γ ε α
    μ_ : Tm (Γ , α ⇒ β ! ε) ε (α ⇒ β ! ε) → Tm Γ ε (α ⇒ β ! ε)
    _!_ : ε ∋ₑ op → Tm Γ ε (Dom' op) → Tm Γ ε (Cod' op)
    handle : Tm Γ ε α → Handler Γ ε ε' α β → Tm Γ ε' β

  record Handler Γ ε ε' α β where
    inductive
    no-eta-equality
    field
      valh : Tm (Γ , α) ε' β
      effh : ε ∋ₑ op → Tm (Γ , Dom' op , Cod' op ⇒ β ! ε') ε' β

  open Handler public

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

  _∋ₑ?_ : ∀ ε op → Dec (ε ∋ₑ op)
  ι ∋ₑ? op = no λ ()
  cons ε op _ ∋ₑ? op' = mapDec
    (λ { (inj₁ refl) → zero; (inj₂ p) → suc p })
    (λ { zero → inj₁ refl; (suc p) → inj₂ p })
    (decEq op op' ⊎-dec (ε ∋ₑ? op'))

  _!#_ : ∀ op {op∈ₑε : True (ε ∋ₑ? op)} → Tm Γ ε (Dom' op) → Tm Γ ε (Cod' op)
  _!#_ _ {op∈ₑε} = _!_ (toWitness op∈ₑε)

--------------------------------------------------------------------------------
-- Renaming and Substitution

  Ren : Ctx → Ctx → Set
  Ren Γ Δ = ∀ {α} → Γ ∋ α → Δ ∋ α

  ext : Ren Γ Δ → Ren (Γ , α) (Δ , α)
  ext ρ zero = zero
  ext ρ (suc i) = suc (ρ i)

  ren : Ren Γ Δ → Tm Γ ε α → Tm Δ ε α
  renH : Ren Γ Δ → Handler Γ ε ε' α β → Handler Δ ε ε' α β

  ren ρ (var i) = var (ρ i)
  ren ρ (ƛ t) = ƛ ren (ext ρ) t
  ren ρ (t · u) = ren ρ t · ren ρ u
  ren ρ zero = zero
  ren ρ (suc t) = suc (ren ρ t)
  ren ρ (case n z s) = case (ren ρ n) (ren ρ z) (ren (ext ρ) s)
  ren ρ (μ t) = μ (ren (ext ρ) t)
  ren ρ (i ! t) = i ! ren ρ t
  ren ρ (handle t h) = handle (ren ρ t) (renH ρ h)

  valh (renH ρ h) = ren (ext ρ) (valh h)
  effh (renH ρ h) op = ren (ext (ext ρ)) (effh h op)

  ↑_ : Tm Γ ε α → Tm (Γ , β) ε α
  ↑_ = ren suc

  ↑H_ : Handler Γ ε ε' α β → Handler (Γ , γ) ε ε' α β
  ↑H_ = renH suc

  Sub : Ctx → Ctx → Set
  Sub Γ Δ = ∀ {α} → Γ ∋ α → (∀ {ε} → Tm Δ ε α)

  exts : Sub Γ Δ → Sub (Γ , α) (Δ , α)
  exts σ zero = var zero
  exts σ (suc i) = ↑ (σ i)

  sub : Sub Γ Δ → Tm Γ ε α → Tm Δ ε α
  subH : Sub Γ Δ → Handler Γ ε ε' α β → Handler Δ ε ε' α β

  sub σ (var i) = σ i
  sub σ (ƛ t) = ƛ sub (exts σ) t
  sub σ (t · u) = sub σ t · sub σ u
  sub σ zero = zero
  sub σ (suc t) = suc (sub σ t)
  sub σ (case n z s) = case (sub σ n) (sub σ z) (sub (exts σ) s)
  sub σ (μ t) = μ (sub (exts σ) t)
  sub σ (i ! t) = i ! sub σ t
  sub σ (handle t h) = handle (sub σ t) (subH σ h)

  valh (subH σ h) = sub (exts σ) (valh h)
  effh (subH σ h) op = sub (exts (exts σ)) (effh h op)

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
    suc : {t : Tm Γ ε `ℕ} → h InPEC t → h InPEC (suc t)
    case : ∀ {n} (c : h InPEC n) (z : Tm Γ ε α) s → h InPEC case n z s
    _!_ : (i : ε ∋ₑ op) {t : Tm Γ ε (Dom' op)} → h InPEC t → h InPEC (i ! t)

  _⟨_⟩ : {h : Tm Γ εₕ αₕ} {t : Tm Γ ε α} → h InPEC t → Tm Γ εₕ αₕ → Tm Γ ε α
  ⟨⟩ ⟨ h' ⟩ = h'
  (c ·₁ t) ⟨ h' ⟩ = (c ⟨ h' ⟩) · t
  (_·₂_ {t = t} _ c) ⟨ h' ⟩ = t · (c ⟨ h' ⟩)
  suc c ⟨ h' ⟩ = suc (c ⟨ h' ⟩)
  case c z s ⟨ h' ⟩ = case (c ⟨ h' ⟩) z s
  (i ! c) ⟨ h' ⟩ = i ! (c ⟨ h' ⟩)

  ⟨⟩-correct : {h : Tm Γ εₕ αₕ} {t : Tm Γ ε α} (c : h InPEC t)
    → t ≡ c ⟨ h ⟩
  ⟨⟩-correct ⟨⟩ = refl
  ⟨⟩-correct (c ·₁ u) = cong (_· u) (⟨⟩-correct c)
  ⟨⟩-correct (v ·₂ c) = cong (_ ·_) (⟨⟩-correct c)
  ⟨⟩-correct (suc c) = cong suc (⟨⟩-correct c)
  ⟨⟩-correct (case c z s) = cong (λ n → case n z s) (⟨⟩-correct c)
  ⟨⟩-correct (i ! c) = cong (i !_) (⟨⟩-correct c)

  renPEC : (ρ : Ren Γ Δ) {h : Tm Γ εₕ αₕ} {t : Tm Γ ε α}
    → h InPEC t
    → ren ρ h InPEC ren ρ t
  renPEC ρ ⟨⟩ = ⟨⟩
  renPEC ρ (c ·₁ u) = renPEC ρ c ·₁ ren ρ u
  renPEC ρ (v ·₂ c) = renVal ρ v ·₂ renPEC ρ c
  renPEC ρ (suc c) = suc (renPEC ρ c)
  renPEC ρ (case c z s) = case (renPEC ρ c) (ren ρ z) (ren (ext ρ) s)
  renPEC ρ (i ! c) = i ! renPEC ρ c

  ↑PEC_ : {h : Tm Γ εₕ αₕ} {t : Tm Γ ε α} → h InPEC t → (↑_ {β = β} h) InPEC (↑ t)
  ↑PEC_ = renPEC suc

--------------------------------------------------------------------------------
-- Reduction rules

  -- Preservation holds by construction
  data _⟶_ : Tm Γ ε α → Tm Γ ε α → Set where
    app : ∀ {t : Tm (Γ , α) ε β} {u}
      → (v : Val u)
      → (ƛ t) · u ⟶ t [ coe v ]

    handle-value : ∀ {t} (v : Val t) {h : Handler Γ ε ε' α β}
      → handle t h ⟶ valh h [ coe v ]

    handle-! : ∀ {i : ε ∋ₑ op} {t u}
      → (c : (i ! u) InPEC t)
      → (v : Val u)
      → {h : Handler Γ ε ε' α β}
      → handle t h ⟶ effh h i [ ƛ handle (↑PEC ↑PEC c ⟨ var# 0 ⟩) (↑H ↑H h) ] [ coe v ]

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

    cong-! : {i : ε ∋ₑ op} {t t' : Tm Γ ε (Dom' op)}
      → t ⟶ t'
      → (i ! t) ⟶ (i ! t')

    cong-handle : ∀ {t t'}
      → t ⟶ t'
      → {h : Handler Γ ε ε' α β} → handle t h ⟶ handle t' h

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
    bare-! : {i : ε ∋ₑ op} {u : Tm ∙ ε (Dom' op)} {t : Tm ∙ ε γ}
      → (c : (i ! u) InPEC t)
      → Val u
      → Progress t

  progress : (t : Tm ∙ ε α) → Progress t
  progress (ƛ t) = done (ƛ t)
  progress (t · u) with progress t
  ... | step t⟶t' = step (cong-·₁ t⟶t')
  ... | bare-! c v = bare-! (c ·₁ u) v
  ... | done (ƛ t') with progress u
  ...   | step u⟶u' = step (cong-·₂ (ƛ t') u⟶u')
  ...   | bare-! c v = bare-! ((ƛ t') ·₂ c) v
  ...   | done vu = step (app vu)
  progress (i ! t) with progress t
  ... | step t⟶t' = step (cong-! t⟶t')
  ... | done vt = bare-! ⟨⟩ vt
  ... | bare-! c v = bare-! (i ! c) v
  progress (handle t h) with progress t
  ... | step t⟶t' = step (cong-handle t⟶t')
  ... | done vt = step (handle-value vt)
  ... | bare-! c v = step (handle-! c v)
  progress zero = done zero
  progress (suc t) with progress t
  ... | step t⟶t' = step (cong-suc t⟶t')
  ... | done vt = done (suc vt)
  ... | bare-! c v = bare-! (suc c) v
  progress (case n z s) with progress n
  ... | step n⟶n' = step (cong-case n⟶n')
  ... | done zero = step case-zero
  ... | done (suc vn) = step (case-suc vn)
  ... | bare-! c v = bare-! (case c z s) v
  progress (μ t) = step unroll

--------------------------------------------------------------------------------
-- Other Properties

  V¬⟶ : {v v' : Tm Γ ε α} → Val v → ¬ (v ⟶ v')
  V¬⟶ (suc v) (cong-suc v⟶v') = V¬⟶ v v⟶v'

  V-unique : {t : Tm Γ ε α} (v v' : Val t) → v ≡ v'
  V-unique (ƛ t) (ƛ .t) = refl
  V-unique zero zero = refl
  V-unique (suc v) (suc v') = cong suc (V-unique v v')

  -- ⟶-deterministic : {t s u : Tm Γ ε α} → t ⟶ s → t ⟶ u → s ≡ u
  -- ⟶-deterministic (app {t = t} v) (app v') = cong (λ u → t [ coe u ]) (V-unique v v')
  -- ⟶-deterministic (β-run₁ v) (β-run₁ v') = cong coe (V-unique v v')
  -- ⟶-deterministic (β-run₂ c v) (β-run₂ c' v') = {!   !}
  -- ⟶-deterministic β-zero β-zero = refl
  -- ⟶-deterministic (β-suc {u = t} v) (β-suc v') = cong (λ u → t [ coe u ]) (V-unique v v')
  -- ⟶-deterministic (cong-·₁ t⟶s) (cong-·₁ t⟶u) = cong (_· _) (⟶-deterministic t⟶s t⟶u)
  -- ⟶-deterministic (cong-·₂ _ t⟶s) (cong-·₂ _ t⟶u) = cong (_ ·_) (⟶-deterministic t⟶s t⟶u)
  -- ⟶-deterministic (cong-! t⟶s) (cong-! t⟶u) = cong send (⟶-deterministic t⟶s t⟶u)
  -- ⟶-deterministic (cong-handle {u = u} t⟶s) (cong-handle t⟶u) = cong (flip run u) (⟶-deterministic t⟶s t⟶u)
  -- ⟶-deterministic (cong-suc t⟶s) (cong-suc t⟶u) = cong suc (⟶-deterministic t⟶s t⟶u)
  -- ⟶-deterministic (cong-case t⟶s) (cong-case t⟶u) = cong (case _ _) (⟶-deterministic t⟶s t⟶u)
  -- ⟶-deterministic (app v) (cong-·₂ _ t⟶u) = ⊥-elim (V¬⟶ v t⟶u)
  -- ⟶-deterministic (cong-·₂ _ t⟶s) (app v) = ⊥-elim (V¬⟶ v t⟶s)
  -- ⟶-deterministic (β-run₁ v) (β-run₂ c _) = ⊥-elim (V¬⟨send⟩ v c)
  -- ⟶-deterministic (β-run₂ c _) (β-run₁ v) = ⊥-elim (V¬⟨send⟩ v c)
  -- ⟶-deterministic (β-run₁ v) (cong-handle t⟶u) = ⊥-elim (V¬⟶ v t⟶u)
  -- ⟶-deterministic (cong-handle t⟶s) (β-run₁ v) = ⊥-elim (V¬⟶ v t⟶s)
  -- ⟶-deterministic (β-run₂ c v) (cong-handle t⟶u) = ⊥-elim (⟨send⟩¬⟶ v c t⟶u)
  -- ⟶-deterministic (cong-handle t⟶s) (β-run₂ c v) = ⊥-elim (⟨send⟩¬⟶ v c t⟶s)
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

open Sig

data ExOp : Set where
  op1 : ExOp

exSig : Sig
Op exSig = ExOp
decEq exSig op1 op1 = yes refl
Dom exSig op1 = `ℕ
Cod exSig op1 = `ℕ

open M exSig

-- {return x. x} ⊎ {op1 x k. k (k x)}
exHandler : Handler ∙ (ι ,# op1) ι `ℕ `ℕ
valh exHandler = var# 0
effh exHandler zero = var# 0 · (var# 0 · var# 1)

-- handle (suc (op1 0)) exHandler
ex : Tm ∙ ι `ℕ
ex = handle (suc (op1 !# zero)) exHandler

_ : let open ⟶*-Reasoning in
    eval 10 ex ≡ steps
      (begin
        handle (suc (op1 !# zero)) exHandler
      ⟶⟨ handle-! (suc ⟨⟩) zero ⟩
        effh exHandler zero
          [ ƛ handle (suc (var# 0)) (↑H ↑H exHandler) ]
          [ zero ]
      ≡⟨⟩
        (ƛ handle (suc (var# 0)) _) ·
          ((ƛ handle (suc (var# 0)) _) · zero)
      ⟶⟨ cong-·₂ (ƛ handle (suc (var# 0)) _) (app zero) ⟩
        (ƛ handle (suc (var# 0)) _) · handle (suc zero) _
      ⟶⟨ cong-·₂ (ƛ handle (suc (var# 0)) _) (handle-value (suc zero)) ⟩
        (ƛ handle (suc (var# 0)) _) · suc zero
      ⟶⟨ app (suc zero) ⟩
        handle (suc (suc zero)) _
      ⟶⟨ handle-value (suc (suc zero)) ⟩
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
