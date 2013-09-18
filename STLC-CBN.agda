open import Preliminaries
open import STLC

-- Technically, these easily turn into strong normalization proofs, by
-- determinacy of the operational semantics.

module STLC-CBN where

  module OpSemCBN where
    -- step relation
    data _↦_ : {τ : Tp} → [] ⊢ τ → [] ⊢ τ → Set where
      Step/app  :{τ1 τ2 : Tp} {e e' : [] ⊢ τ1 ⇒ τ2} {e1 : [] ⊢ τ1}
             → e ↦ e'
             → (app e e1) ↦ (app e' e1)
      Step/β : {τ1 τ2 : Tp} {e : [] ,, τ1 ⊢ τ2} {e1 : [] ⊢ τ1}
             → (app (lam e) e1) ↦ subst1 e1 e 
      Step/if-cond : {τ : Tp} {e e' : [] ⊢ bool} {e₁ e₂ : [] ⊢ τ}
             → e ↦ e'
             → if e then e₁ else e₂ ↦ if e' then e₁ else e₂
      Step/if-true : {τ : Tp} {e e' : [] ⊢ τ}
             → if #t then e else e' ↦ e
      Step/if-false : {τ : Tp} {e e' : [] ⊢ τ}
             → if #f then e else e' ↦ e'

    -- reflexive/transitive closure
    data _↦*_ : {τ : Tp} → [] ⊢ τ → [] ⊢ τ → Set where
      Done : {τ : Tp} {e : [] ⊢ τ} → e ↦* e
      Step : {τ : Tp} {e1 e2 e3 : [] ⊢ τ} 
           → e1 ↦ e2  →  e2 ↦* e3
           → e1 ↦* e3

    Append : {τ : Tp} {e1 e2 e3 : [] ⊢ τ} 
           → e1 ↦* e2  →  e2 ↦* e3
           → e1 ↦* e3
    Append Done g = g
    Append (Step x f) g = Step x (Append f g)

    _⇓_ : {τ : Tp} → [] ⊢ τ → [] ⊢ τ → Set
    e ⇓ z = value z × e ↦* z

    _⇓ : {τ : Tp} → [] ⊢ τ → Set
    e ⇓ = Σ (λ z → e ⇓ z)

    lifts : {τ τ' : Tp} {E : [] ⊢ τ → [] ⊢ τ'} → ({e e' : [] ⊢ τ} → e ↦ e' → E e ↦ E e') → {e e' : [] ⊢ τ}
      → (e ↦* e') → (E e ↦* E e')
    lifts Step/rule Done = Done
    lifts Step/rule (Step e↦e' e'↦*e'') = Step (Step/rule e↦e') (lifts Step/rule e'↦*e'')

  module WeakNormalizationCBN where

    open OpSemCBN

    mutual
      WN' : (τ : Tp) → [] ⊢ τ → Set
      WN' bool e = Unit
      WN' (τ1 ⇒ τ2) e = (e1 : [] ⊢ τ1) → WN τ1 e1 → WN τ2 (app e e1)

      WN : (τ : Tp) → [] ⊢ τ → Set
      WN τ e = e ⇓ × WN' τ e

    WNc : (Γ : Ctx) → [] ⊢c Γ → Set
    WNc [] γ = Unit
    WNc (τ :: Γ) (γ , e) = WNc Γ γ × WN τ e

    open RenamingAndSubstitution using (addvar)
    --- you will want to use
    --    addvar : {Γ Γ' : Ctx} {τ : Tp} → Γ ⊢c Γ' → (Γ ,, τ) ⊢c (Γ' ,, τ)

    -- These lemmas show up in the CBV case, and are proved exactly the
    -- same way. However, CBN does NOT need a fwd-red lemma.
    bwd-red : {τ : Tp} {e e' : [] ⊢ τ} → e ↦ e' → WN τ e' → WN τ e
    bwd-red {bool}      e↦e' ((z , vz , e'↦z) , <>) =
      (z , vz , Step e↦e' e'↦z) , <>
    bwd-red {τ₁ ⇒ τ₂} e↦e' ((z , vz , e'↦z) , WN'τ₁⇒τ₂[e']) =
      (z , vz , Step e↦e' e'↦z) , (λ e₁ WNτ₁[e₁] → bwd-red (Step/app e↦e') (WN'τ₁⇒τ₂[e'] e₁ WNτ₁[e₁]))

    bwd-red* : {τ : Tp} {e e' : [] ⊢ τ} → (e ↦* e') → WN τ e' → WN τ e
    bwd-red* Done wn = wn
    bwd-red* {τ} (Step x p) wn = bwd-red x (bwd-red* p wn)

    fund : {Γ : Ctx} {τ : Tp} {γ : [] ⊢c Γ} 
         → (e : Γ ⊢ τ)
         → WNc Γ γ
         → WN τ (subst γ e)
    fund #t γ⊨Γ = (#t , Value/true , Done) , <>
    fund #f γ⊨Γ = (#f , Value/false , Done) , <>
    fund (if e₁ then e₂ else e₃) γ⊨Γ with fund e₁ γ⊨Γ
    fund (if e₁ then e₂ else e₃) γ⊨Γ | (.#t , Value/true , e₁↦*z) , <> =
      bwd-red* (lifts Step/if-cond e₁↦*z) (bwd-red Step/if-true (fund e₂ γ⊨Γ))
    fund (if e₁ then e₂ else e₃) γ⊨Γ | (.#f , Value/false , e₁↦*z) , <> =
      bwd-red* (lifts Step/if-cond e₁↦*z) (bwd-red Step/if-false (fund e₃ γ⊨Γ))
    fund (var i0) γ⊨Γ = snd γ⊨Γ
    fund (var (iS x)) γ⊨Γ = fund (var x) (fst γ⊨Γ)
    fund {γ = γ} (lam {τ2 = τ₂} e) γ⊨Γ = (lam (subst (addvar γ) e) , Value/lam , Done) , λ e₁ WNτ₁[e₁] →
      let IH = fund e (γ⊨Γ , WNτ₁[e₁])
      in bwd-red Step/β (transport (WN τ₂) (subst-compose1 γ e₁ e) IH)
      -- notice we're done after we finish backwards-reducing!
    fund {γ = γ} (app e₁ e₂) γ⊨Γ = snd IH₁ (subst γ e₂) IH₂
      where
        IH₁ = fund e₁ γ⊨Γ
        IH₂ = fund e₂ γ⊨Γ

    corollary : {τ : Tp} → (e : [] ⊢ τ) → e ⇓
    corollary e = transport (λ e' → e' ⇓) (! subst-id) (fst (fund e <>))
