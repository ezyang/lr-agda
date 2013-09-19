open import Preliminaries
open import STLC
open import STLC-CBV

module STLC-CBV-Normalization where

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

  mutual
    bwd-red : {τ : Tp} {e e' : [] ⊢ τ} → (e ↦ e') → WN τ e' → WN τ e
    bwd-red e↦e' ((v , vv , e'↦*v) , WN'τ[e']) =
      (v , vv , Step e↦e' e'↦*v) , bwd-red' e↦e' WN'τ[e']

    bwd-red' : {τ : Tp} {e e' : [] ⊢ τ} → (e ↦ e') → WN' τ e' → WN' τ e
    bwd-red' {bool} _ _ = <>
    bwd-red' {τ₁ ⇒ τ₂} e↦e' WN'τ[e'] = λ e₁ WNτ₁[e₁] →
      bwd-red (Step/app1 e↦e') (WN'τ[e'] e₁ WNτ₁[e₁])

  bwd-red* : {τ : Tp} {e e'' : [] ⊢ τ} → (e ↦* e'') → WN τ e'' → WN τ e
  bwd-red* Done wn = wn
  bwd-red* (Step x p) wn = bwd-red x (bwd-red* p wn)

  -- Forward reduction requires determinacy

  BackStep : {τ : Tp} {e e' v : [] ⊢ τ} → (e ↦ e') → value v → (e ↦* v) → (e' ↦* v)
  BackStep (Step/here ()) Value/true Done
  BackStep (Step/here ()) Value/false Done
  BackStep (Step/here ()) Value/lam Done
  BackStep (Step/app1 p) () Done
  BackStep (Step/app2 p) () Done
  BackStep (Step/if-cond p) () Done
  BackStep p _ (Step p' _) with det-↦ p p'
  BackStep _ _ (Step _ ps) | Refl = ps

  mutual
    fwd-red : {τ : Tp} {e e' : [] ⊢ τ} → (e ↦ e') → WN τ e → WN τ e'
    fwd-red e↦e' ((v , vv , e↦*v) , WN'τ[e]) =
      (v , vv , BackStep e↦e' vv e↦*v) , fwd-red' e↦e' WN'τ[e]

    fwd-red' : {τ : Tp} {e e' : [] ⊢ τ} → (e ↦ e') → WN' τ e → WN' τ e'
    fwd-red' {bool} _ _ = <>
    fwd-red' {τ₁ ⇒ τ₂} e↦e' WN'τ[e] = λ e₁ WNτ₁[e₁] →
      fwd-red (Step/app1 e↦e') (WN'τ[e] e₁ WNτ₁[e₁])

  fwd-red* : {τ : Tp} {e e'' : [] ⊢ τ} → (e ↦* e'') → WN τ e → WN τ e''
  fwd-red* Done WNτ[e] = WNτ[e]
  fwd-red* (Step e↦e' e'↦*e'') WNτ[e] = fwd-red* e'↦*e'' (fwd-red e↦e' WNτ[e])

  fund : {Γ : Ctx} {τ : Tp} {γ : [] ⊢c Γ} 
       → (e : Γ ⊢ τ)
       → WNc Γ γ
       → WN τ (subst γ e)
  fund #t γ⊨Γ = (#t , Value/true , Done) , <>
  fund #f γ⊨Γ = (#f , Value/false , Done) , <>
  fund (if e₁ then e₂ else e₃) γ⊨Γ with fund e₁ γ⊨Γ
  fund (if e₁ then e₂ else e₃) γ⊨Γ | (.#t , Value/true , e₁↦*v) , <> =
    bwd-red* (lifts Step/if-cond e₁↦*v) (bwd-red (Step/here Step/if-true) (fund e₂ γ⊨Γ))
  fund (if e₁ then e₂ else e₃) γ⊨Γ | (.#f , Value/false , e₁↦*v) , <> =
    bwd-red* (lifts Step/if-cond e₁↦*v) (bwd-red (Step/here Step/if-false) (fund e₃ γ⊨Γ))
  fund (var i0) γ⊨Γ = snd γ⊨Γ
  fund (var (iS x)) γ⊨Γ = fund (var x) (fst γ⊨Γ)
  fund {τ = τ₁ ⇒ τ₂} {γ = γ} (lam e) γ⊨Γ = (lam (subst (addvar γ) e) , Value/lam , Done) , (λ e₁ WNτ₁[e₁] →
    -- Proof idea: (lam e) e₁ ↦* (lam e) v₁ ↦ e[v₁/x]
    -- Go forwards and then backwards
    let (v₁ , e₁⇓v₁) , WN'τ₁[e₁] = WNτ₁[e₁]
        WNτ₁[v₁] = fwd-red* (snd e₁⇓v₁) WNτ₁[e₁]
        IH = fund e (γ⊨Γ , WNτ₁[v₁])
        WNτ₂[γ[e[v₁/x]]] = transport (WN τ₂) (subst-compose1 γ v₁ e) IH
    in bwd-red* (lifts Step/app2 (snd e₁⇓v₁))
      (bwd-red  (Step/here (Step/β (fst e₁⇓v₁))) WNτ₂[γ[e[v₁/x]]]))
  fund {γ = γ} (app e₁ e₂) γ⊨Γ = snd IH₁ (subst γ e₂) IH₂
    where
      IH₁ = fund e₁ γ⊨Γ
      IH₂ = fund e₂ γ⊨Γ

  corollary : {τ : Tp} → (e : [] ⊢ τ) → e ⇓
  corollary e = transport (λ e' → e' ⇓) (! subst-id) (fst (fund e <>))
