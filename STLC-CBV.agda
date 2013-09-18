open import Preliminaries
open import STLC

-- Notation conventions: subscript numbers used for *positional* differences
-- (they are not expected to have the same types) whereas ticks are used to
-- indicate 'morally equivalent' terms, which are expected to be related in some
-- way (e.g. 'reduces to' or 'equivalent to'). We're a little inconsistent about
-- whether we number e e₁ e₂ or τ₁ τ₂; this is mostly because I like being
-- consistent when there are multiples but Agda will always start with e and then
-- tack on subscripts later.  Sometimes we'll omit the tick when it's unambiguous.

module STLC-CBV where

  module OpSemCBV where

    -- local-step relation (computation rules: non-recursive)
    data _↦c_ : {τ : Tp} → [] ⊢ τ → [] ⊢ τ → Set where
      Step/β : {τ₁ τ₂ : Tp} {e : [] ,, τ₁ ⊢ τ₂} {v₁ : [] ⊢ τ₁}
             → value v₁
             → (app (lam e) v₁) ↦c subst1 v₁ e -- vacuously lam e is also a value
      Step/if-true : {τ : Tp} {e₁ e₂ : [] ⊢ τ}
             → if #t then e₁ else e₂ ↦c e₁
      Step/if-false : {τ : Tp} {e₁ e₂ : [] ⊢ τ}
             → if #f then e₁ else e₂ ↦c e₂

    -- step relation in context (evaluation contexts)
    -- these are pretty verbose but I don't know how write them out evaluation
    -- context style
    data _↦_ : {τ : Tp} → [] ⊢ τ → [] ⊢ τ → Set where
      Step/here : {τ : Tp} {e e' : [] ⊢ τ} → e ↦c e' → e ↦ e'
      Step/app1 : {τ₁ τ₂ : Tp} {e e' : [] ⊢ τ₁ ⇒ τ₂} {e₁ : [] ⊢ τ₁}
             → e ↦ e'
             → (app e e₁) ↦ (app e' e₁)
      Step/app2 : {τ₁ τ₂ : Tp}  {e : [] ,, τ₁ ⊢ τ₂} {e₁ e₁' : [] ⊢ τ₁}
             → e₁ ↦ e₁'
             → (app (lam e) e₁) ↦ (app (lam e) e₁')
      Step/if-cond : {τ : Tp} {e e' : [] ⊢ bool} {e₁ e₂ : [] ⊢ τ}
              → e ↦ e'
              → if e then e₁ else e₂ ↦ if e' then e₁ else e₂

    -- reflexive/transitive closure
    data _↦*_ : {τ : Tp} → [] ⊢ τ → [] ⊢ τ → Set where
      Done : {τ : Tp} {e : [] ⊢ τ} → e ↦* e
      Step : {τ : Tp} {e e' e'' : [] ⊢ τ} 
           → e ↦ e'  →  e' ↦* e''
           → e ↦* e''

    Append : {τ : Tp} {e e' e'' : [] ⊢ τ} 
           → e ↦* e'  →  e' ↦* e''
           → e ↦* e''
    Append Done g = g
    Append (Step x f) g = Step x (Append f g)

    _⇓_ : {τ : Tp} → [] ⊢ τ → [] ⊢ τ → Set
    e ⇓ v = value v × e ↦* v

    _⇓ : {τ : Tp} → [] ⊢ τ → Set
    e ⇓ = Σ (λ v → e ⇓ v)

    lifts : {τ τ' : Tp} {E : [] ⊢ τ → [] ⊢ τ'} → ({e e' : [] ⊢ τ} → e ↦ e' → E e ↦ E e') → {e e' : [] ⊢ τ}
      → (e ↦* e') → (E e ↦* E e')
    lifts Step/rule Done = Done
    lifts Step/rule (Step e↦e' e'↦*e'') = Step (Step/rule e↦e') (lifts Step/rule e'↦*e'')

    det-↦cc : {τ : Tp} {e e₁ e₂ : [] ⊢ τ} → e ↦c e₁ → e ↦c e₂ → e₁ == e₂
    det-↦cc (Step/β x) (Step/β y) = Refl
    det-↦cc Step/if-true Step/if-true = Refl
    det-↦cc Step/if-false Step/if-false = Refl

    det-↦c : {τ : Tp} {e e₁ e₂ : [] ⊢ τ} → e ↦ e₁ → e ↦c e₂ → e₁ == e₂
    det-↦c (Step/here x) s2 = det-↦cc x s2
    det-↦c (Step/app1 (Step/here ())) (Step/β x₁)
    det-↦c (Step/app2 (Step/here ())) (Step/β Value/true)
    det-↦c (Step/app2 (Step/here ())) (Step/β Value/false)
    det-↦c (Step/app2 (Step/here ())) (Step/β Value/lam)
    det-↦c (Step/if-cond (Step/here ())) Step/if-true
    det-↦c (Step/if-cond (Step/here ())) Step/if-false

    det-↦ : {τ : Tp} {e e₁ e₂ : [] ⊢ τ} → e ↦ e₁ → e ↦ e₂ → e₁ == e₂
    det-↦ (Step/here x) s2 = ! (det-↦c s2 x)
    det-↦ s1 (Step/here x) = det-↦c s1 x
    det-↦ (Step/app1 s1) (Step/app1 s2) = ap (λ y → app y _) (det-↦ s1 s2)
    det-↦ (Step/app1 (Step/here ())) (Step/app2 s2)
    det-↦ (Step/app2 s1) (Step/app1 (Step/here ()))
    det-↦ (Step/app2 s1) (Step/app2 s2) = ap (λ y → app _ y) (det-↦ s1 s2)
    det-↦ (Step/if-cond s1) (Step/if-cond s2) = ap (λ y → if y then _ else _) (det-↦ s1 s2)

    determinacy : {e v₁ v₂ : [] ⊢ bool} → e ⇓ v₁ → e ⇓ v₂ → v₁ == v₂
    determinacy (_ , Done) (_ , Done) = Refl
    determinacy (Value/true , Done) (_ , Step (Step/here ()) _)
    determinacy (Value/false , Done) (_ , Step (Step/here ()) _)
    determinacy (_ , Step (Step/here ()) _) (Value/true , Done)
    determinacy (_ , Step (Step/here ()) _) (Value/false , Done)
    determinacy (_ , Step (Step/app1 _) _) (() , Done)
    determinacy (_ , Step (Step/app2 _) _) (() , Done)
    determinacy (_ , Step (Step/if-cond _) _) (() , Done)
    determinacy (fst , Step x snd) (fst₁ , Step x₁ snd₁) = determinacy (fst , snd) (transport (λ □ → □ ⇓ _) (! (det-↦ x x₁)) (fst₁ , snd₁))

  module WeakNormalizationCBV where

    open OpSemCBV

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

  module EquivCBV where

    open OpSemCBV

    -- One should always prefer an inductive definition, but the naive formulation
    -- is not strictly positive!
    {-
    module FailsStrictPositivity where
      mutual
        data V⟦_⟧ : (τ : Tp) → [] ⊢ τ → [] ⊢ τ → Set where
          V/bool-#t : V⟦ bool ⟧ #t #t
          V/bool-#f : V⟦ bool ⟧ #f #f
          V/⇒ : {τ₁ τ₂ : Tp} {e₁ e₂ : [] ,, τ₁ ⊢ τ₂}
            → ((v₁ v₂ : [] ⊢ τ₁) → V⟦ τ₁ ⟧ v₁ v₂ → E⟦ τ₂ ⟧ (subst1 v₁ e₁) (subst1 v₂ e₂))
            → V⟦ τ₁ ⇒ τ₂ ⟧ (lam e₁) (lam e₂)

        data E⟦_⟧ (τ : Tp) (e₁ : [] ⊢ τ) (e₂ : [] ⊢ τ) : Set where
          E : (v₁ : [] ⊢ τ) → (v₂ : [] ⊢ τ) → e₁ ↦* v₁ → e₂ ↦* v₂ → V⟦ τ ⟧ v₁ v₂ → E⟦ τ ⟧ e₁ e₂

      data G⟦_⟧ : (Γ : Ctx) → [] ⊢c Γ → [] ⊢c Γ → Set where
        G/[] : G⟦ [] ⟧ <> <>
        G/:: : {Γ : Ctx} {γ₁ γ₂ : [] ⊢c Γ} {τ : Tp} {v₁ v₂ : [] ⊢ τ}
          → G⟦ Γ ⟧ γ₁ γ₂ 
          → V⟦ τ ⟧ v₁ v₂
          → G⟦ τ :: Γ ⟧ (γ₁ , v₁) (γ₂ , v₂)
    -}

    mutual
      V⟦_⟧ : (τ : Tp) → [] ⊢ τ → [] ⊢ τ → Set
      V⟦ bool ⟧    #t #t = Unit
      V⟦ bool ⟧    #f #f = Unit
      V⟦ bool ⟧ _ _  = Void
      V⟦ τ₁ ⇒ τ₂ ⟧ (lam e) (lam e') = (v v' : [] ⊢ τ₁) → V⟦ τ₁ ⟧ v v' → E⟦ τ₂ ⟧ (subst1 v e) (subst1 v' e')
      V⟦ τ₁ ⇒ τ₂ ⟧ _ _ = Void

      E⟦_⟧ : (τ : Tp) → [] ⊢ τ → [] ⊢ τ → Set
      E⟦ τ ⟧ e e' = Σ (λ v → Σ (λ v' → e ↦* v × e' ↦* v' × V⟦ τ ⟧ v v'))

    G⟦_⟧ : (Γ : Ctx) → ([] ⊢c Γ) → ([] ⊢c Γ) → Set
    G⟦ [] ⟧ <> <> = Unit
    G⟦ τ :: Γ ⟧ (γ , v) (γ' , v') = G⟦ Γ ⟧ γ γ' × V⟦ τ ⟧ v v'

    equiv : (Γ : Ctx) → (τ : Tp) → Γ ⊢ τ → Γ ⊢ τ → Set
    equiv Γ τ e e' = (γ γ' : [] ⊢c Γ) → G⟦ Γ ⟧ γ γ' → E⟦ τ ⟧ (subst γ e) (subst γ' e')

    -- The fact that the LR is not inductive can be a bit painful for the proofs.
    -- So also define an unfolding which we can do case-analysis over:

    mutual
      data V'⟦_⟧ : (τ : Tp) → [] ⊢ τ → [] ⊢ τ → Set where
        V/bool-#t : V'⟦ bool ⟧ #t #t
        V/bool-#f : V'⟦ bool ⟧ #f #f
        V/⇒ : {τ₁ τ₂ : Tp} {e e' : [] ,, τ₁ ⊢ τ₂}
          → (V : (v v' : [] ⊢ τ₁) → V⟦ τ₁ ⟧ v v' {- the critical position! -} → E'⟦ τ₂ ⟧ (subst1 v e) (subst1 v' e'))
          → V'⟦ τ₁ ⇒ τ₂ ⟧ (lam e) (lam e')

      data E'⟦_⟧ (τ : Tp) (e : [] ⊢ τ) (e' : [] ⊢ τ) : Set where
        E' : {v v' : [] ⊢ τ} → (e↦*v : e ↦* v) → (e'↦*v' : e' ↦* v') → (V' : V'⟦ τ ⟧ v v') → E'⟦ τ ⟧ e e'

    data G'⟦_⟧ : (Γ : Ctx) → [] ⊢c Γ → [] ⊢c Γ → Set where
      G/[] : G'⟦ [] ⟧ <> <>
      G/:: : {Γ : Ctx} {γ γ' : [] ⊢c Γ} {τ : Tp} {v v' : [] ⊢ τ}
        → G'⟦ Γ ⟧ γ γ'
        → V'⟦ τ ⟧ v v'
        → G'⟦ τ :: Γ ⟧ (γ , v) (γ' , v')

    equiv' : (Γ : Ctx) → (τ : Tp) → Γ ⊢ τ → Γ ⊢ τ → Set
    equiv' Γ τ e e' = (γ γ' : [] ⊢c Γ) → G'⟦ Γ ⟧ γ γ' → E'⟦ τ ⟧ (subst γ e) (subst γ' e')

    -- Show that the non-inductive version implies the inductive version

    mutual
      pE : {τ : Tp} → {e e' : [] ⊢ τ} → E⟦ τ ⟧ e e' → E'⟦ τ ⟧ e e'
      pE (_ , _ , e↦v , e'↦v' , V) = E' e↦v e'↦v' (pV V)

      pV : {τ : Tp} → {e e' : [] ⊢ τ} → V⟦ τ ⟧ e e' → V'⟦ τ ⟧ e e'
      pV {bool} {#t} {#t} V = V/bool-#t
      pV {bool} {#t} {#f} ()
      pV {bool} {#t} {if _ then _ else _} ()
      pV {bool} {#t} {var _} ()
      pV {bool} {#t} {app _ _} ()
      pV {bool} {#f} {#t} ()
      pV {bool} {#f} {#f} V = V/bool-#f
      pV {bool} {#f} {if _ then _ else _} ()
      pV {bool} {#f} {var _} ()
      pV {bool} {#f} {app _ _} ()
      pV {bool} {if _ then _ else _} ()
      pV {bool} {var _} ()
      pV {bool} {app _ _} ()
      pV {_ ⇒ _} {if _ then _ else _} ()
      pV {_ ⇒ _} {var _} ()
      pV {_ ⇒ _} {lam _} {if _ then _ else _} ()
      pV {_ ⇒ _} {lam _} {var _} ()
      pV {_ ⇒ _} {lam _} {lam _} f = V/⇒ (\ v v' V → pE (f v v' V))
      pV {_ ⇒ _} {lam _} {app _ _} ()
      pV {_ ⇒ _} {app _ _} ()

    pG : {Γ : Ctx} → {γ γ' : [] ⊢c Γ} → G⟦ Γ ⟧ γ γ' → G'⟦ Γ ⟧ γ γ'
    pG {[]} _ = G/[]
    pG {τ :: Γ} (G , V) = G/:: (pG G) (pV V)

    -- Show the inverse

    mutual
      Vp : {τ : Tp} → {e e' : [] ⊢ τ} → V'⟦ τ ⟧ e e' → V⟦ τ ⟧ e e'
      Vp V/bool-#t = <>
      Vp V/bool-#f = <>
      Vp (V/⇒ f) = \ v v' V → Ep (f v v' V)

      Ep : {τ : Tp} → {e e' : [] ⊢ τ} → E'⟦ τ ⟧ e e' → E⟦ τ ⟧ e e'
      Ep (E' {v} {v'} e↦v e'↦v' V') = (v , v' , e↦v , e'↦v' , Vp V')

    Gp : {Γ : Ctx} → {γ γ' : [] ⊢c Γ} → G'⟦ Γ ⟧ γ γ' → G⟦ Γ ⟧ γ γ'
    Gp G/[] = <>
    Gp (G/:: G' V') = Gp G' , Vp V'

    -- Relies on both the forward and backwards direction

    pequiv : {Γ : Ctx} → {τ : Tp} → (e e' : Γ ⊢ τ) → equiv Γ τ e e' → equiv' Γ τ e e'
    pequiv _ _ eq = λ γ γ' G' → pE (eq γ γ' (Gp G'))

    equivp : {Γ : Ctx} → {τ : Tp} → (e e' : Γ ⊢ τ) → equiv' Γ τ e e' → equiv Γ τ e e'
    equivp _ _ eq = λ γ γ' G → Ep (eq γ γ' (pG G))

    -- using the prime'd versions, we can prove some theorems easily

    V'-value : {τ : Tp} → {e e' : [] ⊢ τ} → V'⟦ τ ⟧ e e' → value e × value e'
    V'-value V/bool-#t = Value/true , Value/true
    V'-value V/bool-#f = Value/false , Value/false
    V'-value (V/⇒ _) = Value/lam , Value/lam

    V'-bool-equal : {e₁ e₂ : [] ⊢ bool} → V'⟦ bool ⟧ e₁ e₂ → e₁ == e₂
    V'-bool-equal V/bool-#t = Refl
    V'-bool-equal V/bool-#f = Refl

    -- some parameters are delicately asked to be explicit, for fear of the
    -- underconstrained hole

    compat-if' : {Γ : Ctx} → {τ : Tp} → (e e' : Γ ⊢ bool) → (e₁ e₁' e₂ e₂' : Γ ⊢ τ) → equiv' Γ bool e e' → equiv' Γ τ e₁ e₁' → equiv' Γ τ e₂ e₂' → equiv' Γ τ (if e then e₁ else e₂) (if e' then e₁' else e₂')
    compat-if' _ _ _ _ _ _ e≈e' e₁≈e₁' e₂≈e₂' γ γ' G with e₁≈e₁' γ γ' G
    ... | E' e₁↦*v₁ e₁'↦*v₁' V₁ with e₂≈e₂' γ γ' G
    ...   | E' e₂↦*v₂ e₂'↦*v₂' V₂ with e≈e' γ γ' G
    ...     | E' e↦*v e'↦*v' V/bool-#t
              = E' (Append (lifts Step/if-cond e↦*v) (Step (Step/here Step/if-true) e₁↦*v₁))
                   (Append (lifts Step/if-cond e'↦*v') (Step (Step/here Step/if-true) e₁'↦*v₁')) V₁
    ...     | E' e↦*v e'↦*v' V/bool-#f
              = E' (Append (lifts Step/if-cond e↦*v) (Step (Step/here Step/if-false) e₂↦*v₂))
                   (Append (lifts Step/if-cond e'↦*v') (Step (Step/here Step/if-false) e₂'↦*v₂')) V₂

    compat-app' : {Γ : Ctx} → {τ τ₁ : Tp} → (e e' : Γ ⊢ τ ⇒ τ₁) → (e₁ e₁' : Γ ⊢ τ) → equiv' Γ (τ ⇒ τ₁) e e' → equiv' Γ τ e₁ e₁' → equiv' Γ τ₁ (app e e₁) (app e' e₁')
    compat-app' _ _ _ _ e≈e' e₁≈e₁' γ γ' G with e≈e' γ γ' G
    ... | E' e↦*v e'↦*v' (V/⇒ f) with e₁≈e₁' γ γ' G
    ...   | E' {v₁} {v₁'} e₁↦*v₁ e₁'↦*v₁' V' with f v₁ v₁' (Vp V')
    ...     | E' v[v₁]↦*v₂ v'[v₁']↦*v₂' V''
            = E' (Append (lifts Step/app1 e↦*v)
                         (Append (lifts Step/app2 e₁↦*v₁)
                                 (Step (Step/here (Step/β (fst (V'-value V')))) v[v₁]↦*v₂)))
                 (Append (lifts Step/app1 e'↦*v')
                         (Append (lifts Step/app2 e₁'↦*v₁')
                                 (Step (Step/here (Step/β (snd (V'-value V')))) v'[v₁']↦*v₂'))) V''

    compat-lam' : {Γ : Ctx} → {τ τ₁ : Tp} → (e e' : Γ ,, τ ⊢ τ₁) → equiv' (Γ ,, τ) τ₁ e e' → equiv' Γ (τ ⇒ τ₁) (lam e) (lam e')
    compat-lam' e e' e≈e' γ γ' G
      = E' Done Done (V/⇒ (λ v v' V → transport (λ p → E'⟦ _ ⟧ (fst p) (snd p))
                                                (ap2 _,_ (subst-compose1 γ v e) (subst-compose1 γ' v' e'))
                                                (e≈e' (γ , v) (γ' , v') (G/:: G (pV V)))))

    -- these theorems can be projected back into the function versions

    V-value : {τ : Tp} → {e₁ e₂ : [] ⊢ τ} → V⟦ τ ⟧ e₁ e₂ → value e₁ × value e₂
    V-value V = V'-value (pV V)

    V-bool-equal : {e₁ e₂ : [] ⊢ bool} → V⟦ bool ⟧ e₁ e₂ → e₁ == e₂
    V-bool-equal V = V'-bool-equal (pV V)

    compat-if : {Γ : Ctx} → {τ : Tp} → (e e' : Γ ⊢ bool) → (e₁ e₁' e₂ e₂' : Γ ⊢ τ) → equiv Γ bool e e' → equiv Γ τ e₁ e₁' → equiv Γ τ e₂ e₂' → equiv Γ τ (if e then e₁ else e₂) (if e' then e₁' else e₂')
    compat-if e e' e₁ e₁' e₂ e₂' e≈e' e₁≈e₁' e₂≈e₂' = equivp (if e then e₁ else e₂) (if e' then e₁' else e₂') (compat-if' e e' e₁ e₁' e₂ e₂' (pequiv e e' e≈e') (pequiv e₁ e₁' e₁≈e₁') (pequiv e₂ e₂' e₂≈e₂'))

    compat-lam : {Γ : Ctx} → {τ τ₁ : Tp} → (e e' : Γ ,, τ ⊢ τ₁) → equiv (Γ ,, τ) τ₁ e e' → equiv Γ (τ ⇒ τ₁) (lam e) (lam e')
    compat-lam e e' e≈e' = equivp (lam e) (lam e') (compat-lam' e e' (pequiv e e' e≈e'))

    compat-app : {Γ : Ctx} → {τ τ₁ : Tp} → (e e' : Γ ⊢ τ ⇒ τ₁) → (e₁ e₁' : Γ ⊢ τ) → equiv Γ (τ ⇒ τ₁) e e' → equiv Γ τ e₁ e₁' → equiv Γ τ₁ (app e e₁) (app e' e₁')
    compat-app e e' e₁ e₁' e≈e' e₁≈e₁' = equivp (app e e₁) (app e' e₁') (compat-app' e e' e₁ e₁' (pequiv e e' e≈e') (pequiv e₁ e₁' e₁≈e₁'))

    -- some of the compatibility lemmas are simple enough to not benefit from the transformation

    compat-var : {Γ : Ctx} → {τ : Tp} → (x : τ ∈ Γ) → equiv Γ τ (var x) (var x)
    compat-var i0 (_ , v) (_ , v') (_ , V) = v , v' , Done , Done , V
    compat-var (iS x) (γ , _) (γ' , _) (G , _) = compat-var x γ γ' G

    fund : {Γ : Ctx} → {τ : Tp} → (e : Γ ⊢ τ) → equiv Γ τ e e
    fund #t = \ _ _ _ → #t , #t , Done , Done , <> -- these are sufficiently trivial...
    fund #f = \ _ _ _ → #f , #f , Done , Done , <>
    fund (if e then e₁ else e₂) = compat-if e e e₁ e₁ e₂ e₂ (fund e) (fund e₁) (fund e₂)
    fund (var x) = compat-var x
    fund (lam e) = compat-lam e e (fund e)
    fund (app e e₁) = compat-app e e e₁ e₁ (fund e) (fund e₁)

    -- as in C
    -- apparently for technical reasons it is more convenient
    -- to build in weakening; perhaps we will see why later...
    data _⊢_↝_⊢_ : Ctx → Tp → Ctx → Tp → Set where
      -- Apparently, the weakening is only needed for the step-indexed version,
      -- and this is /exactly/ what makes this a Kripke logical relation
      -- (Check Andy Pitts chapter)
      -- (Other note: when you have an extra constructor which
      -- just says "well, whatever" then it really gets in the
      -- way of inductions)
      [·] : {Γ {- Γ' -} : Ctx} {τ : Tp} → {- Γ' ⊇ Γ → -} Γ ⊢ τ ↝ Γ ⊢ τ
      if[_]then_else_ : {Γ Γ' : Ctx} {τ τ' : Tp}
        → Γ ⊢ τ ↝ Γ' ⊢ bool
        →         Γ' ⊢ τ'
        →         Γ' ⊢ τ'
        → Γ ⊢ τ ↝ Γ' ⊢ τ'
      if_then[_]else_ : {Γ Γ' : Ctx} {τ τ' : Tp}
        →         Γ' ⊢ bool
        → Γ ⊢ τ ↝ Γ' ⊢ τ'
        →         Γ' ⊢ τ'
        → Γ ⊢ τ ↝ Γ' ⊢ τ'
      if_then_else[_] : {Γ Γ' : Ctx} {τ τ' : Tp}
        →         Γ' ⊢ bool
        →         Γ' ⊢ τ'
        → Γ ⊢ τ ↝ Γ' ⊢ τ'
        → Γ ⊢ τ ↝ Γ' ⊢ τ'
      lam[_] : {Γ Γ' : Ctx} {τ τ₁ τ₂ : Tp}
        → (Γ ,, τ₁) ⊢ τ ↝ (Γ' ,, τ₁) ⊢ τ₂
        → (Γ ,, τ₁) ⊢ τ ↝ Γ' ⊢ (τ₁ ⇒ τ₂)
      app[_]_ : {Γ Γ' : Ctx} {τ τ₁ τ₂ : Tp}
        → Γ ⊢ τ ↝ Γ' ⊢ (τ₁ ⇒ τ₂)
        →         Γ' ⊢ τ₁
        → Γ ⊢ τ ↝ Γ' ⊢ τ₂
      app_[_] : {Γ Γ' : Ctx} {τ τ₁ τ₂ : Tp}
        →         Γ' ⊢ τ₁ ⇒ τ₂
        → Γ ⊢ τ ↝ Γ' ⊢ τ₁
        → Γ ⊢ τ ↝ Γ' ⊢ τ₂

    fill : {Γ Γ' : Ctx} {τ τ' : Tp} → (Γ ⊢ τ ↝ Γ' ⊢ τ') → Γ ⊢ τ → Γ' ⊢ τ'
    -- fill ([·] x) e = rename x e
    fill [·] e = e
    fill (if[ C ]then  x  else  x₁ ) e = if fill C e then x else x₁
    fill (if  x  then[ C ]else  x₁ ) e = if x then fill C e else x₁
    fill (if  x  then  x₁ else[ C ]) e = if x then x₁ else fill C e
    fill lam[ C ] e = lam (fill C e)
    fill (app[ C ] x  ) e = app (fill C e) x
    fill (app  x [ C ]) e = app x (fill C e)

    module ContextExamples where
      C1 : ([] ,, bool) ⊢ (bool ⇒ bool) ↝ [] ⊢ bool
      C1 = app[ app[ lam[ [·] ] ] #t ] #t

      e1 : ([] ,, bool) ⊢ (bool ⇒ bool)
      e1 = lam (if var i0 then var (iS i0) else var i0)

      Ce1 : [] ⊢ bool
      Ce1 = fill C1 e1

      eq1 : Ce1 == app (app (lam (lam (if var i0 then var (iS i0) else var i0))) #t) #t
      eq1 = Refl

    -- compatibility lemma for CONTEXTS!

    equiv-contexts : (Γ Γ' : Ctx) → (τ τ' : Tp) → (C C' : Γ ⊢ τ ↝ Γ' ⊢ τ') → Set
    equiv-contexts Γ Γ' τ τ' C C' = (e e' : Γ ⊢ τ) → equiv Γ τ e e' → equiv Γ' τ' (fill C e) (fill C e')

    compat-contexts : {Γ Γ' : Ctx} → {τ τ' : Tp} → (C : Γ ⊢ τ ↝ Γ' ⊢ τ') → equiv-contexts Γ Γ' τ τ' C C
    compat-contexts [·] e e' e≈e' = e≈e'
    compat-contexts (if[ C ]then x else x₁) e e' e≈e'
      = compat-if (fill C e) (fill C e') x x x₁ x₁ (compat-contexts C e e' e≈e') (fund x) (fund x₁)
    compat-contexts (if x then[ C ]else x₁) e e' e≈e'
      = compat-if x x (fill C e) (fill C e') x₁ x₁ (fund x) (compat-contexts C e e' e≈e') (fund x₁)
    compat-contexts if x then x₁ else[ C ] e e' e≈e'
      = compat-if x x x₁ x₁ (fill C e) (fill C e') (fund x) (fund x₁) (compat-contexts C e e' e≈e')
    compat-contexts lam[ C ] e e' e≈e' = compat-lam (fill C e) (fill C e') (compat-contexts C e e' e≈e')
    compat-contexts (app[ C ] x) e e' e≈e'
      = compat-app (fill C e) (fill C e') x x (compat-contexts C e e' e≈e') (fund x)
    compat-contexts app x [ C ] e e' e≈e'
      = compat-app x x (fill C e) (fill C e') (fund x) (compat-contexts C e e' e≈e')

    -- unidirectional version; other direction follows wlog, and combined
    -- form follows easily from determinacy

    -- If you're cross-referencing with the ESOP paper, note that because
    -- we don't have nontermination, we can't simply say "if e₁ terminates, then
    -- e₂ must too"; we have to say something stronger.  Fortunately, we can
    -- specialize on bools. Determinacy helps here.

    ctx-equiv : (Γ : Ctx) → (τ : Tp) → Γ ⊢ τ → Γ ⊢ τ → Set
    ctx-equiv Γ τ e₁ e₂ = (C : Γ ⊢ τ ↝ [] ⊢ bool) → (v : [] ⊢ bool) → fill C e₁ ⇓ v → fill C e₂ ⇓ v --) × (fill C e₂ ⇓ v → fill C e₁ ⇓ v)

    soundness : {Γ : Ctx} {τ : Tp} (e e' : Γ ⊢ τ) → equiv Γ τ e e' → ctx-equiv Γ τ e e'
    soundness e e' pf C v C[e]⇓v with compat-contexts C e e' pf <> <> <>
    ... | v₀ , v' , sC[e]⇓v₀ , sC[e']⇓v' , V = fst C[e]⇓v , transport (λ □ → fill C e' ↦* □) (! (v₀=v' ∘ v=v₀))
                                                              (transport (λ □ → □ ↦* v') (! subst-id) sC[e']⇓v')
      where v=v₀ : v == v₀
            v=v₀ = determinacy C[e]⇓v (fst (V-value V) , transport (λ □ → □ ↦* v₀) (! subst-id) sC[e]⇓v₀)
            v₀=v' : v₀ == v'
            v₀=v' = V-bool-equal V

