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
