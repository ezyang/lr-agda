open import Preliminaries
open import STLC
open import STLC-CBV
open import STLC-CBV-Equivalence

module STLC-CBV-Ex where

  module Ex1 where

    prog1 : {Γ : Ctx} → Γ ⊢ bool ⇒ bool
    prog1 = lam (var i0)

    prog2 : {Γ : Ctx} → Γ ⊢ bool ⇒ bool
    prog2 = lam (if var i0 then var i0 else #f)

    sub : {v v' : [] ⊢ bool} → V'⟦ bool ⟧ v v' → E'⟦ bool ⟧ v (if v' then v' else #f)
    sub V/bool-#t = E' Done (Step (Step/here Step/if-true) Done) V/bool-#t
    sub V/bool-#f = E' Done (Step (Step/here Step/if-false) Done) V/bool-#f

    eq : {Γ : Ctx} → ctx-equiv Γ (bool ⇒ bool) prog1 prog2
    eq = soundness _ _ (equivp prog1 prog2 (λ _ _ _ → E' Done Done (V/⇒ (λ _ _ V → sub (pV V)))))

  module Ex2 where

    prog1 : {Γ : Ctx} → Γ ⊢ (bool ⇒ bool) ⇒ (bool ⇒ bool)
    prog1 = lam (var i0)

    prog2 : {Γ : Ctx} → Γ ⊢ (bool ⇒ bool) ⇒ (bool ⇒ bool)
    prog2 = lam (lam (app (var (iS i0)) (app (var (iS i0)) (app (var (iS i0)) (var i0)))))

    data Code (f : [] ⊢ bool ⇒ bool) : Set where
      c-id : E'⟦ bool ⇒ bool ⟧ f (lam (var i0)) → Code f
      c-not : E'⟦ bool ⇒ bool ⟧ f (lam (if (var i0) then #f else #t)) → Code f
      c-true : E'⟦ bool ⇒ bool ⟧ f (lam #t) → Code f
      c-false : E'⟦ bool ⇒ bool ⟧ f (lam #f) → Code f

    lem : (f : [] ⊢ bool ⇒ bool) → E⟦ bool ⇒ bool ⟧ f f
    lem f = transport (\ f → E⟦ bool ⇒ bool ⟧ f f) (! subst-id) (fund f <> <> <>)

    sub-true : {v v' : [] ⊢ bool} → {e' : bool :: [] ⊢ bool}
      → (subst1 #t e' ↦* #t)
      → (subst1 #f e' ↦* #t)
      → V'⟦ bool ⟧ v v' → E'⟦ bool ⟧ (subst1 v e') (subst1 v' #t)
    sub-true a b V/bool-#t = E' a Done V/bool-#t
    sub-true a b V/bool-#f = E' b Done V/bool-#t

    sub : {f : [] ⊢ bool ⇒ bool} → E'⟦ bool ⇒ bool ⟧ f f → Code f
    sub (E' {lam e} {lam e'} e↦*v e'↦*v' (V/⇒ V)) with (V #t #t <> , V #f #f <>)
    ... | E' e↦*v₁ e'↦*v'₁ V/bool-#t , E' e↦*v₂ e'↦*v'₂ V/bool-#t = c-true (E' e'↦*v' Done (V/⇒ (λ v v' x → sub-true {v} {v'} {e'} e'↦*v'₁ e'↦*v'₂ (pV x))))
    ... | E' e↦*v₁ e'↦*v'₁ V/bool-#t , E' e↦*v₂ e'↦*v'₂ V/bool-#f = c-id {!!}
    ... | E' e↦*v₁ e'↦*v'₁ V/bool-#f , E' e↦*v₂ e'↦*v'₂ V/bool-#t = c-not {!!}
    ... | E' e↦*v₁ e'↦*v'₁ V/bool-#f , E' e↦*v₂ e'↦*v'₂ V/bool-#f = c-false {!!}

    eq : {Γ : Ctx} → ctx-equiv Γ ((bool ⇒ bool) ⇒ (bool ⇒ bool)) prog1 prog2
    eq = soundness _ _ (equivp prog1 prog2 (λ γ γ' x → E' Done Done (V/⇒ (λ v v' x₁ → E' Done Done {!!}))))
