open import Preliminaries
open import STLC
open import STLC-CBV

module STLC-CBV-Ex where

  open OpSemCBV
  open EquivCBV

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
