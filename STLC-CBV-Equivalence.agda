open import Preliminaries
open import STLC
open import STLC-CBV

-- Notation conventions: subscript numbers used for *positional* differences
-- (they are not expected to have the same types) whereas ticks are used to
-- indicate 'morally equivalent' terms, which are expected to be related in some
-- way (e.g. 'reduces to' or 'equivalent to'). We're a little inconsistent about
-- whether we number e e₁ e₂ or τ₁ τ₂; this is mostly because I like being
-- consistent when there are multiples but Agda will always start with e and then
-- tack on subscripts later.  Sometimes we'll omit the tick when it's unambiguous.

module STLC-CBV-Equivalence where

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

  -- Just ignore the right-hand-side...
  normalization : {τ : Tp} → (e : [] ⊢ τ) -> e ⇓
  normalization e with fund e <> <> <>
  normalization e | v , _ , e↦*v , _ , V = v , fst (V-value V) , transport (λ e' → e' ↦* v) (! subst-id) e↦*v

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
