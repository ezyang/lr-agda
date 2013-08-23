open import Preliminaries

{-
The simply typed lambda calculus in Agda.

This particular implementation was developed by Dan Licata for
OPLSS 2013.  The method for "correct-by-construction" lambda terms
is standard, but we also provide some important lemmas about
substitutions and renamings that are quite important when
reasoning about operational semantics, and frequently omitted from
most presentations about STLC.
-}
module STLC where

  {- types of the STLC -}
  data Tp : Set where
    bool : Tp          -- booleans (for non-trivial equivalence proofs)
    _⇒_ : Tp → Tp → Tp -- type \=> in agda-mode to get the ⇒ character

  {- contexts are lists of Tp's -}
  Ctx = List Tp
  _,,_ : Ctx → Tp → Ctx
  Γ ,, τ = τ :: Γ

  infixr 10 _⇒_
  infixr 9 _,,_
  infixr 8 _⊢_ -- type \entails or \|-

  {- de Bruijn indices are represented as proofs that 
     an element is in a list -}
  data _∈_ {A : Set} : (x : A) (l : List A) → Set where -- type \in
    i0 : {x : A} {xs : List A} → x ∈ x :: xs
    iS : {x y : A} {xs : List A} → x ∈ xs → x ∈ y :: xs

  {- Γ ⊢ τ represents a term of type τ in context Γ -}
  data _⊢_ (Γ : Ctx) : Tp → Set where
    #t  : Γ ⊢ bool
    #f  : Γ ⊢ bool
    if_then_else_ : {τ : Tp} → Γ ⊢ bool → Γ ⊢ τ → Γ ⊢ τ → Γ ⊢ τ
    var : {τ : Tp} 
        → τ ∈ Γ
        → Γ ⊢ τ 
    lam : {τ1 τ2 : Tp} 
        → Γ ,, τ1 ⊢ τ2
        → Γ ⊢ τ1 ⇒ τ2
    app : {τ1 τ2 : Tp} 
        → Γ ⊢ τ1 ⇒ τ2 
        → Γ ⊢ τ1 
        → Γ ⊢ τ2

  {- values are true, false and lambda terms -}
  data value :  {τ : Tp} → [] ⊢ τ → Set where
    Value/true : value #t
    Value/false : value #f
    Value/lam : {τ₁ τ₂ : Tp} {e : [] ,, τ₁ ⊢ τ₂} → value (lam e)

  module Examples where
    i : [] ⊢ bool ⇒ bool
    i = lam (var i0) -- \ x -> x
  
    k : [] ⊢ bool ⇒ bool ⇒ bool
    k = lam (lam (var (iS i0))) -- \ x -> \ y -> x
  
    k' : [] ⊢ bool ⇒ bool ⇒ bool
    k' = lam (lam (var i0))
  

  {- The following proof is like a "0-ary" logical relation.
     It gives a semantics of the STLC in Agda.
     This shows that the STLC is sound, relative to Agda.  
  -}
  module Semantics where 

    -- function mapping STLC types to Agda types
    ⟦_⟧t : Tp → Set  -- type \(0 and \)0
    ⟦ bool ⟧t = Bool
    ⟦ τ1 ⇒ τ2 ⟧t = ⟦ τ1 ⟧t → ⟦ τ2 ⟧t

    -- function mapping STLC contexts to Agda types
    ⟦_⟧c : Ctx → Set
    ⟦ [] ⟧c = Unit
    ⟦ τ :: Γ ⟧c = ⟦ Γ ⟧c × ⟦ τ ⟧t

    ⟦_⟧ : {Γ : Ctx} {τ : Tp} → Γ ⊢ τ → ⟦ Γ ⟧c → ⟦ τ ⟧t
    ⟦_⟧ #t γ = True
    ⟦_⟧ #f γ = False
    ⟦_⟧ (if e₁ then e₂ else e₃) γ with ⟦ e₁ ⟧ γ
    ⟦_⟧ (if e₁ then e₂ else e₃) γ | True = ⟦ e₂ ⟧ γ
    ⟦_⟧ (if e₁ then e₂ else e₃) γ | False = ⟦ e₃ ⟧ γ
    ⟦_⟧ (var i0) γ = snd γ
    ⟦_⟧ (var (iS x)) γ = ⟦ var x ⟧ (fst γ)
    ⟦_⟧ (lam e) γ = λ x → ⟦ e ⟧ (γ , x)
    ⟦_⟧ (app e e₁) γ = ⟦ e ⟧ γ (⟦ e₁ ⟧ γ)

    {- the following test should pass -}
    test : ⟦ Examples.k ⟧ == \ γ x y → x
    test = Refl

  module RenamingAndSubstitution where 
    -- renamings = variable for variable substitutions.
    -- For simplicity, these are defined as tuples, by recursion on the context.
    -- It might clean up some of the proofs to use a functional view,
    --   {τ : Tp} → τ ∈ Γ → τ ∈ Γ'
    -- because then we could avoid some of the inductions here,
    -- and some of the associativity/unit properties would be free.  
    module Renamings where

      infix 9 _⊇_
  
      _⊇_ : Ctx → Ctx → Set -- type \sup=
      Γ' ⊇ [] = Unit
      Γ' ⊇ (τ :: Γ) = (Γ' ⊇ Γ) × (τ ∈ Γ')

      -- variables are functorial in the context
      rename-var : {Γ Γ' : Ctx} {τ : Tp} → Γ' ⊇ Γ → τ ∈ Γ → τ ∈ Γ'
      rename-var (ρ , x') i0 = x'
      rename-var (ρ , _) (iS x) = rename-var ρ x
  
      {- conceptually, we could define p and ⊇-compose and ⊇-id as primitive
         and derive this.
         but this works better inductively than ⊇-single does.
      -}
      p· : {Γ : Ctx} {Γ' : Ctx} → Γ ⊇ Γ' → {τ : Tp} → (Γ ,, τ) ⊇ Γ'
      p· {Γ' = []} ren = <>
      p· {Γ' = (τ :: Γ')} (ρ , x) = p· ρ , iS x
  
      idr : {Γ : Ctx} → Γ ⊇ Γ
      idr {[]} = <>
      idr {τ :: Γ} = p· idr , i0
  
      _·rr_ : {Γ1 Γ2 Γ3 : Ctx} → Γ1 ⊇ Γ2 → Γ2 ⊇ Γ3 → Γ1 ⊇ Γ3
      _·rr_ {Γ1} {Γ2} {[]} ρ2 ρ3 = <>
      _·rr_ {Γ1} {Γ2} {x :: Γ3} ρ2 (ρ3 , x3) = (ρ2 ·rr ρ3) , rename-var ρ2 x3

      -- category with families notation
      p : {Γ : Ctx} {τ : Tp} → (Γ ,, τ ⊇ Γ) 
      p = p· idr 
      
      -- next, we should show associativity and unit laws for ∘rr.
      -- However:
      -- (1) because renamings are defined using variables, this depends on (some of) functoriality of τ ∈ -,
      --     so we define that here, too.  
      -- (2) we only need one of the unit laws

      rename-var-· : {Γ1 Γ2 Γ3 : Ctx} → (ρ2 : Γ1 ⊇ Γ2) (ρ3 : Γ2 ⊇ Γ3) {τ : Tp} (x : τ ∈ Γ3)
                         → rename-var ρ2 (rename-var ρ3 x) == rename-var (_·rr_ ρ2 ρ3) x
      rename-var-· ρ2 ρ3 i0 = Refl
      rename-var-· ρ2 ρ3 (iS x) = rename-var-· ρ2 (fst ρ3) x

      ·rr-assoc : {Γ1 Γ2 Γ3 Γ4 : Ctx} → (ρ2 : Γ1 ⊇ Γ2) (ρ3 : Γ2 ⊇ Γ3) (ρ4 : Γ3 ⊇ Γ4) → _·rr_ ρ2 (_·rr_ ρ3 ρ4) == _·rr_ (_·rr_ ρ2 ρ3) ρ4 
      ·rr-assoc {Γ4 = []} ρ2 ρ3 ρ4 = Refl
      ·rr-assoc {Γ4 = τ4 :: Γ4} ρ2 ρ3 (ρ4 , x4) = ap2 _,_ (·rr-assoc ρ2 ρ3 ρ4) (rename-var-· ρ2 ρ3 x4)

      -- rest of functoriality of rename-var
      mutual
        -- generalization to get the induction to go through
        rename-var-p' : {Γ Γ' : Ctx} {τ τ' : Tp} (ρ : Γ' ⊇ Γ) (x : τ ∈ Γ) → rename-var (p· ρ {τ'}) x == (iS (rename-var ρ x))
        rename-var-p' ρ i0 = Refl
        rename-var-p' (ρ , _) (iS x) = rename-var-p' ρ x
  
        -- this would be definitional if renamings were functions.
        -- this instances is often needed below
        rename-var-p : {Γ : Ctx} {τ τ' : Tp} (x : τ ∈ Γ) → rename-var (p· idr {τ'}) x == (iS x)
        rename-var-p x = ap iS (rename-var-ident _ x) ∘ rename-var-p' idr x

        rename-var-ident : {τ : Tp} (Γ : Ctx) (x : τ ∈ Γ) → rename-var idr x == x
        rename-var-ident .(τ :: Γ) (i0 {τ} {Γ}) = Refl
        rename-var-ident .(τ' :: Γ) (iS {τ} {τ'} {Γ} x) = rename-var-p x

      -- beta reduction for p
      pβ1' : {Γ1 Γ2 Γ3 : Ctx} → (ρ2 : Γ1 ⊇ Γ2) (ρ3 : Γ2 ⊇ Γ3) {τ : Tp} (x : τ ∈ Γ1)
            → (ρ2 , x) ·rr (p· ρ3) == (ρ2 ·rr ρ3)
      pβ1' {Γ1} {_} {[]} ρ2 ρ3 x = Refl
      pβ1' {Γ1} {_} {τ3 :: Γ3} ρ2 (ρ3 , x3) x₁ = ap (λ x → x , rename-var ρ2 x3) (pβ1' ρ2 ρ3 _)

      mutual
        ·rr-unitr : {Γ1 Γ2 : Ctx} → (ρ2 : Γ1 ⊇ Γ2) 
              → ρ2 ·rr idr == ρ2
        ·rr-unitr {Γ1} {[]} ρ2 = Refl
        ·rr-unitr {Γ1} {τ2 :: Γ2} (ρ2 , x2) = ap (λ x → x , x2) (pβ1 ρ2 x2)
  
        pβ1 : {Γ1 Γ2 : Ctx} → (ρ2 : Γ1 ⊇ Γ2) {τ : Tp} (x : τ ∈ Γ1)
              → (ρ2 , x) ·rr p == ρ2
        pβ1 ρ2 x = ·rr-unitr ρ2 ∘ pβ1' ρ2 idr x

      -- p· is equivalent to the alternate definition.
      p·-def : {Γ1 Γ2 : Ctx} {τ : Tp} (ρ : Γ1 ⊇ Γ2) → p· ρ {τ} == p ·rr ρ
      p·-def {_}{[]} ρ = Refl
      p·-def {_}{τ1 :: Γ1} (ρ , x) = ap2 _,_ (p·-def ρ) (! (rename-var-p x))


      -- terms are functorial in renamings

      addvar-ren : {Γ Γ' : Ctx} {τ : Tp} → Γ' ⊇ Γ → Γ' ,, τ ⊇ Γ ,, τ
      addvar-ren ρ = (p· ρ , i0)
  
      rename : {Γ Γ' : Ctx} {τ : Tp} → Γ' ⊇ Γ → Γ ⊢ τ → Γ' ⊢ τ
      rename ρ #t = #t
      rename ρ #f = #f
      rename ρ (if e₁ then e₂ else e₃) = if rename ρ e₁ then rename ρ e₂ else rename ρ e₃
      rename ρ (var x) = var (rename-var ρ x)
      rename ρ (lam e) = lam (rename (addvar-ren ρ) e)
      rename ρ (app e e') = app (rename ρ e) (rename ρ e')

      rename-· : {Γ1 Γ2 Γ3 : Ctx} → (ρ2 : Γ1 ⊇ Γ2) (ρ3 : Γ2 ⊇ Γ3) {τ : Tp} (e : Γ3 ⊢ τ)
                     → rename ρ2 (rename ρ3 e) == rename (ρ2 ·rr ρ3) e
      rename-· ρ2 ρ3 #t = Refl
      rename-· ρ2 ρ3 #f = Refl
      rename-· ρ2 ρ3 (if e₁ then e₂ else e₃) = ap3 if_then_else_ (rename-· ρ2 ρ3 e₁) (rename-· ρ2 ρ3 e₂) (rename-· ρ2 ρ3 e₃)
      rename-· ρ2 ρ3 (var x) = ap var (rename-var-· ρ2 ρ3 x)
      rename-·{Γ1}{Γ2}{Γ3} ρ2 ρ3 (lam e) = ap lam (ap (λ x → rename (x , i0) e) lemma1 ∘ rename-· (addvar-ren ρ2) (addvar-ren ρ3) e) where
        lemma1 : (p· ρ2 , i0) ·rr (p· ρ3) == p· (ρ2 ·rr ρ3)
        lemma1 = (p· ρ2 , i0) ·rr (p· ρ3)  =〈 pβ1' (p· ρ2) ρ3 i0 〉
                 (p· ρ2) ·rr ρ3            =〈 ap (λ x → _·rr_ x ρ3) (p·-def ρ2) 〉
                 (p ·rr ρ2) ·rr ρ3         =〈 ! (·rr-assoc p ρ2 ρ3) 〉 
                 p ·rr (ρ2 ·rr ρ3)         =〈 ! (p·-def (ρ2 ·rr ρ3))〉
                 p· (ρ2 ·rr ρ3) ∎
      rename-· ρ2 ρ3 (app e e₁) = ap2 app (rename-· ρ2 ρ3 e) (rename-· ρ2 ρ3 e₁)

      -- not necessary for the proof, but an easy corollary of the above
      rename-id : {Γ : Ctx}{τ : Tp} (e : Γ ⊢ τ) → rename idr e == e
      rename-id #t = Refl
      rename-id #f = Refl
      rename-id (if e₁ then e₂ else e₃) = ap3 if_then_else_ (rename-id e₁) (rename-id e₂) (rename-id e₃)
      rename-id (var x) = ap var (rename-var-ident _ x)
      rename-id (lam e) = ap lam (rename-id e)
      rename-id (app e e₁) = ap2 app (rename-id e) (rename-id e₁)
    open Renamings

    -- expression-for-variable substitutions

    module Subst where

      _⊢c_ : Ctx → Ctx → Set
      Γ' ⊢c [] = Unit
      Γ' ⊢c (τ :: Γ) = (Γ' ⊢c Γ) × (Γ' ⊢ τ) 
  
      _·rs_ : {Γ1 Γ2 Γ3 : Ctx} →  Γ1 ⊇ Γ2 → Γ2 ⊢c Γ3 → Γ1 ⊢c Γ3
      _·rs_ {Γ1} {Γ2} {[]} ρ θ = <>
      _·rs_ {Γ1} {Γ2} {τ3 :: Γ3} ρ (θ , e) = ρ ·rs θ , rename ρ e
    
      addvar : {Γ Γ' : Ctx} {τ : Tp} → Γ ⊢c Γ' → (Γ ,, τ) ⊢c (Γ' ,, τ)
      addvar θ = p ·rs θ , var i0
  
      ids : {Γ : Ctx} → Γ ⊢c Γ
      ids {[]} = <>
      ids {τ :: Γ} = p ·rs ids , var i0
  
      subst-var : {Γ Γ' : Ctx}{τ : Tp} → Γ ⊢c Γ' → τ ∈ Γ' → Γ ⊢ τ
      subst-var (θ , e) i0 = e
      subst-var (θ , _) (iS x) = subst-var θ x

      subst : {Γ Γ' : Ctx}{τ : Tp} → Γ ⊢c Γ' → Γ' ⊢ τ  → Γ ⊢ τ
      subst θ #t = #t
      subst θ #f = #f
      subst θ (if e₁ then e₂ else e₃) = if subst θ e₁ then subst θ e₂ else subst θ e₃
      subst θ (var x) = subst-var θ x
      subst θ (lam e) = lam (subst (addvar θ) e)
      subst θ (app e e') = app (subst θ e) (subst θ e')
  
      subst1 : {τ τ0 : Tp} → [] ⊢ τ0 → ([] ,, τ0) ⊢ τ → [] ⊢ τ
      subst1 e0 e = subst (<> , e0) e

      -- composition of renamings and substitutions

      _·sr_ : {Γ1 Γ2 Γ3 : Ctx} →  Γ1 ⊢c Γ2 → Γ2 ⊇ Γ3 → Γ1 ⊢c Γ3
      _·sr_ {Γ1} {Γ2} {[]} θ ρ = <>
      _·sr_ {Γ1} {Γ2} {τ3 :: Γ3} θ (ρ , x) = _·sr_ θ ρ , subst-var θ x

      _·ss_ : {Γ1 Γ2 Γ3 : Ctx} → Γ1 ⊢c Γ2 → Γ2 ⊢c Γ3 → Γ1 ⊢c Γ3
      _·ss_ {Γ3 = []} θ1 θ2 = <>
      _·ss_ {Γ1} {Γ2} {τ :: Γ3} θ1 (θ2 , e2) = θ1 ·ss θ2 , subst θ1 e2

  
      -- subst var functoriality

      subst-var-·rs : {Γ1 Γ2 Γ3 : Ctx} (ρ : Γ1 ⊇ Γ2) (θ : Γ2 ⊢c Γ3) {τ : Tp} (x : τ ∈ Γ3)
                           → subst-var (ρ ·rs θ) x == rename ρ (subst-var θ x)
      subst-var-·rs ρ θ i0 = Refl
      subst-var-·rs ρ (θ , _) (iS x) = subst-var-·rs ρ θ x

      subst-var-∘ss : {Γ1 Γ2 Γ3 : Ctx} → (θ2 : Γ1 ⊢c Γ2) (θ3 : Γ2 ⊢c Γ3) {τ : Tp} (x : τ ∈ Γ3)
                        → subst-var (_·ss_ θ2 θ3) x == subst θ2 (subst-var θ3 x)
      subst-var-∘ss θ2 θ3 i0 = Refl
      subst-var-∘ss θ2 (θ3 , _) (iS x) = subst-var-∘ss θ2 θ3 x

      subst-var-·sr : {Γ1 Γ2 Γ3 : Ctx} {τ : Tp} → (θ2 : Γ1 ⊢c Γ2) (ρ : Γ2 ⊇ Γ3) (x : τ ∈ Γ3)
                           → (subst-var θ2 (rename-var ρ x)) == subst-var (_·sr_ θ2 ρ) x
      subst-var-·sr θ2 ρ i0 = Refl
      subst-var-·sr θ2 ρ (iS x) = subst-var-·sr θ2 (fst ρ) x

      subst-var-id : {Γ : Ctx} {τ : Tp} → (x : τ ∈ Γ) → var x == subst-var ids x
      subst-var-id i0 = Refl
      subst-var-id {τ :: Γ} (iS x) = !
        (_ =〈 subst-var-·rs (p· idr) ids x 〉
         rename (p· idr) _ =〈 ! (ap (rename (p· idr)) (subst-var-id x)) 〉
         rename (p· idr) (var x) =〈 ap var (rename-var-p x) 〉
         var (iS x) ∎)


      -- associativity and unit laws for composition.
      -- also includes some β rules for composing with p.
      -- and functoriality of subst in the various compositions, since substitutions involve terms.

      ∘rsr-assoc : {Γ1 Γ2 Γ3 Γ4 : Ctx} → (ρ2 : Γ1 ⊇ Γ2) (θ3 : Γ2 ⊢c Γ3) (ρ4 : Γ3 ⊇ Γ4)
                 → (ρ2 ·rs θ3) ·sr ρ4 == ρ2 ·rs (θ3 ·sr ρ4)
      ∘rsr-assoc {Γ1} {Γ2} {Γ3} {[]} ρ2 θ3 ρ4 = Refl
      ∘rsr-assoc {Γ1} {Γ2} {Γ3} {τ4 :: Γ4} ρ2 θ3 (ρ4 , x4) = ap2 _,_ (∘rsr-assoc ρ2 θ3 ρ4) (subst-var-·rs ρ2 θ3 x4)

      ·sr-pβ'  : {Γ1 Γ2 Γ3 : Ctx} {τ : Tp} → (θ2 : Γ1 ⊢c Γ2) (ρ : Γ2 ⊇ Γ3) {e : _ ⊢ τ}
                → (θ2 , e) ·sr (p· ρ) == θ2 ·sr ρ
      ·sr-pβ' {Γ1} {Γ2} {[]} θ2 ρ = Refl
      ·sr-pβ' {Γ1} {Γ2} {τ :: Γ3} θ2 (ρ , x) = ap2 _,_ (·sr-pβ' θ2 ρ) Refl

      mutual
        ·sr-unitr : {Γ1 Γ2 : Ctx} → (θ : Γ1 ⊢c Γ2) → θ ·sr idr == θ
        ·sr-unitr {Γ1} {[]} θ = Refl
        ·sr-unitr {Γ1} {τ2 :: Γ2} (θ , e) = ap (λ x → x , e) (·sr-pβ θ)
  
        ·sr-pβ  : {Γ1 Γ2 : Ctx} {τ : Tp} → (θ2 : Γ1 ⊢c Γ2) {e : _ ⊢ τ}
                         → (θ2 , e) ·sr p == θ2
        ·sr-pβ θ2 = ·sr-unitr θ2 ∘ ·sr-pβ' θ2 idr

      subst-id : {Γ : Ctx} {τ : Tp} {e : Γ ⊢ τ} → e == subst (ids) e 
      subst-id {e = #t} = Refl
      subst-id {e = #f} = Refl
      subst-id {e = if e₁ then e₂ else e₃} = ap3 if_then_else_ subst-id subst-id subst-id
      subst-id {e = var x} = subst-var-id x
      subst-id {e = lam e} = ap lam (subst-id)
      subst-id {e = app e e₁} = ap2 app subst-id subst-id 

      subst-·rs : {Γ1 Γ2 Γ4 : Ctx} {τ : Tp} → (ρ : Γ4 ⊇ Γ1) (θ2 : Γ1 ⊢c Γ2) (e : Γ2 ⊢ τ)
                → rename ρ (subst θ2 e) == subst (ρ ·rs θ2) e
      subst-·rs ρ θ2 #t = Refl
      subst-·rs ρ θ2 #f = Refl
      subst-·rs ρ θ2 (if e₁ then e₂ else e₃) = ap3 if_then_else_ (subst-·rs ρ θ2 e₁) (subst-·rs ρ θ2 e₂) (subst-·rs ρ θ2 e₃)
      subst-·rs ρ θ2 (var x) = ! (subst-var-·rs ρ θ2 x)
      subst-·rs ρ θ2 (lam e) = ap lam (ap (λ x → subst x e) (ap (λ x → x , var i0) (lemma2 ρ θ2)) ∘ subst-·rs (addvar-ren ρ) (addvar θ2) e) where
              lemma1 : {Γ3 Γ5 : Ctx} (ρ₁ : Γ5 ⊇ Γ3) {τ3 : Tp}
                     →  (addvar-ren {_}{_}{τ3} ρ₁) ·rr (p· idr) == (p· idr) ·rr ρ₁
              lemma1 {Γ3} {Γ5} ρ₁ = (p· ρ₁ , i0) ·rr (p· idr) =〈 Refl 〉
                                   (p· ρ₁ , i0) ·rr  p       =〈 ap (λ x → (x , i0) ·rr p) (p·-def ρ₁)〉 
                                   (p ·rr ρ₁ , i0) ·rr  p    =〈 pβ1 (p ·rr ρ₁) i0 〉 
                                   p ·rr ρ₁                  =〈 Refl 〉
                                   (p· idr) ·rr ρ₁ ∎

              lemma2 : {Γ1 Γ2 Γ4 : Ctx} {τ : Tp} → (ρ : Γ4 ⊇ Γ1) (θ2 : Γ1 ⊢c Γ2) 
                     → (addvar-ren{_}{_}{τ} ρ) ·rs (fst (addvar θ2)) == p ·rs (ρ ·rs θ2)
              lemma2 {Γ2 = []} ρ₁ θ3 = Refl
              lemma2 {Γ2 = τ2 :: Γ2} ρ₁ (θ3 , e3) = ap2 _,_ (lemma2 ρ₁ θ3) 
                         (! (rename-· (p·  idr) ρ₁ e3) ∘ 
                          (ap (λ x → rename x e3) (lemma1 ρ₁) ∘ 
                           rename-· (addvar-ren ρ₁) (p·  idr) e3))
      subst-·rs ρ θ2 (app e e₁) = ap2 app (subst-·rs ρ θ2 e) (subst-·rs ρ θ2 e₁) 

      ·rss-assoc : {Γ1 Γ2 Γ3 Γ4 : Ctx} → (ρ : Γ4 ⊇ Γ1) (θ2 : Γ1 ⊢c Γ2) (θ3 : Γ2 ⊢c Γ3)
                           → ρ ·rs (θ2 ·ss θ3) == (ρ ·rs θ2) ·ss θ3
      ·rss-assoc {Γ1} {Γ2} {[]} ρ θ2 θ3 = Refl
      ·rss-assoc {Γ1} {Γ2} {x :: Γ3} ρ θ2 (θ3 , e3) = ap2 _,_ (·rss-assoc ρ θ2 θ3) (subst-·rs ρ θ2 e3)

      subst-·sr : {Γ1 Γ2 Γ3 : Ctx} {τ : Tp} → (θ2 : Γ1 ⊢c Γ2) (ρ : Γ2 ⊇ Γ3) (e : Γ3 ⊢ τ)
                           → (subst θ2 (rename ρ e)) == subst (θ2 ·sr ρ) e
      subst-·sr θ2 ρ #t = Refl
      subst-·sr θ2 ρ #f = Refl
      subst-·sr θ2 ρ (if e₁ then e₂ else e₃) = ap3 if_then_else_ (subst-·sr θ2 ρ e₁) (subst-·sr θ2 ρ e₂) (subst-·sr θ2 ρ e₃) 
      subst-·sr θ2 ρ (var x) = subst-var-·sr θ2 ρ x
      subst-·sr θ2 ρ (lam e) = ap lam (ap (λ x → subst x e) (ap (λ x → x , var i0) (lemma θ2 ρ)) ∘ subst-·sr (addvar θ2) (addvar-ren ρ) e) where
         lemma :  {Γ1 Γ2 Γ3 : Ctx} {τ : Tp} → (θ2 : Γ1 ⊢c Γ2) (ρ : Γ2 ⊇ Γ3) → (addvar{_}{_}{τ} θ2) ·sr (p· ρ) == p ·rs (θ2 ·sr ρ)
         lemma θ2 ρ = ∘rsr-assoc (p·  idr) θ2 ρ ∘ ·sr-pβ' (_·rs_ (p·  idr) θ2) ρ {var i0}
      subst-·sr θ2 ρ (app e e₁) = ap2 app (subst-·sr θ2 ρ e) (subst-·sr θ2 ρ e₁) 

      ·srs-assoc : {Γ1 Γ2 Γ3 Γ4 : Ctx} (θ : Γ1 ⊢c Γ2) (ρ : Γ2 ⊇ Γ3) (θ' : Γ3 ⊢c Γ4) 
                 → θ ·ss (ρ ·rs θ') == (θ ·sr ρ) ·ss θ'
      ·srs-assoc {Γ1} {Γ2} {Γ3} {[]} θ ρ θ' = Refl
      ·srs-assoc {Γ1} {Γ2} {Γ3} {x :: Γ4} θ ρ (θ' , e') = ap2 _,_ (·srs-assoc θ ρ θ') (subst-·sr θ ρ e')

      subst-·ss : {Γ1 Γ2 Γ3 : Ctx} → (θ2 : Γ1 ⊢c Γ2) (θ3 : Γ2 ⊢c Γ3) {τ : Tp} (e : Γ3 ⊢ τ)
                    → subst (θ2 ·ss θ3) e == subst θ2 (subst θ3 e)
      subst-·ss θ2 θ3 #t = Refl
      subst-·ss θ2 θ3 #f = Refl
      subst-·ss θ2 θ3 (var x) = subst-var-∘ss θ2 θ3 x
      subst-·ss θ2 θ3 (lam e) = ap lam (subst-·ss (addvar θ2) (addvar θ3) e ∘ 
                                            ap (λ x → subst x e) (ap (λ x → x , var i0) 
                                               (lemma1 ∘ ·rss-assoc p θ2 θ3))) where
                    lemma1 : (p ·rs θ2) ·ss θ3 ==
                             (addvar θ2) ·ss (fst (addvar θ3))
                    lemma1 = (p ·rs θ2) ·ss θ3 =〈 ! (ap (λ x → x ·ss θ3) (·sr-pβ (p ·rs θ2) {var i0})) 〉 
                             ((p ·rs θ2 , var i0) ·sr p) ·ss θ3 =〈 ! (·srs-assoc (p ·rs θ2 , var i0) p θ3) 〉
                             (p ·rs θ2 , var i0) ·ss (p ·rs θ3) ∎
      subst-·ss θ2 θ3 (app e e₁) = ap2 app (subst-·ss θ2 θ3 e) (subst-·ss θ2 θ3 e₁)
      subst-·ss θ2 θ3 (if e₁ then e₂ else e₃) = ap3 if_then_else_ (subst-·ss θ2 θ3 e₁) (subst-·ss θ2 θ3 e₂) (subst-·ss θ2 θ3 e₃)

      ·ss-unitl : {Γ1 Γ2 : Ctx} → (θ : Γ1 ⊢c Γ2) → ids ·ss θ == θ
      ·ss-unitl {Γ2 = []} θ = Refl
      ·ss-unitl {Γ2 = τ :: Γ2} (θ , e) = ap2 _,_ (·ss-unitl θ) (! subst-id)

      compose1 : {τ1 τ2 : Tp} {Γ : Ctx} (θ : [] ⊢c Γ) (e' : [] ⊢ τ1) 
               → (θ , e') == (<> , e') ·ss (addvar θ)
      compose1 {τ1}{τ2} θ e' = ap (λ x → x , e') (! (·srs-assoc (<> , e') (p{_}{τ1}) θ) ∘ ! (·ss-unitl θ))

      subst-compose1 : {τ1 τ2 : Tp} {Γ : Ctx} (θ : [] ⊢c Γ) (e' : [] ⊢ τ1) (e : Γ ,, τ1 ⊢ τ2)
              → subst (θ , e') e == subst1 e' (subst (addvar θ) e)
      subst-compose1{τ1}{τ2}{Γ} θ e' e = subst-·ss (<> , e') (addvar θ) e ∘ ap (λ x → subst x e) (compose1{τ1}{τ2}{Γ} θ e')

    open Subst public

  open RenamingAndSubstitution public -- using (_⊇_ ; rename ; subst1 ; _⊢c_ ; subst ; ident ; compose)
