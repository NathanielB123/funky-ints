{-# OPTIONS --cubical #-}
{-# OPTIONS --type-in-type #-}

open import Agda.Primitive.Cubical 
  renaming ( primTransp to transp ; primINeg  to ~_ )
open import Agda.Builtin.Cubical.Path using (_≡_)
open import Agda.Builtin.Nat using (zero; suc) renaming (Nat to ℕ)
open import Agda.Builtin.Int using (pos; negsuc) renaming (Int to ℤ)
open import Agda.Builtin.Unit using (⊤; tt)
open import Function.Base using (_$_; _∘_; id)
open import Data.Empty using (⊥; ⊥-elim)

module FunkyInt where

-- Cubical Utilities
-- These are all defined in the cubical prelude 
-- (https://agda.github.io/cubical/Cubical.Foundations.Prelude.html)
transport : ∀ {a b} → a ≡ b → a → b
transport p a = transp (λ i → p i) i0 a

subst : ∀ {a x y} → (P : a → Set) → x ≡ y → P x → P y
subst B p pa = transport (λ i → B (p i)) pa

sym : ∀ {a} {x y : a} → x ≡ y → y ≡ x
sym p i = p (~ i)

refl : ∀ {a} {x : a} → x ≡ x
refl {x = x} _ = x

cong : ∀ {A} {B : A → Set} {x y} → (f : (a : A) → B a) (p : x ≡ y) →
       PathP (λ i → B (p i)) (f x) (f y)
cong f p i = f (p i)
-- End Cubical Utilities

data FunkyInt : Set where
  Z : FunkyInt
  P : FunkyInt → FunkyInt
  S : FunkyInt → FunkyInt
  n≡n   : ∀ {n} → n ≡ n
  n≡PSn : ∀ {n} → n ≡ P (S n)
  n≡SPn : ∀ {n} → n ≡ S (P n)

pred : ℤ → ℤ
pred (pos (suc n)) = pos n
pred (pos zero   ) = negsuc zero
pred (negsuc n   ) = negsuc $ suc n

succ : ℤ → ℤ
succ (pos n         ) = pos $ suc n
succ (negsuc zero   ) = pos zero
succ (negsuc (suc n)) = negsuc n

eval : FunkyInt → ℤ
eval (Z  ) = pos zero
eval (P n) = pred $ eval n
eval (S n) = succ $ eval n
eval (n≡n   {n} i) = {!!}
eval (n≡PSn {n} i) = {!!}
eval (n≡SPn {n} i) = {!!}

succ-inverts-pred : ∀ {n} → succ (pred n) ≡ n
succ-inverts-pred {pos zero      } = refl
succ-inverts-pred {pos (suc n)   } = refl
succ-inverts-pred {negsuc zero   } = refl
succ-inverts-pred {negsuc (suc n)} = refl

pred-inverts-succ : ∀ {n} → pred (succ n) ≡ n
pred-inverts-succ {pos zero      } = refl
pred-inverts-succ {pos (suc n)   } = refl
pred-inverts-succ {negsuc zero   } = refl
pred-inverts-succ {negsuc (suc n)} = refl

-- Some examples of using the axioms
n≡PSSPn : ∀ {n} → n ≡ P (S $ S $ P n)
n≡PSSPn {n} = subst (λ x → n ≡ P (S x)) n≡SPn n≡PSn

n≡PPSSn : ∀ {n} → n ≡ P (P (S (S n)))
n≡PPSSn {n} = subst (λ x → x ≡ P (P $ S $ S n)) (sym n≡PSn) 
            $ subst (λ x → P (S n) ≡ P x) n≡PSn n≡n

eval⁻¹ : ℤ → FunkyInt
eval⁻¹ (pos zero) = Z
eval⁻¹ (pos (suc n)) = S $ eval⁻¹ (pos n)
eval⁻¹ (negsuc zero) = P Z
eval⁻¹ (negsuc (suc n)) = P $ eval⁻¹ (negsuc n)

lemma-1 : ∀ {n} → eval⁻¹ (succ n) ≡ S (eval⁻¹ n)
lemma-1 {pos zero      } = refl
lemma-1 {pos (suc n)   } = refl
lemma-1 {negsuc zero   } = n≡SPn
lemma-1 {negsuc (suc n)} = n≡SPn

lemma-2 : ∀ {n} → eval⁻¹ (pred n) ≡ P (eval⁻¹ n)
lemma-2 {pos zero      } = refl
lemma-2 {pos (suc n)   } = n≡PSn
lemma-2 {negsuc zero   } = refl
lemma-2 {negsuc (suc n)} = refl

-- Perform large elimination on ℤ in order to prove a contradiction
large-elim : ℤ → Set
large-elim (pos zero)    = ⊤
large-elim (pos (suc _)) = ⊥
large-elim (negsuc n)    = ⊥

⊤≡⊥-elim : ∀ {a : Set} → ⊤ ≡ ⊥ → a
⊤≡⊥-elim ⊤≡⊥ = ⊥-elim $ subst id ⊤≡⊥ tt 

eval⟨a⟩≡b→n≡b : ∀ {a b} → eval a ≡ b → a ≡ eval⁻¹ b
eval⟨a⟩≡b→n≡b {Z} {pos zero   } _ = refl
eval⟨a⟩≡b→n≡b {Z} {pos (suc n)} eval⟨Z⟩≡n+1  
  = ⊤≡⊥-elim $ cong large-elim eval⟨Z⟩≡n+1
eval⟨a⟩≡b→n≡b {Z} {negsuc n   } eval⟨Z⟩≡-n-1 
  = ⊤≡⊥-elim $ cong large-elim eval⟨Z⟩≡-n-1
eval⟨a⟩≡b→n≡b {P a} {b} eval⟨a⟩-1≡b 
  = subst (λ x → P a ≡ x) (sym n≡PSn) $ cong P $ subst (λ x → a ≡ x) lemma-1 
  $ eval⟨a⟩≡b→n≡b $ subst (λ x → x ≡ succ b) succ-inverts-pred 
  $ cong succ eval⟨a⟩-1≡b
eval⟨a⟩≡b→n≡b {S a} {b} eval⟨a⟩+1≡b 
  = subst (λ x → S a ≡ x) (sym n≡SPn) $ cong S $ subst (λ x → a ≡ x) lemma-2 
  $ eval⟨a⟩≡b→n≡b $ subst (λ x → x ≡ pred b) pred-inverts-succ 
  $ cong pred eval⟨a⟩+1≡b
eval⟨a⟩≡b→n≡b {n≡n   a} {b} _ = {!!}
eval⟨a⟩≡b→n≡b {n≡PSn a} {b} _ = {!!}
eval⟨a⟩≡b→n≡b {n≡SPn a} {b} _ = {!!}

0≡eval⟨n⟩→0≡n : ∀ {n} → pos zero ≡ eval n → Z ≡ n
0≡eval⟨n⟩→0≡n = sym ∘ eval⟨a⟩≡b→n≡b ∘ sym

eval⟨a⟩≡eval⟨b⟩→a≡b : ∀ {a b} → eval a ≡ eval b → a ≡ b
eval⟨a⟩≡eval⟨b⟩→a≡b {Z} {b} 0≡eval⟨b⟩ = 0≡eval⟨n⟩→0≡n 0≡eval⟨b⟩
eval⟨a⟩≡eval⟨b⟩→a≡b {P a} {b} eval⟨a⟩-1≡eval⟨b⟩ 
  = subst (λ x → P a ≡ x) (sym n≡PSn) $ cong P $ eval⟨a⟩≡eval⟨b⟩→a≡b 
  $ subst (λ x → x ≡ succ (eval b)) succ-inverts-pred 
  $ cong succ eval⟨a⟩-1≡eval⟨b⟩
eval⟨a⟩≡eval⟨b⟩→a≡b {S a} {b} eval⟨a⟩+1≡eval⟨b⟩ 
  = subst (λ x → S a ≡ x) (sym n≡SPn) $ cong S $ eval⟨a⟩≡eval⟨b⟩→a≡b 
  $ subst (λ x → x ≡ pred (eval b)) pred-inverts-succ 
  $ cong pred eval⟨a⟩+1≡eval⟨b⟩
eval⟨a⟩≡eval⟨b⟩→a≡b {n≡n   _} _ = {!!}
eval⟨a⟩≡eval⟨b⟩→a≡b {n≡PSn _} _ = {!!}
eval⟨a⟩≡eval⟨b⟩→a≡b {n≡SPn _} _ = {!!}
 