# funky-ints
A short Cubical Agda proof about some funky integers

We define the higher inductive type:
```agda
data FunkyInt : Set where
  Z : FunkyInt
  P : FunkyInt → FunkyInt
  S : FunkyInt → FunkyInt
  n≡n   : ∀ {n} → n ≡ n
  n≡PSn : ∀ {n} → n ≡ P (S n)
  n≡SPn : ∀ {n} → n ≡ S (P n)
```
With an interpretation into `ℤ`:
```agda
eval : FunkyInt → ℤ
eval (Z  ) = pos zero
eval (P n) = pred $ eval n
eval (S n) = succ $ eval n
```
And aim to prove 
```agda
eval⟨a⟩≡eval⟨b⟩→a≡b : ∀ {a b} → eval a ≡ eval b → a ≡ b
```

## TODO

- Fill in remaining holes (cases for the path type constructors - I need to learn what an interval type is lol)
- Avoid relying on `--type-in-type`
