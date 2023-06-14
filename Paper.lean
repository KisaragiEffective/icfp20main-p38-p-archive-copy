/-
This file contains all the code from the paper.
For definitions that are part of the Lean standard library,
we print the actual definitions using `#print` rather than duplicating them.
-/
namespace Paper

/-
The following declaration means that these variables can be used in definitions
without declaring them explicitly. Note that the curly braces indicates that they
will be implicit arguments.
-/

variables {α β γ σ : Type} {f : α → β}

-------------------------------------
-- Section 2:  Preliminaries
-------------------------------------

#print Squash
#print Squash.mk
#print Squash.lift

@[inline]
def modifySquash (f : α → α) : StateM (Squash α) Unit :=
modify (λ s => Squash.lift s (λ x => Squash.mk (f x)))

/-
Note: `StateM` is just a specialization of the monad transformer `StateT`,
where the underlying monad is the identity monad Id.
-/
#print StateT
#print StateM
#print StateT.get
#print StateT.set
#print StateT.bind

#print Subsingleton

structure Result (f : α → β) (x : α) : Type := (output : β) (h : output = f x)

-- Note: ⟨...⟩ syntax is used for anonymous constructors.
-- ⟨y, rfl⟩ corresponds to `Result.mk y rfl`
instance Result.Subsingleton {x : α} : Subsingleton (Result f x) :=
⟨λ ⟨y,rfl⟩ ⟨z,rfl⟩ => rfl⟩

#print Decidable

section ToBool

variables {p : Prop}

def toBool : Decidable p → Bool
| Decidable.isTrue _ => true
| Decidable.isFalse _ => false

theorem toBoolEqTrue : ∀ (d : Decidable p) (h : p), toBool d = true
| Decidable.isTrue hp, h => Eq.refl _
| Decidable.isFalse hnp, hp => absurd hp hnp

theorem ofToBoolEqTrue : ∀ (d : Decidable p) (h : toBool d = true), p
| Decidable.isTrue hp, h => hp

theorem ofToBoolEqFalse : ∀ (d : Decidable p) (h : toBool d = false), ¬ p
| Decidable.isFalse hnp, h => hnp

end ToBool

#print condEq

---------------------------------------------
-- Section 3:  Pointer Equality Optimizations
---------------------------------------------

-- [S3.1] withPtrEq
-------------------

#print withPtrEq

@[inline]
def withPtrRel (r : α → α → Bool) (h : ∀ (x : α), r x x = true) : α → α → Bool :=
λ (x y : α) => withPtrEq x y (λ _ => r x y) (λ (p : x = y) => p ▸ h x)

-- [S3.2] One-off pointer equality tests
-----------------------------------------

abbrev Addr := USize

/-
We include the `Addr` field to support intrusive hashing as discussed in S4.1,
though some of our experimental baselines do not use the field.
-/
inductive Term : Type
| one  : Term
| add  : Term → Term → Addr → Term

open Term

/-
Without intrusive hashing, even computing a hash can be exponential time.
-/
def hashTermSlow : Term → Addr
| one => 7
| add t₁ t₂ _ => (mixHash (hashTermSlow t₁) (hashTermSlow t₂))

/-
With intrusive hashing, hashing is constant time.
-/
def hashTermFast : Term → Addr
| one => 7
| add t₁ t₂ h => h

/-
For intrusive hashing to produce the same results as naive hashing,
we need to make sure we always use the following smart constructor `mkAdd`
instead of using `add` directly.
-/
def mkAdd (t₁ t₂ : Term) : Term :=
Term.add t₁ t₂ (mixHash (hashTermFast t₁) (hashTermFast t₂))

/-
Create a tower where the tree size is exponential in the graph size of the term.
-/
def tower : Nat → Term
| 0   => one
| n+1 => let t := tower n; mkAdd t t

/-
Create a tower where, like `tower`, the tree size is exponential
in the graph size of the term but, unlike `tower`, each term is represented
at two distinct addresses in memory.
-/
@[neverExtract]
def twoTowersAux (n : Nat) (t : Term) : Term := mkAdd (tower n) t
def twoTowers (n : Nat) : Term := twoTowersAux (n-1) (tower (n-1))

/-
Naive structural equality check on terms.
-/
def termEqPure : Term → Term → Bool
| one, one => true
| add x₁ y₁ _, add x₂ y₂ _ => termEqPure x₁ x₂ && termEqPure y₁ y₂
| _, _ => false

theorem termEqPureRefl : ∀ (t : Term), termEqPure t t = true
| one => rfl
| add t₁ t₂ _ =>
  let h₁ : termEqPure t₁ t₁ = true := termEqPureRefl t₁;
  let h₂ : termEqPure t₂ t₂ = true := termEqPureRefl t₂;
  show (termEqPure t₁ t₁ && termEqPure t₂ t₂) = true
    from h₁.symm ▸ h₂.symm ▸ rfl

/-
Structural equality check that short-circuits if the roots have the same addresses.
-/
def termEqOneOff : Term → Term → Bool := withPtrRel termEqPure termEqPureRefl

-- [S3.3] Recursive pointer equality tests
------------------------------------------
#print withPtrEqDecEq

/-
Recursive, short-circuiting equality on terms with the intrusive hash.
-/
def termDecEqAux : ∀ (t₁ t₂ : Term), Decidable (t₁ = t₂)
| one, one => isTrue rfl
| add x₁ y₁ hash₁, add x₂ y₂ hash₂ =>
  if h₁ : hash₁ = hash₂ then
    match withPtrEqDecEq x₁ x₂ (λ _ => termDecEqAux x₁ x₂) with
    | isTrue h₂ =>
      match withPtrEqDecEq y₁ y₂ (λ _ => termDecEqAux y₁ y₂) with
      | isTrue h₃  => isTrue (h₁ ▸ h₂ ▸ h₃ ▸ rfl)
      | isFalse h₃ => isFalse (λ h => Term.noConfusion h (λ _ h => absurd h h₃))
    | isFalse h₂   => isFalse (λ h => Term.noConfusion h (λ h _ => absurd h h₂ ))
  else
   isFalse (λ h => Term.noConfusion h (λ _ _ h => absurd h h₁))
| one,       add x y _ => isFalse (λ h => Term.noConfusion h)
| add x y _, one       => isFalse (λ h => Term.noConfusion h)

def termDecEq : ∀ (t₁ t₂ : Term), Decidable (t₁ = t₂) :=
λ t₁ t₂ => withPtrEqDecEq t₁ t₂ (λ _ => termDecEqAux t₁ t₂)

def termEqRec (x y : Term) : Bool := toBool (termDecEq x y)

-----------------------------------------------
-- Section 4: Traversing Terms in Linear Time
-----------------------------------------------

/-
The simplest possible definition of `evalNat`. Evaluating it
directly can take exponential time with the graph size of the term.
-/
def evalNatNoCache : Term → Nat
| Term.one => 1
| Term.add t₁ t₂ _ => evalNatNoCache t₁ + evalNatNoCache t₂

-- [S4.2] Traversing near-perfect towers
-----------------------------------------
section EvalNatCache

/-
Evaluating terms into natural numbers by traversing with a HashMap cache.
It is marked as `partial` because although the recursion is well-founded (WF)
and the proof obligations are simple, well-founded recursion is currently disabled in Lean 4.
To facilitate our performance experiments, we implement the caching version of `evalNat`
parameterized by the choice of equality test and hashing function.
-/
partial def evalNatAux (beq : HasBeq Term) (hashable : Hashable Term) : Term → StateM (@HashMap Term Nat beq hashable) Nat
| t => do
map ← get;
match map.find? t with
| some n => pure n
| none =>
  match t with
  | one => pure 1
  | Term.add t₁ t₂ _ => do
    n₁ ← evalNatAux t₁;
    n₂ ← evalNatAux t₂;
    let n := n₁ + n₂;
    modify (λ map => map.insert t n);
    pure n

def evalNat (beq : HasBeq Term) (hashable : Hashable Term) (t : Term) : Nat :=
Id.run (StateT.run' (evalNatAux beq hashable t) {})

end EvalNatCache

-- [S4.3] Traversing arbitrary terms
-----------------------------------------

/-
The implementation of withShareCommon traverses the memory nodes of
`x` to create a table mapping the subtrees encountered to a pointer
where that subtree is represented in memory. This way, when
encountering a repeated subtree, it can be replaced with a cannonical
address and maximize sharing. As a consequence, for every subtree in
the result of `withShareCommon x`, value equality implies pointer
equality. `withShareCommon x` runs in time linear with the size of
the graph of `x`. -/
#print withShareCommon
#print ShareCommon.State
#print ShareCommon.State.empty
#print shareCommon

def evalNatRobust (beq : HasBeq Term) (hashable : Hashable Term) (t : Term) : Nat := evalNat beq hashable (shareCommon t)

-------------------------------------
-- Section 5:  Extensions
-------------------------------------

#print PtrEqResult
open PtrEqResult

#print withPtrEqResult

structure Entry (f : α → β) : Type := (input : α) (result : Result f input)

def evalReadImpreciseListCacheOneOff (x₀ : α) : List (Entry f) → Result f x₀
| [] => Result.mk (f x₀) rfl -- rfl is the reflexivity proof of type f x₀ = f x₀
| (Entry.mk x r)::es =>
  withPtrEqResult x x₀ (λ (pr : PtrEqResult x x₀) =>
    match x, pr, r with
    | _, yesEqual rfl, r => r
    | _, unknown, _ => evalReadImpreciseListCacheOneOff es)

@[specialize]
def evalImpreciseBucketAux [Subsingleton σ] (x₀ : α) (k : StateM σ (Result f x₀))
  (update : Entry f → StateM σ Unit) : List (Entry f) → StateM σ (Result f x₀)
| [] => do
  r ← k;
  update ⟨x₀, r⟩;
  pure r
| (Entry.mk x r)::es =>
  withPtrEqResult x x₀ (λ (pr : PtrEqResult x x₀) =>
    match x, pr, r with
    | x, yesEqual rfl, r => pure r
    | x, unknown, r => evalImpreciseBucketAux es)

@[inline]
def evalImpreciseBucket (x : α) (k : StateM (Squash (List (Entry f))) (Result f x))
  : StateM (Squash (List (Entry f))) (Result f x) := do
b ← get;
Squash.lift b
  (λ es => evalImpreciseBucketAux x k
    (λ x => modifySquash (λ xs => x :: xs)) es)

/-
Note that Lean defines a slightly more general version of `withPtrAddr` than the one
shown in the paper.
-/
#print withPtrAddr

/-
We define the one in the paper easily in terms of the more general `withPtrAddr`.
-/
@[inline]
def withPtrAddr' [Subsingleton β] (x : α) (k : Addr → β) : β :=
withPtrAddr x k (λ _ _ => Subsingleton.elim _ _)

abbrev PtrCache (f : α → β) : Type := Squash (Array (List (Entry f)))

/-
The monadic type of function that uses and updates a cache and evaluates `f x`.
-/
abbrev PtrCacheM (f : α → β) (x : α) := StateM (PtrCache f) (Result f x)

@[inline]
def evalPtrCache (x : α) (k : PtrCacheM f x) : PtrCacheM f x := do
s ← get;
withPtrAddr' x (λ xₚ =>
  Squash.lift s (λ buckets =>
    if buckets.size = 0 then k else do -- alt: store proof of nonempty in PtrCache type
      -- pointers are word aligned and thus their least significant bits are
      -- two zeros (on 32 bits systems) or three zeros (on 64 bits systems);
      -- dismissing those zeros makes for a better hash code
      let hash := xₚ.toNat / (System.Platform.numBits / 8);
      let i := hash % buckets.size;
      let es := Array.get! buckets i;
      let update (e : Entry f) : StateM (PtrCache f) Unit :=
        modifySquash (λ buckets =>
          Array.modify buckets i (λ es => e :: es));
      evalImpreciseBucketAux x k update es))

/-
Evaluate `evalNat` using the pointer cache.
-/
def evalNatPtrCacheAux : ∀ (t : Term), PtrCacheM evalNatNoCache t
| Term.one => pure ⟨1, rfl⟩ -- by definition `evalNatNoCache one = 1` so
                           -- `⟨1,rfl⟩ : Result evalNatNoCache one`
| Term.add t₁ t₂ _ => do
  ⟨r₁,hr₁⟩ ← evalPtrCache t₁ (evalNatPtrCacheAux t₁);
    -- hr₁ : r₁ = evalNatNoCache t₁
    --
    -- Whether `evalPtrCache` executes the recursive call
    -- `evalNatPtrCacheAux t₁` to evaluate `evalNatNoCache t₁` or
    -- fetches it from the cache, the types guarantee that `r₁` is
    -- the right value and `hr₁` encodes that information.
  ⟨r₂,hr₂⟩ ← evalPtrCache t₂ (evalNatPtrCacheAux t₂);
    -- hr₂ : r₂ = evalNatNoCache t₂
    --
    -- ditto for `r₂`, `t₂` and `hr₂`.
  let hr : r₁ + r₂ = evalNatNoCache t₁ + evalNatNoCache t₂ := hr₁ ▸ hr₂ ▸ rfl;
    -- by using hr₁ and `hr₂`, we prove that `r₁ + r₂` is the right
    -- value to return.
  pure ⟨r₁+r₂, hr⟩

def evalNatPtrCache (t : Term) : Nat :=
((evalNatPtrCacheAux t).run (Squash.mk (mkArray 1000 []))).1.output

/-
Because the return value of `evalNatPtrCacheAux` carries a proof of
its validity, it is easy to verify that the complex logic beneath
`evalNatPtrCache` (i.e. `evalNatPtrCache` and
`evalImpreciseBucketAux`) implements `evalNatNoCache` faithfully (see
`evalNatPtrCache_eq`).
-/
theorem evalNatPtrCache_eq (t : Term) : evalNatPtrCache t = evalNatNoCache t :=
((evalNatPtrCacheAux t).run _).1.h

def evalNatPtrCacheRobust (t : Term) : Nat :=
evalNatPtrCache (shareCommon t)

namespace EvalNats
/-
For convenience, we collect all `evalNat` implementations that we wish to empirically evaluate
into one place.
-/

def evalNatNoCache : Term → Nat := Paper.evalNatNoCache
def evalNatCacheSlowEqSlowHash : Term → Nat := Paper.evalNat ⟨termEqPure⟩ ⟨hashTermSlow⟩
def evalNatCacheSlowEqFastHash : Term → Nat := Paper.evalNat ⟨termEqPure⟩ ⟨hashTermFast⟩
def evalNatCacheFastEqSlowHash : Term → Nat := Paper.evalNat ⟨termEqRec⟩  ⟨hashTermSlow⟩
def evalNatCacheFastEqFastHash : Term → Nat := Paper.evalNat ⟨termEqRec⟩  ⟨hashTermFast⟩
def evalNatCacheFastEqFastHashRobust : Term → Nat := Paper.evalNatRobust ⟨termEqRec⟩  ⟨hashTermFast⟩
def evalNatPtrCache : Term → Nat := Paper.evalNatPtrCache
def evalNatPtrCacheRobust : Term → Nat := Paper.evalNatPtrCacheRobust

end EvalNats

end Paper
