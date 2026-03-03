/-
Copyright (c) 2026 Bashar Hamade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bashar Hamade
-/

import Cslib.Logics.HennessyMilnerLogic.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Lattice  -- Add this for ℕ∞ lattice instances
import Mathlib.Order.Lattice       -- Add this for Sup/Inf typeclasses
import Mathlib.Order.CompleteLattice.Basic
import Cslib.Foundations.Semantics.GameSemantics.BehavoiralEquivalenceSpectrum
/-!
# Formula Expressiveness Prices

This module formalizes the **formula price lattice** (Definition 2.19) and the
**expressiveness price function** (Definition 2.20) from [BispingEtAl2022].

## Overview

The key insight of Bisping et al. is that the linear-time–branching-time spectrum
can be characterized by a six-dimensional price metric measuring the syntactic
complexity of HML formulas. Each behavioral equivalence in the spectrum corresponds
to a rectangular region (upper bounds on each dimension) in this price lattice.

## The Six Dimensions

The price of a formula captures six aspects of its expressive power:

1. **`observations`** (o): Maximum depth of modal operator `⟨a⟩` nesting.
   - Measures how deep we can observe action sequences
   - Example: `⟨a⟩⟨b⟩⊤` has observation depth 2

2. **`conjunctions`** (c): Maximum depth of conjunction nesting.
   - Negations after observations count as implicit conjunctions
   - Captures the branching structure of the formula

3. **`posDeepBranches`** (pdb): Maximum number of positive deep branches per conjunction.
   - "Deep" branches are positive branches that are not just `⟨a⟩⊤`
   - Distinguishes nested conjunctions from flat ones

4. **`posBranches`** (pb): Maximum number of positive (non-negated) branches per conjunction.
   - Counts non-negated conjuncts
   - Distinguishes conjunctions with many positive branches

5. **`negations`** (n): Maximum depth of negation nesting.
   - Measures how deeply negations are nested
   - Used to characterize nested simulation equivalences

6. **`negatedObs`** (no): Maximum observation depth under negations.
   - Captures the complexity of observations within negated subformulas

## Mathematical Structure

The price lattice **Pr** is the complete lattice `(ℕ∞)^6` with:
- Pointwise partial order `≤` (written `⊑` in the paper)
- Pointwise join `⊔` and meet `⊓`
- Bottom `⊥ = (0,0,0,0,0,0)` and top `⊤ = (∞,∞,∞,∞,∞,∞)`

## Observation Languages (Table 1)

Each equivalence in the spectrum corresponds to a rectangular region:

| Language | Bound | Description |
|----------|-------|-------------|
| `O_E` (Enabledness) | `(1,0,0,0,0,0)` | Single observations only |
| `O_T` (Traces) | `(∞,0,0,0,0,0)` | Sequences, no conjunctions |
| `O_F` (Failures) | `(∞,1,0,0,1,1)` | One conjunction of negations |
| `O_R` (Readiness) | `(∞,1,0,∞,1,1)` | Failures + positive flats |
| `O_FT` (Failure-traces) | `(∞,∞,1,1,1,1)` | Interleaved traces and failures |
| `O_RT` (Ready-traces) | `(∞,∞,1,∞,1,1)` | Ready-trace equivalence |
| `O_IF` (Impossible futures) | `(∞,1,0,0,1,∞)` | Single conjunction of negated traces |
| `O_PF` (Possible futures) | `(∞,1,∞,∞,1,∞)` | Mixing positive and negated traces |
| `O_1S` (Simulation) | `(∞,∞,∞,∞,0,0)` | Full conjunctions, no negations |
| `O_RS` (Ready-simulation) | `(∞,∞,∞,∞,1,1)` | Shallow negations allowed |
| `O_nS` (n-nested simulation) | `(∞,∞,∞,∞,n,∞)` | n levels of negation nesting |
| `O_B` (Bisimulation) | `(∞,∞,∞,∞,∞,∞)` | Full HML |

## Main Definitions

- `FormulaPrice`: Six-dimensional price vector over `ℕ∞`
- `FormulaPrice.Lattice`: Complete lattice structure
- `Formula.expr`: Expressiveness price function (Definition 2.20)
- `Formula.exprStandalone`: Standalone price `expr(φ̂)`
- `Formula.isPositiveBranch`, `Formula.isPositiveFlat`: Conjunct classifiers
- `Formula.hat`: The `φ̂` operation for wrapping negations
- `bound_E`, `bound_T`, `bound_F`, etc.: Price bounds for observation languages

## References

* [B. Bisping, D. N. Jansen, and U. Nestmann,
  *Deciding All Behavioral Equivalences at Once:
  A Game for Linear-Time–Branching-Time Spectroscopy*][BispingEtAl2022]
-/

namespace Cslib

open HennessyMilner

universe v

variable {Label : Type v}

/-! ## Formula Price Lattice (Definition 2.19)

The formula price lattice **Pr** is the complete lattice over `(ℕ ∪ {∞})⁶`
with the partial order `⊑` defined by pointwise comparison. -/

/-- Six-dimensional expressiveness price of an HML formula (Definition 2.19).

Each dimension captures a distinct aspect of the syntactic complexity of
formulas in the linear-time–branching-time spectrum:

1. **`observations`**: Depth of modal operator `⟨a⟩` nesting.
   - Counts the maximum number of nested observations `⟨a⟩` along any path
   - Example: `⟨a⟩⟨b⟩⊤` has observation depth 2
   - Example: `⟨a⟩⊤ ∧ ⟨b⟩⊤` has observation depth 1 (conjunction doesn't add)

2. **`conjunctions`**: Depth of conjunction nesting.
   - Negations immediately after observations count as implicit conjunctions
   - Example: `⋀{φ₁, φ₂, φ₃}` has conjunction depth 1
   - Example: `⋀{⋀{φ₁, φ₂}, φ₃}` has conjunction depth 2

3. **`posDeepBranches`**: Maximum number of positive deep branches per conjunction.
   - A "deep" branch is a positive branch that is NOT of the form `⟨a⟩⊤`
   - Distinguishes flat conjunctions (just observations) from nested ones
   - Example: `⋀{⟨a⟩⟨b⟩⊤, ⟨c⟩⊤}` has 1 positive deep branch

4. **`posBranches`**: Maximum number of positive branches per conjunction.
   - Counts all non-negated conjuncts
   - Example: `⋀{φ, ¬ψ, χ}` has 2 positive branches (φ and χ)

5. **`negations`**: Depth of negation nesting.
   - Counts how deeply negations are nested
   - Used to characterize nested simulation equivalences
   - Example: `¬¬φ` has negation depth 2

6. **`negatedObs`**: Maximum observation depth under each negation.
   - Measures the observation complexity within negated subformulas
   - Example: `¬⟨a⟩⟨b⟩⊤` has negated observation depth 2

The type `ℕ∞` (extended natural numbers) allows representing both finite
bounds (natural numbers) and infinite bounds (⊤ = ∞) for each dimension.

## Mathematical Properties

`FormulaPrice` forms a complete lattice with:
- Partial order: pointwise comparison `≤`
- Join: pointwise maximum `⊔`
- Meet: pointwise minimum `⊓`
- Bottom: `(0,0,0,0,0,0)` - the price of `⊤`
- Top: `(∞,∞,∞,∞,∞,∞)` - unbounded expressiveness

## Implementation Notes

We use `ℕ∞` (from Mathlib) which is `ℕ ∪ {∞}` with the standard order where
`n < ∞` for all `n : ℕ`. This allows us to represent both concrete finite
bounds and "unbounded" (∞) for each dimension.
-/
structure FormulaPrice where
  /-- Dimension 1: depth of modal operator nesting. -/
  observations : ℕ∞
  /-- Dimension 2: depth of conjunction nesting. -/
  conjunctions    : ℕ∞
  /-- Dimension 3: max positive deep branches per conjunction. -/
  posDeepBranches : ℕ∞
  /-- Dimension 4: max positive branches per conjunction. -/
  posBranches     : ℕ∞
  /-- Dimension 5: depth of negation nesting. -/
  negations       : ℕ∞
  /-- Dimension 6: max observation depth under negations. -/
  negatedObs      : ℕ∞
  deriving DecidableEq, Inhabited

namespace FormulaPrice

/-! ### Lattice Structure (Definition 2.19)

The formula price lattice **Pr** is defined as the complete lattice over `(ℕ∞)^6`
with the partial order `⊑` (written as `≤` in Lean) defined by pointwise comparison.

For two prices `p = (p₁,...,p₆)` and `q = (q₁,...,q₆)`:
- `p ≤ q` iff `pᵢ ≤ qᵢ` for all `i ∈ {1,...,6}`
- `p ⊔ q = (p₁ ⊔ q₁, ..., p₆ ⊔ q₆)` (componentwise maximum)
- `p ⊓ q = (p₁ ⊓ q₁, ..., p₆ ⊓ q₆)` (componentwise minimum)
- `⊥ = (0,0,0,0,0,0)` (bottom element)
- `⊤ = (∞,∞,∞,∞,∞,∞)` (top element)

This structure makes `FormulaPrice` a **bounded complete lattice**, which is essential
for defining the expressiveness price of composite formulas (conjunctions, disjunctions
via supremum of constituent prices).

## Why Pointwise?

The pointwise ordering reflects the intuition that:
- A formula with lower price is "simpler" (belongs to coarser equivalences)
- A formula with higher price is more expressive (belongs to finer equivalences)
- The join (`⊔`) captures the price of alternatives (disjunctive information)

This aligns with the paper's notion that observation languages form rectangular regions
in this price lattice. -/

/-- Extensionality principle for `FormulaPrice`. -/
@[ext]
theorem ext {a b : FormulaPrice}
    (h1 : a.observations = b.observations)
    (h2 : a.conjunctions = b.conjunctions)
    (h3 : a.posDeepBranches = b.posDeepBranches)
    (h4 : a.posBranches = b.posBranches)
    (h5 : a.negations = b.negations)
    (h6 : a.negatedObs = b.negatedObs) : a = b := by
  cases a; cases b; simp_all

/-- Pointwise `≤` on `FormulaPrice` (the `⊑` of the paper). -/
instance : LE FormulaPrice where
  le a b := a.observations ≤ b.observations ∧
            a.conjunctions ≤ b.conjunctions ∧
            a.posDeepBranches ≤ b.posDeepBranches ∧
            a.posBranches ≤ b.posBranches ∧
            a.negations ≤ b.negations ∧
            a.negatedObs ≤ b.negatedObs

/-- Strict comparison `⊏` derived from `⊑`. -/
instance : LT FormulaPrice where
  lt a b := a ≤ b ∧ ¬(b ≤ a)

/-- Bottom element `⊥ = (0, 0, 0, 0, 0, 0)`. -/
instance : Bot FormulaPrice where
  bot := ⟨0, 0, 0, 0, 0, 0⟩

/-- Top element `⊤ = (∞, ∞, ∞, ∞, ∞, ∞)`. -/
instance : Top FormulaPrice where
  top := ⟨⊤, ⊤, ⊤, ⊤, ⊤, ⊤⟩

/-- Unpacking `≤` into component-wise conditions. -/
theorem le_def (a b : FormulaPrice) :
    a ≤ b ↔ a.observations ≤ b.observations ∧
            a.conjunctions ≤ b.conjunctions ∧
            a.posDeepBranches ≤ b.posDeepBranches ∧
            a.posBranches ≤ b.posBranches ∧
            a.negations ≤ b.negations ∧
            a.negatedObs ≤ b.negatedObs :=
  Iff.rfl

noncomputable def psup (a b : FormulaPrice) : FormulaPrice :=
  ⟨a.observations ⊔ b.observations,
   a.conjunctions ⊔ b.conjunctions,
   a.posDeepBranches ⊔ b.posDeepBranches,
   a.posBranches ⊔ b.posBranches,
   a.negations ⊔ b.negations,
   a.negatedObs ⊔ b.negatedObs⟩

noncomputable def pinf (a b : FormulaPrice) : FormulaPrice :=
  ⟨a.observations ⊓ b.observations,
   a.conjunctions ⊓ b.conjunctions,
   a.posDeepBranches ⊓ b.posDeepBranches,
   a.posBranches ⊓ b.posBranches,
   a.negations ⊓ b.negations,
   a.negatedObs ⊓ b.negatedObs⟩

@[simp] theorem psup_observations (a b : FormulaPrice) :
    (psup a b).observations = a.observations ⊔ b.observations := rfl
@[simp] theorem psup_conjunctions (a b : FormulaPrice) :
    (psup a b).conjunctions = a.conjunctions ⊔ b.conjunctions := rfl
@[simp] theorem psup_posDeepBranches (a b : FormulaPrice) :
    (psup a b).posDeepBranches = a.posDeepBranches ⊔ b.posDeepBranches := rfl
@[simp] theorem psup_posBranches (a b : FormulaPrice) :
    (psup a b).posBranches = a.posBranches ⊔ b.posBranches := rfl
@[simp] theorem psup_negations (a b : FormulaPrice) :
    (psup a b).negations = a.negations ⊔ b.negations := rfl
@[simp] theorem psup_negatedObs (a b : FormulaPrice) :
    (psup a b).negatedObs = a.negatedObs ⊔ b.negatedObs := rfl

@[simp] theorem pinf_observations (a b : FormulaPrice) :
    (pinf a b).observations = a.observations ⊓ b.observations := rfl
@[simp] theorem pinf_conjunctions (a b : FormulaPrice) :
    (pinf a b).conjunctions = a.conjunctions ⊓ b.conjunctions := rfl
@[simp] theorem pinf_posDeepBranches (a b : FormulaPrice) :
    (pinf a b).posDeepBranches = a.posDeepBranches ⊓ b.posDeepBranches := rfl
@[simp] theorem pinf_posBranches (a b : FormulaPrice) :
    (pinf a b).posBranches = a.posBranches ⊓ b.posBranches := rfl
@[simp] theorem pinf_negations (a b : FormulaPrice) :
    (pinf a b).negations = a.negations ⊓ b.negations := rfl
@[simp] theorem pinf_negatedObs (a b : FormulaPrice) :
    (pinf a b).negatedObs = a.negatedObs ⊓ b.negatedObs := rfl

@[simp] theorem bot_observations : (⊥ : FormulaPrice).observations = 0 := rfl
@[simp] theorem bot_conjunctions : (⊥ : FormulaPrice).conjunctions = 0 := rfl
@[simp] theorem bot_posDeepBranches : (⊥ : FormulaPrice).posDeepBranches = 0 := rfl
@[simp] theorem bot_posBranches : (⊥ : FormulaPrice).posBranches = 0 := rfl
@[simp] theorem bot_negations : (⊥ : FormulaPrice).negations = 0 := rfl
@[simp] theorem bot_negatedObs : (⊥ : FormulaPrice).negatedObs = 0 := rfl

@[simp] theorem top_observations : (⊤ : FormulaPrice).observations = ⊤ := rfl
@[simp] theorem top_conjunctions : (⊤ : FormulaPrice).conjunctions = ⊤ := rfl
@[simp] theorem top_posDeepBranches : (⊤ : FormulaPrice).posDeepBranches = ⊤ := rfl
@[simp] theorem top_posBranches : (⊤ : FormulaPrice).posBranches = ⊤ := rfl
@[simp] theorem top_negations : (⊤ : FormulaPrice).negations = ⊤ := rfl
@[simp] theorem top_negatedObs : (⊤ : FormulaPrice).negatedObs = ⊤ := rfl

/-! #### Order instances -/

instance : Preorder FormulaPrice where
  le_refl a := by simp [le_def]
  le_trans a b c hab hbc := by
    simp only [le_def] at *
    exact ⟨le_trans hab.1 hbc.1,
           le_trans hab.2.1 hbc.2.1,
           le_trans hab.2.2.1 hbc.2.2.1,
           le_trans hab.2.2.2.1 hbc.2.2.2.1,
           le_trans hab.2.2.2.2.1 hbc.2.2.2.2.1,
           le_trans hab.2.2.2.2.2 hbc.2.2.2.2.2⟩

instance : PartialOrder FormulaPrice where
  le_antisymm a b hab hba := by
    simp only [le_def] at hab hba
    ext <;>
    apply le_antisymm
    <;> grind




noncomputable instance : SemilatticeSup FormulaPrice where
  sup := psup
  le_sup_left a b := by simp [le_def, psup, le_sup_left]
  le_sup_right a b := by simp [le_def, psup, le_sup_right]
  sup_le a b c hac hbc := by
    simp only [le_def, psup] at *
    grind


noncomputable instance : SemilatticeInf FormulaPrice where
  inf := pinf
  inf_le_left a b := by simp [le_def, pinf]
  inf_le_right a b := by simp [le_def]
  le_inf a b c hac hbc := by
    simp only [le_def] at *
    <;> constructor ; simp ; grind
    simp
    grind





/-! #### Accessor lemmas -/

@[simp] theorem sup_observations (a b : FormulaPrice) :
    (a ⊔ b).observations = a.observations ⊔ b.observations := rfl
@[simp] theorem sup_conjunctions (a b : FormulaPrice) :
    (a ⊔ b).conjunctions = a.conjunctions ⊔ b.conjunctions := rfl
@[simp] theorem sup_posDeepBranches (a b : FormulaPrice) :
    (a ⊔ b).posDeepBranches = a.posDeepBranches ⊔ b.posDeepBranches := rfl
@[simp] theorem sup_posBranches (a b : FormulaPrice) :
    (a ⊔ b).posBranches = a.posBranches ⊔ b.posBranches := rfl
@[simp] theorem sup_negations (a b : FormulaPrice) :
    (a ⊔ b).negations = a.negations ⊔ b.negations := rfl
@[simp] theorem sup_negatedObs (a b : FormulaPrice) :
    (a ⊔ b).negatedObs = a.negatedObs ⊔ b.negatedObs := rfl

@[simp] theorem inf_observations (a b : FormulaPrice) :
    (a ⊓ b).observations = a.observations ⊓ b.observations := rfl
@[simp] theorem inf_conjunctions (a b : FormulaPrice) :
    (a ⊓ b).conjunctions = a.conjunctions ⊓ b.conjunctions := rfl
@[simp] theorem inf_posDeepBranches (a b : FormulaPrice) :
    (a ⊓ b).posDeepBranches = a.posDeepBranches ⊓ b.posDeepBranches := rfl
@[simp] theorem inf_posBranches (a b : FormulaPrice) :
    (a ⊓ b).posBranches = a.posBranches ⊓ b.posBranches := rfl
@[simp] theorem inf_negations (a b : FormulaPrice) :
    (a ⊓ b).negations = a.negations ⊓ b.negations := rfl
@[simp] theorem inf_negatedObs (a b : FormulaPrice) :
    (a ⊓ b).negatedObs = a.negatedObs ⊓ b.negatedObs := rfl


noncomputable instance : Lattice FormulaPrice where
  __ := FormulaPrice.instSemilatticeSup
  __ := FormulaPrice.instSemilatticeInf


instance : OrderBot FormulaPrice where
  bot_le a := by simp [le_def]

instance : OrderTop FormulaPrice where
  le_top a := by simp [le_def, le_top]

instance : BoundedOrder FormulaPrice where
  __ := FormulaPrice.instOrderBot
  __ := FormulaPrice.instOrderTop

/-! #### Convenience constructors -/

/-- Build a price with a single nonzero dimension. -/
def ofObs (n : ℕ∞) : FormulaPrice          := ⟨n, 0, 0, 0, 0, 0⟩
def ofConj (n : ℕ∞) : FormulaPrice         := ⟨0, n, 0, 0, 0, 0⟩
def ofPosDeep (n : ℕ∞) : FormulaPrice      := ⟨0, 0, n, 0, 0, 0⟩
def ofPosBranch (n : ℕ∞) : FormulaPrice    := ⟨0, 0, 0, n, 0, 0⟩
def ofNeg (n : ℕ∞) : FormulaPrice          := ⟨0, 0, 0, 0, n, 0⟩
def ofNegObs (n : ℕ∞) : FormulaPrice       := ⟨0, 0, 0, 0, 0, n⟩

namespace Formula

variable {Label : Type v}

/-- Check if a formula is a negation: `∃φ'. φ = ¬φ'`. -/
def isNeg : Formula Label → Bool
  | .neg _ => true
  | _      => false

/-- The hat operation `φ̂`: wraps negations in singleton conjunctions. -/
def hat : Formula Label → Formula Label
  | .neg φ => .conj [.neg φ]
  | φ      => φ

@[simp] theorem hat_neg (φ : Formula Label) : hat (.neg φ) = .conj [.neg φ] := rfl
@[simp] theorem hat_modal (a : Label) (φ : Formula Label) : hat (.modal a φ) = .modal a φ := rfl
@[simp] theorem hat_conj (φs : List (Formula Label)) : hat (.conj φs) = .conj φs := rfl

/-! ### Positive Branches (pb)

The **positive branches** of a conjunction are the conjuncts that are not negations.
Formally, for a conjunction `⋀{φ₁, ..., φₙ}`:

$$pb = \{\varphi_i \mid \not\exists \varphi'. \varphi_i = \neg \varphi'\}$$

This classification is crucial for dimensions 3 and 4 of the price lattice:
- **`posBranches`**: The count `|pb|` of all positive branches
- **`posDeepBranches`**: The count of positive branches that are NOT of the form `⟨a⟩⊤`

## Intuition

In the linear-time–branching-time spectrum, different equivalences allow different
kinds of conjunctions:

- **Traces** (`O_T`): No conjunctions at all
- **Failures** (`O_F`): One conjunction of negated observations only
- **Readiness** (`O_R`): One conjunction mixing negations and positive flats `⟨a⟩⊤`
- **Simulation** (`O_1S`): Arbitrary conjunctions, but no negations
- **Bisimulation** (`O_B`): Arbitrary conjunctions with negations

The `posBranches` and `posDeepBranches` dimensions capture exactly these distinctions.

## Examples

- `⋀{⟨a⟩⊤, ⟨b⟩⊤}`: 2 positive branches, 0 positive deep branches (both are flats)
- `⋀{⟨a⟩⟨b⟩⊤, ⟨c⟩⊤}`: 2 positive branches, 1 positive deep branch (`⟨a⟩⟨b⟩⊤` is deep)
- `⋀{¬⟨a⟩⊤, ⟨b⟩⊤}`: 1 positive branch, 0 positive deep branches (the negation doesn't count)
- `⋀{¬⟨a⟩⊤, ¬⟨b⟩⊤}`: 0 positive branches, 0 positive deep branches (all negated)

## Implementation Notes

We define:
- `isPositiveBranch φ`: Returns true if `φ` is not a negation
- `positiveBranches φs`: Filters the list to keep only positive branches
- `countPosBranches φs`: The cardinality `|pb|`
- `isPositiveFlat φ`: Returns true if `φ = ⟨a⟩⊤` for some action `a`
- `positiveFlatBranches φs`: Filters to keep only positive flat branches
- `countPosFlatBranches φs`: The cardinality `|pf|`
- `countPosDeepBranches φs`: Computes `|pb| - |pf|` (deep branches only)

The subtraction is safe because `pf ⊆ pb` (every flat branch is a positive branch). -/

/-- **Positive Branch Classifier**: Returns true if `φ` is not a negation.

A positive branch is a conjunct that is not of the form `¬ψ`.

## Examples
- `isPositiveBranch ⟨a⟩⊤ = true` (observations are positive)
- `isPositiveBranch (⋀{φ₁, φ₂}) = true` (conjunctions are positive)
- `isPositiveBranch (¬φ) = false` (negations are not positive)

Used to compute `countPosBranches` and `positiveBranches`. -/
def isPositiveBranch (φ : Formula Label) : Bool := !(isNeg φ)

/-- The list of positive branches in a conjunction. -/
def positiveBranches (φs : List (Formula Label)) : List (Formula Label) :=
  φs.filter isPositiveBranch

/-- Count of positive branches: `|pb|`. -/
def countPosBranches (φs : List (Formula Label)) : ℕ :=
  (positiveBranches φs).length

/-- Check if a formula is a positive flat branch `⟨a⟩⊤`. -/
def isPositiveFlat : Formula Label → Bool
  | .modal _ (.conj []) => true
  | _                   => false

/-- The list of positive flat branches in a conjunction. -/
def positiveFlatBranches (φs : List (Formula Label)) : List (Formula Label) :=
  φs.filter isPositiveFlat

/-- Count of positive flat branches: `|pf|`. -/
def countPosFlatBranches (φs : List (Formula Label)) : ℕ :=
  (positiveFlatBranches φs).length

/-- Count of positive deep branches: `|pb| - |pf|`. -/
def countPosDeepBranches (φs : List (Formula Label)) : ℕ :=
  countPosBranches φs - countPosFlatBranches φs

/-- **List Supremum** for extended natural numbers (`ℕ∞`).

Computes the supremum (least upper bound) of a list of `ℕ∞` values by folding
with the maximum operation (`⊔`).

## Mathematical Properties

- `listSupENat [] = 0` (identity element for `⊔`)
- `listSupENat [x₁, ..., xₙ] = x₁ ⊔ x₂ ⊔ ... ⊔ xₙ ⊔ 0`
- For any `b : ℕ∞`, if `∀ x ∈ xs, x ≤ b`, then `listSupENat xs ≤ b`

## Usage

Used to compute the maximum conjunction depth across all conjuncts in the
`conjunctions` dimension of `expr`:

```
conjunctions = listSupENat (es.map (fun e => 1 + e.conjunctions))
```

This gives the maximum `1 + e.conjunctions` over all conjunct prices `e`,
which represents the conjunction nesting depth of the current formula. -/
noncomputable def listSupENat (xs : List ℕ∞) : ℕ∞ :=
  xs.foldl (· ⊔ ·) 0


/-- **List Supremum** for formula prices.

Computes the pointwise supremum of a list of `FormulaPrice` values by folding
with the join operation (`⊔`).

## Mathematical Properties

- `listSupPrice [] = ⊥ = (0,0,0,0,0,0)` (bottom element)
- `listSupPrice [p₁, ..., pₙ] = p₁ ⊔ p₂ ⊔ ... ⊔ pₙ ⊔ ⊥`
- Each dimension is computed independently using `listSupENat`

## Usage

Used in `expr` for conjunctions to compute the supremum of all conjunct prices:

```
localPrice ⊔ listSupPrice es
```

This captures the "worst case" price among all conjuncts, which is necessary
for characterizing the expressiveness of the entire conjunction. -/
noncomputable def listSupPrice (ps : List FormulaPrice) : FormulaPrice :=
  ps.foldl (· ⊔ ·) ⊥


/-! ### Size for termination proofs -/

/-- Syntactic size of a formula for well-founded recursion. -/
def Formula.fsize : Formula Label → ℕ
  | .modal _ φ => 1 + (Formula.fsize φ)
  | .neg φ => 1 + (Formula.fsize φ)
  | .conj φs => 1 + φs.foldr (fun φ acc => (Formula.fsize φ) + acc) 0

/-- Elements of a list have smaller size than the conjunction. -/
theorem Formula.fsize_lt_conj {φ : Formula Label} {φs : List (Formula Label)}
    (h : φ ∈ φs) : Formula.fsize φ < Formula.fsize (Formula.conj φs) := by
  simp only [Formula.fsize]
  induction φs with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.foldr_cons]
    cases h with
    | head => omega
    | tail _ htl =>
      have := ih htl
      omega

/-- The expressiveness price function `expr(φ)` (Definition 2.20).

Computes the six-dimensional price of an HML formula. The price captures the
formula's position in the linear-time–branching-time spectrum.

## Pricing Rules

### Observations: `⟨a⟩φ`

An observation `⟨a⟩φ` contributes:
- `observations`: `1 + expr(φ).observations` (adds one observation level)
- Other dimensions from `expr(φ̂)` (the "hat" of φ)

The hat operation `φ̂` handles negations specially:
- If `φ = ¬ψ`, then `φ̂ = ⋀{¬ψ}` (wraps negation in singleton conjunction)
- Otherwise `φ̂ = φ`

This accounts for the implicit conjunction created when negations follow observations.

### Negations: `¬φ`

A negation `¬φ` contributes:
- `negations`: `1 + expr(φ).negations` (adds one negation level)
- `negatedObs`: `expr(φ).observations` (captures observation depth under negation)
- Plus the price of `φ` itself

### Conjunctions: `⋀{φ₁, ..., φₙ}`

A conjunction contributes:
- `conjunctions`: `⊔ᵢ(1 + expr(φᵢ).conjunctions)` (max conjunction depth + 1)
- `posDeepBranches`: `|pb| - |pf|` (deep branches only)
- `posBranches`: `|pb|` (all positive branches)
- Plus the supremum of all `expr(φᵢ)`

The conjunction depth is computed as the supremum (maximum) over all conjuncts,
reflecting the "deepest" branch.

## Termination

The function uses well-founded recursion on `Formula.fsize φ`, which measures
syntactic size. Each recursive call is on a structurally smaller subformula.

## Implementation Notes

We inline `expr(φ̂)` in the modal case to avoid termination issues:
- When `φ` is a negation, `hat φ = ⋀{φ}` which is NOT structurally smaller
- By inlining, we compute the price directly without an explicit recursive call
- For other cases, `hat φ = φ` which is structurally equal
-/
noncomputable def expr : Formula Label → FormulaPrice
  | .modal _a φ =>
      have : Formula.fsize φ < Formula.fsize (.modal _a φ) := by
        simp [Formula.fsize];
      let e := expr φ
      let localPrice : FormulaPrice := ⟨1 + e.observations, 0, 0, 0, 0, 0⟩
      -- Inline expr(φ̂) to avoid termination issues:
      -- When φ is a negation: hat φ = ⋀{φ}, so expr(hat φ) = ⟨0, 1+e.conj, 0, 0, 0, 0⟩ ⊔ e
      -- When φ is not a negation: hat φ = φ, so expr(hat φ) = e
      let hatExpr := match φ with
        | .neg _ => ⟨0, 1 + e.conjunctions, 0, 0, 0, 0⟩ ⊔ e
        | _      => e
      localPrice ⊔ hatExpr

  | .neg φ =>
      have : Formula.fsize φ < Formula.fsize (.neg φ) := by
        simp [Formula.fsize];
      let e := expr φ
      let localPrice : FormulaPrice := ⟨0, 0, 0, 0, 1 + e.negations, e.observations⟩
      localPrice ⊔ e

    | .conj φs =>
      let es := φs.attach.map (fun ⟨φ, hφ⟩ =>
        have : Formula.fsize φ < Formula.fsize (.conj φs) :=
          Formula.fsize_lt_conj hφ
        expr φ)
      let conjDepths := es.map (fun e => 1 + e.conjunctions)
      let localPrice : FormulaPrice :=
        ⟨0,
         listSupENat conjDepths,
         countPosDeepBranches φs,
         countPosBranches φs,
         0,
         0⟩
      localPrice ⊔ listSupPrice es
termination_by φ => (Formula.fsize φ)

/-- **Standalone Expressiveness Price**: `expr(φ̂)`.

Computes the expressiveness price of the "hat" of a formula. The hat operation
`φ̂` wraps bare negations in singleton conjunctions to ensure proper accounting
of conjunction depth.

## The Hat Operation

For any formula `φ`:
- If `φ = ¬ψ` (a bare negation), then `φ̂ = ⋀{¬ψ}` (wrap in singleton conjunction)
- Otherwise, `φ̂ = φ` (leave unchanged)

## Purpose

The standalone price is used for characterization theorems. A formula `φ`
belongs to observation language `O_X` if and only if:

```
exprStandalone φ ≤ bound_X
```

## Why the Hat?

Without the hat, bare negations like `¬⟨a⟩⊤` would have:
- `conjunctions = 0` (no explicit conjunction)
- `negations = 1`

But in the game semantics, a negation after an observation implicitly creates
a conjunction context. The hat makes this explicit, giving:
- `conjunctions = 1` (the singleton conjunction)
- `negations = 1`

This correctly places `¬⟨a⟩⊤` in the failures language `O_F` which requires
`conjunctions ≤ 1`. -/
noncomputable def exprStandalone (φ : Formula Label) : FormulaPrice :=
  expr (hat φ)


/-! ## Price Bounds for Observation Languages (Table 1)

Each observation language from the linear-time–branching-time spectrum corresponds
to a rectangular region (upper bounds) in the price lattice. This section defines
the bounds for each language from Table 1 of [BispingEtAl2022].

## Characterization Theorem (Lemma 2.23)

A formula `φ` belongs to observation language `O_X` if and only if:

```
expr(φ̂) ≤ bound_X
```

where `φ̂` is the hat operation (wrapping bare negations in singleton conjunctions)
and `≤` is the pointwise order on prices.

## Bounds Summary

| Language | Notation | Bound (o,c,pdb,pb,n,no) | Description |
|----------|----------|------------------------|-------------|
| Enabledness | `O_E` | `(1,0,0,0,0,0)` | Single observations `⟨a⟩⊤` |
| Traces | `O_T` | `(∞,0,0,0,0,0)` | Observation sequences only |
| Failures | `O_F` | `(∞,1,0,0,1,1)` | One conjunction of negated observations |
| Readiness | `O_R` | `(∞,1,0,∞,1,1)` | Failures + positive flat branches |
| Failure-traces | `O_FT` | `(∞,∞,1,1,1,1)` | Interleaved traces and failures |
| Ready-traces | `O_RT` | `(∞,∞,1,∞,1,1)` | Ready-trace equivalence |
| Impossible futures | `O_IF` | `(∞,1,0,0,1,∞)` | One conjunction of negated traces |
| Possible futures | `O_PF` | `(∞,1,∞,∞,1,∞)` | Mixing positive and negated traces |
| Simulation | `O_1S` | `(∞,∞,∞,∞,0,0)` | Full conjunctions, no negations |
| Ready-simulation | `O_RS` | `(∞,∞,∞,∞,1,1)` | Shallow negations only |
| n-nested simulation | `O_nS` | `(∞,∞,∞,∞,n,∞)` | n levels of negation nesting |
| Bisimulation | `O_B` | `(∞,∞,∞,∞,∞,∞)` | Full HML |

## Notation

- `∞` (⊤): Unbounded in this dimension
- `o`: observations
- `c`: conjunctions
- `pdb`: positive deep branches
- `pb`: positive branches
- `n`: negations
- `no`: negated observations

## Inclusion Hierarchy

The bounds form a lattice under inclusion. Finer equivalences have larger bounds:

```
bound_E ≤ bound_T ≤ bound_F ≤ bound_R ≤ bound_RT ≤ bound_RS ≤ bound_2S ≤ ... ≤ bound_B
          bound_T ≤ bound_1S ≤ bound_RS
          bound_F ≤ bound_FT ≤ bound_RT
          bound_F ≤ bound_IF ≤ bound_PF ≤ bound_2S
```

These inclusions are proven in the section "Inclusion Lemmas" below. -/

namespace ObservationLanguage

open FormulaPrice

/-- **Enabledness** `O_E`: `(1, 0, 0, 0, 0, 0)`.

The simplest observation language. Only single observations `⟨a⟩⊤` are allowed.

- `observations = 1`: At most one observation (no nesting)
- `conjunctions = 0`: No conjunctions allowed
- `negations = 0`: No negations allowed

Corresponds to formulas that can only observe single actions. -/
def bound_E : FormulaPrice := ⟨1, 0, 0, 0, 0, 0⟩

/-- **Traces** `O_T`: `(∞, 0, 0, 0, 0, 0)`.

Trace formulas are sequences of observations `⟨a₁⟩⟨a₂⟩...⟨aₙ⟩⊤`.

- `observations = ∞`: Unbounded observation depth (arbitrary sequences)
- `conjunctions = 0`: No conjunctions (linear traces only)
- `negations = 0`: No negations

This is the language of trace equivalence. -/
def bound_T : FormulaPrice := ⟨⊤, 0, 0, 0, 0, 0⟩

/-- **Failures** `O_F`: `(∞, 1, 0, 0, 1, 1)`.

Failure formulas extend traces with a single conjunction of negated observations.
Example: `⟨a₁⟩...⟨aₙ⟩⋀{¬⟨b₁⟩⊤, ..., ¬⟨bₖ⟩⊤}`.

- `observations = ∞`: Unbounded trace prefix
- `conjunctions = 1`: Exactly one conjunction (at the end)
- `posBranches = 0`: Only negated branches in the conjunction
- `negations = 1`: One level of negation
- `negatedObs = 1`: Simple observations under negation

Characterizes failures equivalence (must/should testing). -/
def bound_F : FormulaPrice := ⟨⊤, 1, 0, 0, 1, 1⟩

/-- **Readiness** `O_R`: `(∞, 1, 0, ∞, 1, 1)`.

Readiness formulas extend failures with positive flat branches.
Example: `⟨a₁⟩...⟨aₙ⟩⋀{⟨b₁⟩⊤, ..., ⟨bₖ⟩⊤, ¬⟨c₁⟩⊤, ..., ¬⟨cₘ⟩⊤}`.

- `observations = ∞`: Unbounded trace prefix
- `conjunctions = 1`: Exactly one conjunction
- `posBranches = ∞`: Arbitrary positive flat branches `⟨b⟩⊤`
- `posDeepBranches = 0`: No deep positive branches
- `negations = 1`: One level of negation

Characterizes readiness equivalence. -/
def bound_R : FormulaPrice := ⟨⊤, 1, 0, ⊤, 1, 1⟩

/-- **Failure-Traces** `O_FT`: `(∞, ∞, 1, 1, 1, 1)`.

Failure-trace formulas allow interleaving of traces and failure sets.
They can have nested conjunctions with at most one deep positive branch.

- `observations = ∞`: Unbounded
- `conjunctions = ∞`: Nested conjunctions allowed
- `posDeepBranches = 1`: At most one deep positive branch per conjunction
- `posBranches = 1`: At most one positive branch per conjunction
- `negations = 1`: One level of negation

Characterizes failure-trace equivalence. -/
def bound_FT : FormulaPrice := ⟨⊤, ⊤, 1, 1, 1, 1⟩

/-- **Ready-Traces** `O_RT`: `(∞, ∞, 1, ∞, 1, 1)`.

Ready-trace formulas extend failure-traces with arbitrary positive branches.

- `observations = ∞`: Unbounded
- `conjunctions = ∞`: Nested conjunctions allowed
- `posDeepBranches = 1`: At most one deep positive branch per conjunction
- `posBranches = ∞`: Arbitrary positive branches allowed
- `negations = 1`: One level of negation

Characterizes ready-trace equivalence. -/
def bound_RT : FormulaPrice := ⟨⊤, ⊤, 1, ⊤, 1, 1⟩

/-- **Impossible Futures** `O_IF`: `(∞, 1, 0, 0, 1, ∞)`.

Impossible-futures formulas are traces ending in a single conjunction
of negated traces (not just negated observations).

- `observations = ∞`: Unbounded trace prefix
- `conjunctions = 1`: Exactly one conjunction
- `posBranches = 0`: No positive branches
- `negations = 1`: One level of negation
- `negatedObs = ∞`: Arbitrary observations under negation (negated traces)

Characterizes impossible-futures equivalence. -/
def bound_IF : FormulaPrice := ⟨⊤, 1, 0, 0, 1, ⊤⟩

/-- **Possible Futures** `O_PF`: `(∞, 1, ∞, ∞, 1, ∞)`.

Possible-futures formulas allow a single conjunction mixing positive traces
and negated traces.

- `observations = ∞`: Unbounded
- `conjunctions = 1`: Exactly one conjunction
- `posDeepBranches = ∞`: Arbitrary deep positive branches
- `posBranches = ∞`: Arbitrary positive branches
- `negations = 1`: One level of negation
- `negatedObs = ∞`: Arbitrary observations under negation

Characterizes possible-futures equivalence. -/
def bound_PF : FormulaPrice := ⟨⊤, 1, ⊤, ⊤, 1, ⊤⟩

/-- **Simulation** `O_1S`: `(∞, ∞, ∞, ∞, 0, 0)`.

Simulation formulas have full conjunctive power but no negations.

- `observations = ∞`: Unbounded
- `conjunctions = ∞`: Arbitrary conjunction nesting
- `posDeepBranches = ∞`: Arbitrary deep positive branches
- `posBranches = ∞`: Arbitrary positive branches
- `negations = 0`: No negations allowed
- `negatedObs = 0`: No observations under negation (no negations)

Characterizes simulation equivalence. -/
def bound_1S : FormulaPrice := ⟨⊤, ⊤, ⊤, ⊤, 0, 0⟩

/-- **Ready-Simulation** `O_RS`: `(∞, ∞, ∞, ∞, 1, 1)`.

Ready-simulation formulas extend simulation with shallow negations
(negations only applied to simple observations `¬⟨a⟩⊤`).

- `observations = ∞`: Unbounded
- `conjunctions = ∞`: Arbitrary conjunctions
- `posDeepBranches = ∞`: Arbitrary deep positive branches
- `posBranches = ∞`: Arbitrary positive branches
- `negations = 1`: One level of negation
- `negatedObs = 1`: Only simple observations under negation

Characterizes ready-simulation equivalence. -/
def bound_RS : FormulaPrice := ⟨⊤, ⊤, ⊤, ⊤, 1, 1⟩

/-- **n-Nested Simulation** `O_{(n+1)S}`: `(∞, ∞, ∞, ∞, n, ∞)`.

(n+1)-nested simulation allows n levels of negation nesting.
The parameter `n` specifies the maximum negation depth.

- `observations = ∞`: Unbounded
- `conjunctions = ∞`: Arbitrary conjunctions
- `posDeepBranches = ∞`: Arbitrary deep positive branches
- `posBranches = ∞`: Arbitrary positive branches
- `negations = n`: n levels of negation nesting
- `negatedObs = ∞`: Arbitrary observations under negation

Characterizes (n+1)-nested simulation equivalence.
Note: `bound_nS 0 = bound_1S` (simulation), `bound_nS 1 = bound_RS` (ready-simulation). -/
def bound_nS (n : ℕ) : FormulaPrice := ⟨⊤, ⊤, ⊤, ⊤, n, ⊤⟩

/-- **Bisimulation** `O_B`: `(∞, ∞, ∞, ∞, ∞, ∞)`.

Full Hennessy-Milner Logic (HML) with no restrictions.
All dimensions are unbounded (⊤ = ∞).

This is the top of the price lattice and characterizes bisimulation equivalence,
the finest equivalence in the linear-time–branching-time spectrum. -/
def bound_B : FormulaPrice := ⟨⊤, ⊤, ⊤, ⊤, ⊤, ⊤⟩

/-! ### Inclusion Lemmas

The observation languages form a lattice under inclusion. Finer equivalences
(those that distinguish more processes) have larger price bounds.

This section proves all the inclusions from the linear-time–branching-time
spectrum (Figure 1 of [BispingEtAl2022]):

```
                        O_E (enabledness)
                          |
                    O_T (traces)
                   /          \
          O_F (failures)   O_1S (simulation)
            |    \         /    |
        O_R (readiness)   O_RS (ready-sim)
            |    \         /    |
      O_FT (fail-traces)  O_2S (2-nested)
            |    \         /    |
      O_RT (ready-traces) O_3S (3-nested)
            |              ...
        O_IF (impossible)     |
            |    \           O_B (bisimulation)
        O_PF (possible)       |
            |                ...
           O_2S <------------┘
```

All inclusions are proven by showing `bound_X ≤ bound_Y` using the pointwise
order on `FormulaPrice`. -/

theorem bound_E_le_bound_T : bound_E ≤ bound_T := by
  simp [bound_E, bound_T, le_def, le_top]

theorem bound_T_le_bound_F : bound_T ≤ bound_F := by
  simp [bound_T, bound_F, le_def, le_top]

theorem bound_T_le_bound_1S : bound_T ≤ bound_1S := by
  simp [bound_T, bound_1S, le_def, le_top]

theorem bound_F_le_bound_R : bound_F ≤ bound_R := by
  simp [bound_F, bound_R, le_def, le_top]

theorem bound_F_le_bound_FT : bound_F ≤ bound_FT := by
  simp [bound_F, bound_FT, le_def, le_top]

theorem bound_F_le_bound_IF : bound_F ≤ bound_IF := by
  simp [bound_F, bound_IF, le_def, le_top]

theorem bound_R_le_bound_RT : bound_R ≤ bound_RT := by
  simp [bound_R, bound_RT, le_def, le_top]

theorem bound_FT_le_bound_RT : bound_FT ≤ bound_RT := by
  simp [bound_FT, bound_RT, le_def, le_top]

theorem bound_IF_le_bound_PF : bound_IF ≤ bound_PF := by
  simp [bound_IF, bound_PF, le_def, le_top]

theorem bound_R_le_bound_PF : bound_R ≤ bound_PF := by
  simp [bound_R, bound_PF, le_def, le_top]

theorem bound_1S_le_bound_RS : bound_1S ≤ bound_RS := by
  simp [bound_1S, bound_RS, le_def, le_top]

theorem bound_RT_le_bound_RS : bound_RT ≤ bound_RS := by
  simp [bound_RT, bound_RS, le_def, le_top]

theorem bound_PF_le_bound_2S : bound_PF ≤ bound_nS 2 := by
  simp [bound_PF, bound_nS, le_def, le_top]

theorem bound_RS_le_bound_2S : bound_RS ≤ bound_nS 2 := by
  simp [bound_RS, bound_nS, le_def, le_top]

theorem bound_nS_le_succ (n : ℕ) : bound_nS n ≤ bound_nS (n + 1) := by
  simp [bound_nS, le_def]


theorem bound_nS_le_bound_B (n : ℕ) : bound_nS n ≤ bound_B := by
  simp [bound_nS, bound_B, le_def, le_top]

/-! ### Unfolding lemmafs for `expr` -/

@[simp] theorem expr_conj_nil :
    expr (Formula.conj ([] : List (Formula Label))) = ⊥ := by
  unfold expr
  simp only [listSupENat, List.attach_nil, List.map_nil, List.foldl_nil, countPosDeepBranches,
    countPosFlatBranches, positiveFlatBranches, List.filter_nil, List.length_nil, tsub_zero,
    listSupPrice, bot_le, sup_of_le_left]
  ext <;> simp
  constructor
  constructor

@[simp] theorem expr_top' :
    expr (Formula.top (Label := Label)) = ⊥ := expr_conj_nil

@[simp] theorem expr_modal_conj_nil (a : Label) :
    expr (Formula.modal a (Formula.conj ([] : List (Formula Label)))) =
      ⟨1, 0, 0, 0, 0, 0⟩ := by
  unfold expr
  simp [expr_conj_nil]

/-- Unfolding `expr` for negation. -/
theorem expr_neg_formula (φ : Formula Label) :
    expr (.neg φ) =
      ⟨0, 0, 0, 0, 1 + (expr φ).negations, (expr φ).observations⟩ ⊔ expr φ := by
  conv_lhs => unfold expr

theorem expr_modal_of_not_neg (a : Label) (φ : Formula Label) (h : ∀ ψ, φ ≠ .neg ψ) :
    expr (.modal a φ) = ⟨1 + (expr φ).observations, 0, 0, 0, 0, 0⟩ ⊔ expr φ := by
  cases φ with
  | modal b ψ => sorry
  | conj φs   => sorry
  | neg ψ     => exact (False.elim <| h ψ rfl)

theorem expr_modal_neg (a : Label) (ψ : Formula Label) :
    expr (.modal a (.neg ψ)) =
      ⟨1 + (expr (.neg ψ)).observations, 0, 0, 0, 0, 0⟩ ⊔
      ⟨0, 1 + (expr (.neg ψ)).conjunctions, 0, 0, 0, 0⟩ ⊔
      expr (.neg ψ) := by
  simp [expr, sup_assoc]

theorem expr_attach_map_eq (φs : List (Formula Label)) :
    φs.attach.map (fun ⟨φ, hφ⟩ =>
      have : Formula.fsize φ < Formula.fsize (.conj φs) := Formula.fsize_lt_conj hφ
      expr φ) = φs.map expr := by
  classical
  induction φs with
  | nil => simp
  | cons hd tl ih =>
      simp [List.attach_cons]


theorem InOE_implies_price_bound {φ : Formula Label} (h : InOE φ) :
    exprStandalone φ ≤ bound_E := by
  cases h with
  | top =>
    simp [exprStandalone, hat, bound_E]
  | act a =>
    simp only [exprStandalone, hat, obsAct, Formula.top,
               expr_modal_conj_nil, bound_E, le_def]
    grind






/-- Concrete computation: `expr(¬⟨a⟩⊤) = (1, 0, 0, 0, 1, 1)`. -/
@[simp] theorem expr_negObsAct (a : Label) :
    expr (Formula.neg (Formula.modal a (Formula.conj ([] : List (Formula Label))))) =
      ⟨1, 0, 0, 0, 1, 1⟩ := by
  rw [expr_neg_formula]
  simp only [expr_modal_conj_nil, add_zero]
  ext <;> simp

/-! ### Helper: trace formulas are never negations -/

theorem InOT_not_neg {φ : Formula Label} (h : InOT φ) : ∀ ψ, φ ≠ .neg ψ := by
  cases h with
  | top       => intro ψ; simp
  | modal _ _ => intro ψ; simp

theorem InOT_exprStandalone_eq_expr {φ : Formula Label} (h : InOT φ) :
    exprStandalone φ = expr φ := by
  simp only [exprStandalone]
  cases h with
  | top       => rfl
  | modal _ _ => rfl

/-! ### Traces `O_T` -/

theorem InOT_implies_price_bound {φ : Formula Label} (h : InOT φ) :
    exprStandalone φ ≤ bound_T := by
  induction h with
  | top =>
    simp [exprStandalone, hat, bound_T]
  | @modal a ψ hψ ih =>
    rw [InOT_exprStandalone_eq_expr (InOT.modal a hψ)]
    rw [expr_modal_of_not_neg a ψ (InOT_not_neg hψ)]
    rw [InOT_exprStandalone_eq_expr hψ] at ih
    simp only [bound_T, le_def] at ih ⊢
    obtain ⟨_, h2, h3, h4, h5, h6⟩ := ih
    simp only [sup_observations, self_le_add_left, sup_of_le_left, le_top, sup_conjunctions,
      zero_le, sup_of_le_right, nonpos_iff_eq_zero, sup_posDeepBranches, sup_posBranches,
      sup_negations, sup_negatedObs, true_and]
    constructor
    · exact nonpos_iff_eq_zero.mp h2
    · exact ⟨nonpos_iff_eq_zero.mp h3,
      nonpos_iff_eq_zero.mp h4, nonpos_iff_eq_zero.mp h5,
      nonpos_iff_eq_zero.mp h6⟩

/-! ### Helper: failure subformula classification -/

/-- InOF formulas that are NOT negAct are not negations. -/
theorem InOF_not_neg_of_not_negAct {φ : Formula Label} (h : InOF φ)
    (h_not_negAct : ∀ a, φ ≠ negObsAct a) : ∀ ψ, φ ≠ .neg ψ := by
  cases h with
  | top          => intro ψ; simp
  | modal _ _    => intro ψ; simp
  | negAct a     => exact absurd rfl (h_not_negAct a)
  | failConj _   => intro ψ; simp

/-- For InOF formulas that are not bare negations, exprStandalone = expr. -/
theorem InOF_exprStandalone_eq_expr_of_not_negAct {φ : Formula Label} (h : InOF φ)
    (h_not_negAct : ∀ a, φ ≠ negObsAct a) :
    exprStandalone φ = expr φ := by
  simp only [exprStandalone]
  cases h with
  | top          => rfl
  | modal _ _    => rfl
  | negAct a     => exact absurd rfl (h_not_negAct a)
  | failConj _   => rfl
/-! ### Helper: `exprStandalone` of `negObsAct`

`exprStandalone(¬⟨a⟩⊤) = expr(⋀{¬⟨a⟩⊤}) = (1, 1, 0, 0, 1, 1)` -/

@[simp] theorem exprStandalone_negObsAct (a : Label) :
    exprStandalone (negObsAct (Label := Label) a) = ⟨1, 1, 0, 0, 1, 1⟩ := by
  simp only [exprStandalone, negObsAct, obsAct, Formula.top, hat]
  -- Goal: expr (.conj [.neg (.modal a (.conj []))]) = ⟨1, 1, 0, 0, 1, 1⟩
  unfold expr
  simp only [listSupENat, countPosDeepBranches, countPosBranches, positiveBranches,
    List.filter_cons, isPositiveBranch, isNeg, Bool.not_true, List.filter_nil, countPosFlatBranches,
    positiveFlatBranches, isPositiveFlat, listSupPrice]
  ext <;> simp

/-! ### Helper: price of `failConj` conjunctions

For a conjunction `⋀(as.map negObsAct)`, all conjuncts are negations,
so `|pb| = 0`, `|pf| = 0`. Each conjunct has price `(1, 0, 0, 0, 1, 1)`,
so the conjunction has price `(1, 1, 0, 0, 1, 1)` when non-empty. -/

/-- `negObsAct a` is a negation, so it is not a positive branch. -/
@[simp] theorem isPositiveBranch_negObsAct (a : Label) :
    isPositiveBranch (negObsAct (Label := Label) a) = false := by
  simp [isPositiveBranch, isNeg, negObsAct]

/-- `negObsAct a` is not a positive flat branch. -/
@[simp] theorem isPositiveFlat_negObsAct (a : Label) :
    isPositiveFlat (negObsAct (Label := Label) a) = false := by
  simp [isPositiveFlat, negObsAct]

/-- All elements of `as.map negObsAct` are not positive branches. -/
theorem countPosBranches_map_negObsAct (as : List Label) :
    countPosBranches (as.map negObsAct) = 0 := by
  simp [countPosBranches, positiveBranches]


/-- All elements of `as.map negObsAct` have zero positive flat branches. -/
theorem countPosFlatBranches_map_negObsAct (as : List Label) :
    countPosFlatBranches (as.map negObsAct) = 0 := by
  simp [countPosFlatBranches, positiveFlatBranches]


/-- **Boundedness of List Supremum**.

If all elements of a list are bounded by `b`, and the initial value is also
bounded by `b`, then the fold of supremum is bounded by `b`.

## Mathematical Statement

For any semilattice with supremum (`⊔`), if:
- `init ≤ b` (initial value is bounded)
- `∀ x ∈ xs, x ≤ b` (all elements are bounded)

Then: `xs.foldl (· ⊔ ·) init ≤ b`

## Proof Strategy

Induction on the list `xs`:
- Base: `foldl f init [] = init ≤ b` by assumption
- Step: `foldl f init (x :: xs) = foldl f (init ⊔ x) xs`
  - By induction hypothesis, suffices to show `init ⊔ x ≤ b`
  - This follows from `init ≤ b` and `x ≤ b`

## Usage

Used to prove `listSupENat_le` and `listSupPrice_le`, which are the main
lemmas for showing that expressiveness prices respect the bounds of
observation languages. -/
theorem foldl_sup_le {α : Type _} [SemilatticeSup α] {xs : List α} {b init : α}
    (hinit : init ≤ b) (hxs : ∀ x ∈ xs, x ≤ b) :
    xs.foldl (· ⊔ ·) init ≤ b := by
  induction xs generalizing init with
  | nil =>
      simpa using hinit
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact sup_le hinit (hxs x (by simp))
      · intro y hy
        exact hxs y (by simp [hy])

/-- **Boundedness of `listSupENat`**.

If all elements of a list are bounded by `b`, then the list supremum is bounded by `b`.

## Mathematical Statement

For `xs : List ℕ∞` and `b : ℕ∞`:

```
(∀ x ∈ xs, x ≤ b) → listSupENat xs ≤ b
```

## Corollary

This is the key lemma for proving that the `conjunctions` dimension of a formula
is bounded. When computing `expr` for a conjunction, we show that each conjunct's
conjunction depth (plus one) is bounded, hence the supremum is bounded.

## Example Usage

In `expr_failConj_le_bound_F`, we use this to show:
```
listSupENat depths ≤ 1
```
where `depths` contains `1 + e.conjunctions` for each conjunct price `e`. -/
theorem listSupENat_le {xs : List ℕ∞} {b : ℕ∞}
    (hxs : ∀ x ∈ xs, x ≤ b) :
    listSupENat xs ≤ b := by
  unfold listSupENat
  exact foldl_sup_le (α := ℕ∞) (xs := xs) (init := 0) (b := b) (by simp) hxs

/-- **Boundedness of `listSupPrice`**.

If all formula prices in a list are bounded by `b`, then the list supremum is bounded by `b`.

## Mathematical Statement

For `xs : List FormulaPrice` and `b : FormulaPrice`:

```
(∀ x ∈ xs, x ≤ b) → listSupPrice xs ≤ b
```

## Proof

This follows directly from `foldl_sup_le` with:
- Initial value: `⊥` (bottom)
- Bound: `b`
- Proof that `⊥ ≤ b`: `bot_le`

## Usage

Main lemma for proving that the supremum of conjunct prices is bounded.
In `expr_failConj_le_bound_F`, we use this to show:
```
listSupPrice es ≤ bound_F
```
where `es` contains the prices of all conjuncts. -/
theorem listSupPrice_le {xs : List FormulaPrice} {b : FormulaPrice}
    (hxs : ∀ x ∈ xs, x ≤ b) :
    listSupPrice xs ≤ b := by
  unfold listSupPrice
  exact foldl_sup_le (α := FormulaPrice) (xs := xs) (init := ⊥) (b := b) bot_le hxs

theorem expr_negObsAct_eq (a : Label) :
    expr (negObsAct (Label := Label) a) = ⟨1, 0, 0, 0, 1, 1⟩ := by
  simp [negObsAct, obsAct, Formula.top, expr_negObsAct]

/-- Each element of `(as.map negObsAct).map expr` equals `⟨1,0,0,0,1,1⟩`. -/
theorem mem_map_expr_negObsAct {e : FormulaPrice} {as : List Label}
    (h : e ∈ (as.map (negObsAct (Label := Label))).map expr) :
    e = ⟨1, 0, 0, 0, 1, 1⟩ := by
  rw [List.mem_map] at h
  obtain ⟨φ, hφ, rfl⟩ := h
  rw [List.mem_map] at hφ
  obtain ⟨a, _, rfl⟩ := hφ
  exact expr_negObsAct_eq a




/-- Unfolding `expr` for negation. -/
theorem expr_neg_formula2 (φ : Formula Label) :
    expr (.neg φ) =
      ⟨0, 0, 0, 0, 1 + (expr φ).negations, (expr φ).observations⟩ ⊔ expr φ := by
  simp [expr]



/-- Unfolding `expr` for modals with negation subformula. -/
theorem expr_modal_neg2 (a : Label) (ψ : Formula Label) :
    expr (.modal a (.neg ψ)) =
      ⟨1 + (expr (.neg ψ)).observations, 0, 0, 0, 0, 0⟩ ⊔
      ⟨0, 1 + (expr (.neg ψ)).conjunctions, 0, 0, 0, 0⟩ ⊔
      expr (.neg ψ) := by
  simp [expr, sup_assoc]

/-! ### Helpers for `failConj` -/

private def pNeg : FormulaPrice := (⟨(1 : ℕ∞), 0, 0, 0, 1, 1⟩ : FormulaPrice)

private lemma foldl_sup_eq_self {α} [SemilatticeSup α] (x : α) :
    ∀ xs : List α, (∀ y ∈ xs, y = x) → xs.foldl (· ⊔ ·) x = x
  | [], _ => by simp
  | y :: ys, h => by
      have hy : y = x := h y (by simp)
      subst hy
      have hys : ∀ z ∈ ys, z = y := by
        intro z hz; exact h z (by simp [hz])
      simpa [List.foldl_cons, sup_idem] using foldl_sup_eq_self y ys hys

private lemma foldl_sup_eq_self_enat (x : ℕ∞) :
    ∀ xs : List ℕ∞, (∀ y ∈ xs, y = x) → xs.foldl (· ⊔ ·) x = x :=
  foldl_sup_eq_self x

@[simp] private lemma expr_negObsAct' (a : Label) :
    expr (negObsAct (Label := Label) a) = pNeg := by
  -- your lemma `expr_negObsAct` is already `[simp]`-friendly via these unfoldings
  simpa [pNeg, negObsAct, obsAct, Formula.top] using (expr_negObsAct (Label := Label) a)

private lemma attach_map_val (φs : List (Formula Label)) :
    φs.attach.map (fun x => expr x.1) = φs.map expr := by
  induction φs with
  | nil => simp
  | cons hd tl ih => simp [ih]

private lemma listSupPrice_const (x : FormulaPrice) (xs : List FormulaPrice)
    (h : ∀ y ∈ xs, y = x) :
    listSupPrice (x :: xs) = x := by
  unfold listSupPrice
  simp [List.foldl_cons, bot_sup_eq, foldl_sup_eq_self x xs h]

private lemma listSupENat_const (x : ℕ∞) (xs : List ℕ∞) (h : ∀ y ∈ xs, y = x) :
    listSupENat (x :: xs) = x := by
  unfold listSupENat
  simp only [List.foldl_cons, zero_le, sup_of_le_right, foldl_sup_eq_self_enat x xs h]

private lemma countPosDeepBranches_map_negObsAct (as : List Label) :
    countPosDeepBranches ((as.map (negObsAct (Label := Label)))) = 0 := by
  simp [countPosDeepBranches, countPosBranches_map_negObsAct, countPosFlatBranches_map_negObsAct]



theorem expr_failConj_le_bound_F (as : List Label) :
    expr (.conj (as.map (negObsAct (Label := Label)))) ≤ bound_F := by
  cases as with
  | nil =>
      simp [expr, bound_F, FormulaPrice.le_def]
  | cons hd tl =>
      let φs : List (Formula Label) := (hd :: tl).map (negObsAct (Label := Label))
      have hes :
          φs.attach.map (fun ⟨φ, hφ⟩ =>
            have : Formula.fsize φ < Formula.fsize (.conj φs) := Formula.fsize_lt_conj hφ
            expr φ) = φs.map expr :=
        expr_attach_map_eq (Label := Label) φs

      -- unfold expr on the conjunction; rewrite away attach.map; simp turns ⊔-bound into ∧
      simp only [List.map_cons, expr, List.attach_cons, expr_negObsAct', List.map_map, sup_le_iff]

      constructor
      · -- local ≤ bound_F
        have hpb : countPosBranches φs = 0 := by
          simpa [φs] using (countPosBranches_map_negObsAct (Label := Label) (as := hd :: tl))
        have hpf : countPosFlatBranches φs = 0 := by
          simpa [φs] using (countPosFlatBranches_map_negObsAct (Label := Label) (as := hd :: tl))
        have hpd : countPosDeepBranches φs = 0 := by
          simp [countPosDeepBranches, hpb, hpf]

        set es : List FormulaPrice := (φs.map expr)
        set depths : List ℕ∞ := es.map (fun e => 1 + e.conjunctions)

        have h_depths : ∀ x ∈ depths, x ≤ (1 : ℕ∞) := by
          intro x hx
          rcases List.mem_map.1 hx with ⟨p, hp, rfl⟩
          have hp' : p ∈ ((hd :: tl).map (negObsAct (Label := Label))).map expr := by
            simpa [es, depths, φs] using hp
          have hpconst : p = (⟨1, 0, 0, 0, 1, 1⟩ : FormulaPrice) :=
            mem_map_expr_negObsAct (Label := Label) (as := hd :: tl) hp'
          subst hpconst
          simp

        have h_listSup : listSupENat depths ≤ (1 : ℕ∞) :=
          listSupENat_le (xs := depths) (b := (1 : ℕ∞)) h_depths

        -- build the 6 components of `≤` (nested ∧)
        simp only [bound_F, le_def, le_top, nonpos_iff_eq_zero, Nat.cast_eq_zero, zero_le, and_self,
          and_true, true_and]
        constructor
        · -- listSupENat (...) ≤ 1
          apply listSupENat_le (b := (1 : ℕ∞))
          intro x hx
          rcases List.mem_cons.1 hx with hx | hx
          · subst hx
            simp [pNeg]     -- uses `pNeg.conjunctions = 0`
          · rcases List.mem_map.1 hx with ⟨y, hy, rfl⟩
            -- `simp` reduces the mapped term to `1`

            simp only [Function.comp]
            apply h_depths
            set φ := ↑y with hφ
            simp only [depths, es, φs, List.map_cons, List.mem_cons]
            left
            have : expr y.val = pNeg := by
              have h1 : y.val ∈ List.map negObsAct tl := y.prop
              rw [List.mem_map] at h1
              rcases h1 with ⟨a, ha, heq⟩
              rw [<-heq]
              simp [expr_negObsAct']


            simp only [expr_negObsAct']
            rw [this]

        constructor
        simp only [List.map_cons, φs] at hpd ⊢
        exact hpd

        simp only [List.map_cons, φs] at hpb ⊢

        exact hpb










      · -- listSupPrice (φs.map expr) ≤ bound_F
        set es : List FormulaPrice := ((hd :: tl).map (negObsAct (Label := Label))).map expr
        have h_es : ∀ p ∈ es, p ≤ bound_F := by
          intro p hp
          have hpconst : p = (⟨1, 0, 0, 0, 1, 1⟩ : FormulaPrice) :=
            mem_map_expr_negObsAct (Label := Label) (as := hd :: tl) hp
          subst hpconst
          simp [bound_F, FormulaPrice.le_def]


        have : listSupPrice es ≤ bound_F :=
          listSupPrice_le h_es

        simp only [ge_iff_le]
        have h : listSupPrice es ≤ bound_F :=
        listSupPrice_le h_es

        simp only [ge_iff_le]
        -- Rewrite es in the goal
        simp only [List.map_map, List.map_cons, Function.comp, expr_negObsAct', es] at h ⊢
        have h : listSupPrice es ≤ bound_F := listSupPrice_le h_es

        -- Use convert which is more flexible with slightly different expressions
        convert h
        -- Now prove the lists are equal
        simp only [List.map_map, List.map_cons, Function.comp, expr_negObsAct', List.cons.injEq,
          true_and, es]
        -- Simplify the function composition first

        -- Prove the lists are equal by showing they're equal element-wise
        apply List.ext_getElem
        · -- Show lengths are equal
          simp only [List.length_map, List.length_attach]
        · -- Show elements at each index are equal
          intro i hi1 hi2
          simp only [List.getElem_map, List.getElem_attach, Function.comp_apply, expr_negObsAct']


end ObservationLanguage


end Formula

end FormulaPrice

end Cslib
