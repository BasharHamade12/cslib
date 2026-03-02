/-
Copyright (c) 2025 Bashar Hamade. All rights reserved.
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

This module formalizes the formula price lattice (Definition 2.19) and the
expressiveness price function (Definition 2.20) from [BispingEtAl2022].

The key idea is to overlay the linear-time–branching-time spectrum with a
six-dimensional price metric that captures the amount of HML expressiveness
used by a formula. Each dimension measures a different aspect of syntactic
complexity, and observation languages from the spectrum correspond to
rectangular regions (upper bounds) in this price lattice.

## Main definitions

- `FormulaPrice`: A six-dimensional price vector over `ℕ∞`.
- `FormulaPrice.Lattice`: The pointwise lattice structure on prices.
- `Formula.isPositiveBranch`, `Formula.isPositiveFlat`: Classifiers for
  conjuncts used in computing dimensions 3 and 4.
- `Formula.hat`: The hat operation `φ̂` that wraps negations in a
  singleton conjunction.
- `observations`, `conjunctions`, `posDeepBranches`, `posBranches`,
  `negations`, `negatedObs`: Each dimension defined as a separate
  recursive function on HML formulas.
- `Formula.expr`: The combined expressiveness price (Definition 2.20).
- `Formula.exprStandalone`: The standalone price `expr(φ̂)`.

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

/-- Six-dimensional expressiveness price of an HML formula.

Each dimension captures a distinct aspect of the syntactic complexity of
formulas in the linear-time–branching-time spectrum:

1. `observations`:    Depth of modal operator `⟨a⟩` nesting.
2. `conjunctions`:    Depth of conjunction nesting (negations after
                      observations count as implicit conjunctions).
3. `posDeepBranches`: Maximum number of positive deep branches per conjunction.
4. `posBranches`:     Maximum number of positive branches per conjunction.
5. `negations`:       Depth of negation nesting.
6. `negatedObs`:      Maximum observation depth under each negation.
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

/-! ### Lattice Structure

We equip `FormulaPrice` with a pointwise partial order, join, meet,
bottom, and top, making it a bounded lattice. -/

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

The set of positive branches in a conjunction—conjuncts that are not negations.

$$pb = \{\varphi_i \mid \not\exists \varphi'. \varphi_i = \neg \varphi'\}$$
-/

/-- A formula is a positive branch if it is not a negation. -/
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

noncomputable def listSupENat (xs : List ℕ∞) : ℕ∞ :=
  xs.foldl (· ⊔ ·) 0


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

/-- The expressiveness price of an HML formula (Definition 2.20).

We inline the computation of `expr(φ̂)` in the modal case to ensure termination,
since `hat φ` is not structurally smaller when `φ` is a negation.
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

/-- The standalone price of a formula is `expr(φ̂)`. -/
noncomputable def exprStandalone (φ : Formula Label) : FormulaPrice :=
  expr (hat φ)


/-! ## Price Bounds for Observation Languages (Table 1)

Each observation language from the linear-time–branching-time spectrum
corresponds to a rectangular region in the price lattice, defined by an
upper bound on each dimension. A formula φ belongs to language O_X
precisely when expr(φ̂) ⊑ bound_X (Lemma 2.23). -/

namespace ObservationLanguage

open FormulaPrice

/-- Price bound for enabledness `O_E`: `(1, 0, 0, 0, 0, 0)`.
    Only single observations ⟨a⟩ with no nesting. -/
def bound_E : FormulaPrice := ⟨1, 0, 0, 0, 0, 0⟩

/-- Price bound for traces `O_T`: `(∞, 0, 0, 0, 0, 0)`.
    Arbitrary observation depth, but no conjunctions or negations. -/
def bound_T : FormulaPrice := ⟨⊤, 0, 0, 0, 0, 0⟩

/-- Price bound for failures `O_F`: `(∞, 1, 0, 0, 1, 1)`.
    Traces extended with a single conjunction of negated actions. -/
def bound_F : FormulaPrice := ⟨⊤, 1, 0, 0, 1, 1⟩

/-- Price bound for readiness `O_R`: `(∞, 1, 0, ∞, 1, 1)`.
    Like failures but allowing positive flat branches (enabled actions). -/
def bound_R : FormulaPrice := ⟨⊤, 1, 0, ⊤, 1, 1⟩

/-- Price bound for failure-traces `O_FT`: `(∞, ∞, 1, 1, 1, 1)`.
    Interleaved traces and failure sets with one deep branch per conjunction. -/
def bound_FT : FormulaPrice := ⟨⊤, ⊤, 1, 1, 1, 1⟩

/-- Price bound for ready-traces `O_RT`: `(∞, ∞, 1, ∞, 1, 1)`.
    Like failure-traces but with arbitrary positive branches. -/
def bound_RT : FormulaPrice := ⟨⊤, ⊤, 1, ⊤, 1, 1⟩

/-- Price bound for impossible futures `O_IF`: `(∞, 1, 0, 0, 1, ∞)`.
    Single conjunction of negated trace observations. -/
def bound_IF : FormulaPrice := ⟨⊤, 1, 0, 0, 1, ⊤⟩

/-- Price bound for possible futures `O_PF`: `(∞, 1, ∞, ∞, 1, ∞)`.
    Single conjunction mixing positive and negated traces. -/
def bound_PF : FormulaPrice := ⟨⊤, 1, ⊤, ⊤, 1, ⊤⟩

/-- Price bound for simulation `O_1S`: `(∞, ∞, ∞, ∞, 0, 0)`.
    Full conjunctive power but no negations. -/
def bound_1S : FormulaPrice := ⟨⊤, ⊤, ⊤, ⊤, 0, 0⟩

/-- Price bound for ready-simulation `O_RS`: `(∞, ∞, ∞, ∞, 1, 1)`.
    Simulation with shallow negations (only ¬⟨a⟩). -/
def bound_RS : FormulaPrice := ⟨⊤, ⊤, ⊤, ⊤, 1, 1⟩

/-- Price bound for `(n+1)`-nested simulation `O_{(n+1)S}`: `(∞, ∞, ∞, ∞, n, ∞)`.
    Simulation with n levels of negation alternation. -/
def bound_nS (n : ℕ) : FormulaPrice := ⟨⊤, ⊤, ⊤, ⊤, n, ⊤⟩

/-- Price bound for bisimulation `O_B`: `(∞, ∞, ∞, ∞, ∞, ∞)`.
    Full HML with no restrictions. -/
def bound_B : FormulaPrice := ⟨⊤, ⊤, ⊤, ⊤, ⊤, ⊤⟩

/-! ### Inclusion Lemmas

The spectrum forms a lattice under inclusion. Finer equivalences have
larger price bounds. -/

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
  simp [expr_modal_conj_nil]
  ext <;> simp

/-! ### Helper: trace formulas are never negations -/

theorem InOT_not_neg {φ : Formula Label} (h : InOT φ) : ∀ ψ, φ ≠ .neg ψ := by
  cases h with
  | top       => intro ψ; simp
  | modal _ _ => intro ψ; simp

theorem InOT_exprStandalone_eq_expr {φ : Formula Label} (h : InOT φ) :
    exprStandalone φ = expr φ := by
  simp [exprStandalone]
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
    simp
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
  simp only [expr_negObsAct,
             countPosDeepBranches, countPosBranches, positiveBranches,
             countPosFlatBranches, positiveFlatBranches,
             isPositiveBranch, isNeg, isPositiveFlat,
             List.filter_cons, List.filter_nil, Bool.not_true,
             ite_false, List.length_nil,
             listSupENat, List.map, List.foldl,
             listSupPrice]
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


/-- `foldl (⊔)` over `ℕ∞` is bounded when init and all elements are bounded. -/
theorem foldl_sup_le {α : Type _} [SemilatticeSup α] {xs : List α} {b init : α}
    (hinit : init ≤ b) (hxs : ∀ x ∈ xs, x ≤ b) :
    xs.foldl (· ⊔ ·) init ≤ b := by
  induction xs generalizing init with
  | nil =>
      simpa using hinit
  | cons x xs ih =>
      simp [List.foldl_cons]
      apply ih
      · exact sup_le hinit (hxs x (by simp))
      · intro y hy
        exact hxs y (by simp [hy])

theorem listSupENat_le {xs : List ℕ∞} {b : ℕ∞}
    (hxs : ∀ x ∈ xs, x ≤ b) :
    listSupENat xs ≤ b := by
  unfold listSupENat
  exact foldl_sup_le (α := ℕ∞) (xs := xs) (init := 0) (b := b) (by simpa) hxs

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
      simp [expr, φs, hes]

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
