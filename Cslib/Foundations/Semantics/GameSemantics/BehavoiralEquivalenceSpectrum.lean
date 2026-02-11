/-
Copyright (c) 2025 Bashar Hamade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bashar Hamade
-/

import Cslib.Init
import Cslib.Foundations.Semantics.LTS.Basic
import Cslib.Logics.HennessyMilnerLogic.Basic
import Cslib.Foundations.Semantics.GameSemantics.Basic
import Cslib.Foundations.Semantics.GameSemantics.HMLGame

namespace Cslib

open HennessyMilner

universe u v

variable {State : Type u} {Label : Type v}

variable {G : HMLGame}

def isDistinguishingFormula {State : Type u} {Label : Type v}
  (lts : LTS State Label) (s t : State) (φ : Formula Label) : Prop :=
  (satisfies lts s φ) ∧ ¬(satisfies lts t φ)

/-- An observation language (set of HML formulas over `Label`). -/
abbrev ObservationsSet (Label : Type v) : Type v :=
  Set (Formula Label)

/-- `s` is preordered to `t` w.r.t. observation language `O_x`
    iff no formula in `O_x` distinguishes `s` from `t`. -/
def observations_preorders_states
    (O_x : ObservationsSet Label) (lts : LTS State Label) (s t : State) : Prop :=
  ∀ φ, φ ∈ O_x → ¬ isDistinguishingFormula lts s t φ


def obsAct (a : Label) : Formula Label :=
  Formula.modal a Formula.true

/-- Abbreviation for the “negated atomic observation” `¬⟨a⟩` (i.e. `¬⟨a⟩⊤`). -/
def negObsAct (a : Label) : Formula Label :=
  Formula.neg (obsAct (Label := Label) a)

/-- Ready-literals: either `⟨a⟩` or `¬⟨a⟩`. -/
inductive IsReadyLit : Formula Label → Prop
  | pos (a : Label) : IsReadyLit (obsAct (Label := Label) a)
  | neg (a : Label) : IsReadyLit (negObsAct (Label := Label) a)

/-! ### Trace observations 𝒪_T -/
inductive InOT : Formula Label → Prop
  | top : InOT Formula.true
  | modal (a : Label) {φ : Formula Label} : InOT φ → InOT (Formula.modal a φ)

/-- Trace observation language `𝒪_T`. -/
def O_T : ObservationsSet Label := { φ | InOT (Label := Label) φ }

/-! ### Failure observations 𝒪_F -/
inductive InOF : Formula Label → Prop
  | top : InOF Formula.true
  | modal (a : Label) {φ : Formula Label} : InOF φ → InOF (Formula.modal a φ)
  /-- `⋀ ¬⟨aᵢ⟩` is a failure observation (finitary list version). -/
  | failConj (as : List Label) :
      InOF (Formula.conj (as.map (negObsAct (Label := Label))))

def O_F : ObservationsSet Label := { φ | InOF (Label := Label) φ }

/-! ### Readiness observations 𝒪_R -/
inductive InOR : Formula Label → Prop
  | top : InOR Formula.true
  | modal (a : Label) {φ : Formula Label} : InOR φ → InOR (Formula.modal a φ)
  /-- `⋀ φᵢ` where each `φᵢ` is either `⟨a⟩` or `¬⟨a⟩`. -/
  | readyConj (φs : List (Formula Label)) :
      (∀ φ, φ ∈ φs → IsReadyLit (Label := Label) φ) →
      InOR (Formula.conj φs)

def O_R : ObservationsSet Label := { φ | InOR (Label := Label) φ }

/-! ### Failure-trace observations 𝒪_FT -/
inductive InOFT : Formula Label → Prop
  | top : InOFT Formula.true
  | modal (a : Label) {φ : Formula Label} : InOFT φ → InOFT (Formula.modal a φ)
  /-- `⋀ᵢ φᵢ` where one distinguished conjunct `φ₀ ∈ 𝒪_FT`
      and all others are `¬⟨a⟩` (list version: we put `φ₀` first). -/
  | ftConj {φ0 : Formula Label} (as : List Label) :
      InOFT φ0 →
      InOFT (Formula.conj (φ0 :: as.map (negObsAct (Label := Label))))

def O_FT : ObservationsSet Label := { φ | InOFT (Label := Label) φ }

/-! ### Ready-trace observations 𝒪_RT -/
inductive InORT : Formula Label → Prop
  | top : InORT Formula.true
  | modal (a : Label) {φ : Formula Label} : InORT φ → InORT (Formula.modal a φ)
  /-- `⋀ᵢ φᵢ` where one distinguished conjunct `φ₀ ∈ 𝒪_RT`
      and all others are ready-literals (`⟨a⟩` or `¬⟨a⟩`). -/
  | rtConj {φ0 : Formula Label} (lits : List (Formula Label)) :
      InORT φ0 →
      (∀ ψ, ψ ∈ lits → IsReadyLit (Label := Label) ψ) →
      InORT (Formula.conj (φ0 :: lits))

def O_RT : ObservationsSet Label := { φ | InORT (Label := Label) φ }

/-! ### Impossible futures 𝒪_IF -/
inductive InOIF : Formula Label → Prop
  | top : InOIF Formula.true
  | modal (a : Label) {φ : Formula Label} : InOIF φ → InOIF (Formula.modal a φ)
  /-- `⋀ ¬ψᵢ` where each `ψᵢ ∈ 𝒪_T`. -/
  | ifConj (ψs : List (Formula Label)) :
      (∀ ψ, ψ ∈ ψs → InOT (Label := Label) ψ) →
      InOIF (Formula.conj (ψs.map Formula.neg))

def O_IF : ObservationsSet Label := { φ | InOIF (Label := Label) φ }

/-! ### Possible futures 𝒪_PF -/
inductive IsPFLit : Formula Label → Prop
  | pos {ψ : Formula Label} : InOT (Label := Label) ψ → IsPFLit ψ
  | neg {ψ : Formula Label} : InOT (Label := Label) ψ → IsPFLit (Formula.neg ψ)

inductive InOPF : Formula Label → Prop
  | top : InOPF Formula.true
  | modal (a : Label) {φ : Formula Label} : InOPF φ → InOPF (Formula.modal a φ)
  /-- `⋀ φᵢ` where each `φᵢ` is either `ψ` or `¬ψ` for some trace `ψ ∈ 𝒪_T`. -/
  | pfConj (φs : List (Formula Label)) :
      (∀ φ, φ ∈ φs → IsPFLit (Label := Label) φ) →
      InOPF (Formula.conj φs)

def O_PF : ObservationsSet Label := { φ | InOPF (Label := Label) φ }

/-! ## Simulation-side observation languages -/

/-! ### Simulation observations 𝒪_1S (positive HML: modal + conjunction) -/
inductive InO1S : Formula Label → Prop
  | top : InO1S Formula.true
  | modal (a : Label) {φ : Formula Label} : InO1S φ → InO1S (Formula.modal a φ)
  | conj (φs : List (Formula Label)) :
      (∀ φ, φ ∈ φs → InO1S φ) →
      InO1S (Formula.conj φs)

def O_1S : ObservationsSet Label := { φ | InO1S (Label := Label) φ }

/-! ### Ready simulation observations 𝒪_RS -/
inductive InORS : Formula Label → Prop
  | top : InORS Formula.true
  | modal (a : Label) {φ : Formula Label} : InORS φ → InORS (Formula.modal a φ)
  | conj (φs : List (Formula Label)) :
      (∀ φ, φ ∈ φs → InORS φ) →
      InORS (Formula.conj φs)
  /-- Ready simulation additionally allows `¬⟨a⟩`. -/
  | negAct (a : Label) : InORS (negObsAct (Label := Label) a)

def O_RS : ObservationsSet Label := { φ | InORS (Label := Label) φ }

/-! ### n-nested simulation observations 𝒪_nS -/
inductive InOnS : Nat → Formula Label → Prop
  | base {φ : Formula Label} : InO1S (Label := Label) φ → InOnS 1 φ
  | lift {n : Nat} {φ : Formula Label} : InOnS n φ → InOnS (n + 1) φ
  | modal {n : Nat} (a : Label) {φ : Formula Label} : InOnS n φ → InOnS n (Formula.modal a φ)
  | conj {n : Nat} (φs : List (Formula Label)) :
      (∀ φ, φ ∈ φs → InOnS n φ) →
      InOnS n (Formula.conj φs)
  /-- Nesting step: if `φ ∈ 𝒪_nS` then `¬φ ∈ 𝒪_(n+1)S`. -/
  | negStep {n : Nat} {φ : Formula Label} : InOnS n φ → InOnS (n + 1) (Formula.neg φ)

/-- The language `𝒪_nS` as a set (for any `n ≥ 1`). -/
def O_nS (n : Nat) : ObservationsSet Label := { φ | InOnS (Label := Label) n φ }

/-! ### Bisimulation observations 𝒪_B -/

/-- In the paper, `𝒪_B` is (equivalent to) full HML. Here we take it as all formulas. -/
def O_B : ObservationsSet Label := Set.univ


def ClosedObservationLanguage (O : ObservationsSet Label) : Prop :=
  (∀ {a : Label} {φ : Formula Label},
      Formula.modal a φ ∈ O → φ ∈ O) ∧
  (∀ {φs : List (Formula Label)},
      Formula.conj φs ∈ O →
        (∀ {φ : Formula Label}, φ ∈ φs → φ ∈ O) ∧
        (∀ {φs' : List (Formula Label)}, φs' ⊆ φs → Formula.conj φs' ∈ O)) ∧
  (∀ {φ : Formula Label},
      Formula.neg φ ∈ O → φ ∈ O)





end Cslib
