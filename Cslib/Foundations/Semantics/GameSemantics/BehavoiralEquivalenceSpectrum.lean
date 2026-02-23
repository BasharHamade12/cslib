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

/-!
# Observation Languages and the Linear-Time–Branching-Time Spectrum

This module formalizes the observation languages from van Glabbeek's
linear-time–branching-time spectrum, as presented in Definition 2.14 of
[BispingEtAl2022].

## References

* [B. Bisping, D. N. Jansen, and U. Nestmann,
*Deciding All Behavioral Equivalences at Once:
A Game for Linear-Time–Branching-Time Spectroscopy*][BispingEtAl2022]
-/

namespace Cslib

open HennessyMilner

universe u v

variable {State : Type u} {Label : Type v}

/-! ## Basic Definitions -/

def isDistinguishingFormula
    (lts : LTS State Label) (s t : State) (φ : Formula Label) : Prop :=
  satisfies lts s φ ∧ ¬ satisfies lts t φ

abbrev ObservationsSet (Label : Type v) : Type v :=
  Set (Formula Label)

def observations_preorders_states
    (O_X : ObservationsSet Label) (lts : LTS State Label) (s t : State) : Prop :=
  ∀ φ, φ ∈ O_X → ¬ isDistinguishingFormula lts s t φ

/-! ## Auxiliary Formula Constructors -/

def obsAct (a : Label) : Formula Label :=
  Formula.modal a Formula.true

def negObsAct (a : Label) : Formula Label :=
  Formula.neg (obsAct a)

inductive IsReadyLit : Formula Label → Prop
  | pos (a : Label) : IsReadyLit (obsAct a)
  | neg (a : Label) : IsReadyLit (negObsAct a)

/-! ## Closed Observation Languages (Definition 2.15) -/

def ClosedObservationLanguage (O : ObservationsSet Label) : Prop :=
  (∀ {a : Label} {φ : Formula Label},
      Formula.modal a φ ∈ O → φ ∈ O) ∧
  (∀ {φs : List (Formula Label)},
      Formula.conj φs ∈ O →
        (∀ {φ : Formula Label}, φ ∈ φs → φ ∈ O) ∧
        (∀ {φs' : List (Formula Label)}, φs' ⊆ φs → Formula.conj φs' ∈ O)) ∧
  (∀ {φ : Formula Label},
      Formula.neg φ ∈ O → φ ∈ O)

/-! ## Observation Languages (Definition 2.14) -/

/-! ### Enabledness observations `O_E` (Example 2.13) -/

inductive InOE : Formula Label → Prop
  | top : InOE Formula.true
  | act (a : Label) : InOE (obsAct a)

def O_E : ObservationsSet Label := { φ | InOE φ }

/-! ### Trace observations `O_T` -/

inductive InOT : Formula Label → Prop
  | top : InOT Formula.true
  | modal (a : Label) {φ : Formula Label} : InOT φ → InOT (Formula.modal a φ)

def O_T : ObservationsSet Label := { φ | InOT φ }

/-! ### Failure observations `O_F` -/

inductive InOF : Formula Label → Prop
  | top : InOF Formula.true
  | modal (a : Label) {φ : Formula Label} : InOF φ → InOF (Formula.modal a φ)
  | negAct (a : Label) : InOF (negObsAct (Label := Label) a)
  | failConj (as : List Label) :
      InOF (Formula.conj (as.map negObsAct))

def O_F : ObservationsSet Label := { φ | InOF φ }

/-! ### Readiness observations `O_R` -/

inductive InOR : Formula Label → Prop
  | top : InOR Formula.true
  | modal (a : Label) {φ : Formula Label} : InOR φ → InOR (Formula.modal a φ)
  | negAct (a : Label) : InOR (negObsAct (Label := Label) a)
  | readyConj (φs : List (Formula Label)) :
      (∀ φ, φ ∈ φs → IsReadyLit φ) →
      InOR (Formula.conj φs)

def O_R : ObservationsSet Label := { φ | InOR φ }

/-! ### Failure-trace observations `O_FT` -/

inductive InOFT : Formula Label → Prop
  | top : InOFT Formula.true
  | modal (a : Label) {φ : Formula Label} : InOFT φ → InOFT (Formula.modal a φ)
  | negAct (a : Label) : InOFT (negObsAct (Label := Label) a)    -- ← ADD THIS
  | ftConj (φs : List (Formula Label)) (φ₀ : Formula Label) :
      φ₀ ∈ φs →
      InOFT φ₀ →
      (∀ ψ, ψ ∈ φs → ψ ≠ φ₀ → ∃ a, ψ = negObsAct (Label := Label) a) →
      InOFT (Formula.conj φs)

def O_FT : ObservationsSet Label := { φ | InOFT φ }

/-! ### Ready-trace observations `O_RT` -/

inductive InORT : Formula Label → Prop
  | top : InORT Formula.true
  | modal (a : Label) {φ : Formula Label} : InORT φ → InORT (Formula.modal a φ)
  | rtConj (φs : List (Formula Label)) (φ₀ : Formula Label) :
      φ₀ ∈ φs →
      InORT φ₀ →
      (∀ ψ, ψ ∈ φs → ψ ≠ φ₀ → IsReadyLit ψ) →
      InORT (Formula.conj φs)

def O_RT : ObservationsSet Label := { φ | InORT φ }

/-! ### Impossible futures `O_IF` -/

inductive InOIF : Formula Label → Prop
  | top : InOIF Formula.true
  | modal (a : Label) {φ : Formula Label} : InOIF φ → InOIF (Formula.modal a φ)
  | ifConj (ψs : List (Formula Label)) :
      (∀ ψ, ψ ∈ ψs → InOT ψ) →
      InOIF (Formula.conj (ψs.map Formula.neg))

def O_IF : ObservationsSet Label := { φ | InOIF φ }

/-! ### Possible futures `O_PF` -/

inductive IsPFLit : Formula Label → Prop
  | pos {ψ : Formula Label} : InOT ψ → IsPFLit ψ
  | neg {ψ : Formula Label} : InOT ψ → IsPFLit (Formula.neg ψ)

inductive InOPF : Formula Label → Prop
  | top : InOPF Formula.true
  | modal (a : Label) {φ : Formula Label} : InOPF φ → InOPF (Formula.modal a φ)
  | pfConj (φs : List (Formula Label)) :
      (∀ φ, φ ∈ φs → IsPFLit φ) →
      InOPF (Formula.conj φs)

def O_PF : ObservationsSet Label := { φ | InOPF φ }

/-! ### Simulation observations `O_1S` -/

inductive InO1S : Formula Label → Prop
  | top : InO1S Formula.true
  | modal (a : Label) {φ : Formula Label} : InO1S φ → InO1S (Formula.modal a φ)
  | conj (φs : List (Formula Label)) :
      (∀ φ, φ ∈ φs → InO1S φ) →
      InO1S (Formula.conj φs)

def O_1S : ObservationsSet Label := { φ | InO1S φ }

/-! ### Ready-simulation observations `O_RS` -/

inductive InORS : Formula Label → Prop
  | top : InORS Formula.true
  | modal (a : Label) {φ : Formula Label} : InORS φ → InORS (Formula.modal a φ)
  | conj (φs : List (Formula Label)) :
      (∀ φ, φ ∈ φs → InORS φ) →
      InORS (Formula.conj φs)
  | negAct (a : Label) : InORS (negObsAct a)

def O_RS : ObservationsSet Label := { φ | InORS φ }

/-! ### n-nested simulation observations `O_nS` -/

inductive InOnS : Nat → Formula Label → Prop
  | base {φ : Formula Label} : InO1S φ → InOnS 1 φ
  | lift {n : Nat} {φ : Formula Label} : InOnS n φ → InOnS (n + 1) φ
  | modal {n : Nat} (a : Label) {φ : Formula Label} :
      InOnS n φ → InOnS n (Formula.modal a φ)
  | conj {n : Nat} (φs : List (Formula Label)) :
      (∀ φ, φ ∈ φs → InOnS n φ) →
      InOnS n (Formula.conj φs)
  | negStep {n : Nat} {φ : Formula Label} :
      InOnS n φ → InOnS (n + 1) (Formula.neg φ)

def O_nS (n : Nat) : ObservationsSet Label := { φ | InOnS n φ }

/-! ### Bisimulation observations `O_B` -/

def O_B : ObservationsSet Label := Set.univ

/-! ## Helper Lemmas -/

/-- `InOT` is preserved by the `InOT → InOF` embedding. -/
lemma InOT_to_InOF {φ : Formula Label} (h : InOT φ) : InOF φ := by
  induction h with
  | top => exact InOF.top
  | modal a ih =>
    apply InOF.modal a
    trivial

/-- `InOT` is preserved by the `InOT → InO1S` embedding. -/
lemma InOT_to_InO1S {φ : Formula Label} (h : InOT φ) : InO1S φ := by
  induction h with
  | top => exact InO1S.top
  | modal a ih =>
    apply InO1S.modal a
    trivial

/-- `InO1S` is preserved by the `InO1S → InORS` embedding. -/
lemma InO1S_to_InORS {φ : Formula Label} (h : InO1S φ) : InORS φ := by
  induction h with
  | top => exact InORS.top
  | modal a ih =>
    apply InORS.modal a
    trivial
  | conj φs ih =>
    apply InORS.conj
    trivial

/-- `InOT` is preserved by the `InOT → InORS` embedding. -/
lemma InOT_to_InORS {φ : Formula Label} (h : InOT φ) : InORS φ :=
  InO1S_to_InORS (InOT_to_InO1S h)

/-- `InOT` is preserved by the `InOT → InOFT` embedding. -/
lemma InOT_to_InOFT {φ : Formula Label} (h : InOT φ) : InOFT φ := by
  induction h with
  | top => exact InOFT.top
  | modal a ih =>
    apply InOFT.modal a
    trivial

/-- `InOT` is preserved by the `InOT → InORT` embedding. -/
lemma InOT_to_InORT {φ : Formula Label} (h : InOT φ) : InORT φ := by
  induction h with
  | top => exact InORT.top
  | modal a ih =>
    apply InORT.modal a
    trivial

/-- `InOT` is preserved by the `InOT → InOIF` embedding. -/
lemma InOT_to_InOIF {φ : Formula Label} (h : InOT φ) : InOIF φ := by
  induction h with
  | top => exact InOIF.top
  | modal a ih =>
    apply InOIF.modal a
    trivial

/-- `InOT` is preserved by the `InOT → InOPF` embedding. -/
lemma InOT_to_InOPF {φ : Formula Label} (h : InOT φ) : InOPF φ := by
  induction h with
  | top => exact InOPF.top
  | modal a ih =>
    apply InOPF.modal a
    trivial

/-- `obsAct a` is a trace observation. -/
lemma obsAct_InOT (a : Label) : InOT (obsAct (Label := Label) a) :=
  InOT.modal a InOT.top

/-- `as.map negObsAct = (as.map obsAct).map Formula.neg` -/
lemma map_negObsAct_eq_map_neg_obsAct (as : List Label) :
    as.map (negObsAct (Label := Label)) = (as.map obsAct).map Formula.neg := by
  induction as with
  | nil => simp
  | cons hd tl ih =>
    simp [negObsAct, ih]

/-- A sublist of `as.map negObsAct` is a mapped list of some `as'`. -/
lemma sublist_map_negObsAct {as : List Label}
    {φs' : List (Formula Label)}
    (hsub : φs' ⊆ as.map (negObsAct (Label := Label))) :
    ∃ as' : List Label, φs' = as'.map negObsAct := by
  induction φs' with
  | nil => exact ⟨[], rfl⟩
  | cons hd tl ih =>
    have hhd : hd ∈ as.map negObsAct := hsub (List.mem_cons.mpr (Or.inl rfl))
    rw [List.mem_map] at hhd
    obtain ⟨a, _, rfl⟩ := hhd
    have htl : tl ⊆ as.map negObsAct := by
      intro x hx
      exact hsub (List.mem_cons.mpr (Or.inr hx))
    obtain ⟨as', rfl⟩ := ih htl
    exact ⟨a :: as', rfl⟩

/-- A sublist of `ψs.map Formula.neg` is a mapped list. -/
lemma sublist_map_neg {ψs : List (Formula Label)}
    {φs' : List (Formula Label)}
    (hsub : φs' ⊆ ψs.map Formula.neg) :
    ∃ ψs', φs' = ψs'.map Formula.neg ∧ ψs' ⊆ ψs := by
  induction φs' with
  | nil => exact ⟨[], rfl, List.nil_subset _⟩
  | cons hd tl ih =>
    have hhd : hd ∈ ψs.map Formula.neg := hsub (List.mem_cons.mpr (Or.inl rfl))
    rw [List.mem_map] at hhd
    obtain ⟨ψ, hψ_mem, rfl⟩ := hhd
    have htl : tl ⊆ ψs.map Formula.neg := by
      intro x hx
      exact hsub (List.mem_cons.mpr (Or.inr hx))
    obtain ⟨ψs', rfl, hψs'_sub⟩ := ih htl
    exact ⟨ψ :: ψs', rfl, by
      intro x hx
      simp [List.mem_cons] at hx
      cases hx with
      | inl h => rw [h]; exact hψ_mem
      | inr h => exact hψs'_sub h⟩

/-- Every element of `as.map negObsAct` is a `negObsAct`. -/
lemma mem_map_negObsAct {as : List Label} {φ : Formula Label}
    (h : φ ∈ as.map (negObsAct (Label := Label))) : ∃ a, φ = negObsAct a := by
  rw [List.mem_map] at h
  obtain ⟨a, _, rfl⟩ := h
  exact ⟨a, rfl⟩

/-- A sublist of ready-literals consists of ready-literals. -/
lemma sublist_readyLits {φs φs' : List (Formula Label)}
    (hall : ∀ φ, φ ∈ φs → IsReadyLit φ)
    (hsub : φs' ⊆ φs) :
    ∀ φ, φ ∈ φs' → IsReadyLit φ :=
  fun φ hφ => hall φ (hsub hφ)

/-- A sublist of PF-literals consists of PF-literals. -/
lemma sublist_pfLits {φs φs' : List (Formula Label)}
    (hall : ∀ φ, φ ∈ φs → IsPFLit φ)
    (hsub : φs' ⊆ φs) :
    ∀ φ, φ ∈ φs' → IsPFLit φ :=
  fun φ hφ => hall φ (hsub hφ)


/-! ## Closure Proofs (Proposition 2.16) -/

/-! ### Enabledness `O_E` is closed -/

theorem O_E_closed : ClosedObservationLanguage (O_E (Label := Label)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a φ h
    simp only [O_E, Set.mem_setOf_eq] at h
    cases h with
    | act a' =>
      constructor
  · intro φs h
    simp only [O_E, Set.mem_setOf_eq] at h
    cases h
  · intro φ h
    simp only [O_E, Set.mem_setOf_eq] at h
    cases h

/-! ### Trace observations `O_T` is closed -/

theorem O_T_closed : ClosedObservationLanguage (O_T (Label := Label)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a φ h
    simp only [O_T, Set.mem_setOf_eq] at *
    cases h with
    | modal _ hφ => exact hφ
  · intro φs h
    simp only [O_T, Set.mem_setOf_eq] at h
    cases h
  · intro φ h
    simp only [O_T, Set.mem_setOf_eq] at h
    cases h

/-! ### Failure observations `O_F` is closed -/



theorem O_F_closed : ClosedObservationLanguage (O_F (Label := Label)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- closed_modal
    intro a φ h
    simp only [O_F, Set.mem_setOf_eq] at *
    cases h with
    | modal _ hφ => exact hφ
  · -- closed_conj
    intro φs h
    simp only [O_F, Set.mem_setOf_eq] at *
    cases h with
    | failConj as =>
      constructor
      ·
        intro φ hφ
        unfold negObsAct at hφ
        obtain ⟨a, rfl⟩ := mem_map_negObsAct hφ
        exact InOF.negAct a

      · -- Partial conjunctions
        intro φs' hsub
        obtain ⟨as', rfl⟩ := sublist_map_negObsAct hsub
        exact InOF.failConj as'
  ·
    intro φ h
    simp only [O_F, Set.mem_setOf_eq] at h
    cases h
    unfold obsAct
    apply InOF.modal
    exact InOF.top


/-! ### Readiness observations `O_R` is closed -/

theorem O_R_closed : ClosedObservationLanguage (O_R (Label := Label)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a φ h
    simp only [O_R, Set.mem_setOf_eq] at *
    cases h with
    | modal _ hφ => exact hφ
  · intro φs h
    simp only [O_R, Set.mem_setOf_eq] at *
    cases h with
    | readyConj _ hall =>
      constructor
      · intro φ hφ
        have hrl := hall φ hφ
        cases hrl with
        | pos a => apply InOR.modal a InOR.top
        | neg a =>
          simp only [negObsAct] at *
          constructor




      · intro φs' hsub
        exact InOR.readyConj φs' (sublist_readyLits hall hsub)
  · intro φ h
    simp only [O_R, Set.mem_setOf_eq] at h
    cases h
    constructor
    constructor

/-! ### Failure-trace observations `O_FT` is closed -/

theorem O_FT_closed : ClosedObservationLanguage (O_FT (Label := Label)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a φ h
    cases h
    trivial
  .
    intro φs h
    constructor
    · intro φ hφ
      have h' : InOFT (Label := Label) (Formula.conj φs) := by
        simpa [O_FT, Set.mem_setOf_eq] using h
      cases h' with
      | ftConj φs φ₀ h₀mem hφ₀ hOthers =>
        specialize hOthers φ hφ
        by_cases heq : φ = φ₀
        · subst heq
          exact hφ₀
        · specialize hOthers heq
          obtain ⟨a, hψ_eq⟩ := hOthers
          rw [hψ_eq]
          exact InOFT.negAct a


    .
      intro φs' hsub
      cases h with
      | ftConj φs φ₀ h₀mem hφ₀ hOthers =>
          by_cases hmem : φ₀ ∈ φs'
          · -- keep φ₀ as the distinguished conjunct
            refine InOFT.ftConj (Label := Label) φs' φ₀ hmem hφ₀ ?_
            intro ψ hψ hne
            exact hOthers ψ (hsub hψ) hne
          ·  by_cases hempty : φs' = []
             subst hempty

             sorry

             cases φs' with
             | nil => contradiction
             | cons hd tl =>
                  have hhd_mem_big : hd ∈ φs := hsub (by simp)
                  sorry



  ·
    intro φ h
    cases h
    constructor
    constructor



/-! ### Ready-trace observations `O_RT` is closed -/

theorem O_RT_closed : ClosedObservationLanguage (O_RT (Label := Label)) := by
  sorry

/-! ### Impossible-future observations `O_IF` is closed -/

theorem O_IF_closed : ClosedObservationLanguage (O_IF (Label := Label)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a φ h
    simp only [O_IF, Set.mem_setOf_eq] at *
    cases h with
    | modal _ hφ => exact hφ
  · intro φs h
    simp only [O_IF, Set.mem_setOf_eq] at *
    cases h with
    | ifConj ψs hall =>
      constructor
      · -- Each Formula.neg ψᵢ is in O_IF
        intro φ hφ
        rw [List.mem_map] at hφ
        obtain ⟨ψ, hψ_mem, rfl⟩ := hφ
        -- ψ ∈ O_T, need Formula.neg ψ ∈ O_IF
        -- Use ifConj [ψ]: [ψ].map neg = [neg ψ], and ψ ∈ O_T
        sorry
      · -- Partial conjunctions
        intro φs' hsub
        obtain ⟨ψs', rfl, hψs'_sub⟩ := sublist_map_neg hsub
        exact InOIF.ifConj ψs' (fun ψ hψ => hall ψ (hψs'_sub hψ))
  · intro φ h
    simp only [O_IF, Set.mem_setOf_eq] at h
    cases h

/-! ### Possible-future observations `O_PF` is closed -/

theorem O_PF_closed : ClosedObservationLanguage (O_PF (Label := Label)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a φ h
    simp only [O_PF, Set.mem_setOf_eq] at *
    cases h with
    | modal _ hφ => exact hφ
  · intro φs h
    simp only [O_PF, Set.mem_setOf_eq] at *
    cases h with
    | pfConj _ hall =>
      constructor
      · intro φ hφ
        have hpf := hall φ hφ
        cases hpf with
        | pos hψ => exact InOT_to_InOPF hψ
        | neg hψ =>
          sorry
      · intro φs' hsub
        exact InOPF.pfConj φs' (sublist_pfLits hall hsub)
  · intro φ h
    simp only [O_PF, Set.mem_setOf_eq] at h
    cases h

/-! ### Simulation observations `O_1S` is closed -/

theorem O_1S_closed : ClosedObservationLanguage (O_1S (Label := Label)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a φ h
    simp only [O_1S, Set.mem_setOf_eq] at *
    cases h with
    | modal _ hφ => exact hφ
  · intro φs h
    simp only [O_1S, Set.mem_setOf_eq] at *
    cases h with
    | conj _ hall =>
        sorry
  · intro φ h
    simp only [O_1S, Set.mem_setOf_eq] at h
    cases h

/-! ### Ready-simulation observations `O_RS` is closed -/

theorem O_RS_closed : ClosedObservationLanguage (O_RS (Label := Label)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- closed_modal
    intro a φ h
    simp only [O_RS, Set.mem_setOf_eq] at *
    cases h with
    | modal _ hφ => exact hφ

  · -- closed_conj
    intro φs h
    simp only [O_RS, Set.mem_setOf_eq] at *
    cases h with
    | conj _ hall =>
      sorry
  · -- closed_neg: neg φ ∈ O_RS means neg φ was produced by InORS
    -- Only negAct produces a neg: negObsAct a = neg (modal a true)
    -- So φ = modal a true, which is InORS.modal a InORS.top
    intro φ h
    simp only [O_RS, Set.mem_setOf_eq] at *
    cases h with
    | negAct a =>
      simp [negObsAct, obsAct]
      exact InORS.modal a InORS.top

/-! ### Bisimulation observations `O_B` is closed -/

theorem O_B_closed : ClosedObservationLanguage (O_B (Label := Label)) := by
  simp only [ClosedObservationLanguage, O_B]
  exact ⟨fun _ => Set.mem_univ _,
         fun _ => ⟨fun _ => Set.mem_univ _, fun _ => Set.mem_univ _⟩,
         fun _ => Set.mem_univ _⟩

/-! ## Inclusion Relations (Figure 2) -/

theorem O_E_sub_O_T : O_E (Label := Label) ⊆ O_T := by
  intro φ hφ
  simp only [O_E, O_T, Set.mem_setOf_eq] at *
  cases hφ with
  | top => exact InOT.top
  | act a => exact InOT.modal a InOT.top

theorem O_T_sub_O_F : O_T (Label := Label) ⊆ O_F := by
  intro φ hφ
  simp only [O_T, O_F, Set.mem_setOf_eq] at *
  exact InOT_to_InOF hφ

theorem O_T_sub_O_1S : O_T (Label := Label) ⊆ O_1S := by
  intro φ hφ
  simp only [O_T, O_1S, Set.mem_setOf_eq] at *
  exact InOT_to_InO1S hφ




theorem O_IF_sub_O_PF : O_IF (Label := Label) ⊆ O_PF := by
  intro φ hφ
  simp only [O_IF, O_PF, Set.mem_setOf_eq] at *
  induction hφ with
  | top => exact InOPF.top
  | modal a ih =>
    apply InOPF.modal a
    trivial
  | ifConj ψs hall =>
    exact InOPF.pfConj (ψs.map Formula.neg) (fun φ hφ => by
      rw [List.mem_map] at hφ
      obtain ⟨ψ, hψ_mem, rfl⟩ := hφ
      exact IsPFLit.neg (hall ψ hψ_mem))

theorem O_1S_sub_O_RS : O_1S (Label := Label) ⊆ O_RS := by
  intro φ hφ
  simp only [O_1S, O_RS, Set.mem_setOf_eq] at *
  exact InO1S_to_InORS hφ

theorem sub_O_B (O : ObservationsSet Label) : O ⊆ O_B := by
  intro _ _; exact Set.mem_univ _

end Cslib
