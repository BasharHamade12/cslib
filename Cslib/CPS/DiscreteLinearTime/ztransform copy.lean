

import Cslib.Init
import Mathlib


open scoped ComplexOrder


set_option linter.style.emptyLine false
set_option linter.deprecated.module false

universe u v

section DiscreteLinearSystem

/-!
# Basic definitions for Discrete Linear Time Systems

This module defines the state space representation of a discrete-time linear dynamical system.
It includes the definition of the system state, the evolution function,
and the property of satisfying the state equation.

## Main Definitions
* `DiscreteLinearSystemState`: Structure representing the system matrices (A and B),
the current state, input, and initial state.
* `DiscreteLinearSystemState.system_evolution`: Function computing the state at time `k`
given an input sequence.
* `DiscreteLinearSystemState.satisfies_state_equation`: Proposition stating that
the sequence `x` satisfies the linear difference equation `x(k+1) = A x(k) + B u(k)`.
-/

variable {σ : Type u} {ι : Type v}
variable [TopologicalSpace σ] [NormedAddCommGroup σ] [NormedSpace ℂ σ]
variable [TopologicalSpace ι] [NormedAddCommGroup ι] [NormedSpace ℂ ι]
* `DiscreteLinearSystemState`: Structure representing the system matrices (A and B),
the current state, input, and initial state.
* `DiscreteLinearSystemState.system_evolution`: Function computing the state at time `k`
given an input sequence.
* `DiscreteLinearSystemState.satisfies_state_equation`: Proposition stating that
the sequence `x` satisfies the linear difference equation `x(k+1) = A x(k) + B u(k)`.
-/

variable {σ : Type u} {ι : Type v}
variable [TopologicalSpace σ] [NormedAddCommGroup σ] [NormedSpace ℂ σ]
variable [TopologicalSpace ι] [NormedAddCommGroup ι] [NormedSpace ℂ ι]
variable [Inhabited ι]

/-- Discrete-time linear dynamical system with state equation x(k+1) = A·x(k) + B·u(k). -/
structure DiscreteLinearSystemState (σ : Type u) (ι : Type v)
    [TopologicalSpace σ] [NormedAddCommGroup σ] [NormedSpace ℂ σ]
    [TopologicalSpace ι] [NormedAddCommGroup ι] [NormedSpace ℂ ι] where
  /-- State transition matrix (A), mapping the current state to the next state component (n×n). -/
  a : σ →L[ℂ] σ
  /-- Input matrix (B), mapping the current input to the next state component (n×p). -/
  B : ι →L[ℂ] σ
  /-- Initial state -/
  x₀ : σ
  /-- State sequence -/
  x : ℕ → σ
  /-- Input sequence -/
  u : ℕ → ι

variable {sys : DiscreteLinearSystemState σ ι}

/-- System evolution function from initial state -/
noncomputable def DiscreteLinearSystemState.system_evolution (u : ℕ → ι) : ℕ → σ
  | 0 => sys.x₀
  | k + 1 => sys.a (system_evolution u k) + sys.B (u k)

/-- Discrete state space representation property -/
def DiscreteLinearSystemState.satisfies_state_equation : Prop :=
  ∀ k : ℕ, sys.x (k + 1) = sys.a (sys.x k) + sys.B (sys.u k)


/-- Evolution from zero initial state with given input -/
noncomputable def DiscreteLinearSystemState.evolve_from_zero
   (u : ℕ → ι) (sys : DiscreteLinearSystemState σ ι) : ℕ → σ
  | 0 => 0
  | k + 1 => sys.a (evolve_from_zero u sys k) + sys.B (u k)




/-- Zero input sequence -/
def zero_input : ℕ → ι := fun _ => 0


def DiscreteSignal (σ : Type*) := ℕ → σ

/-- The zero signal (constantly zero). -/
def DiscreteSignal.zero : DiscreteSignal σ := fun _ => 0

/-- Unit impulse signal: δ(k) = 1 if k = 0, else 0. -/
def DiscreteSignal.impulse : DiscreteSignal ℂ :=
  fun k => if k = 0 then 1 else 0

/-- Unit step signal: u(k) = 1 for all k ≥ 0. -/
def DiscreteSignal.step : DiscreteSignal ℂ :=
  fun _ => 1

def DiscreteSignal.exponential (a : ℂ) : DiscreteSignal ℂ :=
  fun k => a ^ k

/-- Delayed signal: shifts signal by n steps (with zero padding). -/
def DiscreteSignal.delay (e : DiscreteSignal σ) (n : ℕ) : DiscreteSignal σ :=
  fun k => if n ≤ k then e (k - n) else 0

/-- Extract signal from a DiscreteLinearSystemState's state sequence. -/
def DiscreteSignal.fromState {ι : Type*}
    [NormedAddCommGroup ι] [NormedSpace ℂ ι]
    (sys : DiscreteLinearSystemState σ ι) : DiscreteSignal σ :=
  sys.x

/-- Extract signal from a DiscreteLinearSystemState's input sequence. -/
def DiscreteSignal.fromInput {ι : Type*}
    [NormedAddCommGroup ι] [NormedSpace ℂ ι]
    (sys : DiscreteLinearSystemState σ ι) : DiscreteSignal ι :=
  sys.u


noncomputable def zTransform (e : DiscreteSignal σ) (z : ℂ) : σ :=
  ∑' k : ℕ, (z⁻¹ ^ k) • e k


structure SamplingPeriod where
  /-- The sampling period value (must be positive). -/
  val : ℝ
  /-- The sampling period is positive. -/
  pos : 0 < val


/-- A sampled signal pairs a discrete signal with its sampling period T.
    The value at index k represents the signal at time t = kT. -/
structure SampledSignal (σ : Type*) where
  signal : DiscreteSignal σ
  T : SamplingPeriod

/-- The z-transform of a sampled signal e(kT).
    E(z) = ∑_{k=0}^{∞} e(kT) z⁻ᵏ -/
noncomputable def zTransformSampled (e : SampledSignal σ) (z : ℂ) : σ :=
  ∑' k : ℕ, (z⁻¹ ^ k) • e.signal k

/-- The two z-transform definitions are equal:
    ∑_{k=0}^{∞} e(kT) z⁻ᵏ = ∑_{k=0}^{∞} eₖ z⁻ᵏ
    since e(kT) = eₖ by definition of discrete sampling. -/
theorem zTransform_eq_zTransformSampled (e : SampledSignal σ) (z : ℂ) :
    zTransformSampled e z = zTransform e.signal z := rfl

/-- Notation: Z{f} denotes the z-transform of a sampled signal f. -/
notation "Z{" f "}" => zTransformSampled f

/-- F(z) = Z{f(kT)} represents the z-transform of signal f evaluated at z. -/
noncomputable def ZTransformAt (f : SampledSignal σ) (z : ℂ) : σ := Z{f} z

/-- Delayed sampled signal: shifts signal by n sampling periods (with zero padding).
    Represents f(kT - nT) = f((k-n)T). -/
def SampledSignal.delay (f : SampledSignal σ) (n : ℕ) : SampledSignal σ where
  signal := fun k => if n ≤ k then f.signal (k - n) else 0
  T := f.T

/-- Time delay property: Z{f(kT - nT)} = z⁻ⁿ F(z) for n > 0.
    Assumes f is causal (f(kT) = 0 for k < 0). -/

lemma delay_signal_of_ge
(f : DiscreteSignal σ) (n k : ℕ) (hk : n ≤ k) :
    (f.delay n) k = f (k - n) := by
  simp [DiscreteSignal.delay, hk]

lemma delay_signal_of_ge_sampled
(f : SampledSignal σ) (n k : ℕ) (hk : n ≤ k) :
    (f.delay n).signal k = f.signal (k - n) := by
  simp [SampledSignal.delay, hk]

#print Summable.add


/-! ### Z-Transform Summability -/

/-- A discrete signal's z-transform is summable at z. -/
def ZTransformSummable (e : DiscreteSignal σ) (z : ℂ) : Prop :=
  Summable (fun k : ℕ => (z⁻¹ ^ k) • e k)

/-- A sampled signal's z-transform is summable at z. -/
def ZTransformSampledSummable (e : SampledSignal σ) (z : ℂ) : Prop :=
  ZTransformSummable e.signal z

/-- Region of convergence: the set of z where the z-transform converges. -/
def regionOfConvergence (e : DiscreteSignal σ) : Set ℂ :=
  {z : ℂ | ZTransformSummable e z}

/-! ### Summability Lemmas -/

/-- The zero signal is summable everywhere. -/
lemma zTransformSummable_zero (z : ℂ) :
ZTransformSummable (DiscreteSignal.zero : DiscreteSignal σ) z := by
  simp only [ZTransformSummable, DiscreteSignal.zero, smul_zero]
  exact summable_zero

/-- The impulse signal is summable everywhere. -/
lemma zTransformSummable_impulse (z : ℂ) : ZTransformSummable DiscreteSignal.impulse z := by
  simp only [ZTransformSummable, DiscreteSignal.impulse]
  apply summable_of_ne_finset_zero (s := {0})
  intro k hk
  simp only [Finset.mem_singleton] at hk
  simp [hk]

/-- A signal bounded by a geometric series is summable for |z| > r. -/
lemma zTransformSummable_of_norm_le {e : DiscreteSignal σ} {r : ℝ} (hr : 0 ≤ r)
    (he : ∀ k, ‖e k‖ ≤ r ^ k) {z : ℂ} (hz : r < ‖z‖) :
    ZTransformSummable e z := by
  refine Classical.choice ?_
  simp
  constructor

  ·

    sorry
  ·
    sorry






/-- The exponential signal aᵏ is summable for |z| > |a|. -/
lemma zTransformSummable_exponential {a z : ℂ} (hz : ‖a‖ < ‖z‖)  :
    ZTransformSummable (DiscreteSignal.exponential a) z := by
  apply zTransformSummable_of_norm_le (norm_nonneg a)
  · intro k
    simp [DiscreteSignal.exponential, norm_pow]
  · exact hz

/-- Summability of delayed signal from summability of original. -/
lemma zTransformSummable_delay {e : DiscreteSignal σ} {z : ℂ} (n : ℕ)
    [IsTopologicalAddGroup σ] [T2Space σ] [Neg ℕ] [ContinuousConstSMul ℂ σ]:
     ZTransformSummable e z ↔ ZTransformSummable (e.delay n) z := by
  have h_eq : (fun m => z⁻¹ ^ (m + n) • e m) = (fun m => z⁻¹ ^ n • (z⁻¹ ^ m • e m)) := by
      ext m
      rw [pow_add, mul_smul]
      exact smul_comm (z⁻¹ ^ m) (z⁻¹ ^ n) (e m)
  constructor
  ·
    intro he
    simp only [ZTransformSummable, DiscreteSignal.delay]
    -- Use summable_nat_add_iff: Summable f ↔ Summable (fun m => f (m + n))
    rw [← summable_nat_add_iff n]
    -- Goal: Summable fun m => z⁻¹ ^ (m + n) • if n ≤ m + n then e (m + n - n) else 0
    -- Simplify: n ≤ m + n is always true, and m + n - n = m
    simp only [le_add_iff_nonneg_left, zero_le, ↓reduceIte, add_tsub_cancel_right]
    -- Goal: Summable fun m => z⁻¹ ^ (m + n) • e m
    -- Factor: z⁻¹ ^ (m + n) = z⁻¹ ^ n * z⁻¹ ^ m

    rw [h_eq]
    simp
    -- exact Summable.const_smul he (z⁻¹ ^ n) (does not work)
    apply Summable.const_smul
    unfold ZTransformSummable at he
    simp only [inv_pow] at he
    exact he
  ·
    intro h_delay
    simp only [ZTransformSummable, DiscreteSignal.delay] at h_delay
    simp only [ZTransformSummable]
    rw [← summable_nat_add_iff n] at h_delay
    simp only [le_add_iff_nonneg_left, zero_le, ↓reduceIte, add_tsub_cancel_right] at h_delay
    rw [h_eq] at h_delay
    simp only [inv_pow] at h_delay
    -- h_delay : Summable (fun m => (z ^ n)⁻¹ • (z ^ m)⁻¹ • e m)
    -- Goal: Summable (fun k => (z ^ k)⁻¹ • e k)
    by_cases hz : z = 0
    · -- z = 0 case: only k = 0 term matters
      simp only [hz, inv_zero, zero_pow] at h_delay ⊢
      apply summable_of_ne_finset_zero (s := {0})
      intro k hk
      simp only [Finset.mem_singleton] at hk
      simp only [ne_eq, hk, not_false_eq_true, zero_pow, zero_smul]
    · have h_smul := h_delay.const_smul (z ^ n)
      simp only [smul_smul] at h_smul
      convert h_smul using 1
      ext k
      simp only [inv_pow]
      nth_rewrite 1 [<-mul_assoc]
      have : z ^ n * (z ^ n)⁻¹ = 1 := by
        field_simp
      rw [this, one_mul]










    -- Goal: Summable fun m => z⁻¹ ^ (m + n) • e m





/-- Summability of sampled delayed signal. -/
lemma zTransformSampledSummable_delay {f : SampledSignal σ} {z : ℂ} (n : ℕ)
    (hf : ZTransformSampledSummable f z) :
    ZTransformSampledSummable (f.delay n) z := by
  simp only [ZTransformSampledSummable, SampledSignal.delay]
  simp only [ZTransformSummable]

  -- Similar to above
  sorry


theorem h_summable (f : SampledSignal σ) (n : ℕ) (z : ℂ)
    (hf : Summable (fun k : ℕ => (z⁻¹ ^ k) • f.signal k))
    [IsTopologicalAddGroup σ] [ContinuousConstSMul ℂ σ] [T2Space σ]  :
    Summable (fun k => (z⁻¹ ^ k) • (if n ≤ k then f.signal (k - n) else 0)) := by
    obtain ⟨x, hx⟩ := hf
    refine ⟨(z⁻¹ ^ n) • x, ?_⟩

    have h_shift : HasSum (fun m => z⁻¹ ^ (m + n) • f.signal m) ((z⁻¹ ^ n) • x) := by
      simp_rw [pow_add, mul_smul]
      simp_rw [smul_comm (z⁻¹ ^ _) (z⁻¹ ^ n)]
      exact hx.const_smul (z⁻¹ ^ n)

    have h_zero_prefix : ∑ i ∈ Finset.range n,
        (z⁻¹ ^ i • if n ≤ i then f.signal (i - n) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [Nat.not_le.mpr (Finset.mem_range.mp hi)]

    have h_eq : (fun k => z⁻¹ ^ (k + n) • if n ≤ k + n then f.signal (k + n - n) else 0) =
            (fun k => z⁻¹ ^ (k + n) • f.signal k) := by
      ext k
      simp only [le_add_iff_nonneg_left, zero_le, ↓reduceIte, add_tsub_cancel_right]

    have : (fun k => z⁻¹ ^ k • if n ≤ k then f.signal (k - n) else 0) =
      fun k => if k < n then 0 else z⁻¹ ^ k • f.signal (k - n) := by
      ext k
      split_ifs <;> simp [*]
      · omega
      · omega

    rw [this]

    have h_prefix_zero : ∑ i ∈ Finset.range n,
      (if i < n then 0 else z⁻¹ ^ i • f.signal (i - n)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [Finset.mem_range.mp hi]

  -- Use hasSum_nat_add_iff': shift the index by n
    rw [← hasSum_nat_add_iff' n, h_prefix_zero, sub_zero]

  -- Now goal is: HasSum (fun k => if (k+n) < n then 0 else ...) (z⁻¹ ^ n • x)
  -- Since k+n ≥ n always, the if-condition is false
    convert h_shift using 1
    ext m
    simp only [Nat.not_lt.mpr (Nat.le_add_left n m), ↓reduceIte, Nat.add_sub_cancel]









theorem zTransform_time_delay (f : SampledSignal σ) (n : ℕ) (z : ℂ)
    (hf : Summable (fun k : ℕ => (z⁻¹ ^ k) • f.signal k))
    [IsTopologicalAddGroup σ] [ContinuousConstSMul ℂ σ] [T2Space σ] :
    Z{f.delay n} z = (z⁻¹ ^ n) • Z{f} z := by
  simp only [zTransformSampled, SampledSignal.delay]
  have h_zero_range : ∑ i ∈ Finset.range n, (z⁻¹ ^ i) •
  (if n ≤ i then f.signal (i - n) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_range] at hi
    simp [Nat.not_le.mpr hi]

  have h_summable := h_summable f n z hf
  rw [← Summable.sum_add_tsum_nat_add n h_summable]
  rw [h_zero_range, zero_add]
  -- Now goal is: ∑' m, z⁻¹^(m+n) • f.signal m = z⁻¹^n • ∑' k, z⁻¹^k • f.signal k
  -- Simplify the if-condition since m + n ≥ n
  have h_simp : ∀ m, (z⁻¹ ^ (m + n)) • (if n ≤ m + n then f.signal (m + n - n) else 0) =
      (z⁻¹ ^ (m + n)) • f.signal m := by
    intro m
    simp only [inv_pow, le_add_iff_nonneg_left, zero_le, ↓reduceIte, add_tsub_cancel_right]
  simp_rw [h_simp]
  -- Factor: z⁻¹^(m+n) = z⁻¹^n * z⁻¹^m
  have h_pow : ∀ m, z⁻¹ ^ (m + n) = z⁻¹ ^ n * z⁻¹ ^ m := by
    intro m
    rw [pow_add]
    simp only [inv_pow]
    rw [mul_comm]

  simp_rw [h_pow, mul_smul]
  -- Pull out the constant z⁻¹^n
  -- simp only [inv_pow]

  rw [Summable.tsum_const_smul (z⁻¹ ^ n) hf]


/-! ### Z-Transform Summability -/

/-- A discrete signal's z-transform is summable at z. -/
def ZTransformSummable (e : DiscreteSignal σ) (z : ℂ) : Prop :=
  Summable (fun k : ℕ => (z⁻¹ ^ k) • e k)

/-- A sampled signal's z-transform is summable at z. -/
def ZTransformSampledSummable (e : SampledSignal σ) (z : ℂ) : Prop :=
  ZTransformSummable e.signal z

/-- Region of convergence: the set of z where the z-transform converges. -/
def regionOfConvergence (e : DiscreteSignal σ) : Set ℂ :=
  {z : ℂ | ZTransformSummable e z}

/-! ### Summability Lemmas -/

/-- The zero signal is summable everywhere. -/
lemma zTransformSummable_zero (z : ℂ) :
ZTransformSummable (DiscreteSignal.zero : DiscreteSignal σ) z := by
  simp only [ZTransformSummable, DiscreteSignal.zero, smul_zero]
  exact summable_zero

/-- The impulse signal is summable everywhere. -/
lemma zTransformSummable_impulse (z : ℂ) : ZTransformSummable DiscreteSignal.impulse z := by
  simp only [ZTransformSummable, DiscreteSignal.impulse]
  apply summable_of_ne_finset_zero (s := {0})
  intro k hk
  simp only [Finset.mem_singleton] at hk
  simp [hk]

/-- A signal bounded by a geometric series is summable for |z| > r. -/
lemma zTransformSummable_of_norm_le {e : DiscreteSignal σ} {r : ℝ} (hr : 0 ≤ r)
    (he : ∀ k, ‖e k‖ ≤ r ^ k) {z : ℂ} (hz : r < ‖z‖) :
    ZTransformSummable e z := by
  refine Classical.choice ?_
  simp
  constructor

  ·

    sorry
  ·
    sorry






/-- The exponential signal aᵏ is summable for |z| > |a|. -/
lemma zTransformSummable_exponential {a z : ℂ} (hz : ‖a‖ < ‖z‖) :
    ZTransformSummable (DiscreteSignal.exponential a) z := by
  apply zTransformSummable_of_norm_le (norm_nonneg a)
  · intro k
    simp [DiscreteSignal.exponential, norm_pow]
  · exact hz

/-- Summability of delayed signal from summability of original. -/
lemma zTransformSummable_delay {e : DiscreteSignal σ} {z : ℂ} (n : ℕ)
    (he : ZTransformSummable e z) [IsTopologicalAddGroup σ] [T2Space σ] [ContinuousConstSMul ℂ σ]:
    ZTransformSummable (e.delay n) z := by
  simp only [ZTransformSummable, DiscreteSignal.delay]
  -- Use summable_nat_add_iff: Summable f ↔ Summable (fun m => f (m + n))
  rw [← summable_nat_add_iff n]
  -- Goal: Summable fun m => z⁻¹ ^ (m + n) • if n ≤ m + n then e (m + n - n) else 0
  -- Simplify: n ≤ m + n is always true, and m + n - n = m
  simp only [le_add_iff_nonneg_left, zero_le, ↓reduceIte, add_tsub_cancel_right]
  -- Goal: Summable fun m => z⁻¹ ^ (m + n) • e m
  -- Factor: z⁻¹ ^ (m + n) = z⁻¹ ^ n * z⁻¹ ^ m
  have h_eq : (fun m => z⁻¹ ^ (m + n) • e m) = (fun m => z⁻¹ ^ n • (z⁻¹ ^ m • e m)) := by
    ext m
    rw [pow_add, mul_smul]
    exact smul_comm (z⁻¹ ^ m) (z⁻¹ ^ n) (e m)
  rw [h_eq]
  simp
  -- exact Summable.const_smul he (z⁻¹ ^ n) (does not work)
  apply Summable.const_smul
  unfold ZTransformSummable at he
  simp only [inv_pow] at he
  exact he




/-- Summability of sampled delayed signal. -/
lemma zTransformSampledSummable_delay {f : SampledSignal σ} {z : ℂ} (n : ℕ)
    (hf : ZTransformSampledSummable f z) :
    ZTransformSampledSummable (f.delay n) z := by
  simp only [ZTransformSampledSummable, SampledSignal.delay]
  simp only [ZTransformSummable]

  -- Similar to above
  sorry
end DiscreteLinearSystem
