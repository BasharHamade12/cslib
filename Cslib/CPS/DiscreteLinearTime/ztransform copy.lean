

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
variable [NormedAddCommGroup σ] [NormedSpace ℂ σ]
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
  simp [SampledSignal.delay, hk ]

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

/-- Summability of delayed signal from summability of original.
    Note: Removed spurious [Neg ℕ] requirement. -/
lemma zTransformSummable_delay {e : DiscreteSignal σ} {z : ℂ} (n : ℕ)
    [IsTopologicalAddGroup σ] [T2Space σ] [ContinuousConstSMul ℂ σ]:
     ZTransformSummable e z ↔ ZTransformSummable (e.delay n) z := by
  have h_eq : (fun m => z⁻¹ ^ (m + n) • e m) = (fun m => z⁻¹ ^ n • (z⁻¹ ^ m • e m)) := by
      ext m
      rw [pow_add, mul_smul]
      exact smul_comm (z⁻¹ ^ m) (z⁻¹ ^ n) (e m)
  constructor
  ·
    intro he
    simp only [ZTransformSummable, DiscreteSignal.delay]
    rw [← summable_nat_add_iff n]
    simp only [le_add_iff_nonneg_left, zero_le, ↓reduceIte, add_tsub_cancel_right]
    rw [h_eq]
    apply Summable.const_smul
    exact he
  ·
    intro h_delay
    simp only [ZTransformSummable, DiscreteSignal.delay] at h_delay
    simp only [ZTransformSummable]
    rw [← summable_nat_add_iff n] at h_delay
    simp only [le_add_iff_nonneg_left, zero_le, ↓reduceIte, add_tsub_cancel_right] at h_delay
    rw [h_eq] at h_delay
    by_cases hz : z = 0
    · simp only [inv_pow]
      apply summable_of_ne_finset_zero (s := {0})
      intro k hk
      simp [Finset.mem_singleton] at hk
      simp [hk]
    · have h_smul := h_delay.const_smul (z ^ n)
      simp only [smul_smul] at h_smul
      convert h_smul using 1
      ext k
      simp only [inv_pow]
      nth_rewrite 1 [<-mul_assoc]
      have : z ^ n * (z ^ n)⁻¹ = 1 := by field_simp
      rw [this, one_mul]

theorem zTransform_time_delay (f : SampledSignal σ) (n : ℕ) (z : ℂ)
    (hf : Summable (fun k : ℕ => (z⁻¹ ^ k) • f.signal k))
    [IsTopologicalAddGroup σ] [ContinuousConstSMul ℂ σ] [T2Space σ] :
    Z{f.delay n} z = (z⁻¹ ^ n) • Z{f} z := by
  simp only [zTransformSampled, SampledSignal.delay]
  let g := fun k => z⁻¹ ^ k • (if n ≤ k then f.signal (k - n) else (0 : σ))
  have hg : Summable g := by
    -- Now this works because zTransformSummable_delay no longer requires [Neg ℕ]
    have := (zTransformSummable_delay n (z := z)).mp hf
    exact this
  have h_prefix_zero : ∀ k ∈ Finset.range n, g k = 0 := by
    intro k hk
    simp only [g, Finset.mem_range] at hk ⊢
    simp [Nat.not_le.mpr hk]
  calc ∑' k, g k
      = (∑ k ∈ Finset.range n, g k) + ∑' k, g (k + n) := by
          exact (hg.sum_add_tsum_nat_add n).symm
    _ = 0 + ∑' k, g (k + n) := by
          rw [Finset.sum_eq_zero h_prefix_zero]
    _ = ∑' k, z⁻¹ ^ (k + n) • f.signal k := by
          simp only [g, zero_add, le_add_iff_nonneg_left, zero_le, ↓reduceIte,
                     add_tsub_cancel_right]
    _ = ∑' k, z⁻¹ ^ n • (z⁻¹ ^ k • f.signal k) := by
          congr 1
          ext k
          rw [pow_add, mul_smul]
          exact smul_comm (z⁻¹ ^ k) (z⁻¹ ^ n) (f.signal k)
    _ = z⁻¹ ^ n • ∑' k, z⁻¹ ^ k • f.signal k := by
          exact tsum_const_smul'' (z⁻¹ ^ n)
theorem zTransform_linear {f g : SampledSignal σ} {α β : ℂ} {z : ℂ}
    (hf : Summable (fun k : ℕ => (z⁻¹ ^ k) • f.signal k))
    (hg : Summable (fun k : ℕ => (z⁻¹ ^ k) • g.signal k))
    [ContinuousConstSMul ℂ σ] [ IsTopologicalAddGroup σ] [T2Space σ] :
    Z{⟨fun k => α • f.signal k + β • g.signal k, f.T⟩} z =
    α • Z{f} z + β • Z{g} z := by
  simp only [zTransformSampled]

  simp_rw [smul_add]

  -- Step 2: Commute scalars
  -- z⁻¹^k • (α • f k) = α • (z⁻¹^k • f k)
  simp_rw [smul_comm (z⁻¹ ^ _) α, smul_comm (z⁻¹ ^ _) β]

  -- Step 3: Split the tsum using tsum_add
  -- ∑' k, (α • ... + β • ...) = ∑' k, α • ... + ∑' k, β • ...
  have hf' : Summable (fun k => α • (z⁻¹ ^ k • f.signal k)) := sorry
  have hg' : Summable (fun k => β • (z⁻¹ ^ k • g.signal k)) := sorry

  -- ∑' (k : ℕ), (α • z⁻¹ ^ k • f.signal k + β • z⁻¹ ^ k • g.signal k)
  -- = ∑' (k : ℕ), α • z⁻¹ ^ k • f.signal k + ∑' (k : ℕ), β • z⁻¹ ^ k • g.signal k
  have h_split : ∑' (k : ℕ), (α • z⁻¹ ^ k • f.signal k + β • z⁻¹ ^ k • g.signal k) =
    ∑' (k : ℕ), α • z⁻¹ ^ k • f.signal k + ∑' (k : ℕ), β • z⁻¹ ^ k • g.signal k := by
      have hf'' := hf'.hasSum
      have hg'' := hg'.hasSum

      exact (hf''.add hg'').tsum_eq
  have h_split2 : ∑' (k : ℕ), (α • z⁻¹ ^ k • f.signal k + β • z⁻¹ ^ k • g.signal k) =
    ∑' (k : ℕ), α • z⁻¹ ^ k • f.signal k + ∑' (k : ℕ), β • z⁻¹ ^ k • g.signal k := by
      have hf_hassum := hf'.hasSum
      have hg_hassum := hg'.hasSum
      have h_add := hf_hassum.add hg_hassum
      exact Summable.tsum_add hf' hg'


  rw [h_split2]

  -- Step 4: Factor out scalars from the sums using tsum_const_smul''
  -- (same lemma used in zTransform_time_delay)
  rw [tsum_const_smul'' α, tsum_const_smul'' β]



theorem zTransform_mul_sub_one_eq_sub {f : DiscreteSignal σ} {z : ℂ}
    [IsTopologicalAddGroup σ] [ContinuousConstSMul ℂ σ] [T2Space σ] :
    (z - 1) • (∑' k, (z⁻¹ ^ k) • f k) =
    -- We express the image's term ∑ f_k z^{-(k-1)} as z • F(z)
    (z • (∑' k, (z⁻¹ ^ k) • f k)) - (∑' k, (z⁻¹ ^ k) • f k) := by
  -- The proof is immediate from algebra: (a-b)*x = a*x - b*x
  rw [sub_smul]
  simp

theorem zTransform_mul_sub_one_split {f : DiscreteSignal σ} {z : ℂ}
    (hz : z ≠ 0)
    (hf : Summable (fun k => (z⁻¹ ^ k) • f k))
    [IsTopologicalAddGroup σ] [ContinuousConstSMul ℂ σ] [T2Space σ] :
    (z - 1) • (∑' k, (z⁻¹ ^ k) • f k) =
    (z • f 0 + ∑' k, (z⁻¹ ^ k) • f (k + 1)) - (∑' k, (z⁻¹ ^ k) • f k) := by
  rw [sub_smul]


  congr 1
  · rw [Summable.tsum_eq_zero_add hf]
    simp only [pow_zero, one_smul]
    rw [smul_add]
    congr 1
    rw [← tsum_const_smul'']
    congr 1
    ext k
    rw [smul_smul]
    congr 1
    rw [pow_succ, mul_comm z, mul_assoc, inv_mul_cancel₀ hz, mul_one]
  · exact one_smul _ _


theorem tsum_reindex_shift {f : ℕ → σ} {z : ℂ}
    [IsTopologicalAddGroup σ] [ContinuousConstSMul ℂ σ] [T2Space σ] :
    ∑' k : ℕ, (z⁻¹ ^ k) • f (k + 1) = ∑' k : ℕ, (z⁻¹ ^ k) • f (k + 1) := rfl




theorem zTransform_difference_limit {f : ℕ → σ} {z : ℂ}
    (hf : Summable (fun k => (z⁻¹ ^ k) • f k))
    (hf' : Summable (fun k => (z⁻¹ ^ k) • f (k + 1)))
    [IsTopologicalAddGroup σ] [ContinuousConstSMul ℂ σ] [T2Space σ] :
    Filter.Tendsto
      (fun K => ∑ k ∈  Finset.range (K + 1), (z⁻¹ ^ k) • (f (k + 1) - f k))
      Filter.atTop
      (nhds (∑' k, (z⁻¹ ^ k) • f (k + 1) - ∑' k, (z⁻¹ ^ k) • f k)) := by
  have hdiff : Summable (fun k => (z⁻¹ ^ k) • (f (k + 1) - f k)) := by
    simp_rw [smul_sub]
    exact Summable.sub hf' hf
  rw [← Summable.tsum_sub hf' hf]
  have : (fun k => z⁻¹ ^ k • f (k + 1) - z⁻¹ ^ k • f k) =
         (fun k => z⁻¹ ^ k • (f (k + 1) - f k)) := by
    ext k
    rw [smul_sub]
  rw [this]
  simpa [Function.comp] using
    (hdiff.tendsto_sum_tsum_nat).comp (Filter.tendsto_add_atTop_nat 1)

/-- Final Value Theorem (limit form):
    lim_{z→1} (z-1)·F(z) = f₀ + lim_{K→∞} ∑_{k=0}^{K} (f_{k+1} - f_k)
    whenever the partial sums converge. -/
theorem zTransform_final_value_limit {f : ℕ → σ} {L : σ}
    (hconv : Filter.Tendsto
      (fun K => ∑ k ∈ Finset.range (K + 1), (f (k + 1) - f k))
      Filter.atTop
      (nhds L))
    [IsTopologicalAddGroup σ] [ContinuousConstSMul ℂ σ] [T2Space σ] :
    Filter.Tendsto
      (fun K => f 0 + ∑ k ∈ Finset.range (K + 1), (f (k + 1) - f k))
      Filter.atTop
      (nhds (f 0 + L)) := by
  -- The limit of (f₀ + partial sums) is f₀ + L
  exact Filter.Tendsto.const_add (f 0) hconv



/-- At z = 1 the expression z • f 0 + ∑' k, z⁻¹ ^ k • (f (k+1) - f k)
    simplifies to f 0 + ∑' k, (f (k+1) - f k).

    This is the algebraic core of the Final Value Theorem step:
      lim_{z→1}(f₀·z + ∑_k (f_{k+1} - f_k) z⁻ᵏ) = f₀ + ∑_k (f_{k+1} - f_k). -/
theorem zTransform_difference_eval_at_one {f : ℕ → σ}
    [IsTopologicalAddGroup σ] [ContinuousConstSMul ℂ σ] [T2Space σ] :
    (1 : ℂ) • f 0 + ∑' k, ((1 : ℂ)⁻¹ ^ k) • (f (k + 1) - f k) =
    f 0 + ∑' k, (f (k + 1) - f k) := by
  congr 1
  · exact one_smul ℂ (f 0)
  · simp only [inv_one, one_pow, one_smul]


/-- As z → 1, the expression z • f 0 + ∑' k, z⁻¹^k • (f(k+1) - f k)
    tends to f 0 + ∑' k, (f(k+1) - f k).

    This is the analytic (limit) form of the Final Value Theorem step:
      lim_{z→1}(f₀·z + ∑_{k≥0}(f_{k+1}-f_k)z⁻ᵏ) = f₀ + ∑_{k≥0}(f_{k+1}-f_k).

    The hypothesis `hcont` asserts that the z-transform of the difference signal
    is continuous at z = 1 (which follows, e.g., from uniform convergence of
    the power series on a neighbourhood of z = 1). -/
theorem zTransform_difference_tendsto_one {f : ℕ → σ}

    (hcont : Filter.Tendsto
      (fun z : ℂ => ∑' k, (z⁻¹ ^ k) • (f (k + 1) - f k))
      (nhds 1)
      (nhds (∑' k, (f (k + 1) - f k))))
    [IsTopologicalAddGroup σ] [ContinuousSMul ℂ σ] [ContinuousConstSMul ℂ σ] [T2Space σ] :
    Filter.Tendsto
      (fun z : ℂ => z • f 0 + ∑' k, (z⁻¹ ^ k) • (f (k + 1) - f k))
      (nhds 1)
      (nhds (f 0 + ∑' k, (f (k + 1) - f k))) := by
  apply Filter.Tendsto.add
  · -- Part 1: z • f 0 → 1 • f 0 = f 0 as z → 1
    have h : Filter.Tendsto (fun z : ℂ => z • f 0) (nhds 1) (nhds ((1 : ℂ) • f 0)) :=  by
      apply Filter.Tendsto.smul
      · exact Filter.tendsto_id
      · exact tendsto_const_nhds
    rwa [one_smul] at h
  · -- Part 2: the tsum is continuous at z = 1 (by hypothesis)
    exact hcont


/-- Finite telescoping sum: ∑_{k=0}^{K} (f_{k+1} - f_k) = f_{K+1} - f_0 -/
theorem telescoping_sum_finite (f : ℕ → σ) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), (f (k + 1) - f k) = f (K + 1) - f 0 := by
  induction K with
  | zero =>
    simp [Finset.range_one]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    abel

/-- Adding f_0 to the telescoping sum gives f_{K+1}:
    f_0 + ∑_{k=0}^{K} (f_{k+1} - f_k) = f_{K+1} -/
theorem telescoping_sum_with_initial (f : ℕ → σ) (K : ℕ) :
    f 0 + ∑ k ∈ Finset.range (K + 1), (f (k + 1) - f k) = f (K + 1) := by
  rw [telescoping_sum_finite]
  abel

open Filter

theorem limit_of_telescoping_sum {f : ℕ → σ} {L : σ} [ContinuousAdd σ]
    (hconv : Filter.Tendsto (fun K => ∑ k ∈ Finset.range (K + 1),
    (f (k + 1) - f k)) atTop (nhds L)) :
    Filter.Tendsto (fun K => f (K + 1)) atTop (nhds (f 0 + L)) := by
  have h_eq : (fun K => f (K + 1)) =
  (fun K => f 0 + ∑ k ∈ Finset.range (K + 1), (f (k + 1) - f k)) := by
    ext K
    exact (telescoping_sum_with_initial f K).symm
  rw [h_eq]
  exact Filter.Tendsto.const_add (f 0) hconv

theorem final_value_theorem_limit_step {f : ℕ → σ} {L : σ} [ContinuousAdd σ] [T2Space σ]
    (hconv : Filter.Tendsto (fun K => ∑ k ∈ Finset.range (K + 1), (f (k + 1) - f k)) atTop (nhds L))
    (hlim_f : Filter.Tendsto f atTop (nhds L)) :
    f 0 + L = L := by
  have h_sum := telescoping_sum_with_initial f
  have h_tendsto : Filter.Tendsto (fun K =>
  f 0 + ∑ k ∈ Finset.range (K + 1), (f (k + 1) - f k)) atTop (nhds (f 0 + L)) := by
    exact Filter.Tendsto.const_add (f 0) hconv
  have h_eq : (fun K => f 0 + ∑ k ∈ Finset.range (K + 1),
  (f (k + 1) - f k)) = (fun K => f (K + 1)) := by
    ext K
    rw [h_sum]
  rw [h_eq] at h_tendsto
  have h_succ : Filter.Tendsto (fun K => f (K + 1)) atTop (nhds L) := by
    apply Filter.Tendsto.comp
    simpa
    exact Filter.tendsto_add_atTop_nat 1
  exact tendsto_nhds_unique h_tendsto h_succ

/-- Poles of (z-1)F(z) are inside the unit circle: formalized as the existence of
    R > 1 such that ∑ ‖aₖ‖ · Rᵏ converges. This implies absolute and uniform
    convergence of ∑ aₖ z⁻ᵏ on a neighborhood of z = 1. -/
def PolesInsideUnitCircle (a : ℕ → σ) : Prop :=
  ∃ R : ℝ, 1 < R ∧ Summable (fun k => ‖a k‖ * R ^ k)


theorem zTransform_continuousAt_one {a : ℕ → σ}
    (hpoles : PolesInsideUnitCircle a)
    [IsTopologicalAddGroup σ] [ContinuousConstSMul ℂ σ] [T2Space σ] [ContinuousSMul ℂ σ]  [ContinuousInv ℂ]
    [CompleteSpace σ] :
    Filter.Tendsto
      (fun z : ℂ => ∑' k, (z⁻¹ ^ k) • a k)
      (nhds 1)
      (nhds (∑' k, a k)) := by
  -- Extract R > 1 and the summability bound
  obtain ⟨R, hR1, hRsum⟩ := hpoles
  -- Pick r with 1 < r < R, and work on the closed ball B = Metric.closedBall 1 ε
  -- where ε = 1 - 1/R, so that z ∈ B implies |z| ≥ 1/R, hence |z⁻¹| ≤ R
  set ε := 1 - R⁻¹ with hε_def
  have hR_pos : (0 : ℝ) < R := by linarith
  have hRinv_lt_one : R⁻¹ < 1 := by
    exact inv_lt_one_of_one_lt₀ hR1
  have hε_pos : 0 < ε := by simp [hε_def]; linarith
  -- Define the set S = Metric.closedBall 1 (ε/2) (an open neighborhood of 1 is enough)
  -- Actually, let's use an open ball for continuity purposes
  set S := Metric.ball (1 : ℂ) (ε / 2)
  -- Key bound: for z ∈ S, ‖z⁻¹‖ ≤ R
  have hz_bound : ∀ z ∈ S, ‖z⁻¹‖ ≤ R := by
    intro z hz
    simp only [Metric.mem_ball, S] at hz
    -- |z - 1| < ε/2, so |z| > 1 - ε/2 = 1 - (1 - R⁻¹)/2 = (1 + R⁻¹)/2 > R⁻¹
    -- Therefore |z⁻¹| < 1/R⁻¹ = R... but this needs care
    rw [norm_inv]

    have h_dist : ‖z - 1‖ < ε / 2 := by rwa [Complex.dist_eq] at hz
    have h_Rinv_pos : (0 : ℝ) < R⁻¹ := inv_pos.mpr hR_pos
    have h_norm_lower : R⁻¹ < ‖z‖ := by
      have h_tri := norm_sub_norm_le (1 : ℂ) z
      rw [norm_one, norm_sub_rev] at h_tri
      linarith
    have h_inv : ‖z‖⁻¹ < (R⁻¹)⁻¹ := by
     -- inv_lt_inv_of_lt h_Rinv_pos h_norm_lower
     exact inv_strictAnti₀ h_Rinv_pos h_norm_lower
    rw [inv_inv] at h_inv
    linarith

  -- Define summands as functions of z
  let F : ℕ → ℂ → σ := fun k z => (z⁻¹ ^ k) • a k
  -- Each F k is continuous (it's a power of z⁻¹ times a constant)
  have hF_cont : ∀ k, ContinuousOn (F k) S := by
    intro k
    apply ContinuousOn.smul
    · exact (continuous_inv.pow k).continuousOn
    · exact continuousOn_const
  -- Norm bound: for z ∈ S, ‖F k z‖ ≤ ‖a k‖ * R ^ k
  have hF_bound : ∀ k, ∀ z ∈ S, ‖F k z‖ ≤ ‖a k‖ * R ^ k := by
    intro k z hz
    simp only [F, norm_smul, norm_pow]
    nth_rewrite 2 [mul_comm]
    apply mul_le_mul_of_nonneg_right
    specialize hz_bound z hz
    · refine pow_le_pow_left₀ ?_ hz_bound k
      simp


    · simp



  have hUnif : HasSumUniformlyOn F (fun z => ∑' k, F k z) S :=
    HasSumUniformlyOn.of_norm_le_summable hRsum hF_bound

  have hContOn : ContinuousOn (fun z => ∑' k, F k z) S := by
      apply hUnif.tendstoUniformlyOn.continuousOn
      exact Filter.Frequently.of_forall
        fun s => continuousOn_finset_sum s fun k _ => hF_cont k

  have h_at_one : (fun z => ∑' k, F k z) 1 = ∑' k, a k := by
    simp [F, inv_one, one_pow, one_smul]

  have h1S : (1 : ℂ) ∈ S := Metric.mem_ball_self (by linarith)
  have hContAt := ContinuousOn.continuousAt hContOn (Metric.isOpen_ball.mem_nhds h1S)
  have h_at_one : (fun z => ∑' k, F k z) 1 = ∑' k, a k := by
    simp [F, inv_one, one_pow, one_smul]
  simp only [ContinuousAt, F] at hContAt
  simp only [inv_one, one_pow, one_smul] at hContAt
  exact hContAt



/-- If the poles of (z-1)F(z) are inside the unit circle, then the z-transform of
    the difference signal f(k+1) - f(k) is continuous at z = 1. -/
theorem difference_zTransform_continuousAt_one (f : SampledSignal σ)
    (hpoles : PolesInsideUnitCircle (fun k => f.signal (k + 1) - f.signal k))

    [IsTopologicalAddGroup σ] [ContinuousConstSMul ℂ σ] [T2Space σ]
    [ContinuousSMul ℂ σ] [ContinuousInv ℂ] [CompleteSpace σ]:
    Filter.Tendsto
      (fun z : ℂ => ∑' k, (z⁻¹ ^ k) • (f.signal (k + 1) - f.signal k))
      (nhds 1)
      (nhds (∑' k, (f.signal (k + 1) - f.signal k)))
      :=
  zTransform_continuousAt_one hpoles

theorem final_value_theorem (f : SampledSignal σ) (L : σ)
    [IsTopologicalAddGroup σ] [ContinuousConstSMul ℂ σ]
    [ContinuousAdd σ] [T2Space σ] [ContinuousSMul ℂ σ] [CompleteSpace σ]
    [ContinuousInv ℂ]
    (hpoles : PolesInsideUnitCircle (fun k => f.signal (k + 1) - f.signal k))
    (hconv : ∀ z : ℂ, z ≠ 0 → Summable (fun k => (z⁻¹ ^ k) • f.signal k)) :
    Filter.Tendsto f.signal atTop (nhds L) ↔
    Filter.Tendsto (fun z : ℂ => (z - 1) • Z{f} z) (nhds 1) (nhds L) := by
  simp only [zTransformSampled]

  have h_step1 :
      ∀ z : ℂ,
        z ≠ 0 →
        Summable (fun k => (z⁻¹ ^ k) • f.signal k) →
        (z - 1) • (∑' k, (z⁻¹ ^ k) • f.signal k)
          =
        z • (∑' k, (z⁻¹ ^ k) • f.signal k) -
          (∑' k, (z⁻¹ ^ k) • f.signal k) :=  by
          intros z hz hsummable
          rw [sub_smul]
          simp


  have h_step2 :
      ∀ z : ℂ,
        z ≠ 0 →
        Summable (fun k => (z⁻¹ ^ k) • f.signal k) →
        z • (∑' k, (z⁻¹ ^ k) • f.signal k)
          =
        z • f.signal 0 + ∑' k, (z⁻¹ ^ k) • f.signal (k + 1) := by
      intros z hz hsummable
      rw [Summable.tsum_eq_zero_add]
      simp
      rw [<- tsum_const_smul'']
      congr 1
      ext k
      rw [smul_smul]
      congr 1

      rw [pow_succ, mul_comm z]
      simp
      nth_rewrite 2 [mul_comm]
      nth_rewrite 1 [mul_assoc]
      have : (z⁻¹) * z = 1 := by field_simp
      rw [this]
      simp
      exact hsummable





  have h_step3 :
      ∀ z : ℂ,
        z ≠ 0 →
        Summable (fun k => (z⁻¹ ^ k) • f.signal k) →
        (z - 1) • (∑' k, (z⁻¹ ^ k) • f.signal k)
          =
        (z • f.signal 0 + ∑' k, (z⁻¹ ^ k) • f.signal (k + 1)) -
          (∑' k, (z⁻¹ ^ k) • f.signal k) := by
      intros z hz hsummable
      rw [sub_smul]
      rw [h_step2 z hz hsummable]
      congr 1
      simp


  have h_step4 :
      ∀ z : ℂ,
        z ≠ 0 →
        Summable (fun k => (z⁻¹ ^ k) • f.signal k) →
        Summable (fun k => (z⁻¹ ^ k) • f.signal (k + 1)) →
        (z • f.signal 0 + ∑' k, (z⁻¹ ^ k) • f.signal (k + 1)) -
          (∑' k, (z⁻¹ ^ k) • f.signal k)
          =
        z • f.signal 0 + ∑' k, (z⁻¹ ^ k) • (f.signal (k + 1) - f.signal k) := by
      intros z hz hsummable hsummable'


      abel_nf
      congr 1
      have : ∑' (k : ℕ),
      z⁻¹ ^ k • f.signal (k + 1) + -1 • ∑' (k : ℕ), z⁻¹ ^ k • f.signal k = ∑' (k : ℕ), z⁻¹ ^ k • f.signal (k + 1) -  ∑' (k : ℕ), z⁻¹ ^ k • f.signal k := by
        abel

      rw [this]
      rw [← Summable.tsum_sub hsummable' hsummable]
      congr 1
      ext k
      rw [<-smul_sub]
      congr 1
      simp
      have : k+1 = 1+k := by
        linarith
      rw [this]
      abel




  have h_step5 :
      (∀ z : ℂ, z ≠ 0 → Summable (fun k => (z⁻¹ ^ k) • f.signal k)) →
      (∀ z : ℂ, z ≠ 0 → Summable (fun k => (z⁻¹ ^ k) • f.signal (k + 1))) →
      (Filter.Tendsto
        (fun z : ℂ => (z - 1) • ∑' k, (z⁻¹ ^ k) • f.signal k)
        (nhds 1) (nhds L)
      ↔
      Filter.Tendsto
        (fun z : ℂ =>
          z • f.signal 0 + ∑' k, (z⁻¹ ^ k) • (f.signal (k + 1) - f.signal k))
        (nhds 1) (nhds L)) := by
    intro hsumm hsumm'  -- First introduce the two hypotheses
    have h_eq : ∀ᶠ (z : ℂ) in nhds (1 : ℂ),
      (z - 1) • ∑' k, (z⁻¹ ^ k) • f.signal k =
      z • f.signal 0 + ∑' k, (z⁻¹ ^ k) • (f.signal (k + 1) - f.signal k) := by
      filter_upwards [isOpen_ne.mem_nhds (one_ne_zero)] with z hz
      rw [h_step3 z hz (hsumm z hz), h_step4 z hz (hsumm z hz) (hsumm' z hz)]

    constructor
    · intro h
      rwa [Filter.tendsto_congr' h_eq] at h


    · intro h
      rwa [<-Filter.tendsto_congr' h_eq] at h





  have h_step6 :
      Filter.Tendsto
        (fun z : ℂ =>
          z • f.signal 0 + ∑' k, (z⁻¹ ^ k) • (f.signal (k + 1) - f.signal k))
        (nhds 1)
        (nhds (f.signal 0 + ∑' k, (f.signal (k + 1) - f.signal k))) := by
    apply Filter.Tendsto.add
    · -- z • f.signal 0 → 1 • f.signal 0 = f.signal 0 as z → 1
      have h : Filter.Tendsto (fun z : ℂ => z • f.signal 0) (nhds 1)
          (nhds ((1 : ℂ) • f.signal 0)) :=
        Filter.Tendsto.smul tendsto_id tendsto_const_nhds
      rwa [one_smul] at h
    · -- Continuity of the tsum at z = 1, from the poles condition
      exact difference_zTransform_continuousAt_one f hpoles

  have h_step7 :
      Filter.Tendsto
        (fun K => ∑ k ∈ Finset.range (K + 1), (f.signal (k + 1) - f.signal k))
        Filter.atTop
        (nhds (∑' k, (f.signal (k + 1) - f.signal k))) := by
    -- Extract R > 1 and summability bound from hpoles
    obtain ⟨R, hR1, hRsum⟩ := hpoles
    -- ‖aₖ‖ ≤ ‖aₖ‖ * R^k since R^k ≥ 1, so summability follows

    have hdiff_summable : Summable (fun k => f.signal (k + 1) - f.signal k) := by
      have h_bound : ∀ k, ‖f.signal (k + 1) - f.signal k‖ ≤
          ‖f.signal (k + 1) - f.signal k‖ * R ^ k := by
        intro k
        have hRk : (1 : ℝ) ≤ R ^ k := by
          induction k with
          | zero => simp
          | succ n ih =>
            calc (1 : ℝ) ≤ 1 * R := by linarith
              _ ≤ R ^ n * R := by nlinarith
              _ = R ^ (n + 1) := (pow_succ R n).symm
        nlinarith [norm_nonneg (f.signal (k + 1) - f.signal k)]
      have h_summ : Summable (fun k => ‖f.signal (k + 1) - f.signal k‖ * R ^ k) := by
        convert hRsum using  1
      convert Summable.of_norm_bounded h_summ h_bound

    simpa [Function.comp] using
      hdiff_summable.tendsto_sum_tsum_nat.comp (Filter.tendsto_add_atTop_nat 1)


  have h_step8 :
      ∀ K : ℕ,
        f.signal 0 + ∑ k ∈ Finset.range (K + 1), (f.signal (k + 1) - f.signal k)
          =
        f.signal (K + 1) := by
      intro K
      have telescoping_sum_finite : ∑ k ∈ Finset.range (K + 1),
      (f.signal (k + 1) - f.signal k) = f.signal (K + 1) - f.signal 0 := by
        induction K with
        | zero =>
          simp [Finset.range_one]
        | succ K ih =>
          rw [Finset.sum_range_succ, ih]
          abel
      rw [telescoping_sum_finite]
      abel






  have h_step9 :
      Filter.Tendsto
        (fun K => f.signal (K + 1))
        Filter.atTop
        (nhds (f.signal 0 + ∑' k, (f.signal (k + 1) - f.signal k))) := by
    have h_eq : (fun K => f.signal (K + 1)) =
        (fun K => f.signal 0 + ∑ k ∈ Finset.range (K + 1), (f.signal (k + 1) - f.signal k)) := by
      ext K
      exact (h_step8 K).symm
    rw [h_eq]
    exact Filter.Tendsto.const_add (f.signal 0) h_step7

  have h_step10 :
      ∀ L' : σ,
        Filter.Tendsto f.signal atTop (nhds L') →
        Filter.Tendsto (fun K => f.signal (K + 1)) atTop (nhds L') := by
    intro L' hlim
    exact hlim.comp (Filter.tendsto_add_atTop_nat 1)

  have h_step11 :
      Filter.Tendsto f.signal atTop (nhds L) →
      f.signal 0 + ∑' k, (f.signal (k + 1) - f.signal k) = L := by
    intro hlim
    have hshift := h_step10 L hlim
    exact tendsto_nhds_unique h_step9 hshift

  have h_step12 :
      Filter.Tendsto
        (fun z : ℂ =>
          z • f.signal 0 + ∑' k, (z⁻¹ ^ k) • (f.signal (k + 1) - f.signal k))
        (nhds 1) (nhds L)
      ↔
      f.signal 0 + ∑' k, (f.signal (k + 1) - f.signal k) = L := by
    constructor
    · intro h
      exact tendsto_nhds_unique h_step6 h
    · intro h
      rw [← h]
      exact h_step6

  constructor
  · -- Forward: f.signal → L  ⟹  (z-1)·F(z) → L
    intro hlim
    -- Step 1: get the algebraic equality from convergence of f
    have h_eqL : f.signal 0 + ∑' k, (f.signal (k + 1) - f.signal k) = L :=
      h_step11 hlim
    -- Step 2: the middle expression tends to L  (by h_step12)
    have h_mid : Filter.Tendsto
        (fun z : ℂ => z • f.signal 0 + ∑' k, (z⁻¹ ^ k) • (f.signal (k + 1) - f.signal k))
        (nhds 1) (nhds L) :=
      h_step12.mpr h_eqL
    -- Step 3: Need summability to use h_step5
    have hsumm : ∀ z : ℂ, z ≠ 0 → Summable (fun k => (z⁻¹ ^ k) • f.signal k) := hconv
    have hsumm' : ∀ z : ℂ, z ≠ 0 → Summable (fun k => (z⁻¹ ^ k) • f.signal (k + 1)) := by
      intro z hz
      have h := hconv z hz
      -- From Summable (k ↦ z⁻¹^k • f k), get Summable (k ↦ z⁻¹^(k+1) • f (k+1))
      rw [<-summable_nat_add_iff 1] at h
      -- Rewrite z⁻¹^(k+1) = z⁻¹ * z⁻¹^k, so we have Summable (k ↦ z⁻¹ • (z⁻¹^k • f (k+1)))
      simp_rw [pow_succ', mul_smul] at h
      -- Multiply by z to cancel the z⁻¹: z • z⁻¹ • x = x
      have h2 := h.const_smul z
      convert h2 using 1
      ext k
      abel_nf
      -- nth_rewrite 1 [mul_assoc]
      rw [smul_smul, smul_smul, mul_inv_cancel₀ hz]
      simp only [inv_pow, one_mul]

    -- Step 4: Convert back to (z-1)F(z) form
    exact (h_step5 hsumm hsumm').mpr h_mid

  · -- Backward: (z-1)·F(z) → L  ⟹  f.signal → L
      intro hlim
      -- Step 0: Need summability to use h_step5
      have hsumm : ∀ z : ℂ, z ≠ 0 → Summable (fun k => (z⁻¹ ^ k) • f.signal k) := hconv
      have hsumm' : ∀ z : ℂ, z ≠ 0 → Summable (fun k => (z⁻¹ ^ k) • f.signal (k + 1)) := by
        intro z hz
        have h := hconv z hz
        -- From Summable (k ↦ z⁻¹^k • f k), get Summable (k ↦ z⁻¹^(k+1) • f (k+1))
        rw [<-summable_nat_add_iff 1] at h
        -- Rewrite z⁻¹^(k+1) = z⁻¹ * z⁻¹^k, so we have Summable (k ↦ z⁻¹ • (z⁻¹^k • f (k+1)))
        simp_rw [pow_succ', mul_smul] at h
        -- Multiply by z to cancel the z⁻¹: z • z⁻¹ • x = x
        have h2 := h.const_smul z
        convert h2 using 1
        ext k
        abel_nf
        -- nth_rewrite 1 [mul_assoc]
        rw [smul_smul, smul_smul, mul_inv_cancel₀ hz]
        simp only [inv_pow, one_mul]
      -- Step 1: Convert hlim from (z-1)F(z) form to z·f₀ + ∑... form using h_step5
      have h_mid : Filter.Tendsto
          (fun z : ℂ => z • f.signal 0 + ∑' k, (z⁻¹ ^ k) • (f.signal (k + 1) - f.signal k))
          (nhds 1) (nhds L) :=
        (h_step5 hsumm hsumm').mp hlim
      -- Step 2: by uniqueness of limits
      have h_eq_lim : f.signal 0 + ∑' k, (f.signal (k + 1) - f.signal k) = L :=
        tendsto_nhds_unique h_step6 h_mid
      -- Step 3: f(K+1) → f.signal 0 + ∑' k, ...  (by h_step9)
      --         and that equals L
      have h_shift : Filter.Tendsto (fun K => f.signal (K + 1)) Filter.atTop (nhds L) := by
        rw [← h_eq_lim]
        exact h_step9
      -- Step 4: f(K+1) → L implies f → L  (shift the index back)
      rwa [Filter.tendsto_add_atTop_iff_nat 1] at h_shift





end DiscreteLinearSystem
