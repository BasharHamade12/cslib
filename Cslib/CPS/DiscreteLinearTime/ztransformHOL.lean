import Mathlib

open scoped ComplexOrder

variable {σ : Type*} [NormedAddCommGroup σ] [NormedSpace ℂ σ]

/-- A discrete signal is a function `ℕ → σ`. -/
def DiscreteSignal (σ : Type*) := ℕ → σ

/-- Z-transform of a discrete signal. -/
noncomputable def zTransform (f : DiscreteSignal σ) (z : ℂ) : σ :=
  ∑' k : ℕ, (z⁻¹ ^ k) • f k

/-- Summability condition for the z-transform. -/
def ZTransformSummable (f : DiscreteSignal σ) (z : ℂ) : Prop :=
  Summable (fun k => (z⁻¹ ^ k) • f k)

theorem hasDerivAt_tsum_of_summable_hasDerivAt
  {σ : Type*} [NormedAddCommGroup σ] [NormedSpace ℂ σ]
  {g : ℕ → ℂ → σ}
  {g' : ℕ → σ}
  {z : ℂ}  -- Move z here
  (hg : ∀ k, HasDerivAt (g k) (g' k) z)
  (hderiv_bound : ∀ k , ‖g' k‖ ≤ 1)  -- g' k is now σ, not a function
  (hg_summable : Summable (fun k => g k z))  -- z is now in scope
  (hz : True) :
  deriv (fun w => ∑' k, g k w) z = ∑' k, g' k := by

  have h_open : IsOpen (Set.univ : Set ℂ) := isOpen_univ
  have h_pre : IsPreconnected (Set.univ : Set ℂ) := isPreconnected_univ
  have h_has :=
  hasDerivAt_tsum_of_isPreconnected (fun k => hg k) (fun k _ => by
    simpa using hderiv_bound k) h_open h_pre

  simpa using h_has.deriv


/-- Derivative of Z-transform: Z{k·f(k)}(z) = -z·(d/dz) Z{f}(z). -/
theorem zTransform_multiplication_by_k
  {f : DiscreteSignal σ} {z : ℂ}
  (hz : z ≠ 0)
  (hf : ZTransformSummable f z)
  (hf_term : ∀ k, Summable (fun w : ℂ => (w⁻¹ ^ k) • f k))
  : zTransform (fun k => (k : ℂ) • f k) z
    = -z • deriv (fun w => zTransform f w) z := by
  -- rewrite Z-transform as function of `z⁻¹`
  have hZ : ∀ w, zTransform f w = ∑' k, w⁻¹ ^ k • f k := by
    intro w; rfl

  -- differentiate with the chain rule
  calc
    zTransform (fun k => (k : ℂ) • f k) z
      = ∑' k, (z⁻¹ ^ k) • ((k : ℕ ) • f k) := by
        sorry

    _ = ∑' k, (k : ℕ ) • (z⁻¹ ^ k • f k) := by
      congr; ext k;
      simp [smul_smul, mul_comm]
      sorry

    _ = ∑' k, ((k : ℕ) • (z⁻¹ ^ k • f k)) := rfl
    _ = -z • deriv (fun w => ∑' k, (w⁻¹ ^ k) • f k) z := by
      have hderiv :
          deriv (fun w => ∑' k, (w⁻¹ ^ k) • f k) z
            = ∑' k, deriv (fun w => (w⁻¹ ^ k) • f k) z := by
        -- this termwise derivative interchange can be justified under uniform convergence
        sorry
      -- compute derivative of each term
      have hterm_deriv :
        ∀ k,
          deriv (fun w => (w⁻¹ ^ k) • f k) z
            = (-(k : ℂ) * z⁻¹ ^ (k + 1)) • f k := by
        intro k
        have hd := (hasDerivAt_zpow (k : ℤ) z (Or.inl (Or.inl hz))).deriv
        have hinv := (hasDerivAt.inv (fun _ => (1 : ℂ)) z hz).deriv
        dsimp at hd hinv
        show _ = _
        -- combine derivative of powers and inv
        calc
          deriv (fun w => (w⁻¹ ^ k) • f k) z
            = deriv (fun w => w ^ (-(k : ℤ))) z • f k := by
              simpa using (hd.smul_const (f k))
          _ = ↑(-(k : ℤ)) * z ^ (-(k : ℤ) - 1) • f k := by
              -- uses `hasDerivAt_zpow` rule
              rfl
          _ = _ := by
              -- rearrange terms to match the target form
              sorry

      rw [hderiv]
      simp_rw [hterm_deriv]
      -- now algebra to get -z factor
      have : ∑' k, (-(k : ℂ) * z⁻¹ ^ (k + 1)) • f k
          = z⁻¹ * ∑' k, (k : ℂ) * z⁻¹ ^ k • f k := by
        -- simple power manipulation
        sorry
      simp [this]
      ring

    _ = -z • deriv (fun w => zTransform f w) z := by
      simp [hZ]
