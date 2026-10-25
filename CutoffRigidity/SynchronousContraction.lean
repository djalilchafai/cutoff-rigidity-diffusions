module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic

/-!
# The pathwise contraction calculation for synchronous coupling

The upper bound in Theorem `th:maineucl` uses Wasserstein contraction under
positive curvature. This file proves the deterministic contraction of the
actual difference path after the common driving noise has cancelled.

The scalar estimate is proved with an exponential integrating factor and the
mean value theorem. The vector estimate differentiates the actual squared
norm. The final theorem applies it to the actual potential gradient.

Constructing the coupled diffusion, deriving gradient monotonicity from
curvature, and passing from pathwise contraction to Wasserstein contraction
remain separate obligations.
-/

public section

namespace CutoffRigidity

open Set

/-- The signed scalar Grönwall estimate, proved by an integrating factor.
Only continuity at the interval endpoints and differentiability inside are
required, so this also applies to forward-time diffusion difference paths. -/
theorem exponential_decay_of_deriv_le {f f' : ℝ → ℝ} {rate t : ℝ}
    (ht : 0 ≤ t) (hcont : ContinuousOn f (Icc 0 t))
    (hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt f (f' s) s)
    (hineq : ∀ s ∈ Ioo 0 t, f' s ≤ -rate * f s) :
    f t ≤ Real.exp (-rate * t) * f 0 := by
  let F : ℝ → ℝ := fun s => Real.exp (rate * s) * f s
  have hFd (s : ℝ) (hs : s ∈ Ioo 0 t) :
      HasDerivAt F (rate * Real.exp (rate * s) * f s + Real.exp (rate * s) * f' s) s := by
    have he : HasDerivAt (fun u => Real.exp (rate * u))
        (rate * Real.exp (rate * s)) s := by
      simpa [mul_comm] using ((hasDerivAt_id s).const_mul rate).exp
    exact he.mul (hderiv s hs)
  have hFcont : ContinuousOn F (Icc 0 t) := by
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hcont
  have hanti : AntitoneOn F (Icc 0 t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t) hFcont
    · intro s hs
      have hs' : s ∈ Ioo 0 t := by simpa only [interior_Icc] using hs
      exact (hFd s hs').differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Ioo 0 t := by simpa only [interior_Icc] using hs
      rw [(hFd s hs').deriv]
      have h := mul_le_mul_of_nonneg_left (hineq s hs') (Real.exp_nonneg (rate * s))
      nlinarith
  have hbound : Real.exp (rate * t) * f t ≤ f 0 := by
    have h := hanti (show (0 : ℝ) ∈ Icc 0 t by exact ⟨le_rfl, ht⟩)
      (show t ∈ Icc 0 t by exact ⟨ht, le_rfl⟩) ht
    simpa only [F, mul_zero, Real.exp_zero, one_mul] using h
  calc
    f t = Real.exp (-rate * t) * (Real.exp (rate * t) * f t) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp only [neg_mul, neg_add_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (-rate * t) * f 0 :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg _)

/-- A dissipative derivative contracts the squared norm exponentially. -/
theorem norm_sq_contraction_of_dissipative_derivative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Z Z' : ℝ → E} {rate t : ℝ} (ht : 0 ≤ t)
    (hcont : ContinuousOn Z (Icc 0 t))
    (hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt Z (Z' s) s)
    (hdiss : ∀ s ∈ Ioo 0 t, inner ℝ (Z s) (Z' s) ≤ -rate * ‖Z s‖ ^ 2) :
    ‖Z t‖ ^ 2 ≤ Real.exp (-2 * rate * t) * ‖Z 0‖ ^ 2 := by
  have h := exponential_decay_of_deriv_le (f := fun s => ‖Z s‖ ^ 2)
    (f' := fun s => 2 * inner ℝ (Z s) (Z' s)) (rate := 2 * rate) ht
    (hcont.norm.pow 2) (fun s hs => (hderiv s hs).norm_sq) (fun s hs => by
      have h := hdiss s hs
      nlinarith)
  simpa only [neg_mul] using h

/-- Taking square roots gives the corresponding norm contraction. -/
theorem norm_contraction_of_dissipative_derivative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Z Z' : ℝ → E} {rate t : ℝ} (ht : 0 ≤ t)
    (hcont : ContinuousOn Z (Icc 0 t))
    (hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt Z (Z' s) s)
    (hdiss : ∀ s ∈ Ioo 0 t, inner ℝ (Z s) (Z' s) ≤ -rate * ‖Z s‖ ^ 2) :
    ‖Z t‖ ≤ Real.exp (-rate * t) * ‖Z 0‖ := by
  have h := norm_sq_contraction_of_dissipative_derivative ht hcont hderiv hdiss
  have hexp : Real.exp (-2 * rate * t) = Real.exp (-rate * t) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp] at h
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow] using h

/-- Synchronous coupling removes the common noise. The remaining difference
path contracts when the actual potential gradient is strongly monotone. -/
theorem synchronous_difference_norm_sq_contraction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (V : E → ℝ) (X Y : ℝ → E) {rate t : ℝ} (ht : 0 ≤ t)
    (hcont : ContinuousOn (fun s => X s - Y s) (Icc 0 t))
    (hderiv : ∀ s ∈ Ioo 0 t,
      HasDerivAt (fun u => X u - Y u) (-gradient V (X s) + gradient V (Y s)) s)
    (hmono : ∀ x y : E, rate * ‖x - y‖ ^ 2 ≤
      inner ℝ (gradient V x - gradient V y) (x - y)) :
    ‖X t - Y t‖ ^ 2 ≤ Real.exp (-2 * rate * t) * ‖X 0 - Y 0‖ ^ 2 := by
  apply norm_sq_contraction_of_dissipative_derivative ht hcont hderiv
  intro s hs
  have h := hmono (X s) (Y s)
  rw [inner_sub_left] at h
  rw [inner_add_right, inner_neg_right, real_inner_comm (gradient V (X s)) (X s - Y s),
    real_inner_comm (gradient V (Y s)) (X s - Y s)]
  linarith

/-- The pathwise distance contraction used by synchronous coupling. -/
theorem synchronous_difference_norm_contraction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (V : E → ℝ) (X Y : ℝ → E) {rate t : ℝ} (ht : 0 ≤ t)
    (hcont : ContinuousOn (fun s => X s - Y s) (Icc 0 t))
    (hderiv : ∀ s ∈ Ioo 0 t,
      HasDerivAt (fun u => X u - Y u) (-gradient V (X s) + gradient V (Y s)) s)
    (hmono : ∀ x y : E, rate * ‖x - y‖ ^ 2 ≤
      inner ℝ (gradient V x - gradient V y) (x - y)) :
    ‖X t - Y t‖ ≤ Real.exp (-rate * t) * ‖X 0 - Y 0‖ := by
  apply norm_contraction_of_dissipative_derivative ht hcont hderiv
  intro s hs
  have h := hmono (X s) (Y s)
  rw [inner_sub_left] at h
  rw [inner_add_right, inner_neg_right, real_inner_comm (gradient V (X s)) (X s - Y s),
    real_inner_comm (gradient V (Y s)) (X s - Y s)]
  linarith

end CutoffRigidity
