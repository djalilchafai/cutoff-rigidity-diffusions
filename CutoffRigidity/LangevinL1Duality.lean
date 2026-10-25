module
public import CutoffRigidity.InvariantKernelL1
public import CutoffRigidity.LangevinL2Operator

/-! # Actual reversible density duality on the genuine L¹ domain

True L² symmetry is first tested on bounded inputs. Actual nonnegative
L¹ inputs are truncated; genuine dominated convergence on both sides then
extends that symmetry without a supplied detailed-balance premise.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem langevinKernel_integral_mul_comm_bounded
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {f g : E → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) (hgb : ∃ N : ℝ, ∀ x, ‖g x‖ ≤ N) (t : ℝ≥0) :
    (∫ x, f x * (∫ y, g y ∂langevinKernel V B P t x) ∂gibbsMeasure volume V) =
      ∫ x, (∫ y, f y ∂langevinKernel V B P t x) * g x ∂gibbsMeasure volume V := by
  let := hp
  let μ := gibbsMeasure volume V
  let K := langevinKernel V B P t
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  have hInv : K ∘ₘ μ = μ := langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess t
  obtain ⟨M, hM⟩ := hfb
  obtain ⟨N, hN⟩ := hgb
  have hfLp : MemLp f 2 μ := MemLp.of_bound hf.aestronglyMeasurable M (Eventually.of_forall hM)
  have hgLp : MemLp g 2 μ := MemLp.of_bound hg.aestronglyMeasurable N (Eventually.of_forall hN)
  have hKF := (langevinL2Operator_coeFn hB hV hp ρ hρ hHess t (hfLp.toLp f)).trans
    (invariantKernel_integral_congr_ae K hInv hfLp.coeFn_toLp)
  have hKG := (langevinL2Operator_coeFn hB hV hp ρ hρ hHess t (hgLp.toLp g)).trans
    (invariantKernel_integral_congr_ae K hInv hgLp.coeFn_toLp)
  have hs := langevinL2Operator_symmetric hB hV hp ρ hρ hHess t (hfLp.toLp f) (hgLp.toLp g)
  have hl : inner ℝ (langevinL2Operator hB hV hp ρ hρ hHess t (hfLp.toLp f)) (hgLp.toLp g) =
      ∫ x, (∫ y, f y ∂K x) * g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hKF, hgLp.coeFn_toLp] with x hx hy
    rw [hx, hy, Real.inner_apply]
  have hr : inner ℝ (hfLp.toLp f) (langevinL2Operator hB hV hp ρ hρ hHess t (hgLp.toLp g)) =
      ∫ x, f x * (∫ y, g y ∂K x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hfLp.coeFn_toLp, hKG] with x hx hy
    rw [hx, hy, Real.inner_apply]
  rw [hl, hr] at hs
  exact hs.symm

/-- Genuine bounded-test symmetry for every actual nonnegative integrable
density, obtained by truncation of the actual L² identity. -/
theorem langevinKernel_integral_mul_comm_integrable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {f g : E → ℝ} (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x)
    (hfI : Integrable f (gibbsMeasure volume V))
    (hg : Measurable g) (hgb : ∃ N : ℝ, ∀ x, ‖g x‖ ≤ N) (t : ℝ≥0) :
    (∫ x, f x * (∫ y, g y ∂langevinKernel V B P t x) ∂gibbsMeasure volume V) =
      ∫ x, (∫ y, f y ∂langevinKernel V B P t x) * g x ∂gibbsMeasure volume V := by
  let := hp
  let μ := gibbsMeasure volume V
  let K := langevinKernel V B P t
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  have hInv : K ∘ₘ μ = μ := langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess t
  obtain ⟨N, hN⟩ := hgb
  let fn := fun (n : ℕ) (x : E) => min (f x) (n : ℝ)
  have hfnm (n : ℕ) : Measurable (fn n) := hf.min measurable_const
  have hfn0 (n : ℕ) (x : E) : 0 ≤ fn n x := le_min (hfn x) (Nat.cast_nonneg n)
  have hfnle (n : ℕ) (x : E) : fn n x ≤ f x := min_le_left _ _
  have hfnb (n : ℕ) (x : E) : ‖fn n x‖ ≤ n := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hfn0 n x)]
    exact min_le_right _ _
  have hfnI (n : ℕ) (η : Measure E) [IsProbabilityMeasure η] : Integrable (fn n) η :=
    (integrable_const (n : ℝ)).mono' (hfnm n).aestronglyMeasurable (Eventually.of_forall (hfnb n))
  have hfnlim (x : E) : Tendsto (fun n => fn n x) atTop (𝓝 (f x)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (f x))] with n hn
    exact (min_eq_left hn).symm
  have hKgB (x : E) : ‖∫ y, g y ∂K x‖ ≤ N := by
    simpa using norm_integral_le_of_norm_le_const (μ := K x) (Eventually.of_forall hN)
  have hLeft : Tendsto (fun n => ∫ x, fn n x * (∫ y, g y ∂K x) ∂μ) atTop
      (𝓝 (∫ x, f x * (∫ y, g y ∂K x) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => f x * N)
      (fun n => ((hfnm n).mul hg.stronglyMeasurable.integral_kernel.measurable).aestronglyMeasurable)
      (hfI.mul_const N) ?_ ?_
    · intro n
      apply Eventually.of_forall
      intro x
      rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs (fn n x), abs_of_nonneg (hfn0 n x)]
      exact mul_le_mul (hfnle n x) (hKgB x) (norm_nonneg _) (hfn x)
    · exact Eventually.of_forall (fun x => (hfnlim x).mul_const _)
  have hKfI := invariantKernel_integral_integrable K hInv hf hfI
  have hRight : Tendsto (fun n => ∫ x, (∫ y, fn n y ∂K x) * g x ∂μ) atTop
      (𝓝 (∫ x, (∫ y, f y ∂K x) * g x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => (∫ y, f y ∂K x) * N)
      (fun n => ((hfnm n).stronglyMeasurable.integral_kernel.measurable.mul hg).aestronglyMeasurable)
      (hKfI.mul_const N) ?_ ?_
    · intro n
      filter_upwards [invariantKernel_integrable_ae K hInv hfI] with x hfx
      have hle := integral_mono (hfnI n (K x)) hfx (hfnle n)
      rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (hfn0 n))]
      exact mul_le_mul hle (hN x) (norm_nonneg _) (integral_nonneg hfn)
    · filter_upwards [invariantKernel_integrable_ae K hInv hfI] with x hfx
      have hLocal : Tendsto (fun n => ∫ y, fn n y ∂K x) atTop (𝓝 (∫ y, f y ∂K x)) := by
        apply tendsto_integral_of_dominated_convergence f
          (fun n => (hfnm n).aestronglyMeasurable) hfx ?_ (Eventually.of_forall hfnlim)
        intro n
        exact Eventually.of_forall (fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hfn0 n y)]; exact hfnle n y)
      exact hLocal.mul_const (g x)
  have hBounded (n : ℕ) := langevinKernel_integral_mul_comm_bounded hB hV hp ρ hρ hHess
    (hfnm n) hg ⟨n, hfnb n⟩ ⟨N, hN⟩ t
  exact tendsto_nhds_unique hLeft (hRight.congr' (Eventually.of_forall (fun n => (hBounded n).symm)))

end CutoffRigidity
