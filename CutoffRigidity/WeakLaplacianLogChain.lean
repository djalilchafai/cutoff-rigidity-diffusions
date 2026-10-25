module
public import CutoffRigidity.WeakLaplacianSquareChain
public import CutoffRigidity.C1WeakLangevinDomain
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # The actual weak logarithm chain at C¹ regularity

The reciprocal compact C¹ test is justified by genuine strong H¹
mollification, preserving precisely the source C² potential regularity.
-/
public section
namespace CutoffRigidity
open MeasureTheory
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem gradient_log_of_c1 {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hpos : ∀ x, 0 < f x) (x : E) :
    gradient (fun y => Real.log (f y)) x = (f x)⁻¹ • gradient f x := by
  simp only [gradient, fderiv.log (hf.differentiable one_ne_zero x) (hpos x).ne', map_smul]

theorem gradient_inv_of_c1 {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hpos : ∀ x, 0 < f x) (x : E) :
    gradient (fun y => (f y)⁻¹) x = (-(f x ^ 2)⁻¹) • gradient f x := by
  have he := ((hasDerivAt_inv (hpos x).ne').comp_hasFDerivAt x
    (hf.differentiable one_ne_zero x).hasFDerivAt).fderiv
  simp only [Function.comp_def] at he
  simp only [gradient, he, map_smul]

/-- A positive lower bound and the actual gradient bound supply the
Lipschitz constant needed for the BGL01 logarithmic profile. -/
theorem lipschitzWith_log_of_c1 {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (m G : ℝ) (hm : 0 < m) (hfloor : ∀ x, m ≤ f x)
    (hG : 0 ≤ G) (hgrad : ∀ x, ‖gradient f x‖ ≤ G) :
    LipschitzWith (Real.toNNReal (G / m)) (fun x => Real.log (f x)) := by
  have hpos (x : E) : 0 < f x := hm.trans_le (hfloor x)
  have hlog := hf.log (fun x => (hpos x).ne')
  apply lipschitzWith_of_nnnorm_fderiv_le (hlog.differentiable one_ne_zero)
  intro x
  change ‖fderiv ℝ (fun y => Real.log (f y)) x‖ ≤ (Real.toNNReal (G / m) : ℝ)
  rw [Real.coe_toNNReal _ (div_nonneg hG hm.le), fderiv.log (hf.differentiable one_ne_zero x) (hpos x).ne',
    norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hpos x)]
  have hnorm : ‖fderiv ℝ f x‖ = ‖gradient f x‖ :=
    ((InnerProductSpace.toDual ℝ E).symm.norm_map _).symm
  rw [hnorm]
  calc
    (f x)⁻¹ * ‖gradient f x‖ = ‖gradient f x‖ / f x := by ring
    _ ≤ G / m := by gcongr; exact hgrad x; exact hfloor x

set_option maxHeartbeats 600000 in
/-- True distributional logarithm chain, derived using the reciprocal
compact test rather than assuming a C² representative of f. -/
theorem weak_laplacian_log_chain {f F : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hpos : ∀ x, 0 < f x)
    (hFloc : ∀ K : Set E, IsCompact K → MemLp F 2 ((volume : Measure E).restrict K))
    (hLap : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      (∫ x, f x * euclideanLaplacian ψ x) = ∫ x, F x * ψ x)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, Real.log (f x) * euclideanLaplacian ψ x) =
      ∫ x, (F x / f x - ‖gradient f x‖ ^ 2 / f x ^ 2) * ψ x := by
  let A (x : E) := (f x)⁻¹ * inner ℝ (gradient f x) (gradient ψ x)
  let B (x : E) := (f x ^ 2)⁻¹ * ‖gradient f x‖ ^ 2 * ψ x
  let C (x : E) := F x * ((f x)⁻¹ * ψ x)
  have hInv : ContDiff ℝ 1 (fun x => (f x)⁻¹) := hf.inv (fun x => (hpos x).ne')
  have hGf := continuous_gradient_of_c1 hf
  have hGψ := continuous_gradient_of_c1 (hψ.of_le (by norm_num))
  have hAcont : Continuous A := hInv.continuous.mul (hGf.inner hGψ)
  have hAoff : ∀ x ∉ tsupport ψ, A x = 0 := by
    intro x hx
    have hgψ : gradient ψ x = 0 := gradient_eq_zero_off_closed_support (isClosed_tsupport ψ)
      (fun y hy => image_eq_zero_of_notMem_tsupport hy) hx
    simp only [A, hgψ, inner_zero_right, mul_zero]
  have hA : Integrable A volume := hAcont.integrable_of_hasCompactSupport
    (compactSupport_of_eq_zero_off_compact hψc hAoff)
  have hBcont : Continuous B := by
    dsimp only [B]
    exact ((hInv.continuous.pow 2).mul (hGf.norm.pow 2)).mul hψ.continuous |>.congr (fun x => by simp only [Pi.mul_apply, Pi.pow_apply, inv_pow])
  have hBc : HasCompactSupport B := by
    simpa only [B, Pi.mul_def] using hψc.mul_left (f := fun x => (f x ^ 2)⁻¹ * ‖gradient f x‖ ^ 2)
  have hB : Integrable B volume := hBcont.integrable_of_hasCompactSupport hBc
  have hη : ContDiff ℝ 1 (fun x => (f x)⁻¹ * ψ x) := hInv.mul (hψ.of_le (by norm_num))
  have hηc : HasCompactSupport (fun x => (f x)⁻¹ * ψ x) := by
    simpa only [Pi.mul_def] using hψc.mul_left (f := fun x => (f x)⁻¹)
  have hC : Integrable C volume := locallyL2_mul_compact_continuous_integrable hFloc hη.continuous hηc
  have hE := weak_laplacian_compact_c1_test hf hFloc hLap hη hηc
  have hpoint (x : E) : inner ℝ (gradient f x) (gradient (fun y => (f y)⁻¹ * ψ y) x) = A x - B x := by
    rw [gradient_cutoff_mul (hInv.differentiable one_ne_zero) (hψ.differentiable (by norm_num)),
      gradient_inv_of_c1 hf hpos, inner_add_right, inner_smul_right, inner_smul_right,
      inner_smul_right, real_inner_self_eq_norm_sq]
    dsimp only [A, B]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_sub hA hB] at hE
  change (∫ x, A x) - (∫ x, B x) = -(∫ x, C x) at hE
  have hlog : ContDiff ℝ 1 (fun x => Real.log (f x)) := hf.log (fun x => (hpos x).ne')
  have hIBP := c1_integral_mul_laplacian_compact_test hlog hψ hψc
  have hlogp (x : E) : inner ℝ (gradient (fun y => Real.log (f y)) x) (gradient ψ x) = A x := by
    rw [gradient_log_of_c1 hf hpos, real_inner_smul_left]
  rw [integral_congr_ae (Filter.Eventually.of_forall hlogp)] at hIBP
  have hrhs (x : E) : (F x / f x - ‖gradient f x‖ ^ 2 / f x ^ 2) * ψ x = C x - B x := by
    dsimp only [C, B]
    simp only [div_eq_mul_inv]
    ring
  rw [hIBP, integral_congr_ae (Filter.Eventually.of_forall hrhs), integral_sub hC hB]
  linarith only [hE]

/-- The drift cancels through the actual C¹ logarithmic gradient rule. -/
theorem weak_langevin_log_chain {V f h : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hpos : ∀ x, 0 < f x)
    (hFloc : ∀ K : Set E, IsCompact K →
      MemLp (fun x => h x + inner ℝ (gradient V x) (gradient f x)) 2
        ((volume : Measure E).restrict K))
    (hLap : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      (∫ x, f x * euclideanLaplacian ψ x) =
      ∫ x, (h x + inner ℝ (gradient V x) (gradient f x)) * ψ x)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, Real.log (f x) * euclideanLaplacian ψ x) =
      ∫ x, ((h x / f x - ‖gradient f x‖ ^ 2 / f x ^ 2) +
        inner ℝ (gradient V x) (gradient (fun y => Real.log (f y)) x)) * ψ x := by
  have he := weak_laplacian_log_chain hf hpos hFloc hLap ψ hψ hψc
  refine he.trans (integral_congr_ae (Filter.Eventually.of_forall ?_))
  intro x
  dsimp only
  rw [gradient_log_of_c1 hf hpos, inner_smul_right]
  simp only [div_eq_mul_inv]
  ring


set_option maxHeartbeats 700000 in
/-- Uniformly positive bounded C¹ weak-generator functions have a genuine
logarithm in the full self-adjoint generator domain. All L² memberships
are derived from the displayed actual pointwise bounds. -/
theorem bounded_c1_weak_langevin_log_mem_operatorGraph
    {V f h : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 1 f) (hh : Measurable h)
    (m M G H : ℝ) (hm : 0 < m) (hfloor : ∀ x, m ≤ f x)
    (hbound : ∀ x, f x ≤ M) (hgradBound : ∀ x, ‖gradient f x‖ ≤ G)
    (hhBound : ∀ x, |h x| ≤ H)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      (∫ x, f x * euclideanLaplacian ψ x) =
      ∫ x, (h x + inner ℝ (gradient V x) (gradient f x)) * ψ x) :
    ∃ (hlog : MemLp (fun x => Real.log (f x)) 2 (gibbsMeasure volume V))
      (hR : MemLp (fun x => h x / f x - ‖gradient f x‖ ^ 2 / f x ^ 2) 2
        (gibbsMeasure volume V)),
      (hlog.toLp (fun x => Real.log (f x)),
        -hR.toLp (fun x => h x / f x - ‖gradient f x‖ ^ 2 / f x ^ 2)) ∈
          (gibbsPositiveGenerator hV hp).graph := by
  let := hp
  have hpos (x : E) : 0 < f x := hm.trans_le (hfloor x)
  have hM : 0 < M := (hpos 0).trans_le (hbound 0)
  have hG : 0 ≤ G := (norm_nonneg _).trans (hgradBound 0)
  have hH : 0 ≤ H := (abs_nonneg _).trans (hhBound 0)
  have hlogC : ContDiff ℝ 1 (fun x => Real.log (f x)) := hf.log (fun x => (hpos x).ne')
  have hlogBound (x : E) : ‖Real.log (f x)‖ ≤ |Real.log m| + |Real.log M| := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    have hl := Real.log_le_log hm (hfloor x)
    have hu := Real.log_le_log (hpos x) (hbound x)
    constructor
    · linarith [neg_abs_le (Real.log m), abs_nonneg (Real.log M)]
    · linarith [le_abs_self (Real.log M), abs_nonneg (Real.log m)]
  have hlogLp : MemLp (fun x => Real.log (f x)) 2 (gibbsMeasure volume V) :=
    MemLp.of_bound hlogC.continuous.aestronglyMeasurable _
      (Filter.Eventually.of_forall hlogBound)
  have hlogGradBound (x : E) : ‖gradient (fun y => Real.log (f y)) x‖ ≤ G / m := by
    rw [gradient_log_of_c1 hf hpos, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos (hpos x)]
    calc
      (f x)⁻¹ * ‖gradient f x‖ = ‖gradient f x‖ / f x := by ring
      _ ≤ G / m := by gcongr; exact hgradBound x; exact hfloor x
  have hlogGradLp : MemLp (gradient (fun x => Real.log (f x))) 2 (gibbsMeasure volume V) :=
    MemLp.of_bound (continuous_gradient_of_c1 hlogC).aestronglyMeasurable _
      (Filter.Eventually.of_forall hlogGradBound)
  let R : E → ℝ := fun x => h x / f x - ‖gradient f x‖ ^ 2 / f x ^ 2
  have hRmeas : Measurable R :=
    (hh.div hf.continuous.measurable).sub
      (((continuous_gradient_of_c1 hf).norm.pow 2).measurable.div (hf.continuous.pow 2).measurable)
  have hRbound (x : E) : ‖R x‖ ≤ H / m + G ^ 2 / m ^ 2 := by
    have hh1 : |h x / f x| ≤ H / m := by
      rw [abs_div, abs_of_pos (hpos x)]
      gcongr
      exact hhBound x
      exact hfloor x
    have hg1 : |‖gradient f x‖ ^ 2 / f x ^ 2| ≤ G ^ 2 / m ^ 2 := by
      rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
      gcongr
      exact hgradBound x
      exact hfloor x
    exact (abs_sub _ _).trans (add_le_add hh1 hg1)
  have hRLp : MemLp R 2 (gibbsMeasure volume V) :=
    MemLp.of_bound hRmeas.aestronglyMeasurable _ (Filter.Eventually.of_forall hRbound)
  have hhloc : ∀ K : Set E, IsCompact K → MemLp h 2 ((volume : Measure E).restrict K) := by
    intro K hK
    have : IsFiniteMeasure ((volume : Measure E).restrict K) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using (hK.measure_lt_top (μ := (volume : Measure E)))⟩
    exact MemLp.of_bound hh.aestronglyMeasurable H
      (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hhBound x))
  have hFloc : ∀ K : Set E, IsCompact K →
      MemLp (fun x => h x + inner ℝ (gradient V x) (gradient f x)) 2
        ((volume : Measure E).restrict K) := by
    intro K hK
    exact (hhloc K hK).add (continuous_memLp_two_restrict_compact
      ((continuous_gradient_of_c1 (hV.of_le (by norm_num))).inner (continuous_gradient_of_c1 hf)) hK)
  refine ⟨hlogLp, hRLp, ?_⟩
  apply c1_weak_langevin_mem_operatorGraph hV hp ρ hρ hHess hlogC hlogLp hlogGradLp hRLp
  intro ψ hψ hψc
  have he := weak_langevin_log_chain hf hpos hFloc hweak ψ hψ hψc
  exact he.trans (integral_congr_ae (Filter.Eventually.of_forall (fun x => mul_comm _ _)))

end CutoffRigidity
