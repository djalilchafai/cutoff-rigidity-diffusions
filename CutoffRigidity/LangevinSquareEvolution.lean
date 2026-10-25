module
public import CutoffRigidity.WeakLangevinSquareDomain
public import CutoffRigidity.LangevinJointScoreContinuity
public import CutoffRigidity.LangevinLogEvolution

/-! # Actual squared backward-profile evolution for local Poincare

The true C¹ weak square chain rule and dominated strong differentiation
supply the generator domain and time derivative of (K_r g)².
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def langevinSquareProfile (V g : E → ℝ)
    (B : NNReal → Ω → E) (P : Measure Ω) (r : ℝ) (x : E) : ℝ :=
  (∫ y, g y ∂langevinKernel V B P r.toNNReal x) ^ 2
@[expose] noncomputable def langevinSquareProfileDerivative (V g : E → ℝ)
    (B : NNReal → Ω → E) (P : Measure Ω) (r : ℝ) (x : E) : ℝ :=
  2 * (∫ y, g y ∂langevinKernel V B P r.toNNReal x) * langevinProfileGenerator V g B P r x
@[expose] noncomputable def langevinGradientSqProfile (V g : E → ℝ)
    (B : NNReal → Ω → E) (P : Measure Ω) (r : ℝ) (x : E) : ℝ :=
  ‖gradient (fun z => ∫ y, g y ∂langevinKernel V B P r.toNNReal z) x‖ ^ 2

section Square
variable {d : ℕ}
variable {B : NNReal → Ω → EuclideanSpace ℝ (Fin d)} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : EuclideanSpace ℝ (Fin d), ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)

include hB hV hg hgc hρ hHess in
theorem langevinSquareProfile_memLp (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (r : ℝ) :
    MemLp (langevinSquareProfile V g B P r) 2 μ := by
  obtain ⟨M,hM0,hM⟩ := compact_continuous_norm_bound hg.continuous hgc
  have hqC := (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc r.toNNReal).continuous
  apply MemLp.of_bound (hqC.pow 2).aestronglyMeasurable (M ^ 2)
  apply Eventually.of_forall
  intro x
  change ‖(∫ y, g y ∂langevinKernel V B P r.toNNReal x) ^ 2‖ ≤ M ^ 2
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (langevinKernel_integral_compact_test_norm_le hB hV
    ρ hρ.le hHess hM r.toNNReal x) 2

include hB hV hg hgc hρ hHess in
theorem langevinSquareProfileDerivative_memLp (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (r : ℝ) :
    MemLp (langevinSquareProfileDerivative V g B P r) 2 μ := by
  obtain ⟨M,hM0,hM⟩ := compact_continuous_norm_bound hg.continuous hgc
  obtain ⟨N,hN0,hN⟩ := compact_continuous_norm_bound (continuous_langevinDifferentialOperator hV hg)
    (hasCompactSupport_langevinDifferentialOperator V hgc)
  have hqC := (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc r.toNNReal).continuous
  have hDC := continuous_langevinKernel_integral_initial hB hV (continuous_langevinDifferentialOperator hV hg)
    ⟨N,hN⟩ ρ hρ.le hHess r.toNNReal
  apply MemLp.of_bound ((hqC.const_mul 2).mul hDC).aestronglyMeasurable (2 * M * N)
  apply Eventually.of_forall
  intro x
  change ‖2 * (∫ y, g y ∂langevinKernel V B P r.toNNReal x) *
    (∫ y, langevinDifferentialOperator V g y ∂langevinKernel V B P r.toNNReal x)‖ ≤ _
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
  gcongr
  · exact langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hM r.toNNReal x
  · exact langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hN r.toNNReal x

include hB hV hg hgc hρ hHess in
theorem langevinGradientSqProfile_memLp (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (r : ℝ) :
    MemLp (langevinGradientSqProfile V g B P r) 2 μ := by
  obtain ⟨L,hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
  have hl := lipschitzWith_langevinKernel_integral hB hV ρ hρ.le hHess
    (hg.of_le (by norm_num)) hgc hLip r.toNNReal
  have hc := continuous_gradient_of_c1
    (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc r.toNNReal)
  apply MemLp.of_bound (hc.norm.pow 2).aestronglyMeasurable ((L : ℝ) ^ 2)
  apply Eventually.of_forall
  intro x
  change ‖‖gradient (fun z => ∫ y, g y ∂langevinKernel V B P r.toNNReal z) x‖ ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [show ‖gradient (fun z => ∫ y, g y ∂langevinKernel V B P r.toNNReal z) x‖ =
    ‖fderiv ℝ (fun z => ∫ y, g y ∂langevinKernel V B P r.toNNReal z) x‖ from
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.norm_map _]
  exact (norm_fderiv_le_of_lipschitz ℝ hl).trans
    (mul_le_of_le_one_left L.coe_nonneg (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ.le) r.toNNReal.property)))

@[expose] noncomputable def langevinSquareProfileLp
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (r : ℝ) :=
  (langevinSquareProfile_memLp hB hV hg hgc ρ hρ hHess μ r).toLp (langevinSquareProfile V g B P r)
@[expose] noncomputable def langevinSquareProfileDerivativeLp
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (r : ℝ) :=
  (langevinSquareProfileDerivative_memLp hB hV hg hgc ρ hρ hHess μ r).toLp (langevinSquareProfileDerivative V g B P r)
@[expose] noncomputable def langevinGradientSqProfileLp
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (r : ℝ) :=
  (langevinGradientSqProfile_memLp hB hV hg hgc ρ hρ hHess μ r).toLp (langevinGradientSqProfile V g B P r)

include hB hV hg hgc hρ hHess in
theorem hasDerivAt_langevinSquareProfileLp
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) :
    HasDerivAt (langevinSquareProfileLp hB hV hg hgc ρ hρ hHess μ)
      (langevinSquareProfileDerivativeLp hB hV hg hgc ρ hρ hHess μ r) r := by
  obtain ⟨M,hM0,hM⟩ := compact_continuous_norm_bound hg.continuous hgc
  obtain ⟨N,hN0,hN⟩ := compact_continuous_norm_bound (continuous_langevinDifferentialOperator hV hg)
    (hasCompactSupport_langevinDifferentialOperator V hgc)
  apply hasDerivAt_toL2_of_uniform_pointwise_derivative μ
    (langevinSquareProfile V g B P) (langevinSquareProfileDerivative V g B P)
    (langevinSquareProfile_memLp hB hV hg hgc ρ hρ hHess μ)
    (fun s _ => langevinSquareProfileDerivative_memLp hB hV hg hgc ρ hρ hHess μ s)
    (2*M*N) (by positivity) _ _ hr
  · intro s hs x
    have hh := (hasDerivAt_langevinKernel_integral_compact hB hV hg hgc ρ hρ.le hHess x hs).pow 2
    convert! hh using 1; norm_num [langevinSquareProfile, langevinSquareProfileDerivative, langevinProfileGenerator]
  · intro s hs x
    change ‖2 * (∫ y, g y ∂langevinKernel V B P s.toNNReal x) *
      (∫ y, langevinDifferentialOperator V g y ∂langevinKernel V B P s.toNNReal x)‖ ≤ _
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    gcongr
    · exact langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hM s.toNNReal x
    · exact langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hN s.toNNReal x

include hB hV hg hgc hρ hHess in
/-- The actual squared backward test lies in the genuine generator graph,
with its full carré-du-champ action derived from the C¹ weak square chain. -/
theorem langevinSquareProfileLp_mem_operatorGraph
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (r : ℝ) :
    letI := hp
    (langevinSquareProfileLp hB hV hg hgc ρ hρ hHess (gibbsMeasure volume V) r,
      -(langevinSquareProfileDerivativeLp hB hV hg hgc ρ hρ hHess (gibbsMeasure volume V) r +
        (2 : ℝ) • langevinGradientSqProfileLp hB hV hg hgc ρ hρ hHess (gibbsMeasure volume V) r)) ∈
      (gibbsPositiveGenerator hV hp).graph := by
  let := hp
  let μ := gibbsMeasure volume V
  let q := fun x => ∫ y, g y ∂langevinKernel V B P r.toNNReal x
  let D := langevinProfileGenerator V g B P r
  have hq : ContDiff ℝ 1 q :=
    contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc r.toNNReal
  obtain ⟨M, hM0, hM⟩ := compact_continuous_norm_bound hg.continuous hgc
  obtain ⟨N, hN0, hN⟩ := compact_continuous_norm_bound (continuous_langevinDifferentialOperator hV hg)
    (hasCompactSupport_langevinDifferentialOperator V hgc)
  obtain ⟨L, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
  have hqBound (x : EuclideanSpace ℝ (Fin d)) : ‖q x‖ ≤ M :=
    langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hM r.toNNReal x
  have hDBound (x : EuclideanSpace ℝ (Fin d)) : ‖D x‖ ≤ N :=
    langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hN r.toNNReal x
  have hDmeas : Measurable D :=
    (continuous_langevinDifferentialOperator hV hg).measurable.stronglyMeasurable.integral_kernel.measurable
  have hGradBound (x : EuclideanSpace ℝ (Fin d)) : ‖gradient q x‖ ≤ L := by
    change ‖(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ q x)‖ ≤ _
    rw [(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.norm_map]
    have hqLip := lipschitzWith_langevinKernel_integral hB hV ρ hρ.le hHess
      (hg.of_le (by norm_num)) hgc hLip r.toNNReal
    exact (norm_fderiv_le_of_lipschitz ℝ hqLip).trans
      (mul_le_of_le_one_left L.coe_nonneg (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ.le) r.toNNReal.property)))
  have hweak (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
      (∫ x, q x * euclideanLaplacian ψ x) = ∫ x, (D x + inner ℝ (gradient V x) (gradient q x)) * ψ x := by
    have hh := langevinKernel_weak_backward_equation hB hV hg hgc ρ hρ.le hHess hψ hψc r.toNNReal
    exact hh.trans (integral_congr_ae (Eventually.of_forall (fun x => mul_comm _ _)))
  obtain ⟨hSq, hSrc, hGraph⟩ := bounded_c1_weak_langevin_square_mem_operatorGraph hV hp ρ hρ hHess
    hq hDmeas M L N hM0 L.coe_nonneg hN0 hqBound hGradBound hDBound hweak
  have hSqeq : hSq.toLp (fun x => q x ^ 2) = langevinSquareProfileLp hB hV hg hgc ρ hρ hHess μ r := by
    apply Lp.ext
    filter_upwards [hSq.coeFn_toLp,
      (langevinSquareProfile_memLp hB hV hg hgc ρ hρ hHess μ r).coeFn_toLp] with x hx hy
    change _ = (langevinSquareProfile_memLp hB hV hg hgc ρ hρ hHess μ r).toLp _ x
    rw [hx, hy]
    rfl
  have hSrceq : hSrc.toLp (fun x => 2 * q x * D x + 2 * ‖gradient q x‖ ^ 2) =
      langevinSquareProfileDerivativeLp hB hV hg hgc ρ hρ hHess μ r +
        (2 : ℝ) • langevinGradientSqProfileLp hB hV hg hgc ρ hρ hHess μ r := by
    apply Lp.ext
    filter_upwards [hSrc.coeFn_toLp,
      Lp.coeFn_add (langevinSquareProfileDerivativeLp hB hV hg hgc ρ hρ hHess μ r)
        ((2 : ℝ) • langevinGradientSqProfileLp hB hV hg hgc ρ hρ hHess μ r),
      Lp.coeFn_smul (2 : ℝ) (langevinGradientSqProfileLp hB hV hg hgc ρ hρ hHess μ r),
      (langevinSquareProfileDerivative_memLp hB hV hg hgc ρ hρ hHess μ r).coeFn_toLp,
      (langevinGradientSqProfile_memLp hB hV hg hgc ρ hρ hHess μ r).coeFn_toLp] with x hx hadd hsm hDrep hGrep
    change (langevinSquareProfileDerivativeLp hB hV hg hgc ρ hρ hHess μ r : _ → ℝ) x = _ at hDrep
    change (langevinGradientSqProfileLp hB hV hg hgc ρ hρ hHess μ r : _ → ℝ) x = _ at hGrep
    rw [hx, hadd, Pi.add_apply, hsm, Pi.smul_apply, smul_eq_mul, hDrep, hGrep]
    rfl
  rw [hSqeq, hSrceq] at hGraph
  exact hGraph

end Square
end CutoffRigidity
