module
public import CutoffRigidity.WeakLaplacianRpowChain
public import CutoffRigidity.LangevinEntropyInterpolation
public import CutoffRigidity.LangevinPositiveSquareInterpolation

/-! # Actual strong L² real-power evolution and interpolation

For the positive backward profile Q_r = c + P_r g, every real power Q_r^α
is differentiated in L² from the actual Dynkin derivative of P_r g, and it
lies in the genuine generator graph by the weak real-power chain rule.
The moving interpolation r ↦ P_r (Q_{T-r}^α) then has the strong derivative
α(α-1) P_s(Q^(α-2) |∇Q|²). Nothing beyond the source data is assumed.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def langevinRpowGradientProfile (V g : E → ℝ)
    (B : NNReal → Ω → E) (P : Measure Ω) (c α r : ℝ) (x : E) : ℝ :=
  α * (α - 1) * langevinPositiveProfile V g B P c r x ^ (α - 2) *
    ‖gradient (langevinPositiveProfile V g B P c r) x‖ ^ 2

section RpowProfile
variable {d : ℕ}
variable {B : NNReal → Ω → (EuclideanSpace ℝ (Fin d))} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : (EuclideanSpace ℝ (Fin d)) → ℝ} (hV : ContDiff ℝ 2 V)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : (EuclideanSpace ℝ (Fin d)), ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x) (α : ℝ)

include hB hV hg hgc hρ hHess hm hpos in
/-- Uniform actual two-sided bounds for the positive profile, its
gradient, and its Dynkin generator profile, at every time. -/
theorem langevinPositiveProfile_rpow_data :
    ∃ A G N : ℝ, 0 < A ∧ 0 ≤ G ∧ 0 ≤ N ∧
      (∀ r, ContDiff ℝ 1 (langevinPositiveProfile V g B P c r)) ∧
      (∀ r x, m ≤ langevinPositiveProfile V g B P c r x) ∧
      (∀ r x, langevinPositiveProfile V g B P c r x ≤ A) ∧
      (∀ r x, ‖gradient (langevinPositiveProfile V g B P c r) x‖ ≤ G) ∧
      (∀ r x, |langevinProfileGenerator V g B P r x| ≤ N) ∧
      (∀ r, Measurable (langevinProfileGenerator V g B P r)) := by
  obtain ⟨A, _hA, hBound⟩ := langevinPositiveProfile_uniform_norm_bound hB hV hg hgc ρ hρ hHess c
  obtain ⟨G, hG, hGrad⟩ := langevinPositiveProfile_uniform_gradient_bound hB hV hg hgc ρ hρ.le hHess c
  obtain ⟨N, hN0, hN⟩ := compact_continuous_norm_bound
    (continuous_langevinDifferentialOperator hV hg) (hasCompactSupport_langevinDifferentialOperator V hgc)
  have hlo (r : ℝ) (x : (EuclideanSpace ℝ (Fin d))) := langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos r x
  have hup (r : ℝ) (x : (EuclideanSpace ℝ (Fin d))) : langevinPositiveProfile V g B P c r x ≤ A :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hBound r x)
  refine ⟨A, G, N, hm.trans_le ((hlo 0 0).trans (hup 0 0)), hG, hN0, fun r => contDiff_const.add
    (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc r.toNNReal),
    hlo, hup, hGrad, fun r x => ?_, fun r => ?_⟩
  · simpa only [langevinProfileGenerator, Real.norm_eq_abs] using
      langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hN r.toNNReal x
  · exact (continuous_langevinDifferentialOperator hV hg).measurable.stronglyMeasurable.integral_kernel.measurable

include hB hV hg hgc hρ hHess hm hpos in
theorem langevinRpowProfile_memLp (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (r : ℝ) :
    MemLp (fun x => langevinPositiveProfile V g B P c r x ^ α) 2 μ := by
  obtain ⟨A, G, N, hA, hG, hN, hC, hlo, hup, -, -, -⟩ :=
    langevinPositiveProfile_rpow_data hB hV hg hgc ρ hρ hHess c m hm hpos
  apply MemLp.of_bound ((hC r).continuous.rpow_const
    (fun x => Or.inl (hm.trans_le (hlo r x)).ne')).aestronglyMeasurable (m ^ α + A ^ α)
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (hm.trans_le (hlo r x)) _)]
  exact rpow_le_add_of_mem_Icc hm (hlo r x) (hup r x) α

include hB hV hg hgc hρ hHess hm hpos in
theorem langevinRpowDerivative_memLp (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (r : ℝ) :
    MemLp (fun x => α * langevinPositiveProfile V g B P c r x ^ (α - 1) *
      langevinProfileGenerator V g B P r x) 2 μ := by
  obtain ⟨A, G, N, hA, hG, hN, hC, hlo, hup, -, hDN, hDM⟩ :=
    langevinPositiveProfile_rpow_data hB hV hg hgc ρ hρ hHess c m hm hpos
  apply MemLp.of_bound ((((hC r).continuous.rpow_const
    (fun x => Or.inl (hm.trans_le (hlo r x)).ne')).measurable.const_mul α).mul (hDM r)).aestronglyMeasurable
    (|α| * (m ^ (α - 1) + A ^ (α - 1)) * N)
  apply Eventually.of_forall
  intro x
  show ‖α * langevinPositiveProfile V g B P c r x ^ (α - 1) * langevinProfileGenerator V g B P r x‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hm.trans_le (hlo r x)) _)]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (rpow_le_add_of_mem_Icc hm (hlo r x) (hup r x) _)
    (abs_nonneg _)) (hDN r x) (abs_nonneg _) (mul_nonneg (abs_nonneg _)
      (add_nonneg (Real.rpow_nonneg hm.le _) (Real.rpow_nonneg hA.le _)))

include hB hV hg hgc hρ hHess hm hpos in
/-- A uniform bound for the actual real-power gradient profile. -/
theorem langevinRpowGradientProfile_uniform_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r x, |langevinRpowGradientProfile V g B P c α r x| ≤ K := by
  obtain ⟨A, G, N, hA, hG, hN, hC, hlo, hup, hGrad, -, -⟩ :=
    langevinPositiveProfile_rpow_data hB hV hg hgc ρ hρ hHess c m hm hpos
  refine ⟨|α * (α - 1)| * (m ^ (α - 2) + A ^ (α - 2)) * G ^ 2, by positivity, fun r x => ?_⟩
  rw [langevinRpowGradientProfile, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ‖gradient (langevinPositiveProfile V g B P c r) x‖),
    abs_of_pos (Real.rpow_pos_of_pos (hm.trans_le (hlo r x)) _)]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (rpow_le_add_of_mem_Icc hm (hlo r x) (hup r x) _)
    (abs_nonneg _)) (pow_le_pow_left₀ (norm_nonneg _) (hGrad r x) 2) (sq_nonneg _)
    (mul_nonneg (abs_nonneg _) (add_nonneg (Real.rpow_nonneg hm.le _) (Real.rpow_nonneg hA.le _)))

include hB hV hg hgc hρ hHess hm hpos in
theorem langevinRpowGradientProfile_memLp (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (r : ℝ) :
    MemLp (langevinRpowGradientProfile V g B P c α r) 2 μ := by
  obtain ⟨A, G, N, hA, hG, hN, hC, hlo, hup, hGrad, -, -⟩ :=
    langevinPositiveProfile_rpow_data hB hV hg hgc ρ hρ hHess c m hm hpos
  obtain ⟨K, hK, hKb⟩ := langevinRpowGradientProfile_uniform_bound hB hV hg hgc ρ hρ hHess c m hm hpos α
  have hmeas : Measurable (langevinRpowGradientProfile V g B P c α r) :=
    (((hC r).continuous.rpow_const (fun x => Or.inl (hm.trans_le (hlo r x)).ne')).measurable.const_mul
      (α * (α - 1))).mul ((continuous_gradient_of_c1 (hC r)).norm.pow 2).measurable
  exact MemLp.of_bound hmeas.aestronglyMeasurable K
    (Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hKb r x))

@[expose] noncomputable def langevinRpowProfileLp (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (r : ℝ) :
    (EuclideanSpace ℝ (Fin d)) →₂[μ] ℝ :=
  (langevinRpowProfile_memLp hB hV hg hgc ρ hρ hHess c m hm hpos α μ r).toLp
    (fun x => langevinPositiveProfile V g B P c r x ^ α)

@[expose] noncomputable def langevinRpowDerivativeLp (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (r : ℝ) :
    (EuclideanSpace ℝ (Fin d)) →₂[μ] ℝ :=
  (langevinRpowDerivative_memLp hB hV hg hgc ρ hρ hHess c m hm hpos α μ r).toLp
    (fun x => α * langevinPositiveProfile V g B P c r x ^ (α - 1) * langevinProfileGenerator V g B P r x)

@[expose] noncomputable def langevinRpowGradientProfileLp (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (r : ℝ) : (EuclideanSpace ℝ (Fin d)) →₂[μ] ℝ :=
  (langevinRpowGradientProfile_memLp hB hV hg hgc ρ hρ hHess c m hm hpos α μ r).toLp
    (langevinRpowGradientProfile V g B P c α r)

include hB hV hg hgc hρ hHess hm hpos in
/-- The actual strong L² derivative of the backward real-power profile. -/
theorem hasDerivAt_langevinRpowProfileLp (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (langevinRpowProfileLp hB hV hg hgc ρ hρ hHess c m hm hpos α μ)
      (langevinRpowDerivativeLp hB hV hg hgc ρ hρ hHess c m hm hpos α μ t) t := by
  obtain ⟨A, G, N, hA, hG, hN, hC, hlo, hup, -, hDN, -⟩ :=
    langevinPositiveProfile_rpow_data hB hV hg hgc ρ hρ hHess c m hm hpos
  let q := langevinPositiveProfile V g B P c
  let D := langevinProfileGenerator V g B P
  have hDeriv (r : ℝ) (hr : 0 < r) (x : (EuclideanSpace ℝ (Fin d))) :
      HasDerivAt (fun s => q s x ^ α) (α * q r x ^ (α - 1) * D r x) r := by
    have hh := ((hasDerivAt_langevinKernel_integral_compact hB hV hg hgc ρ hρ.le hHess x hr).const_add
      c).rpow_const (p := α) (Or.inl (hm.trans_le (hlo r x)).ne')
    rw [show α * q r x ^ (α - 1) * D r x = D r x * α * q r x ^ (α - 1) by ring]
    exact hh
  have hbound (r : ℝ) (_hr : 0 < r) (x : (EuclideanSpace ℝ (Fin d))) :
      ‖α * q r x ^ (α - 1) * D r x‖ ≤ |α| * (m ^ (α - 1) + A ^ (α - 1)) * N := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hm.trans_le (hlo r x)) _)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (rpow_le_add_of_mem_Icc hm (hlo r x) (hup r x) _)
      (abs_nonneg _)) (hDN r x) (abs_nonneg _) (mul_nonneg (abs_nonneg _)
        (add_nonneg (Real.rpow_nonneg hm.le _) (Real.rpow_nonneg hA.le _)))
  exact hasDerivAt_toL2_of_uniform_pointwise_derivative μ
    (fun r x => q r x ^ α) (fun r x => α * q r x ^ (α - 1) * D r x)
    (fun r => langevinRpowProfile_memLp hB hV hg hgc ρ hρ hHess c m hm hpos α μ r)
    (fun r _hr => langevinRpowDerivative_memLp hB hV hg hgc ρ hρ hHess c m hm hpos α μ r)
    (|α| * (m ^ (α - 1) + A ^ (α - 1)) * N) (mul_nonneg (mul_nonneg (abs_nonneg _)
      (add_nonneg (Real.rpow_nonneg hm.le _) (Real.rpow_nonneg hA.le _))) hN) hDeriv hbound ht

include hB hV hg hgc hρ hHess hm hpos in
set_option maxHeartbeats 700000 in
/-- The real-power transition profile has the exact genuine positive
generator action: minus its time derivative minus the carré-du-champ term. -/
theorem langevinRpowProfileLp_mem_operatorGraph (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (r : ℝ) :
    letI := hp
    (langevinRpowProfileLp hB hV hg hgc ρ hρ hHess c m hm hpos α (gibbsMeasure volume V) r,
      -(langevinRpowDerivativeLp hB hV hg hgc ρ hρ hHess c m hm hpos α (gibbsMeasure volume V) r +
        langevinRpowGradientProfileLp hB hV hg hgc ρ hρ hHess c m hm hpos α (gibbsMeasure volume V) r)) ∈
      (gibbsPositiveGenerator hV hp).graph := by
  let := hp
  let μ := gibbsMeasure volume V
  obtain ⟨A, G, N, hA, hG, hN, hC, hlo, hup, hGrad, hDN, hDM⟩ :=
    langevinPositiveProfile_rpow_data hB hV hg hgc ρ hρ hHess c m hm hpos
  have hqGrad (x : (EuclideanSpace ℝ (Fin d))) : gradient (langevinPositiveProfile V g B P c r) x =
      gradient (fun y => ∫ z, g z ∂langevinKernel V B P r.toNNReal y) x := by
    change gradient (fun y => c + ∫ z, g z ∂langevinKernel V B P r.toNNReal y) x = _
    simp only [gradient, fderiv_const_add]
  have hweak (ψ : (EuclideanSpace ℝ (Fin d)) → ℝ) (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
      (∫ x, langevinPositiveProfile V g B P c r x * euclideanLaplacian ψ x) =
        ∫ x, (langevinProfileGenerator V g B P r x + inner ℝ (gradient V x)
          (gradient (langevinPositiveProfile V g B P c r) x)) * ψ x := by
    have he := langevinKernel_weak_backward_equation hB hV hg hgc ρ hρ.le hHess hψ hψc r.toNNReal
    dsimp only at he
    rw [c1_integral_mul_laplacian_compact_test (hC r) hψ hψc]
    rw [c1_integral_mul_laplacian_compact_test
      (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc r.toNNReal) hψ hψc] at he
    simp_rw [hqGrad]
    exact he.trans (integral_congr_ae (Eventually.of_forall (fun x => mul_comm _ _)))
  obtain ⟨hPow, hR, he⟩ := bounded_c1_weak_langevin_rpow_mem_operatorGraph hV hp ρ hρ hHess (hC r)
    (hDM r) α m A G N hm (hlo r) (hup r) (hGrad r) (hDN r) hweak
  convert he using 1
  apply Prod.ext
  · rfl
  · change -(langevinRpowDerivativeLp hB hV hg hgc ρ hρ hHess c m hm hpos α μ r +
        langevinRpowGradientProfileLp hB hV hg hgc ρ hρ hHess c m hm hpos α μ r) = _
    congr 1

end RpowProfile

set_option maxHeartbeats 650000 in
/-- The actual moving real-power interpolation has precisely the
heat-averaged carré-du-champ term as its strong L² derivative. -/
theorem hasDerivAt_langevin_rpow_interpolation
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x) (α : ℝ)
    (T s : ℝ) (hs : 0 < s) (hsT : s < T) :
    letI := hp
    HasDerivAt (fun r : ℝ =>
      langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal
        (langevinRpowProfileLp hB hV hg hgc ρ hρ hHess c m hm hpos α (gibbsMeasure volume V) (T - r)))
      (langevinL2Operator hB hV hp ρ hρ hHess s.toNNReal
        (langevinRpowGradientProfileLp hB hV hg hgc ρ hρ hHess c m hm hpos α
          (gibbsMeasure volume V) (T - s))) s := by
  let := hp
  let μ := gibbsMeasure volume V
  let S := fun r : ℝ => langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal
  let v := fun r : ℝ => langevinRpowProfileLp hB hV hg hgc ρ hρ hHess c m hm hpos α μ (T - r)
  let D := langevinRpowDerivativeLp hB hV hg hgc ρ hρ hHess c m hm hpos α μ (T - s)
  let I := langevinRpowGradientProfileLp hB hV hg hgc ρ hρ hHess c m hm hpos α μ (T - s)
  have htime : 0 < T - s := by linarith
  have hv : HasDerivAt v (-D) s := by
    have hh := (hasDerivAt_langevinRpowProfileLp hB hV hg hgc ρ hρ hHess c m hm hpos α μ htime).scomp s
      ((hasDerivAt_id s).const_sub T)
    simpa only [Function.comp_def, neg_smul, one_smul] using hh
  have hgraph : (v s, -(D + I)) ∈ (gibbsPositiveGenerator hV hp).graph :=
    langevinRpowProfileLp_mem_operatorGraph hB hV hg hgc ρ hρ hHess c m hm hpos α hp (T - s)
  have hw : HasDerivAt (fun r => S r (v s)) (-S s (-(D + I))) s := by
    simpa only [S, langevinL2Operator_eq_gibbsHeatSemigroup] using
      gibbsHeatSemigroup_hasDerivAt_operatorGraph hV hp ρ hρ hHess s hs (v s) (-(D + I)) hgraph
  have hh := hasDerivAt_strongOperator_apply_moving S 1
    (fun w => (continuous_langevinL2Operator_apply hB hV hp ρ hρ hHess w).comp continuous_real_toNNReal)
    (fun r => norm_langevinL2Operator_le_one hB hV hp ρ hρ hHess r.toNNReal) v (-D) (-S s (-(D + I))) s hv hw
  have hcancel : S s (-D) + -S s (-(D + I)) = S s I := by
    simp only [map_neg, map_add, neg_neg]
    abel
  rw [hcancel] at hh
  exact hh

end CutoffRigidity
