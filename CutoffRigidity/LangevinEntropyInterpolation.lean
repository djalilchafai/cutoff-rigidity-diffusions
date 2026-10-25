module
public import CutoffRigidity.LangevinLogEvolution
public import CutoffRigidity.LangevinL2Operator
public import CutoffRigidity.GibbsHeatGenerator

/-! # The actual moving logarithmic interpolation in BGL01

The source positive compact perturbations have actual logarithmic
operator graphs. Their moving strong L² curve is differentiated using the
true stochastic/form semigroup and its genuine generator domain.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem norm_gradient_log_sq_of_c1 {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hpos : ∀ x, 0 < f x) (x : E) :
    ‖gradient (fun y => Real.log (f y)) x‖ ^ 2 = ‖gradient f x‖ ^ 2 / f x ^ 2 := by
  rw [gradient_log_of_c1 hf hpos, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hpos x), mul_pow, inv_pow]
  ring

section ProfileGraph
variable {d : ℕ}
variable {B : NNReal → Ω → EuclideanSpace ℝ (Fin d)} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : EuclideanSpace ℝ (Fin d), ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)

include hB hV hg hgc hρ hHess in
theorem langevinPositiveProfile_gradient_bound (r : ℝ) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ x, ‖gradient (langevinPositiveProfile V g B P c r) x‖ ≤ G := by
  obtain ⟨L, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
  have hqLip := (lipschitzWith_langevinKernel_integral hB hV ρ hρ.le hHess
    (hg.of_le (by norm_num)) hgc hLip r.toNNReal)
  refine ⟨Real.exp (-ρ * r.toNNReal) * L, mul_nonneg (Real.exp_nonneg _) L.coe_nonneg, ?_⟩
  intro x
  rw [show ‖gradient (langevinPositiveProfile V g B P c r) x‖ =
    ‖fderiv ℝ (langevinPositiveProfile V g B P c r) x‖ from
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.norm_map _]
  change ‖fderiv ℝ (fun y => c + ∫ z, g z ∂langevinKernel V B P r.toNNReal y) x‖ ≤ _
  rw [fderiv_const_add]
  exact norm_fderiv_le_of_lipschitz ℝ hqLip

include hB hV hg hgc hρ hHess hm hpos in
theorem langevinLogGradientSq_memLp (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (r : ℝ) :
    MemLp (fun x => ‖gradient (fun y => Real.log (langevinPositiveProfile V g B P c r y)) x‖ ^ 2) 2 μ := by
  have hq : ContDiff ℝ 1 (langevinPositiveProfile V g B P c r) :=
    contDiff_const.add (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess
      (hg.of_le (by norm_num)) hgc r.toNNReal)
  have hlower := langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos r
  have hlog := hq.log (fun x => (hm.trans_le (hlower x)).ne')
  obtain ⟨G, hG, hGrad⟩ := langevinPositiveProfile_gradient_bound hB hV hg hgc ρ hρ hHess c r
  apply MemLp.of_bound ((continuous_gradient_of_c1 hlog).norm.pow 2).aestronglyMeasurable ((G / m) ^ 2)
  apply Eventually.of_forall
  intro x
  change ‖‖gradient (fun y => Real.log (langevinPositiveProfile V g B P c r y)) x‖ ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_gradient_log_sq_of_c1 hq
    (fun y => hm.trans_le (hlower y)), div_pow]
  gcongr
  · exact hGrad x
  · exact hlower x

@[expose] noncomputable def langevinLogGradientSqLp (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] (r : ℝ) : (EuclideanSpace ℝ (Fin d)) →₂[μ] ℝ :=
  (langevinLogGradientSq_memLp hB hV hg hgc ρ hρ hHess c m hm hpos μ r).toLp
    (fun x => ‖gradient (fun y => Real.log (langevinPositiveProfile V g B P c r y)) x‖ ^ 2)

include hB hV hp hg hgc hρ hHess hm hpos in
set_option maxHeartbeats 650000 in
/-- The logarithmic actual transition profile has the exact genuine
positive-generator action minus its time derivative plus its squared score. -/
theorem langevinLogProfileLp_mem_operatorGraph (r : ℝ) :
    letI := hp
    (langevinLogProfileLp hB hV hg hgc ρ hρ.le hHess c m hm hpos (gibbsMeasure volume V) r,
      -langevinLogProfileDerivativeLp hB hV hg hgc ρ hρ.le hHess c m hm hpos (gibbsMeasure volume V) r +
        langevinLogGradientSqLp hB hV hg hgc ρ hρ hHess c m hm hpos (gibbsMeasure volume V) r) ∈
      (gibbsPositiveGenerator hV hp).graph := by
  let := hp
  let q := langevinPositiveProfile V g B P c r
  let D := langevinProfileGenerator V g B P r
  have hq : ContDiff ℝ 1 q := contDiff_const.add
    (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc r.toNNReal)
  have hlower := langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos r
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  obtain ⟨N, hN0, hN⟩ := compact_continuous_norm_bound
    (continuous_langevinDifferentialOperator hV hg) (hasCompactSupport_langevinDifferentialOperator V hgc)
  obtain ⟨G, _hG, hGrad⟩ := langevinPositiveProfile_gradient_bound hB hV hg hgc ρ hρ hHess c r
  have hqUpper (x : EuclideanSpace ℝ (Fin d)) : q x ≤ |c| + M := by
    exact (le_abs_self _).trans ((abs_add_le _ _).trans
      (add_le_add (le_refl _) (by simpa only [Real.norm_eq_abs] using
        langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hM r.toNNReal x)))
  have hDN (x : EuclideanSpace ℝ (Fin d)) : |D x| ≤ N := by
    simpa only [D, langevinProfileGenerator, Real.norm_eq_abs] using
      langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hN r.toNNReal x
  have hDM : Measurable D :=
    (continuous_langevinDifferentialOperator hV hg).measurable.stronglyMeasurable.integral_kernel.measurable
  have hqGrad (x : EuclideanSpace ℝ (Fin d)) : gradient q x =
      gradient (fun y => ∫ z, g z ∂langevinKernel V B P r.toNNReal y) x := by
    change gradient (fun y => c + ∫ z, g z ∂langevinKernel V B P r.toNNReal y) x = _
    simp only [gradient, fderiv_const_add]
  have hweak (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
      (∫ x, q x * euclideanLaplacian ψ x) =
        ∫ x, (D x + inner ℝ (gradient V x) (gradient q x)) * ψ x := by
    have he := langevinKernel_weak_backward_equation hB hV hg hgc ρ hρ.le hHess hψ hψc r.toNNReal
    dsimp only at he
    rw [c1_integral_mul_laplacian_compact_test hq hψ hψc]
    rw [c1_integral_mul_laplacian_compact_test
      (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc r.toNNReal) hψ hψc] at he
    simp_rw [hqGrad]
    exact he.trans (integral_congr_ae (Eventually.of_forall (fun x => mul_comm _ _)))
  obtain ⟨hLog, hR, he⟩ := bounded_c1_weak_langevin_log_mem_operatorGraph hV hp ρ hρ hHess hq hDM
    m (|c| + M) G N hm hlower hqUpper hGrad hDN hweak
  convert he using 1
  apply Prod.ext
  · rfl
  · apply Lp.ext
    filter_upwards [Lp.coeFn_add
      (-langevinLogProfileDerivativeLp hB hV hg hgc ρ hρ.le hHess c m hm hpos (gibbsMeasure volume V) r)
      (langevinLogGradientSqLp hB hV hg hgc ρ hρ hHess c m hm hpos (gibbsMeasure volume V) r),
      Lp.coeFn_neg (langevinLogProfileDerivativeLp hB hV hg hgc ρ hρ.le hHess c m hm hpos (gibbsMeasure volume V) r),
      (langevinLogProfileDerivative_memLp hB hV hg hgc ρ hρ.le hHess c m hm hpos (gibbsMeasure volume V) r).coeFn_toLp,
      (langevinLogGradientSq_memLp hB hV hg hgc ρ hρ hHess c m hm hpos (gibbsMeasure volume V) r).coeFn_toLp,
      Lp.coeFn_neg (hR.toLp _), hR.coeFn_toLp] with x hadd hneg hD hScore hnegR hRrep
    change (langevinLogProfileDerivativeLp hB hV hg hgc ρ hρ.le hHess c m hm hpos (gibbsMeasure volume V) r : _ → ℝ) x = _ at hD
    change (langevinLogGradientSqLp hB hV hg hgc ρ hρ hHess c m hm hpos (gibbsMeasure volume V) r : _ → ℝ) x = _ at hScore
    rw [hadd, Pi.add_apply, hneg, Pi.neg_apply, hD, hScore, hnegR, Pi.neg_apply, hRrep]
    rw [norm_gradient_log_sq_of_c1 hq (fun y => hm.trans_le (hlower y))]
    dsimp only [D, q]
    ring

end ProfileGraph

/-- Strong operator continuity and a uniform operator bound suffice when
the vector also moves; no operator-norm continuity is assumed. -/
theorem tendsto_strongOperator_apply_moving
    {J H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {l : Filter J} (S : J → H →L[ℝ] H) (S₀ : H →L[ℝ] H)
    (v : J → H) (v₀ : H) (C : ℝ)
    (hS : ∀ w, Tendsto (fun j => S j w) l (𝓝 (S₀ w)))
    (hbound : ∀ j, ‖S j‖ ≤ C) (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun j => S j (v j)) l (𝓝 (S₀ v₀)) := by
  have hsmall : Tendsto (fun j => S j (v j - v₀)) l (𝓝 0) := by
    apply squeeze_zero_norm (a := fun j => C * ‖v j - v₀‖)
    · intro j
      exact (S j).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hbound j) (norm_nonneg _))
    · simpa using ((hv.sub (tendsto_const_nhds (x := v₀))).norm.const_mul C)
  have hh := hsmall.add (hS v₀)
  simpa only [map_sub, sub_add_cancel, zero_add] using hh

/-- The moving-vector product rule for an actual strongly continuous
uniformly bounded family. The static domain derivative is used exactly at
its genuine vector, and the varying vector has its proved strong derivative. -/
theorem hasDerivAt_strongOperator_apply_moving
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (S : ℝ → H →L[ℝ] H) (C : ℝ)
    (hS : ∀ w, Continuous (fun r => S r w)) (hbound : ∀ r, ‖S r‖ ≤ C)
    (v : ℝ → H) (v' w' : H) (t : ℝ)
    (hv : HasDerivAt v v' t) (hw : HasDerivAt (fun r => S r (v t)) w' t) :
    HasDerivAt (fun r => S r (v r)) (S t v' + w') t := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hfirst := tendsto_strongOperator_apply_moving S (S t) (slope v t) v' C
    (fun w => ((hS w).tendsto t).mono_left nhdsWithin_le_nhds) hbound hv.tendsto_slope
  apply (hfirst.add hw.tendsto_slope).congr'
  apply Eventually.of_forall
  intro r
  simp only [slope_def_module, map_smul, map_sub, smul_sub]
  abel


set_option maxHeartbeats 650000 in
/-- The actual BGL01 moving logarithmic interpolation has precisely the
negative heat-averaged squared score as its strong L² derivative. All
logarithmic time derivatives and domain actions are derived above. -/
theorem hasDerivAt_langevin_log_interpolation_of_lt_twice
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (T s : ℝ) (hs : 0 < s) (hsT : s < 2 * T) :
    letI := hp
    HasDerivAt (fun r : ℝ =>
      langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal
        (langevinLogProfileLp hB hV hg hgc ρ hρ.le hHess c m hm hpos (gibbsMeasure volume V) (2 * T - r)))
      (-langevinL2Operator hB hV hp ρ hρ hHess s.toNNReal
        (langevinLogGradientSqLp hB hV hg hgc ρ hρ hHess c m hm hpos (gibbsMeasure volume V) (2 * T - s))) s := by
  let := hp
  let μ := gibbsMeasure volume V
  let S := fun r : ℝ => langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal
  let v := fun r : ℝ => langevinLogProfileLp hB hV hg hgc ρ hρ.le hHess c m hm hpos μ (2 * T - r)
  let D := langevinLogProfileDerivativeLp hB hV hg hgc ρ hρ.le hHess c m hm hpos μ (2 * T - s)
  let I := langevinLogGradientSqLp hB hV hg hgc ρ hρ hHess c m hm hpos μ (2 * T - s)
  have htime : 0 < 2 * T - s := by linarith
  have hv : HasDerivAt v (-D) s := by
    have hh := (hasDerivAt_langevinLogProfileLp hB hV hg hgc ρ hρ.le hHess c m hm hpos μ htime).scomp s
      ((hasDerivAt_id s).const_sub (2 * T))
    simpa only [Function.comp_def, neg_smul, one_smul] using hh
  have hgraph : (v s, -D + I) ∈ (gibbsPositiveGenerator hV hp).graph :=
    langevinLogProfileLp_mem_operatorGraph hB hV hp hg hgc ρ hρ hHess c m hm hpos (2 * T - s)
  have hw : HasDerivAt (fun r => S r (v s)) (-S s (-D + I)) s := by
    simpa only [S, langevinL2Operator_eq_gibbsHeatSemigroup] using
      gibbsHeatSemigroup_hasDerivAt_operatorGraph hV hp ρ hρ hHess s hs (v s) (-D + I) hgraph
  have hh := hasDerivAt_strongOperator_apply_moving S 1
    (fun w => (continuous_langevinL2Operator_apply hB hV hp ρ hρ hHess w).comp continuous_real_toNNReal)
    (fun r => norm_langevinL2Operator_le_one hB hV hp ρ hρ hHess r.toNNReal) v (-D) (-S s (-D + I)) s hv hw
  have hcancel : S s (-D) + -S s (-D + I) = -S s I := by
    rw [map_add, map_neg]
    abel
  rw [hcancel] at hh
  exact hh


theorem hasDerivAt_langevin_log_interpolation
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (T s : ℝ) (hs : 0 < s) (hsT : s < T) :
    letI := hp
    HasDerivAt (fun r : ℝ =>
      langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal
        (langevinLogProfileLp hB hV hg hgc ρ hρ.le hHess c m hm hpos (gibbsMeasure volume V) (2 * T - r)))
      (-langevinL2Operator hB hV hp ρ hρ hHess s.toNNReal
        (langevinLogGradientSqLp hB hV hg hgc ρ hρ hHess c m hm hpos (gibbsMeasure volume V) (2 * T - s))) s := by
  let := hp
  let μ := gibbsMeasure volume V
  let S := fun r : ℝ => langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal
  let v := fun r : ℝ => langevinLogProfileLp hB hV hg hgc ρ hρ.le hHess c m hm hpos μ (2 * T - r)
  let D := langevinLogProfileDerivativeLp hB hV hg hgc ρ hρ.le hHess c m hm hpos μ (2 * T - s)
  let I := langevinLogGradientSqLp hB hV hg hgc ρ hρ hHess c m hm hpos μ (2 * T - s)
  have htime : 0 < 2 * T - s := by linarith
  have hv : HasDerivAt v (-D) s := by
    have hh := (hasDerivAt_langevinLogProfileLp hB hV hg hgc ρ hρ.le hHess c m hm hpos μ htime).scomp s
      ((hasDerivAt_id s).const_sub (2 * T))
    simpa only [Function.comp_def, neg_smul, one_smul] using hh
  have hgraph : (v s, -D + I) ∈ (gibbsPositiveGenerator hV hp).graph :=
    langevinLogProfileLp_mem_operatorGraph hB hV hp hg hgc ρ hρ hHess c m hm hpos (2 * T - s)
  have hw : HasDerivAt (fun r => S r (v s)) (-S s (-D + I)) s := by
    simpa only [S, langevinL2Operator_eq_gibbsHeatSemigroup] using
      gibbsHeatSemigroup_hasDerivAt_operatorGraph hV hp ρ hρ hHess s hs (v s) (-D + I) hgraph
  have hh := hasDerivAt_strongOperator_apply_moving S 1
    (fun w => (continuous_langevinL2Operator_apply hB hV hp ρ hρ hHess w).comp continuous_real_toNNReal)
    (fun r => norm_langevinL2Operator_le_one hB hV hp ρ hρ hHess r.toNNReal) v (-D) (-S s (-D + I)) s hv hw
  have hcancel : S s (-D) + -S s (-D + I) = -S s I := by
    rw [map_add, map_neg]
    abel
  rw [hcancel] at hh
  exact hh

end CutoffRigidity
