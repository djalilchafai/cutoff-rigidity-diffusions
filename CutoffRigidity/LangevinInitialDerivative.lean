module

public import CutoffRigidity.LangevinVariationalEquation
public import CutoffRigidity.DissipationBounds
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Uniform C² Taylor control for actual initial-point differentiation

Only continuous Hessians are used. Uniformity comes from compact finite-
dimensional path tubes, not from a Hessian Lipschitz assumption.
-/

public section

namespace CutoffRigidity

open MeasureTheory Set Filter Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Continuous actual Hessians give a uniform first-order remainder for the
potential gradient throughout any bounded finite-dimensional path tube. -/
theorem uniform_gradient_taylor_remainder_closedBall {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ closedBall (0 : E) R, ∀ h : E, ‖h‖ ≤ δ →
      ‖gradient V (a + h) - gradient V a - fderiv ℝ (gradient V) a h‖ ≤ ε * ‖h‖ := by
  have hG := contDiff_one_gradient_of_contDiff_two hV
  have hUC := (isCompact_closedBall (0 : E) (R + 1)).uniformContinuousOn_of_continuous
    (hG.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨η, hη, hηbound⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
  let δ := min 1 (η / 2)
  have hδ : 0 < δ := lt_min zero_lt_one (half_pos hη)
  refine ⟨δ, hδ, ?_⟩
  intro a ha h hh
  have haR : ‖a‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using ha
  have haS : a ∈ closedBall (0 : E) (R + 1) := by
    rw [mem_closedBall, dist_zero_right]
    linarith
  let F := fun z => gradient V z - gradient V a - fderiv ℝ (gradient V) a (z - a)
  have hD (z : E) : HasFDerivAt F (fderiv ℝ (gradient V) z - fderiv ℝ (gradient V) a) z := by
    have hh := ((hG.differentiable one_ne_zero z).hasFDerivAt.sub_const (gradient V a)).sub
      ((fderiv ℝ (gradient V) a).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const a))
    convert! hh using 1
  have hbound (z : E) (hz : z ∈ closedBall a δ) :
      ‖fderiv ℝ (gradient V) z - fderiv ℝ (gradient V) a‖ ≤ ε := by
    have hza : ‖z - a‖ ≤ δ := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have hzS : z ∈ closedBall (0 : E) (R + 1) := by
      rw [mem_closedBall, dist_zero_right]
      have hn := norm_le_norm_sub_add z a
      have hd1 : δ ≤ 1 := min_le_left _ _
      linarith
    have hdist : dist z a < η := by
      rw [dist_eq_norm]
      have hdη : δ ≤ η / 2 := min_le_right _ _
      linarith
    simpa only [dist_eq_norm] using (hηbound z hzS a haS hdist).le
  have hbase : a ∈ closedBall a δ := mem_closedBall_self hδ.le
  have hhpoint : a + h ∈ closedBall a δ := by simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left] using hh
  have hm := (convex_closedBall a δ).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hD z).hasFDerivWithinAt) hbound hbase hhpoint
  simpa only [F, sub_self, map_zero, sub_zero, add_sub_cancel_left] using hm

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- A zero-initial perturbation with a uniformly small forcing stays
small. This interior-derivative form avoids assuming differentiability of
continuous driving noise at time zero. -/
theorem zero_initial_volterra_stability
    {Z Z' : ℝ → E} {K η t : ℝ} (hK : 0 ≤ K) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (hc : ContinuousOn Z (Icc 0 t)) (hZ0 : Z 0 = 0)
    (hD : ∀ s ∈ Ioo 0 t, HasDerivAt Z (Z' s) s)
    (hbound : ∀ s ∈ Ioo 0 t, ‖Z' s‖ ≤ K * ‖Z s‖ + η) :
    ‖Z t‖ ≤ η * Real.exp ((2 * K + 1) * t / 2) := by
  let c := 2 * K + 1
  have hcpos : 0 < c := by dsimp [c]; linarith
  have hcoef : c * (η ^ 2 / c) = η ^ 2 := by field_simp
  have hf := exponential_decay_of_deriv_le
    (f := fun s => ‖Z s‖ ^ 2 + η ^ 2 / c)
    (f' := fun s => 2 * inner ℝ (Z s) (Z' s)) (rate := -c) ht
    ((hc.norm.pow 2).add continuousOn_const)
    (fun s hs => (hD s hs).norm_sq.add_const _) (fun s hs => ?_)
  · rw [hZ0, norm_zero, zero_pow (by norm_num), zero_add] at hf
    have hexp : Real.exp (-(-c) * t) = Real.exp (c * t / 2) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hexp] at hf
    have hfrac : η ^ 2 / c ≤ η ^ 2 := div_le_self (sq_nonneg _) (by dsimp [c]; linarith)
    have hmul := mul_le_mul_of_nonneg_left hfrac (sq_nonneg (Real.exp (c * t / 2)))
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hη (Real.exp_nonneg _))).mp
    rw [mul_pow]
    nlinarith [div_nonneg (sq_nonneg η) hcpos.le]
  · have hi := real_inner_le_norm (Z s) (Z' s)
    have hb := mul_le_mul_of_nonneg_left (hbound s hs) (norm_nonneg (Z s))
    change 2 * inner ℝ (Z s) (Z' s) ≤ -(-c) * (‖Z s‖ ^ 2 + η ^ 2 / c)
    dsimp only [c] at hcoef ⊢
    nlinarith [sq_nonneg (‖Z s‖ - η)]

/-- The constructed linear variational evolution is the actual initial-
point Fréchet derivative. Only C² potential regularity is used; in
particular no Lipschitz Hessian or differentiable-flow premise is added. -/
theorem hasFDerivAt_langevinSolution_of_variational_equation
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w : ℝ → E} (hw : Continuous w) (x : E) (J : ℝ → E →L[ℝ] E)
    {T : ℝ} (hT : 0 ≤ T) (hJ0 : J 0 = ContinuousLinearMap.id ℝ E)
    (hJC : ContinuousOn J (Icc 0 T))
    (hJD : ∀ s ∈ Ioo 0 T, HasDerivAt J
      (-(fderiv ℝ (gradient V) (langevinSolution V w x s)).comp (J s)) s) :
    HasFDerivAt (fun y => langevinSolution V w y T) (J T) x := by
  let X := fun s => langevinSolution V w x s
  let A := fun s => fderiv ℝ (gradient V) (X s)
  have hX := langevinSolution_isLangevinPathOn hV ρ hρ hHess hw x hT
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hX.1
  have hAC : ContinuousOn A (Icc 0 T) :=
    continuousOn_langevinSolution_linearization hV ρ hρ hHess hw x hT
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hAC
  let K := max K₀ 0
  have hK : 0 ≤ K := le_max_right _ _
  let M := Real.exp ((2 * K + 1) * T / 2)
  have hM : 0 < M := Real.exp_pos _
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  let e := ε / M
  have he : 0 < e := div_pos hε hM
  obtain ⟨δ, hδ, hTaylor⟩ := uniform_gradient_taylor_remainder_closedBall hV R he
  filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with h hh
  have hhn : ‖h‖ ≤ δ := by
    exact (by simpa only [mem_ball, dist_zero_right] using hh : ‖h‖ < δ).le
  let Y := fun s => langevinSolution V w (x + h) s
  let Z := fun s => Y s - X s - J s h
  let Z' := fun s => -gradient V (Y s) + gradient V (X s) + A s (J s h)
  have hY := langevinSolution_isLangevinPathOn hV ρ hρ hHess hw (x + h) hT
  have hZC : ContinuousOn Z (Icc 0 T) :=
    (hY.1.sub hX.1).sub (hJC.clm_apply continuousOn_const)
  have hZ0 : Z 0 = 0 := by
    dsimp only [Z, Y, X]
    rw [langevinSolution_initial hV ρ hρ hHess hw (x + h),
      langevinSolution_initial hV ρ hρ hHess hw x, hJ0, ContinuousLinearMap.id_apply]
    abel
  have hZD (s : ℝ) (hs : s ∈ Ioo 0 T) : HasDerivAt Z (Z' s) s := by
    have hd := (langevin_same_noise_difference_hasDerivAt hV hY hX hs).sub
      ((hJD s hs).clm_apply (hasDerivAt_const s h))
    convert! hd using 1
    simp only [ContinuousLinearMap.comp_apply, neg_apply, map_zero, add_zero]
    dsimp only [Z', A, X, Y]
    abel
  have hΔ (s : ℝ) (hs : s ∈ Icc 0 T) : ‖Y s - X s‖ ≤ ‖h‖ := by
    have hh := langevinSolution_initial_point_contraction hV ρ hρ hHess hw (x + h) x hs.1
    have hexp : Real.exp (-ρ * s) ≤ 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hρ hs.1] : -ρ * s ≤ 0)
    have hh' : ‖Y s - X s‖ ≤ Real.exp (-ρ * s) * ‖h‖ := by
      simpa only [Y, X, add_sub_cancel_left] using hh
    exact hh'.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hexp (norm_nonneg h))
  have hbound (s : ℝ) (hs : s ∈ Ioo 0 T) : ‖Z' s‖ ≤ K * ‖Z s‖ + e * ‖h‖ := by
    have hs' : s ∈ Icc 0 T := Ioo_subset_Icc_self hs
    have hbase : X s ∈ closedBall (0 : E) R := by
      simpa only [mem_closedBall, dist_zero_right, X] using hR s hs'
    have hrem := hTaylor (X s) hbase (Y s - X s) ((hΔ s hs').trans hhn)
    have hid : X s + (Y s - X s) = Y s := by abel
    rw [hid] at hrem
    have heq : Z' s = -(A s (Z s)) -
        (gradient V (Y s) - gradient V (X s) - A s (Y s - X s)) := by
      dsimp only [Z', Z]
      rw [map_sub, map_sub]
      abel
    rw [heq]
    calc
      _ ≤ ‖A s (Z s)‖ + ‖gradient V (Y s) - gradient V (X s) - A s (Y s - X s)‖ := by
        simpa only [norm_neg] using norm_sub_le (-(A s (Z s)))
          (gradient V (Y s) - gradient V (X s) - A s (Y s - X s))
      _ ≤ K * ‖Z s‖ + e * ‖h‖ := by
        have hAK : ‖A s‖ ≤ K := (hK₀ s hs').trans (le_max_left _ _)
        have hAZ := (A s).le_opNorm (Z s)
        have hr := hrem.trans (mul_le_mul_of_nonneg_left (hΔ s hs') he.le)
        exact add_le_add (hAZ.trans (mul_le_mul_of_nonneg_right hAK (norm_nonneg _))) hr
  have hstab := zero_initial_volterra_stability hK (mul_nonneg he.le (norm_nonneg h)) hT
    hZC hZ0 hZD hbound
  have heM : e * M = ε := by dsimp [e]; field_simp
  change ‖Z T‖ ≤ ε * ‖h‖
  calc
    _ ≤ (e * ‖h‖) * M := hstab
    _ = _ := by rw [mul_right_comm, heM]

/-- A continuous nonnegative linearization has an actual variational
solution on every finite horizon. A genuine smooth cutoff gives global
Picard existence; column dissipation forces norm ≤1, removing that cutoff. -/
theorem exists_linear_variation_on_finite_interval
    (A : ℝ → E →L[ℝ] E) {T : ℝ} (hT : 0 ≤ T)
    (hA : ContinuousOn A (Icc 0 T))
    (hpos : ∀ s ∈ Icc 0 T, ∀ z : E, 0 ≤ inner ℝ z (A s z)) :
    ∃ J : ℝ → E →L[ℝ] E, J 0 = ContinuousLinearMap.id ℝ E ∧
      ContinuousOn J (Icc 0 T) ∧
      ∀ s ∈ Icc 0 T, HasDerivWithinAt J (-(A s).comp (J s)) (Icc 0 T) s := by
  let χ : ContDiffBump (0 : E →L[ℝ] E) := ⟨2, 3, by norm_num, by norm_num⟩
  let Q := fun J : E →L[ℝ] E => χ J • J
  have hQ : ContDiff ℝ 1 Q := χ.contDiff.smul contDiff_id
  have hQc : HasCompactSupport Q := χ.hasCompactSupport.smul_right
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hQc hQ (by norm_num)
  obtain ⟨M₀, hM₀⟩ := hQc.exists_bound_of_continuous hQ.continuous
  let M : ℝ≥0 := ⟨max M₀ 0, le_max_right _ _⟩
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  let K : ℝ≥0 := ⟨max K₀ 0, le_max_right _ _⟩
  let L := K * M
  let a : ℝ≥0 := ⟨(L : ℝ) * T + 1, by positivity⟩
  have hAK (s : ℝ) (hs : s ∈ Icc 0 T) : ‖A s‖ ≤ K := (hK₀ s hs).trans (le_max_left _ _)
  have hQM (J : E →L[ℝ] E) : ‖Q J‖ ≤ M := (hM₀ J).trans (le_max_left _ _)
  have hPicard : IsPicardLindelof (fun (s : ℝ) (J : E →L[ℝ] E) => -(A s).comp (Q J))
      (tmin := 0) (tmax := T) ⟨0, ⟨le_rfl, hT⟩⟩ (ContinuousLinearMap.id ℝ E)
      a 0 L (K * C) := by
    constructor
    · intro s hs
      apply LipschitzOnWith.of_dist_le_mul
      intro J _ R _
      rw [dist_eq_norm, dist_eq_norm]
      calc
        _ = ‖(A s).comp (Q J - Q R)‖ := by
          rw [ContinuousLinearMap.comp_sub, neg_sub_neg, norm_sub_rev]
        _ ≤ ‖A s‖ * ‖Q J - Q R‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (K : ℝ) * ((C : ℝ) * ‖J - R‖) :=
          mul_le_mul (hAK s hs) (hC.norm_sub_le J R) (norm_nonneg _) K.coe_nonneg
        _ = _ := by rw [NNReal.coe_mul]; ring
    · intro J _
      exact (hA.clm_comp continuousOn_const).neg
    · intro s hs J _
      rw [norm_neg]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hAK s hs) (hQM J) (norm_nonneg _) K.coe_nonneg)
    · simp only [sub_zero, max_eq_left hT, NNReal.coe_zero]
      change (L : ℝ) * T ≤ (L : ℝ) * T + 1
      linarith
  obtain ⟨J, hJ0, hJD⟩ := hPicard.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hJC : ContinuousOn J (Icc 0 T) := fun s hs => (hJD s hs).continuousWithinAt
  have hJn (t : ℝ) (ht : t ∈ Icc 0 T) : ‖J t‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    have hZC : ContinuousOn (fun s => J s z) (Icc 0 t) :=
      (hJC.mono (fun s hs => ⟨hs.1, hs.2.trans ht.2⟩)).clm_apply continuousOn_const
    have hZD (s : ℝ) (hs : s ∈ Ioo 0 t) : HasDerivAt (fun r => J r z)
        (-(A s).comp (Q (J s)) z) s := by
      have hh := ((hJD s ⟨hs.1.le, hs.2.le.trans ht.2⟩).hasDerivAt
        (Icc_mem_nhds hs.1 (hs.2.trans_le ht.2))).clm_apply (hasDerivAt_const s z)
      convert! hh using 1
      simp only [neg_apply, ContinuousLinearMap.comp_apply, map_zero, add_zero]
    have hdiss (s : ℝ) (hs : s ∈ Ioo 0 t) :
        inner ℝ (J s z) (-(A s).comp (Q (J s)) z) ≤ -(0 : ℝ) * ‖J s z‖ ^ 2 := by
      have hh := mul_nonneg (χ.nonneg' (J s)) (hpos s ⟨hs.1.le, hs.2.le.trans ht.2⟩ (J s z))
      simpa only [Q, ContinuousLinearMap.comp_apply, neg_apply, smul_apply, map_smul,
        inner_neg_right, inner_smul_right, neg_zero, zero_mul] using neg_nonpos.mpr hh
    have hh := norm_contraction_of_dissipative_derivative ht.1 hZC hZD hdiss
    simpa only [hJ0, ContinuousLinearMap.id_apply, neg_zero, zero_mul, Real.exp_zero, one_mul] using hh
  refine ⟨J, hJ0, hJC, ?_⟩
  intro s hs
  have hχ : χ (J s) = 1 := by
    apply χ.one_of_mem_closedBall
    rw [mem_closedBall, dist_zero_right]
    change ‖J s‖ ≤ 2
    linarith [hJn s hs]
  simpa only [Q, hχ, one_smul] using hJD s hs

/-- Actual initial-point differentiability at every finite forward time,
constructed from the true C² potential and continuous noise. -/
theorem differentiable_langevinSolution_initial_point
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w : ℝ → E} (hw : Continuous w) {T : ℝ} (hT : 0 ≤ T) :
    Differentiable ℝ (fun x => langevinSolution V w x T) := by
  intro x
  let A := fun s => fderiv ℝ (gradient V) (langevinSolution V w x s)
  have hA : ContinuousOn A (Icc 0 T) :=
    continuousOn_langevinSolution_linearization hV ρ hρ hHess hw x hT
  have hpos (s : ℝ) (_hs : s ∈ Icc 0 T) (z : E) : 0 ≤ inner ℝ z (A s z) := by
    have hh := hHess (langevinSolution V w x s) z
    have hd := (hV.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
    rw [← inner_fderiv_gradient_apply (hd _)] at hh
    rw [real_inner_comm]
    exact (mul_nonneg hρ (sq_nonneg _)).trans hh
  obtain ⟨J, hJ0, hJC, hJD⟩ := exists_linear_variation_on_finite_interval A hT hA hpos
  apply (hasFDerivAt_langevinSolution_of_variational_equation hV ρ hρ hHess hw x J hT hJ0 hJC ?_).differentiableAt
  intro s hs
  exact (hJD s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)

/-- The actual initial-point derivative obeys the sharp synchronous
operator-norm bound at every finite time. -/
theorem norm_fderiv_langevinSolution_initial_point_le
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w : ℝ → E} (hw : Continuous w) {T : ℝ} (hT : 0 ≤ T) (x : E) :
    ‖fderiv ℝ (fun y => langevinSolution V w y T) x‖ ≤ Real.exp (-ρ * T) :=
  norm_fderiv_le_of_lipschitz ℝ (langevinSolution_initial_point_lipschitz hV ρ hρ hHess hw hT)

end CutoffRigidity
