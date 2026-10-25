module

public import CutoffRigidity.Riemann.DiffSobolevRn1
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! # Mollification in `L²(E)` compatible with weak derivatives

`mol ε f = k_ε ⋆ f` with `k_ε` the normalized Mathlib bump supported in `B(0,ε)`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff Convolution

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The bump function of radii `ε/2`, `ε`. -/
noncomputable def molBump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : E) :=
  ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩

/-- Mollification `k_ε ⋆ f` (`∫ k_ε(y) f(x - y) dy`). -/
noncomputable def mol (ε : ℝ) (hε : 0 < ε) (f : E → ℝ) : E → ℝ :=
  (molBump ε hε : ContDiffBump (0 : E)).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

/-- The normalized kernel. -/
noncomputable abbrev molK (ε : ℝ) (hε : 0 < ε) : E → ℝ :=
  (molBump ε hε : ContDiffBump (0 : E)).normed volume

theorem molK_nonneg (ε : ℝ) (hε : 0 < ε) (x : E) : 0 ≤ molK ε hε x :=
  (molBump ε hε : ContDiffBump (0 : E)).nonneg_normed x

theorem molK_contDiff (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ ∞ (molK ε hε : E → ℝ) :=
  (molBump ε hε : ContDiffBump (0 : E)).contDiff_normed

theorem molK_continuous (ε : ℝ) (hε : 0 < ε) : Continuous (molK ε hε : E → ℝ) :=
  (molK_contDiff ε hε).continuous

theorem molK_compact (ε : ℝ) (hε : 0 < ε) : HasCompactSupport (molK ε hε : E → ℝ) :=
  (molBump ε hε : ContDiffBump (0 : E)).hasCompactSupport_normed

theorem molK_integral (ε : ℝ) (hε : 0 < ε) : ∫ x, (molK ε hε : E → ℝ) x = 1 :=
  (molBump ε hε : ContDiffBump (0 : E)).integral_normed

theorem molK_integrable (ε : ℝ) (hε : 0 < ε) : Integrable (molK ε hε : E → ℝ) volume :=
  (molBump ε hε : ContDiffBump (0 : E)).integrable_normed

theorem molK_norm_lt (ε : ℝ) (hε : 0 < ε) {y : E} (hy : molK ε hε y ≠ 0) : ‖y‖ < ε := by
  have hs : y ∈ Function.support (molK ε hε : E → ℝ) := hy
  rw [(molBump ε hε : ContDiffBump (0 : E)).support_normed_eq] at hs
  have h : (molBump ε hε : ContDiffBump (0 : E)).rOut = ε := rfl
  simpa only [Metric.mem_ball, dist_zero_right, h] using hs

theorem mol_eq_integral (ε : ℝ) (hε : 0 < ε) (f : E → ℝ) (x : E) :
    mol ε hε f x = ∫ y, molK ε hε (x - y) * f y := by
  simp only [mol, molK, convolution_lsmul_swap, smul_eq_mul]

theorem mol_eq_integral' (ε : ℝ) (hε : 0 < ε) (f : E → ℝ) (x : E) :
    mol ε hε f x = ∫ y, molK ε hε y * f (x - y) := by
  simp only [mol, molK, convolution_lsmul, smul_eq_mul]

theorem mol_integrable (ε : ℝ) (hε : 0 < ε) {f : E → ℝ} (hf : LocallyIntegrable f volume) (x : E) :
    Integrable (fun y => molK ε hε y * f (x - y)) volume :=
  (molK_compact ε hε).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (molK_continuous (E := E) ε hε) hf x

theorem mol_contDiff (ε : ℝ) (hε : 0 < ε) {f : E → ℝ} (hf : LocallyIntegrable f volume) :
    ContDiff ℝ ∞ (mol ε hε f) :=
  (molK_compact ε hε).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (molK_contDiff ε hε) hf

/-- `mol ε f` vanishes outside `B(0,R+ε)` if `f` vanishes a.e. outside `B(0,R)`. -/
theorem mol_eq_zero_of_norm_gt (ε : ℝ) (hε : 0 < ε) {f : E → ℝ} (R : ℝ)
    (hf : ∀ᵐ x ∂(volume : Measure E), R < ‖x‖ → f x = 0) {x : E} (hx : R + ε < ‖x‖) :
    mol ε hε f x = 0 := by
  rw [mol_eq_integral']
  apply integral_eq_zero_of_ae
  have h1 : ∀ᵐ y ∂(volume : Measure E), R < ‖x - y‖ → f (x - y) = 0 :=
    (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae hf
  filter_upwards [h1] with y hy
  by_cases hk : molK ε hε y = 0
  · simp [hk]
  · have h2 := molK_norm_lt ε hε hk
    have : R < ‖x - y‖ := by
      have := norm_sub_norm_le x y
      linarith
    simp [hy this]

theorem mol_hasCompactSupport (ε : ℝ) (hε : 0 < ε) {f : E → ℝ} (R : ℝ)
    (hf : ∀ᵐ x ∂(volume : Measure E), R < ‖x‖ → f x = 0) : HasCompactSupport (mol ε hε f) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : E) (R + ε)) fun x hx => ?_
  apply mol_eq_zero_of_norm_gt ε hε R hf
  simpa [mem_closedBall_zero_iff] using hx

/-- Mollification commutes with weak derivatives (global). -/
theorem fderiv_mol (ε : ℝ) (hε : 0 < ε) {v : E} {f w : E → ℝ}
    (h : HasWDeriv Set.univ v f w) (x : E) :
    fderiv ℝ (mol ε hε f) x v = mol ε hε w x := by
  have hloc : LocallyIntegrable f volume := by
    simpa [locallyIntegrableOn_univ] using h.1
  have hk1 : ContDiff ℝ 1 (molK ε hε : E → ℝ) := (molK_contDiff ε hε).of_le (by exact_mod_cast le_top)
  have hd := (molK_compact ε hε).hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ).flip hloc hk1 x
  have hm : mol ε hε f = f ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] (molK ε hε) :=
    (convolution_flip _).symm
  rw [hm, hd.fderiv, convolution_precompR_apply _ hloc ((molK_compact ε hε).fderiv ℝ)
    ((molK_contDiff ε hε).continuous_fderiv (by simp))]
  -- test function `y ↦ k (x - y)`
  have hφd : ∀ y, HasFDerivAt (fun y => molK ε hε (x - y)) (-(fderiv ℝ (molK ε hε) (x - y))) y := by
    intro y
    have h1 : HasFDerivAt (fun y : E => x - y) (-(ContinuousLinearMap.id ℝ E)) y :=
      (hasFDerivAt_const x y).sub (hasFDerivAt_id y) |>.congr_fderiv (by simp)
    have h2 := ((molK_contDiff ε hε).differentiable (by simp)).differentiableAt.hasFDerivAt
      (x := x - y)
    exact (h2.comp y h1).congr_fderiv (by ext; simp)
  have htest : IsTest Set.univ (fun y => molK ε hε (x - y)) := by
    refine ⟨(molK_contDiff ε hε).comp (contDiff_const.sub contDiff_id), ?_, by simp⟩
    have := (molK_compact ε hε).comp_homeomorph ((Homeomorph.neg E).trans (Homeomorph.addLeft x))
    simpa [Function.comp_def, sub_eq_add_neg, add_comm] using this
  have hw := h.2.2 _ htest
  have hpd : ∀ y, pd v (fun y => molK ε hε (x - y)) y = -(fderiv ℝ (molK ε hε) (x - y) v) := by
    intro y; simp [pd, (hφd y).fderiv]
  simp only [hpd, mul_neg, integral_neg, neg_inj] at hw
  rw [mol_eq_integral]
  simp only [convolution_def, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul]
  calc _ = ∫ a, f a * (fderiv ℝ (molK ε hε) (x - a)) v := by congr 1; ext t; ring
    _ = _ := hw
    _ = _ := by congr 1; ext t; ring

theorem mol_sub (ε : ℝ) (hε : 0 < ε) {f g : E → ℝ} (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) : mol ε hε (f - g) = mol ε hε f - mol ε hε g := by
  funext x
  simp only [Pi.sub_apply, mol_eq_integral', ← integral_sub (mol_integrable ε hε hf x)
    (mol_integrable ε hε hg x)]
  congr 1; ext y; simp [mul_sub]

theorem mol_add (ε : ℝ) (hε : 0 < ε) {f g : E → ℝ} (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) : mol ε hε (f + g) = mol ε hε f + mol ε hε g := by
  funext x
  simp only [Pi.add_apply, mol_eq_integral', ← integral_add (mol_integrable ε hε hf x)
    (mol_integrable ε hε hg x)]
  congr 1; ext y; simp [mul_add]

theorem mol_smul (ε : ℝ) (hε : 0 < ε) (c : ℝ) (f : E → ℝ) :
    mol ε hε (fun x => c * f x) = fun x => c * mol ε hε f x := by
  funext x
  simp only [mol_eq_integral', ← integral_const_mul]
  congr 1; ext y; ring

theorem mol_congr_ae (ε : ℝ) (hε : 0 < ε) {f g : E → ℝ}
    (h : f =ᵐ[(volume : Measure E)] g) : mol ε hε f = mol ε hε g := by
  funext x
  simp only [mol_eq_integral']
  apply integral_congr_ae
  have h1 : ∀ᵐ y ∂(volume : Measure E), f (x - y) = g (x - y) :=
    (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae h
  filter_upwards [h1] with y hy
  rw [hy]

theorem mol_sq_le (ε : ℝ) (hε : 0 < ε) {f : E → ℝ} (hf : MemLp f 2 volume) (x : E) :
    (mol ε hε f x) ^ 2 ≤ ∫ y, molK ε hε y * f (x - y) ^ 2 := by
  have hloc : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  obtain ⟨C, hC⟩ := (molK_compact ε hε).exists_bound_of_continuous (molK_continuous (E := E) ε hε)
  have hb2 : Integrable (fun y => f (x - y) ^ 2) volume := hf.integrable_sq.comp_sub_left x
  have hab : Integrable (fun y => molK ε hε y * f (x - y)) volume := mol_integrable ε hε hloc x
  have hab2 : Integrable (fun y => molK ε hε y * f (x - y) ^ 2) volume :=
    hb2.bdd_mul (molK_continuous (E := E) ε hε).aestronglyMeasurable (Filter.Eventually.of_forall hC)
  set t := mol ε hε f x with ht
  have hnn : 0 ≤ ∫ y, molK ε hε y * (f (x - y) - t) ^ 2 :=
    integral_nonneg fun y => mul_nonneg (molK_nonneg ε hε y) (sq_nonneg _)
  have hexp : (fun y => molK ε hε y * (f (x - y) - t) ^ 2) =
      fun y => molK ε hε y * f (x - y) ^ 2 - (2 * t) * (molK ε hε y * f (x - y)) +
        t ^ 2 * molK ε hε y := by
    ext y; ring
  have h1 : Integrable (fun y => molK ε hε y * f (x - y) ^ 2 -
      (2 * t) * (molK ε hε y * f (x - y))) volume := hab2.sub (hab.const_mul _)
  have h2 : Integrable (fun y => (2 * t) * (molK ε hε y * f (x - y))) volume := hab.const_mul _
  rw [hexp, integral_add h1 ((molK_integrable ε hε).const_mul _),
    integral_sub hab2 h2, integral_const_mul, integral_const_mul,
    molK_integral, ← mol_eq_integral', ← ht] at hnn
  nlinarith

theorem lintegral_ofReal_sq_mol_le (ε : ℝ) (hε : 0 < ε) {f : E → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 volume) :
    ∫⁻ x, ENNReal.ofReal ((mol ε hε f x) ^ 2) ≤ ∫⁻ x, ENNReal.ofReal (f x ^ 2) := by
  have hpoint : ∀ x, ENNReal.ofReal ((mol ε hε f x) ^ 2) ≤
      ∫⁻ y, ENNReal.ofReal (molK ε hε y) * ENNReal.ofReal (f (x - y) ^ 2) := by
    intro x
    obtain ⟨C, hC⟩ := (molK_compact ε hε).exists_bound_of_continuous
      (molK_continuous (E := E) ε hε)
    have hb2 : Integrable (fun y => f (x - y) ^ 2) volume := hf.integrable_sq.comp_sub_left x
    have hab2 : Integrable (fun y => molK ε hε y * f (x - y) ^ 2) volume :=
      hb2.bdd_mul (molK_continuous (E := E) ε hε).aestronglyMeasurable (Filter.Eventually.of_forall hC)
    refine (ENNReal.ofReal_le_ofReal (mol_sq_le ε hε hf x)).trans_eq ?_
    rw [ofReal_integral_eq_lintegral_ofReal hab2
      (Filter.Eventually.of_forall fun y => mul_nonneg (molK_nonneg ε hε y) (sq_nonneg _))]
    congr 1; ext y
    rw [ENNReal.ofReal_mul (molK_nonneg ε hε y)]
  refine (lintegral_mono hpoint).trans ?_
  have hmeas : Measurable (Function.uncurry fun x y : E =>
      ENNReal.ofReal (molK ε hε y) * ENNReal.ofReal (f (x - y) ^ 2)) := by
    have hk := (molK_continuous (E := E) ε hε).measurable
    exact (hk.comp measurable_snd).ennreal_ofReal.mul
      (((hfm.comp (measurable_fst.sub measurable_snd)).pow_const 2).ennreal_ofReal)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have hinner : ∀ y, ∫⁻ x, ENNReal.ofReal (molK ε hε y) * ENNReal.ofReal (f (x - y) ^ 2) =
      ENNReal.ofReal (molK ε hε y) * ∫⁻ x, ENNReal.ofReal (f x ^ 2) := by
    intro y
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    exact lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (f x ^ 2)) y
  simp only [hinner]
  rw [lintegral_mul_const' _ _ (by
    rw [← ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    exact ENNReal.ofReal_ne_top),
    ← ofReal_integral_eq_lintegral_ofReal (molK_integrable ε hε)
      (Filter.Eventually.of_forall (molK_nonneg ε hε)), molK_integral]
  simp

theorem mol_sq_integrable_le (ε : ℝ) (hε : 0 < ε) {f : E → ℝ} (hf : MemLp f 2 volume) :
    Integrable (fun x => (mol ε hε f x) ^ 2) volume ∧
      ∫ x, (mol ε hε f x) ^ 2 ≤ ∫ x, f x ^ 2 := by
  have hf' : f =ᵐ[(volume : Measure E)] hf.aestronglyMeasurable.mk f := hf.aestronglyMeasurable.ae_eq_mk
  have hfm : Measurable (hf.aestronglyMeasurable.mk f) := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hmem : MemLp (hf.aestronglyMeasurable.mk f) 2 volume := hf.ae_eq hf'
  rw [mol_congr_ae ε hε hf']
  have hle := lintegral_ofReal_sq_mol_le ε hε hfm hmem
  have hfin : ∫⁻ x, ENNReal.ofReal (hf.aestronglyMeasurable.mk f x ^ 2) < ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hmem.integrable_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    exact ENNReal.ofReal_lt_top
  have hcont : Continuous (mol ε hε (hf.aestronglyMeasurable.mk f)) :=
    (mol_contDiff ε hε (hmem.locallyIntegrable (by norm_num))).continuous
  have hint : Integrable (fun x => (mol ε hε (hf.aestronglyMeasurable.mk f) x) ^ 2) volume := by
    refine ⟨(hcont.pow 2).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => sq_nonneg _)).2
      (hle.trans_lt hfin)
  refine ⟨hint, ?_⟩
  have hint2 : ∫ x, f x ^ 2 = ∫ x, hf.aestronglyMeasurable.mk f x ^ 2 :=
    integral_congr_ae (by filter_upwards [hf'] with x hx; rw [hx])
  rw [hint2]
  rw [← ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x => sq_nonneg _),
    ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _),
    ofReal_integral_eq_lintegral_ofReal hmem.integrable_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  exact hle

/-- Mollification is `L²`-contractive. -/
theorem memLp_mol (ε : ℝ) (hε : 0 < ε) {f : E → ℝ} (hf : MemLp f 2 volume) :
    MemLp (mol ε hε f) 2 volume := by
  have hloc : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  exact (memLp_two_iff_integrable_sq
    (mol_contDiff ε hε hloc).continuous.aestronglyMeasurable).2 (mol_sq_integrable_le ε hε hf).1

theorem integral_sq_mol_le (ε : ℝ) (hε : 0 < ε) {f : E → ℝ} (hf : MemLp f 2 volume) :
    ∫ x, (mol ε hε f x) ^ 2 ≤ ∫ x, f x ^ 2 :=
  (mol_sq_integrable_le ε hε hf).2

theorem mol_unif_close (g : E → ℝ) (hg : Continuous g) (hc : HasCompactSupport g) {δ : ℝ}
    (hδ : 0 < δ) : ∃ η > 0, ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ η → ∀ x, |mol ε hε g x - g x| ≤ δ := by
  obtain ⟨η, hη, hu⟩ := Metric.uniformContinuous_iff.1
    (hc.uniformContinuous_of_continuous hg) δ hδ
  refine ⟨η, hη, fun ε hε hεη x => ?_⟩
  have h := ContDiffBump.dist_normed_convolution_le (μ := (volume : Measure E))
    (φ := (molBump ε hε : ContDiffBump (0 : E))) (x₀ := x) (ε := δ) (g := g)
    hg.aestronglyMeasurable (fun y hy => by
      have hy' : dist y x < η := by
        have : (molBump ε hε : ContDiffBump (0 : E)).rOut = ε := rfl
        rw [this] at hy
        exact lt_of_lt_of_le (Metric.mem_ball.1 hy) hεη
      exact (hu hy').le)
  rw [← Real.dist_eq]; exact h

theorem integral_sq_mol_sub_le (g : E → ℝ) (hg : Continuous g) (hc : HasCompactSupport g)
    {R δ : ℝ} (hR : ∀ x, R < ‖x‖ → g x = 0) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : ∀ x, |mol ε hε g x - g x| ≤ δ) :
    ∫ x, (mol ε hε g x - g x) ^ 2 ≤
      δ ^ 2 * (volume (Metric.closedBall (0 : E) (R + 1))).toReal := by
  have hae : ∀ᵐ x ∂(volume : Measure E), R < ‖x‖ → g x = 0 := Filter.Eventually.of_forall hR
  have hsm := mol_hasCompactSupport ε hε R hae
  have hmc := (mol_contDiff ε hε (hg.locallyIntegrable)).continuous
  have hmem : MemLp (fun x => mol ε hε g x - g x) 2 volume := by
    simpa only [Pi.sub_def] using (hmc.memLp_of_hasCompactSupport hsm).sub
      (hg.memLp_of_hasCompactSupport hc)
  have hbd : ∀ x, (mol ε hε g x - g x) ^ 2 ≤
      (Metric.closedBall (0 : E) (R + 1)).indicator (fun _ => δ ^ 2) x := by
    intro x
    by_cases hx : x ∈ Metric.closedBall (0 : E) (R + 1)
    · rw [Set.indicator_of_mem hx]
      have := hδ x
      have h0 : 0 ≤ δ := (abs_nonneg _).trans this
      calc _ = |mol ε hε g x - g x| ^ 2 := (sq_abs _).symm
        _ ≤ δ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    · rw [Set.indicator_of_notMem hx]
      have hx' : R + 1 < ‖x‖ := by simpa [mem_closedBall_zero_iff] using hx
      rw [mol_eq_zero_of_norm_gt ε hε R hae (by linarith), hR x (by linarith)]
      simp
  calc ∫ x, (mol ε hε g x - g x) ^ 2
      ≤ ∫ x, (Metric.closedBall (0 : E) (R + 1)).indicator (fun _ => δ ^ 2) x :=
        integral_mono hmem.integrable_sq
          ((integrable_indicator_iff measurableSet_closedBall).2
            (integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne))
          hbd
    _ = _ := by
        rw [integral_indicator_const _ measurableSet_closedBall]
        simp [Measure.real, mul_comm]

theorem integral_sq_le_of_eLpNorm_le {h : E → ℝ} (hh : MemLp h 2 volume) {s : ℝ} (hs : 0 ≤ s)
    (hle : eLpNorm h 2 volume ≤ ENNReal.ofReal s) : ∫ x, h x ^ 2 ≤ s ^ 2 := by
  have hn : ‖hh.toLp h‖ ^ 2 = ∫ x, h x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hh.coeFn_toLp] with x hx
    rw [hx, Real.inner_apply, pow_two]
  rw [← hn, Lp.norm_toLp]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_le_of_le_ofReal hs hle) 2

/-- `L²` convergence of mollifiers. -/
theorem tendsto_integral_sq_mol_sub (f : E → ℝ) (hf : MemLp f 2 volume) :
    Tendsto (fun n : ℕ => ∫ x, (mol (1 / ((n : ℝ) + 1)) (by positivity) f x - f x) ^ 2) atTop
      (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  have hs : 0 < Real.sqrt (η / 16) := Real.sqrt_pos.2 (by positivity)
  have hs2 : Real.sqrt (η / 16) ^ 2 = η / 16 := Real.sq_sqrt (by positivity)
  obtain ⟨g, hgc, hgF, hgcont, hgmem⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le
    (by norm_num : (2 : ENNReal) ≠ ⊤) (ε := ENNReal.ofReal (Real.sqrt (η / 16)))
    (by simpa using hs)
  have hFmem : MemLp (f - g) 2 volume := hf.sub hgmem
  have hF : ∫ x, (f - g) x ^ 2 ≤ η / 16 := by
    have := integral_sq_le_of_eLpNorm_le hFmem hs.le hgF
    rwa [hs2] at this
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : E)
  have hRg : ∀ x : E, R < ‖x‖ → g x = 0 := by
    intro x hx
    by_contra hne
    have : x ∈ tsupport g := subset_tsupport _ hne
    have := hR (by simpa [HasCompactSupport] using this)
    have h2 := mem_closedBall_zero_iff.1 this
    linarith
  set V := (volume (Metric.closedBall (0 : E) (R + 1))).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hδ : 0 < Real.sqrt (η / (6 * (V + 1))) := Real.sqrt_pos.2 (by positivity)
  have hδ2 : Real.sqrt (η / (6 * (V + 1))) ^ 2 = η / (6 * (V + 1)) :=
    Real.sq_sqrt (by positivity)
  obtain ⟨η', hη', hunif⟩ := mol_unif_close g hgcont hgc hδ
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (lt_min hη' one_pos)
  refine ⟨N, fun n hn => ?_⟩
  have hεn : 0 < 1 / ((n : ℝ) + 1) := by positivity
  set ε := 1 / ((n : ℝ) + 1) with hεdef
  have hεle : ε ≤ 1 / ((N : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hεlt := lt_of_le_of_lt hεle hN
  have hf_loc : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  have hg_loc : LocallyIntegrable g volume := hgcont.locallyIntegrable
  have hA : ∫ x, (mol ε hεn g x - g x) ^ 2 ≤ η / 6 := by
    have h1 : ε ≤ 1 := (lt_of_lt_of_le hεlt (min_le_right _ _)).le
    have h2 : ε ≤ η' := (lt_of_lt_of_le hεlt (min_le_left _ _)).le
    refine (integral_sq_mol_sub_le g hgcont hgc hRg (δ := Real.sqrt (η / (6 * (V + 1))))
      ε hεn h1 (hunif ε hεn h2)).trans ?_
    rw [hδ2]
    calc η / (6 * (V + 1)) * V ≤ η / (6 * (V + 1)) * (V + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = η / 6 := by field_simp
  have hB : ∫ x, (mol ε hεn (f - g) x) ^ 2 ≤ η / 16 :=
    (integral_sq_mol_le ε hεn hFmem).trans hF
  have hmolsub : mol ε hεn (f - g) = mol ε hεn f - mol ε hεn g := mol_sub ε hεn hf_loc hg_loc
  -- integrability
  have hmg_c : HasCompactSupport (mol ε hεn g) :=
    mol_hasCompactSupport ε hεn R (Filter.Eventually.of_forall hRg)
  have hmg_cont := (mol_contDiff ε hεn hg_loc).continuous
  have hI1 : Integrable (fun x => (mol ε hεn (f - g) x) ^ 2) volume :=
    (memLp_mol ε hεn hFmem).integrable_sq
  have hI2 : Integrable (fun x => (mol ε hεn g x - g x) ^ 2) volume := by
    have : MemLp (fun x => mol ε hεn g x - g x) 2 volume := by
      simpa only [Pi.sub_def] using (hmg_cont.memLp_of_hasCompactSupport hmg_c).sub hgmem
    exact this.integrable_sq
  have hI3 : Integrable (fun x => (f - g) x ^ 2) volume := hFmem.integrable_sq
  have hmf : MemLp (fun x => mol ε hεn f x - f x) 2 volume := (memLp_mol ε hεn hf).sub hf
  have hpt : ∀ x, (mol ε hεn f x - f x) ^ 2 ≤
      3 * ((mol ε hεn (f - g) x) ^ 2 + (mol ε hεn g x - g x) ^ 2 + (f - g) x ^ 2) := by
    intro x
    have e : mol ε hεn f x - f x =
        mol ε hεn (f - g) x + (mol ε hεn g x - g x) - (f - g) x := by
      rw [hmolsub]; simp
    rw [e]
    nlinarith [sq_nonneg (mol ε hεn (f - g) x - (mol ε hεn g x - g x)),
      sq_nonneg (mol ε hεn (f - g) x + (f - g) x),
      sq_nonneg ((mol ε hεn g x - g x) + (f - g) x)]
  have hI12 : Integrable (fun x => (mol ε hεn (f - g) x) ^ 2 + (mol ε hεn g x - g x) ^ 2)
      volume := hI1.add hI2
  have hsum : Integrable (fun x => (mol ε hεn (f - g) x) ^ 2 + (mol ε hεn g x - g x) ^ 2 +
      (f - g) x ^ 2) volume := hI12.add hI3
  have hint := integral_mono hmf.integrable_sq (hsum.const_mul 3) hpt
  have he : ∫ x, ((mol ε hεn (f - g) x) ^ 2 + (mol ε hεn g x - g x) ^ 2 + (f - g) x ^ 2) =
      (∫ x, (mol ε hεn (f - g) x) ^ 2) + (∫ x, (mol ε hεn g x - g x) ^ 2) +
        ∫ x, (f - g) x ^ 2 := by
    rw [integral_add hI12 hI3, integral_add hI1 hI2]
  rw [integral_const_mul, he] at hint
  have h0 : 0 ≤ ∫ x, (mol ε hεn f x - f x) ^ 2 := integral_nonneg fun x => sq_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith

end CutoffRigidity.Riemann.Diff
