module

public import CutoffRigidity.Riemann.DiffKer
public import CutoffRigidity.Riemann.DiffTight
public import CutoffRigidity.Riemann.DiffAPI
public import CutoffRigidity.Riemann.WeightedRigidity
public import CutoffRigidity.Riemann.WeightedIBPGlobal
public import CutoffRigidity.Riemann.WeightedBochnerMain
public import CutoffRigidity.Riemann.WeightedCutoffs
public import CutoffRigidity.Riemann.WeightedRegular

/-! # Integrated calculus on the class `𝒮 = {w smooth, w ∈ L², 𝓛w ∈ L²}` (workstream BE, part A)

Abstract (no semigroup) statements, under the four geometric inputs `WeightedIBP`,
`WeightedRegular`, `WeightedBochnerIneq`, `WeightedCutoffs`.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section ClassS

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  {V : M → ℝ} {μ : Measure M} [IsFiniteMeasure μ]

/-- The class `𝒮`: smooth, `w ∈ L²(μ)` and `𝓛w ∈ L²(μ)`. -/
def InS (V : M → ℝ) (μ : Measure M) (w : M → ℝ) : Prop :=
  MSmooth F w ∧ MemLp w 2 μ ∧ MemLp (mgenerator F V w) 2 μ

/-- Smooth functions which are bounded with bounded generator are in `𝒮`. -/
theorem InS.of_bounded (hReg : WeightedRegular F V) {w : M → ℝ} (hw : MSmooth F w)
    (b1 : ∃ C, ∀ x, |w x| ≤ C) (b2 : ∃ C, ∀ x, |mgenerator F V w x| ≤ C) : InS F V μ w := by
  obtain ⟨C1, h1⟩ := b1
  obtain ⟨C2, h2⟩ := b2
  refine ⟨hw, MemLp.of_bound hw.continuous.aestronglyMeasurable C1
    (Eventually.of_forall fun x => by simpa using h1 x),
    MemLp.of_bound (hReg.2.1 w hw).continuous.aestronglyMeasurable C2
    (Eventually.of_forall fun x => by simpa using h2 x)⟩

/-- `1/(n+1) ≤ 1`. -/
theorem one_div_succ_le_one (n : ℕ) : 1 / ((n : ℝ) + 1) ≤ 1 := by
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]

/-- Caccioppoli inequality for functions of the class `𝒮`. -/
theorem cacc_S {V w χ : M → ℝ} (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V)
    (hw : MSmooth F w) (hw2 : Integrable (fun x => w x ^ 2) μ)
    (hwL : Integrable (fun x => w x * mgenerator F V w x) μ)
    (hχ : MSmooth F χ) (hχc : HasCompactSupport χ) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχg : ∀ x, ‖mgrad F χ x‖ ≤ 1) :
    ∫ x, χ x ^ 2 * carre F w w x ∂μ ≤
      2 * (∫ x, |w x * mgenerator F V w x| ∂μ + 2 * ∫ x, w x ^ 2 ∂μ) := by
  have hG : MSmooth F (carre F w w) := hReg.1 w w hw hw
  have hLw : MSmooth F (mgenerator F V w) := hReg.2.1 w hw
  have hχχ : MSmooth F (χ * χ) := hχ.mul hχ
  have hu : MSmooth F ((χ * χ) * w) := hχχ.mul hw
  have huc : HasCompactSupport ((χ * χ) * w) := (hχc.mul_right.mul_right)
  have hibp := hIBP ((χ * χ) * w) w hu hw huc
  have hpt : ∀ x, carre F ((χ * χ) * w) w x =
      χ x ^ 2 * carre F w w x + 2 * (w x * (χ x * carre F χ w x)) := by
    intro x
    rw [carre_mul_left F hχχ hw x, carre_mul_left F hχ hχ x]
    simp only [Pi.mul_apply]; ring
  have hint_uf : Integrable (fun x => carre F ((χ * χ) * w) w x) μ :=
    integrable_of_cont_cs (hReg.1 _ _ hu hw).continuous (hasCompactSupport_carre F w huc)
  have hint_G : Integrable (fun x => χ x ^ 2 * carre F w w x) μ :=
    integrable_cutoff_sq_mul hχ.continuous hχc hG.continuous
  have hint_uLw : Integrable (fun x => ((χ * χ) * w) x * mgenerator F V w x) μ := by
    refine integrable_of_cont_cs (hu.continuous.mul hLw.continuous) ?_
    exact hcs_of_zero hχc (fun x hx => by simp [hx])
  have hpw : ∀ x, χ x ^ 2 * carre F w w x / 2 ≤ carre F ((χ * χ) * w) w x + 2 * w x ^ 2 := by
    intro x
    rw [hpt x]
    obtain ⟨h0, h1⟩ := hχ01 x
    set s := Real.sqrt (carre F w w x) with hs
    have hs2 : s ^ 2 = carre F w w x := Real.sq_sqrt (carre_nonneg F w x)
    have hgs : ‖mgrad F w x‖ = s := by
      rw [hs, carre_self_eq, Real.sqrt_sq (norm_nonneg _)]
    have hc : |carre F χ w x| ≤ s := by
      refine (abs_carre_le F χ w x).trans ?_
      rw [hgs]
      calc ‖mgrad F χ x‖ * s ≤ 1 * s := by gcongr; exact hχg x
        _ = s := one_mul s
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have habs : |w x * (χ x * carre F χ w x)| ≤ |w x| * (χ x * s) := by
      rw [abs_mul, abs_mul, abs_of_nonneg h0]
      gcongr
    have hlow := neg_abs_le (w x * (χ x * carre F χ w x))
    rw [← hs2]
    nlinarith [sq_nonneg (χ x * s - 2 * |w x|), sq_abs (w x)]
  have h1 : ∫ x, χ x ^ 2 * carre F w w x / 2 ∂μ ≤
      ∫ x, (carre F ((χ * χ) * w) w x + 2 * w x ^ 2) ∂μ :=
    integral_mono (hint_G.div_const 2) (hint_uf.add (hw2.const_mul 2)) hpw
  have h2 : ∫ x, (carre F ((χ * χ) * w) w x + 2 * w x ^ 2) ∂μ =
      ∫ x, carre F ((χ * χ) * w) w x ∂μ + 2 * ∫ x, w x ^ 2 ∂μ := by
    rw [integral_add hint_uf (hw2.const_mul 2), integral_const_mul]
  have h3 : -∫ x, ((χ * χ) * w) x * mgenerator F V w x ∂μ ≤
      ∫ x, |w x * mgenerator F V w x| ∂μ := by
    rw [← integral_neg]
    refine integral_mono hint_uLw.neg hwL.abs fun x => ?_
    obtain ⟨h0, h1⟩ := hχ01 x
    have hc : (χ * χ) x ≤ 1 := by simp only [Pi.mul_apply]; nlinarith
    have hc0 : 0 ≤ (χ * χ) x := by simp only [Pi.mul_apply]; positivity
    have e : ((χ * χ) * w) x * mgenerator F V w x = (χ * χ) x * (w x * mgenerator F V w x) := by
      simp only [Pi.mul_apply]; ring
    rw [e]
    have : |(χ * χ) x * (w x * mgenerator F V w x)| ≤ |w x * mgenerator F V w x| := by
      rw [abs_mul, abs_of_nonneg hc0]
      exact mul_le_of_le_one_left (abs_nonneg _) hc
    linarith [neg_abs_le ((χ * χ) x * (w x * mgenerator F V w x))]
  have h4 : ∫ x, χ x ^ 2 * carre F w w x / 2 ∂μ = (∫ x, χ x ^ 2 * carre F w w x ∂μ) / 2 := by
    rw [integral_div]
  rw [h4, h2, hibp] at h1
  linarith

variable (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V) (hC : WeightedCutoffs F M)

include hIBP hReg hC in
/-- (A1) `Γw ∈ L¹` for `w ∈ 𝒮`. -/
theorem integrable_carre_of_InS {w : M → ℝ} (hw : InS F V μ w) :
    Integrable (fun x => carre F w w x) μ := by
  obtain ⟨χ, hχ, hlim⟩ := hC
  obtain ⟨hws, hw2, hwL2⟩ := hw
  have hf2 : Integrable (fun x => w x ^ 2) μ := hw2.integrable_sq
  have hwL : Integrable (fun x => w x * mgenerator F V w x) μ := hw2.integrable_mul hwL2
  have hG : MSmooth F (carre F w w) := hReg.1 w w hws hws
  set K := 2 * (∫ x, |w x * mgenerator F V w x| ∂μ + 2 * ∫ x, w x ^ 2 ∂μ) with hK
  have hχ1 : ∀ n x, ‖mgrad F (χ n) x‖ ≤ 1 := fun n x =>
    ((hχ n).2.2 x).2.2.trans (one_div_succ_le_one n)
  have hcacc : ∀ n, ∫ x, χ n x ^ 2 * carre F w w x ∂μ ≤ K := fun n =>
    cacc_S F hIBP hReg hws hf2 hwL (hχ n).1 (hχ n).2.1 (fun x => ⟨((hχ n).2.2 x).1,
      ((hχ n).2.2 x).2.1⟩) (hχ1 n)
  have hmeasG : ∀ n, Measurable (fun x => χ n x ^ 2 * carre F w w x) := fun n =>
    ((hχ n).1.continuous.pow 2 |>.mul hG.continuous).measurable
  have hev : ∀ x, ∀ᶠ n in atTop, χ n x ^ 2 * carre F w w x = carre F w w x := by
    intro x
    filter_upwards [hlim x] with n hn
    simp [hn]
  have hlinG : ∫⁻ x, ENNReal.ofReal (carre F w w x) ∂μ ≤ ENNReal.ofReal K := by
    refine lintegral_ofReal_le_of_approx (h := fun n x => χ n x ^ 2 * carre F w w x) hmeasG hev
      (b := fun _ => ENNReal.ofReal K) ?_ tendsto_const_nhds
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_cutoff_sq_mul (hχ n).1.continuous (hχ n).2.1 hG.continuous)
      (Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (carre_nonneg F w x))]
    exact ENNReal.ofReal_le_ofReal (hcacc n)
  refine ⟨hG.continuous.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (carre_nonneg F w))]
  exact lt_of_le_of_lt hlinG ENNReal.ofReal_lt_top

include hIBP hReg hC in
/-- (A2) Integration by parts on `𝒮`: `u` smooth, `u ∈ L²`, `Γu ∈ L¹`, `v ∈ 𝒮`:
`Γ(u,v) ∈ L¹` and `∫Γ(u,v) = -∫ u 𝓛v`. -/
theorem integral_carre_cross {u v : M → ℝ} (hu : MSmooth F u) (hu2 : MemLp u 2 μ)
    (hGu : Integrable (fun x => carre F u u x) μ) (hv : InS F V μ v) :
    Integrable (fun x => carre F u v x) μ ∧
      ∫ x, carre F u v x ∂μ = -∫ x, u x * mgenerator F V v x ∂μ := by
  obtain ⟨χ, hχ, hlim⟩ := hC
  have hv' := hv
  obtain ⟨hvs, hv2, hvL2⟩ := hv
  have hGv : Integrable (fun x => carre F v v x) μ := integrable_carre_of_InS F hIBP hReg ⟨χ, hχ, hlim⟩ hv'
  have hLv : MSmooth F (mgenerator F V v) := hReg.2.1 v hvs
  have hcuv : Continuous (carre F u v) := (hReg.1 u v hu hvs).continuous
  -- AM-GM bound
  have amgm : ∀ x, |u x| * ‖mgrad F v x‖ ≤ (u x ^ 2 + carre F v v x) / 2 := by
    intro x
    rw [carre_self_eq]
    nlinarith [sq_nonneg (|u x| - ‖mgrad F v x‖), sq_abs (u x)]
  have hD : Integrable (fun x => (u x ^ 2 + carre F v v x) / 2) μ :=
    (hu2.integrable_sq.add hGv).div_const 2
  have hΓuv : Integrable (fun x => carre F u v x) μ := by
    refine Integrable.mono' ((hGu.add hGv).div_const 2) hcuv.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_carre_le F u v x).trans ?_
    simp only [Pi.add_apply, carre_self_eq F u, carre_self_eq F v]
    nlinarith [sq_nonneg (‖mgrad F u x‖ - ‖mgrad F v x‖)]
  refine ⟨hΓuv, ?_⟩
  have hχ0 : ∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1 := fun n x => ⟨((hχ n).2.2 x).1, ((hχ n).2.2 x).2.1⟩
  -- the integrated identity for each cutoff
  have hid : ∀ n, ∫ x, χ n x * carre F u v x ∂μ + ∫ x, u x * carre F (χ n) v x ∂μ
      = -∫ x, χ n x * u x * mgenerator F V v x ∂μ := by
    intro n
    have hib := hIBP (χ n * u) v ((hχ n).1.mul hu) hvs ((hχ n).2.1.mul_right)
    have hI1 : Integrable (fun x => χ n x * carre F u v x) μ := by
      refine Integrable.mono' hΓuv.norm
        (((hχ n).1.continuous.mul hcuv).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hχ0 n x).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχ0 n x).2
    have hI2 : Integrable (fun x => u x * carre F (χ n) v x) μ :=
      integrable_of_cont_cs (hu.continuous.mul (hReg.1 _ _ (hχ n).1 hvs).continuous)
        ((hasCompactSupport_carre F v (hχ n).2.1).mul_left)
    rw [← integral_add hI1 hI2]
    have : ∀ x, χ n x * carre F u v x + u x * carre F (χ n) v x = carre F (χ n * u) v x := by
      intro x; rw [carre_mul_left F (hχ n).1 hu x]
    simp_rw [this]
    rw [hib]
    congr 1
  -- limits
  have T1 : Tendsto (fun n => ∫ x, χ n x * carre F u v x ∂μ) atTop
      (𝓝 (∫ x, carre F u v x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖carre F u v x‖)
      (fun n => ((hχ n).1.continuous.mul hcuv).aestronglyMeasurable) hΓuv.norm
      (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hχ0 n x).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχ0 n x).2
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hlim x] with n hn
      simp [hn]
  have hint3 : Integrable (fun x => u x * mgenerator F V v x) μ := hu2.integrable_mul hvL2
  have T3 : Tendsto (fun n => ∫ x, χ n x * u x * mgenerator F V v x ∂μ) atTop
      (𝓝 (∫ x, u x * mgenerator F V v x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖u x * mgenerator F V v x‖)
      (fun n => (((hχ n).1.continuous.mul hu.continuous).mul hLv.continuous).aestronglyMeasurable)
      hint3.norm (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [mul_assoc, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hχ0 n x).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχ0 n x).2
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hlim x] with n hn
      simp [hn]
  have T2 : Tendsto (fun n => ∫ x, u x * carre F (χ n) v x ∂μ) atTop (𝓝 0) := by
    refine squeeze_zero_norm (f := fun n => ∫ x, u x * carre F (χ n) v x ∂μ)
      (a := fun n : ℕ => 1 / ((n : ℝ) + 1) * ∫ x, (u x ^ 2 + carre F v v x) / 2 ∂μ)
      (fun n => ?_) ?_
    · rw [← integral_const_mul]
      refine norm_integral_le_of_norm_le (hD.const_mul _) (Eventually.of_forall fun x => ?_)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |carre F (χ n) v x| ≤ 1 / ((n : ℝ) + 1) * ‖mgrad F v x‖ :=
        (abs_carre_le F (χ n) v x).trans (by gcongr; exact ((hχ n).2.2 x).2.2)
      calc |u x| * |carre F (χ n) v x| ≤ |u x| * (1 / ((n : ℝ) + 1) * ‖mgrad F v x‖) := by gcongr
        _ = 1 / ((n : ℝ) + 1) * (|u x| * ‖mgrad F v x‖) := by ring
        _ ≤ _ := by gcongr; exact amgm x
    · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
        (∫ x, (u x ^ 2 + carre F v v x) / 2 ∂μ)
  have hT : Tendsto (fun n => ∫ x, χ n x * carre F u v x ∂μ) atTop
      (𝓝 (-∫ x, u x * mgenerator F V v x ∂μ)) := by
    have := (T3.neg).sub T2
    simp only [sub_zero] at this
    refine this.congr fun n => ?_
    have := hid n
    linarith
  exact tendsto_nhds_unique T1 hT

include hIBP hReg hC in
/-- (A6) Poincaré inequality extends from test functions to `𝒮`. -/
theorem poincare_of_InS {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hP : ∀ f : M → ℝ, MSmooth F f → HasCompactSupport f →
      ρ * variance f μ ≤ ∫ x, carre F f f x ∂μ)
    {v : M → ℝ} (hv : InS F V μ v) :
    ρ * variance v μ ≤ ∫ x, carre F v v x ∂μ := by
  obtain ⟨χ, hχ, hlim⟩ := hC
  have hv' := hv
  obtain ⟨hvs, hv2, hvL2⟩ := hv
  have hGv : Integrable (fun x => carre F v v x) μ :=
    integrable_carre_of_InS F hIBP hReg ⟨χ, hχ, hlim⟩ hv'
  have hv1 : Integrable v μ := hv2.integrable (by norm_num)
  have hv22 : Integrable (fun x => v x ^ 2) μ := hv2.integrable_sq
  have hχ0 : ∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1 := fun n x => ⟨((hχ n).2.2 x).1, ((hχ n).2.2 x).2.1⟩
  have hgs : ∀ n, MSmooth F (χ n * v) := fun n => (hχ n).1.mul hvs
  have hgc : ∀ n, HasCompactSupport (χ n * v) := fun n => (hχ n).2.1.mul_right
  have hgle : ∀ n x, ‖(χ n * v) x‖ ≤ ‖v x‖ := by
    intro n x
    simp only [Pi.mul_apply, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hχ0 n x).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (hχ0 n x).2
  have hgl : ∀ x, Tendsto (fun n => (χ n * v) x) atTop (𝓝 (v x)) := by
    intro x
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hlim x] with n hn
    simp [hn]
  have hgint : ∀ n, Integrable (χ n * v) μ := fun n =>
    hv1.norm.mono' (hgs n).continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => hgle n x)
  -- means
  have Tc : Tendsto (fun n => ∫ x, (χ n * v) x ∂μ) atTop (𝓝 (∫ x, v x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => ‖v x‖)
      (fun n => (hgs n).continuous.aestronglyMeasurable) hv1.norm
      (fun n => Eventually.of_forall (hgle n)) (Eventually.of_forall hgl)
  have hcb : ∀ n, |∫ x, (χ n * v) x ∂μ| ≤ ∫ x, ‖v x‖ ∂μ := fun n => by
    simpa using norm_integral_le_of_norm_le hv1.norm (Eventually.of_forall (hgle n))
  -- variances
  have Tvar : Tendsto (fun n => variance (χ n * v) μ) atTop (𝓝 (variance v μ)) := by
    have e : ∀ f : M → ℝ, Continuous f → variance f μ = ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ :=
      fun f hf => variance_eq_integral hf.aestronglyMeasurable.aemeasurable
    rw [e v hvs.continuous]
    simp_rw [e _ (hgs _).continuous]
    refine tendsto_integral_of_dominated_convergence
      (fun x => 2 * v x ^ 2 + 2 * (∫ x, ‖v x‖ ∂μ) ^ 2)
      (fun n => (((hgs n).continuous.sub continuous_const).pow 2).aestronglyMeasurable)
      (hv22.const_mul 2 |>.add (integrable_const _))
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 := hgle n x
      have h2 := hcb n
      have h3 : (χ n * v) x ^ 2 ≤ v x ^ 2 :=
        sq_le_sq.mpr (by rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]; exact h1)
      have h4 : (∫ y, (χ n * v) y ∂μ) ^ 2 ≤ (∫ x, ‖v x‖ ∂μ) ^ 2 :=
        sq_le_sq.mpr (h2.trans (le_abs_self _))
      nlinarith [sq_nonneg ((χ n * v) x + ∫ y, (χ n * v) y ∂μ)]
    · exact ((hgl x).sub Tc).pow 2
  -- energies
  have Tgam : Tendsto (fun n => ∫ x, carre F (χ n * v) (χ n * v) x ∂μ) atTop
      (𝓝 (∫ x, carre F v v x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => 2 * carre F v v x + 2 * v x ^ 2)
      (fun n => (hReg.1 _ _ (hgs n) (hgs n)).continuous.aestronglyMeasurable)
      ((hGv.const_mul 2).add (hv22.const_mul 2))
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (carre_nonneg F _ x), carre_self_eq,
        mgrad_mul F (hχ n).1 hvs x, carre_self_eq F v]
      have hq : ‖mgrad F (χ n) x‖ ≤ 1 := ((hχ n).2.2 x).2.2.trans (one_div_succ_le_one n)
      have h1 : ‖χ n x • mgrad F v x + v x • mgrad F (χ n) x‖ ≤ ‖mgrad F v x‖ + |v x| := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (hχ0 n x).1]
        have a1 : χ n x * ‖mgrad F v x‖ ≤ ‖mgrad F v x‖ :=
          mul_le_of_le_one_left (norm_nonneg _) (hχ0 n x).2
        have a2 : |v x| * ‖mgrad F (χ n) x‖ ≤ |v x| := mul_le_of_le_one_right (abs_nonneg _) hq
        linarith
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (‖mgrad F v x‖ - |v x|), sq_abs (v x)]
    · have hq : Tendsto (fun n => v x • mgrad F (χ n) x) atTop (𝓝 0) := by
        refine squeeze_zero_norm (a := fun n : ℕ => |v x| * (1 / ((n : ℝ) + 1)))
          (fun n => ?_) ?_
        · rw [norm_smul, Real.norm_eq_abs]
          gcongr
          exact ((hχ n).2.2 x).2.2
        · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul |v x|
      have hp : Tendsto (fun n => χ n x • mgrad F v x) atTop (𝓝 (mgrad F v x)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hlim x] with n hn
        simp [hn]
      have := (hp.add hq).norm.pow 2
      simp only [add_zero] at this
      rw [carre_self_eq F v]
      refine this.congr fun n => ?_
      rw [carre_self_eq, mgrad_mul F (hχ n).1 hvs x]
  have hle : ∀ n, ρ * variance (χ n * v) μ ≤ ∫ x, carre F (χ n * v) (χ n * v) x ∂μ :=
    fun n => hP _ (hgs n) (hgc n)
  exact le_of_tendsto_of_tendsto (Tvar.const_mul ρ) Tgam (Eventually.of_forall hle)

end ClassS

end CutoffRigidity.Riemann.Diff
