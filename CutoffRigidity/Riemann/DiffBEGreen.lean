module

public import CutoffRigidity.Riemann.DiffBEHess
public import CutoffRigidity.Riemann.DiffMoments

/-! # The Green-type inequality behind Bakry-Emery, `sqrt` version (workstream BE, part B)

For `Φ ≥ 0` and `w` regular enough, with `u = √(Γw + ε)`:
`ρ ∫ Φ (u - √ε) ≤ ∫ (𝓛Φ) u - ∫ Φ Γ(w, 𝓛w) / u`.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Green

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  {V : M → ℝ} {μ : Measure M} [IsFiniteMeasure μ]

theorem msmooth_sqrt_add_pos {G : M → ℝ} (hG : MSmooth F G) (h0 : ∀ y, 0 ≤ G y) {ε : ℝ}
    (hε : 0 < ε) : MSmooth F (fun y => Real.sqrt (G y + ε)) := by
  intro y
  have hpos : G y + ε ≠ 0 := by have := h0 y; positivity
  have hg : ContDiffAt ℝ ∞ (fun v : ℝ => Real.sqrt (v + ε)) (G y) :=
    ContDiffAt.sqrt (by fun_prop) hpos
  exact hg.comp_contMDiffAt (hG y)

/-- Pointwise facts for `u = √(Γw + ε)`. -/
theorem green_pointwise {V : M → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hB : WeightedBochnerIneq F V ρ)
    (hReg : WeightedRegular F V) {w : M → ℝ} (hw : MSmooth F w) {ε : ℝ} (hε : 0 < ε) (x : M) :
    carre F (fun y => Real.sqrt (carre F w w y + ε)) (fun y => Real.sqrt (carre F w w y + ε)) x
        ≤ mHessNormSq F w x ∧
    ρ * (Real.sqrt (carre F w w x + ε) - Real.sqrt ε) ≤
      mgenerator F V (fun y => Real.sqrt (carre F w w y + ε)) x -
        carre F w (mgenerator F V w) x / Real.sqrt (carre F w w x + ε) ∧
    ‖mgrad F w x‖ ≤ Real.sqrt (carre F w w x + ε) := by
  set G := carre F w w with hGdef
  have hG : MSmooth F G := hReg.1 w w hw hw
  have hG0 : ∀ y, 0 ≤ G y := fun y => carre_nonneg F w y
  set u : M → ℝ := fun y => Real.sqrt (G y + ε) with hudef
  have hu : MSmooth F u := msmooth_sqrt_add_pos F hG hG0 hε
  have hux : u x ^ 2 = G x + ε := Real.sq_sqrt (by linarith [hG0 x])
  have hupos : 0 < u x := Real.sqrt_pos.mpr (by linarith [hG0 x])
  have hsq : (fun y => u y ^ 2) = fun y => G y + ε := by
    funext y; exact Real.sq_sqrt (by linarith [hG0 y])
  have hgrad : mgrad F G x = (2 * u x) • mgrad F u x := by
    have e : mgrad F (fun y => u y ^ 2) x = (2 * u x) • mgrad F u x := by
      have := mgrad_mul F hu hu x
      have e2 : (fun y => u y ^ 2) = u * u := by funext z; simp [pow_two]
      rw [e2, this, ← add_smul]; congr 1; ring
    rw [← e, hsq, mgrad_add' F hG contMDiff_const, mgrad_const]; simp
  have hGG : carre F G G x = (2 * u x) ^ 2 * carre F u u x := by
    simp only [carre]
    rw [hgrad, real_inner_smul_left, real_inner_smul_right]; ring
  have hH := mHessNormSq_nonneg F w x
  have hkato : carre F G G x ≤ 4 * (mHessNormSq F w x * G x) := by
    have hk := abs_carre_carre_le F hw G x
    have h1' : carre F G G x ≤ 2 * ‖mgrad F G x‖ * Real.sqrt (mHessNormSq F w x) *
        Real.sqrt (G x) := (le_abs_self _).trans hk
    rw [carre_self_eq] at h1' ⊢
    set n := ‖mgrad F G x‖ with hn
    have h1 : n ^ 2 ≤ 2 * n * Real.sqrt (mHessNormSq F w x) * Real.sqrt (G x) := h1'
    have hs := Real.sqrt_nonneg (mHessNormSq F w x)
    have hs' := Real.sqrt_nonneg (G x)
    have hss : (Real.sqrt (mHessNormSq F w x) * Real.sqrt (G x)) ^ 2 = mHessNormSq F w x * G x := by
      rw [mul_pow, Real.sq_sqrt hH, Real.sq_sqrt (hG0 x)]
    rcases eq_or_lt_of_le (norm_nonneg (mgrad F G x)) with h0 | h0
    · rw [← hn] at h0; rw [← h0]; nlinarith [mul_nonneg hH (hG0 x)]
    · rw [← hn] at h0
      have h2 : n ≤ 2 * (Real.sqrt (mHessNormSq F w x) * Real.sqrt (G x)) := by
        have : n * n ≤ n * (2 * (Real.sqrt (mHessNormSq F w x) * Real.sqrt (G x))) := by
          nlinarith
        exact le_of_mul_le_mul_left this h0
      nlinarith [mul_nonneg hs hs']
  have huu : carre F u u x ≤ mHessNormSq F w x := by
    have h1 : (2 * u x) ^ 2 * carre F u u x ≤ 4 * (mHessNormSq F w x * (u x ^ 2)) := by
      rw [← hGG]; nlinarith [mul_nonneg hH (sq_nonneg (u x))]
    have h2 : u x ^ 2 * carre F u u x ≤ u x ^ 2 * mHessNormSq F w x := by nlinarith
    exact le_of_mul_le_mul_left h2 (by positivity)
  have hLG : mgenerator F V G x = 2 * u x * mgenerator F V u x + 2 * carre F u u x := by
    have := mgenerator_sq F (V := V) hu x
    rw [hsq, mgenerator_add F hG contMDiff_const, mgenerator_const] at this
    simp only [add_zero] at this
    exact this
  have hBx := hB w hw x
  rw [carre2] at hBx
  have hsqe : Real.sqrt ε ≤ u x := Real.sqrt_le_sqrt (by linarith [hG0 x])
  have hsqe2 : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hsqe0 := Real.sqrt_nonneg ε
  refine ⟨huu, ?_, ?_⟩
  · set Q := carre F w (mgenerator F V w) x
    have key : mgenerator F V u x - Q / u x - ρ * (u x - Real.sqrt ε) =
        ((u x * mgenerator F V u x - Q) - ρ * (u x - Real.sqrt ε) * u x) / u x := by
      field_simp
    have h3 : 0 ≤ (u x * mgenerator F V u x - Q) - ρ * (u x - Real.sqrt ε) * u x := by
      have h4 : ρ * (u x - Real.sqrt ε) * u x ≤ ρ * G x := by
        have : ρ * (u x ^ 2 - ε - (u x - Real.sqrt ε) * u x) ≥ 0 := by
          apply mul_nonneg hρ; nlinarith
        nlinarith
      nlinarith
    have := div_nonneg h3 hupos.le
    linarith
  · calc ‖mgrad F w x‖ = Real.sqrt (G x) := by
          rw [hGdef, carre_self_eq, Real.sqrt_sq (norm_nonneg _)]
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)

theorem green_carre_comm (f g : M → ℝ) (x : M) : carre F f g x = carre F g f x :=
  real_inner_comm _ _

theorem integrable_mul_of_sq {f g : M → ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ) : Integrable (fun x => f x * g x) μ := by
  refine (hf2.add hg2).mono' (hf.mul hg) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [sq_abs (f x * g x), sq_nonneg (|f x| - |g x|), abs_mul (f x) (g x),
    sq_abs (f x), sq_abs (g x)]

theorem tendsto_cutoff_integral {χ : ℕ → M → ℝ} (hχ : ∀ n, Continuous (χ n))
    (h01 : ∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1) (hlim : ∀ x, ∀ᶠ n in atTop, χ n x = 1)
    {g : M → ℝ} (hg : Integrable g μ) :
    Tendsto (fun n => ∫ x, χ n x * g x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
    (fun n => (hχ n).aestronglyMeasurable.mul hg.aestronglyMeasurable) hg.norm
    (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (h01 n x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (h01 n x).2
  · refine tendsto_const_nhds.congr' ((hlim x).mono fun n hn => ?_)
    simp [hn]

theorem tendsto_zero_of_bound {f : ℕ → M → ℝ} {D : M → ℝ} (hD : Integrable D μ)
    (hb : ∀ n x, |f n x| ≤ 1 / ((n : ℝ) + 1) * D x) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * ∫ x, D x ∂μ) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (∫ x, D x ∂μ)
  refine squeeze_zero_norm (fun n => ?_) h0
  have := norm_integral_le_of_norm_le (hD.const_mul (1 / ((n : ℝ) + 1)))
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb n x)
  rwa [integral_const_mul] at this

/-- The cutoff identity. -/
theorem cutoff_identity {V : M → ℝ} (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V)
    {χ Φ u : M → ℝ} (hχ : MSmooth F χ) (hχc : HasCompactSupport χ) (hΦ : MSmooth F Φ)
    (hu : MSmooth F u) :
    ∫ x, χ x * (Φ x * mgenerator F V u x) ∂μ =
      ∫ x, χ x * (mgenerator F V Φ x * u x) ∂μ + ∫ x, u x * carre F χ Φ x ∂μ -
        ∫ x, Φ x * carre F χ u x ∂μ := by
  have h1 := hIBP (χ * Φ) u (hχ.mul hΦ) hu (hχc.mul_right)
  have h2 := hIBP (χ * u) Φ (hχ.mul hu) hΦ (hχc.mul_right)
  have hcs : ∀ g : M → ℝ, Continuous g → Integrable (fun x => χ x * g x) μ := fun g hg =>
    integrable_of_cont_cs (hχ.continuous.mul hg)
      (hcs_of_zero hχc (fun x hx => by simp [hx]))
  have T1 : Integrable (fun x => χ x * carre F u Φ x) μ := hcs _ (hReg.1 u Φ hu hΦ).continuous
  have T2 : Integrable (fun x => Φ x * carre F χ u x) μ :=
    integrable_of_cont_cs (hΦ.continuous.mul (hReg.1 χ u hχ hu).continuous)
      ((hasCompactSupport_carre F u hχc).mul_left)
  have T3 : Integrable (fun x => u x * carre F χ Φ x) μ :=
    integrable_of_cont_cs (hu.continuous.mul (hReg.1 χ Φ hχ hΦ).continuous)
      ((hasCompactSupport_carre F Φ hχc).mul_left)
  have p1 : ∀ x, carre F (χ * Φ) u x = χ x * carre F u Φ x + Φ x * carre F χ u x := by
    intro x; rw [carre_mul_left F hχ hΦ, green_carre_comm F Φ u]
  have p2 : ∀ x, carre F (χ * u) Φ x = χ x * carre F u Φ x + u x * carre F χ Φ x := by
    intro x; rw [carre_mul_left F hχ hu, green_carre_comm F u Φ]
  simp only [p1] at h1
  simp only [p2] at h2
  rw [integral_add T1 T2] at h1
  rw [integral_add T1 T3] at h2
  have e1 : ∫ x, χ x * (Φ x * mgenerator F V u x) ∂μ =
      ∫ x, ((χ * Φ) x * mgenerator F V u x) ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  have e2 : ∫ x, χ x * (mgenerator F V Φ x * u x) ∂μ =
      ∫ x, ((χ * u) x * mgenerator F V Φ x) ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  rw [e1, e2]
  linarith

variable (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V) (hC : WeightedCutoffs F M)

include hIBP hReg hC in
/-- **Green-type inequality (sqrt version).**  `Φ ≥ 0` bounded, `Φ ∈ 𝒮`; `w ∈ 𝒮`, `𝓛w ∈ 𝒮`;
`ε > 0`; `u = √(Γw + ε)`.  Then the two integrands are integrable and
`ρ ∫ Φ (u - √ε) ≤ ∫ (𝓛Φ) u - ∫ Φ Γ(w,𝓛w)/u`. -/
theorem green_sqrt {ρ : ℝ} (hρ : 0 ≤ ρ) (hB : WeightedBochnerIneq F V ρ) {ε : ℝ} (hε : 0 < ε)
    {Φ w : M → ℝ} (hΦ0 : ∀ x, 0 ≤ Φ x) (hΦb : ∃ C, ∀ x, Φ x ≤ C) (hΦ : InS F V μ Φ)
    (hw : InS F V μ w) (hLw : InS F V μ (mgenerator F V w)) :
    Integrable (fun x => mgenerator F V Φ x * Real.sqrt (carre F w w x + ε)) μ ∧
    Integrable (fun x => Φ x * (carre F w (mgenerator F V w) x / Real.sqrt (carre F w w x + ε))) μ ∧
    ρ * ∫ x, Φ x * (Real.sqrt (carre F w w x + ε) - Real.sqrt ε) ∂μ ≤
      ∫ x, mgenerator F V Φ x * Real.sqrt (carre F w w x + ε) ∂μ -
      ∫ x, Φ x * (carre F w (mgenerator F V w) x / Real.sqrt (carre F w w x + ε)) ∂μ := by
  have hGint := integrable_carre_of_InS F hIBP hReg hC hw
  have hΦG := integrable_carre_of_InS F hIBP hReg hC hΦ
  have hLwG := integrable_carre_of_InS F hIBP hReg hC hLw
  have hHint := (hess_integrable_of_InS F hIBP hReg hC hρ hB hw).1
  obtain ⟨χ, hχ, hlim⟩ := hC
  obtain ⟨C0, hCb0⟩ := hΦb
  set C := max C0 0 with hCdef
  have hCb : ∀ x, Φ x ≤ C := fun x => (hCb0 x).trans (le_max_left _ _)
  have hC0 : 0 ≤ C := le_max_right _ _
  have hwsm := hw.1
  have hΦsm := hΦ.1
  have hG : MSmooth F (carre F w w) := hReg.1 w w hwsm hwsm
  have hG0 : ∀ y, 0 ≤ carre F w w y := fun y => carre_nonneg F w y
  set u : M → ℝ := fun y => Real.sqrt (carre F w w y + ε) with hudef
  have hu : MSmooth F u := msmooth_sqrt_add_pos F hG hG0 hε
  have hupos : ∀ y, 0 < u y := fun y => Real.sqrt_pos.mpr (by linarith [hG0 y])
  have hu2e : ∀ y, u y ^ 2 = carre F w w y + ε :=
    fun y => Real.sq_sqrt (by linarith [hG0 y])
  have hu2 : Integrable (fun y => u y ^ 2) μ := by
    simp only [hu2e]; exact hGint.add (integrable_const ε)
  have hp : ∀ x, carre F u u x ≤ mHessNormSq F w x ∧
      ρ * (u x - Real.sqrt ε) ≤ mgenerator F V u x -
        carre F w (mgenerator F V w) x / u x ∧ ‖mgrad F w x‖ ≤ u x :=
    fun x => green_pointwise F hρ hB hReg hwsm hε x
  have hLwsm : MSmooth F (mgenerator F V w) := hReg.2.1 w hwsm
  have hLusm : MSmooth F (mgenerator F V u) := hReg.2.1 u hu
  have hLΦsm : MSmooth F (mgenerator F V Φ) := hReg.2.1 Φ hΦsm
  have hΓwLw : MSmooth F (carre F w (mgenerator F V w)) := hReg.1 _ _ hwsm hLwsm
  have hQc : Continuous (fun x => carre F w (mgenerator F V w) x / u x) :=
    hΓwLw.continuous.div hu.continuous (fun y => (hupos y).ne')
  have hs_le : ∀ s : ℝ, s ≤ 1 + s ^ 2 := fun s => by nlinarith [sq_nonneg (s - 1)]
  have hQb : ∀ x, |carre F w (mgenerator F V w) x / u x| ≤
      1 + carre F (mgenerator F V w) (mgenerator F V w) x := by
    intro x
    rw [abs_div, abs_of_pos (hupos x), div_le_iff₀ (hupos x)]
    have h1 := abs_carre_le F w (mgenerator F V w) x
    have h2 := (hp x).2.2
    have h3 : ‖mgrad F (mgenerator F V w) x‖ ≤ 1 + carre F (mgenerator F V w)
        (mgenerator F V w) x := by
      rw [carre_self_eq]; exact hs_le _
    have h4 := norm_nonneg (mgrad F (mgenerator F V w) x)
    have h5 := (hupos x).le
    calc |carre F w (mgenerator F V w) x|
        ≤ ‖mgrad F w x‖ * ‖mgrad F (mgenerator F V w) x‖ := h1
      _ ≤ u x * ‖mgrad F (mgenerator F V w) x‖ := by gcongr
      _ ≤ u x * (1 + carre F (mgenerator F V w) (mgenerator F V w) x) := by gcongr
      _ = _ := by ring
  have hub : ∀ x, ‖mgrad F u x‖ ≤ 1 + mHessNormSq F w x := by
    intro x
    refine (hs_le _).trans ?_
    rw [← carre_self_eq]
    linarith [(hp x).1]
  have hI1 : Integrable (fun x => mgenerator F V Φ x * u x) μ :=
    integrable_mul_of_sq hLΦsm.continuous.aestronglyMeasurable hu.continuous.aestronglyMeasurable
      hΦ.2.2.integrable_sq hu2
  have hI2 : Integrable (fun x => Φ x * (carre F w (mgenerator F V w) x / u x)) μ := by
    refine (((integrable_const (1 : ℝ)).add hLwG).const_mul C).mono'
      (hΦsm.continuous.mul hQc).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hΦ0 x)]
    have := hQb x
    have := hCb x
    have := hΦ0 x
    simp only [Pi.add_apply]
    nlinarith [abs_nonneg (carre F w (mgenerator F V w) x / u x)]
  have hsqe : ∀ x, Real.sqrt ε ≤ u x := fun x => Real.sqrt_le_sqrt (by linarith [hG0 x])
  have hI3 : Integrable (fun x => Φ x * (u x - Real.sqrt ε)) μ := by
    refine (((integrable_const (1 : ℝ)).add hu2).const_mul C).mono'
      (hΦsm.continuous.mul (hu.continuous.sub continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have h1 := hsqe x
    have h2 := Real.sqrt_nonneg ε
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hΦ0 x) (by linarith))]
    simp only [Pi.add_apply]
    nlinarith [hCb x, hΦ0 x, sq_nonneg (u x - 1)]
  have hcut : ∀ n, ρ * ∫ x, χ n x * (Φ x * (u x - Real.sqrt ε)) ∂μ ≤
      ∫ x, χ n x * (mgenerator F V Φ x * u x) ∂μ + ∫ x, u x * carre F (χ n) Φ x ∂μ
        - ∫ x, Φ x * carre F (χ n) u x ∂μ
        - ∫ x, χ n x * (Φ x * (carre F w (mgenerator F V w) x / u x)) ∂μ := by
    intro n
    obtain ⟨hcsm, hcc, hc01⟩ := hχ n
    have hcs : ∀ g : M → ℝ, Continuous g → Integrable (fun x => χ n x * g x) μ := fun g hg =>
      integrable_of_cont_cs (hcsm.continuous.mul hg)
        (hcs_of_zero hcc (fun x hx => by simp [hx]))
    have hA := hcs (fun x => Φ x * mgenerator F V u x) (hΦsm.continuous.mul hLusm.continuous)
    have hQ := hcs (fun x => Φ x * (carre F w (mgenerator F V w) x / u x))
      (hΦsm.continuous.mul hQc)
    have hR := hcs (fun x => Φ x * (u x - Real.sqrt ε))
      (hΦsm.continuous.mul (hu.continuous.sub continuous_const))
    have hD := hcs (fun x => Φ x * (mgenerator F V u x -
        carre F w (mgenerator F V w) x / u x))
      (hΦsm.continuous.mul (hLusm.continuous.sub hQc))
    have hmono : ∫ x, ρ * (χ n x * (Φ x * (u x - Real.sqrt ε))) ∂μ ≤
        ∫ x, χ n x * (Φ x * (mgenerator F V u x -
          carre F w (mgenerator F V w) x / u x)) ∂μ := by
      refine integral_mono (hR.const_mul ρ) hD (fun x => ?_)
      have h1 := mul_le_mul_of_nonneg_left (hp x).2.1 (mul_nonneg (hc01 x).1 (hΦ0 x))
      simp only
      nlinarith [h1]
    have hsub : ∫ x, χ n x * (Φ x * (mgenerator F V u x -
          carre F w (mgenerator F V w) x / u x)) ∂μ =
        ∫ x, χ n x * (Φ x * mgenerator F V u x) ∂μ -
          ∫ x, χ n x * (Φ x * (carre F w (mgenerator F V w) x / u x)) ∂μ := by
      rw [← integral_sub hA hQ]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
    have hid := cutoff_identity F hIBP hReg hcsm hcc hΦsm hu
    rw [integral_const_mul] at hmono
    linarith
  have hch : ∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1 := fun n x => ⟨((hχ n).2.2 x).1, ((hχ n).2.2 x).2.1⟩
  have hcont : ∀ n, Continuous (χ n) := fun n => (hχ n).1.continuous
  have hδ : ∀ n x, ‖mgrad F (χ n) x‖ ≤ 1 / ((n : ℝ) + 1) := fun n x => ((hχ n).2.2 x).2.2
  have hδ0 : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) + 1) := fun n => by positivity
  have tB := tendsto_cutoff_integral hcont hch hlim hI1
  have tQ := tendsto_cutoff_integral hcont hch hlim hI2
  have tC := tendsto_cutoff_integral hcont hch hlim hI3
  have tE1 : Tendsto (fun n => ∫ x, u x * carre F (χ n) Φ x ∂μ) atTop (𝓝 0) := by
    refine tendsto_zero_of_bound (D := fun x => u x ^ 2 + carre F Φ Φ x) (hu2.add hΦG)
      (fun n x => ?_)
    have h1 := abs_carre_le F (χ n) Φ x
    have h2 := mul_le_mul (hδ n x) le_rfl (norm_nonneg (mgrad F Φ x)) (hδ0 n)
    have h3 : ‖mgrad F Φ x‖ ^ 2 = carre F Φ Φ x := (carre_self_eq F Φ x).symm
    have h4 := hupos x
    rw [abs_mul, abs_of_pos h4]
    have h5 : u x * |carre F (χ n) Φ x| ≤ u x * (1 / ((n : ℝ) + 1) * ‖mgrad F Φ x‖) :=
      mul_le_mul_of_nonneg_left (h1.trans h2) h4.le
    refine h5.trans ?_
    have h6 : u x * ‖mgrad F Φ x‖ ≤ u x ^ 2 + carre F Φ Φ x := by
      rw [← h3]; nlinarith [sq_nonneg (u x - ‖mgrad F Φ x‖), norm_nonneg (mgrad F Φ x)]
    calc u x * (1 / ((n : ℝ) + 1) * ‖mgrad F Φ x‖)
        = 1 / ((n : ℝ) + 1) * (u x * ‖mgrad F Φ x‖) := by ring
      _ ≤ _ := by gcongr
  have tE2 : Tendsto (fun n => ∫ x, Φ x * carre F (χ n) u x ∂μ) atTop (𝓝 0) := by
    refine tendsto_zero_of_bound (D := fun x => C * (1 + mHessNormSq F w x))
      (((integrable_const (1 : ℝ)).add hHint).const_mul C) (fun n x => ?_)
    have h1 := abs_carre_le F (χ n) u x
    have h2 := mul_le_mul (hδ n x) (hub x) (norm_nonneg (mgrad F u x)) (hδ0 n)
    rw [abs_mul, abs_of_nonneg (hΦ0 x)]
    have h5 : Φ x * |carre F (χ n) u x| ≤
        Φ x * (1 / ((n : ℝ) + 1) * (1 + mHessNormSq F w x)) :=
      mul_le_mul_of_nonneg_left (h1.trans h2) (hΦ0 x)
    refine h5.trans ?_
    have h7 : 0 ≤ 1 / ((n : ℝ) + 1) * (1 + mHessNormSq F w x) :=
      mul_nonneg (hδ0 n) (by linarith [mHessNormSq_nonneg F w x])
    calc Φ x * (1 / ((n : ℝ) + 1) * (1 + mHessNormSq F w x))
        ≤ C * (1 / ((n : ℝ) + 1) * (1 + mHessNormSq F w x)) := by gcongr; exact hCb x
      _ = _ := by ring
  have hlimit := le_of_tendsto_of_tendsto' (tC.const_mul ρ)
    (((tB.add tE1).sub tE2).sub tQ) hcut
  simp only [add_zero, sub_zero] at hlimit
  exact ⟨hI1, hI2, hlimit⟩


end Green

end CutoffRigidity.Riemann.Diff
