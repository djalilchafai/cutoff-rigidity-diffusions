module

public import CutoffRigidity.Riemann.DiffBESemi
public import CutoffRigidity.Riemann.DiffDynkinBounded

/-! # de Bruijn identity for the canonical semigroup (workstream BE, LSI part b) -/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Bruijn

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} {μ : Measure M} [IsFiniteMeasure μ] {Kk : ℝ≥0 → Kernel M M}

/-- `E_δ(s) = ∫ h_s log h_s dμ` with `h_s = K_s g + δ`. -/
noncomputable def entFun (Kk : ℝ≥0 → Kernel M M) (μ : Measure M) (g : M → ℝ) (δ : ℝ) (s : ℝ) : ℝ :=
  ∫ x, (semi Kk s.toNNReal g x + δ) * Real.log (semi Kk s.toNNReal g x + δ) ∂μ

/-- `log` is bounded on `[δ, B]`. -/
theorem abs_log_le_of_mem {δ B y : ℝ} (hδ : 0 < δ) (h1 : δ ≤ y) (h2 : y ≤ B) :
    |Real.log y| ≤ |Real.log δ| + |Real.log B| := by
  have hy : 0 < y := lt_of_lt_of_le hδ h1
  have a := Real.log_le_log hδ h1
  have b := Real.log_le_log hy h2
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log B), neg_abs_le (Real.log δ),
    abs_nonneg (Real.log δ), abs_nonneg (Real.log B), neg_abs_le (Real.log B)]

/-- `log ∘ h + 1` is smooth when `h > 0`. -/
theorem msmooth_log_add_one {h : M → ℝ} (hh : MSmooth F h) (hpos : ∀ y, 0 < h y) :
    MSmooth F (fun y => Real.log (h y) + 1) := by
  have : MSmooth F (fun y => Real.log (h y)) := fun x =>
    (Real.contDiffAt_log.2 (hpos x).ne').contMDiffAt.comp x (hh x)
  exact this.add contMDiff_const

/-- chain rule for `log (P + δ) + 1`. -/
theorem mgrad_log_add_one {P : M → ℝ} (hP : MSmooth F P) {δ : ℝ} (hpos : ∀ y, 0 < P y + δ)
    (x : M) :
    mgrad F (fun y => Real.log (P y + δ) + 1) x = (P x + δ)⁻¹ • mgrad F P x := by
  have hh : MSmooth F (fun y => P y + δ) := hP.add contMDiff_const
  have hl : MSmooth F (fun y => Real.log (P y + δ)) := fun x =>
    (Real.contDiffAt_log.2 (hpos x).ne').contMDiffAt.comp x (hh x)
  rw [mgrad_add_const F hl 1 x]
  apply ext_inner_right ℝ
  intro v
  rw [mgrad_inner F]
  have := mvfderiv_comp_real F Real.log (fun y => P y + δ) (x := x)
    (Real.differentiableAt_log (hpos x).ne') (mdifferentiableAt_of_msmooth F hh x) v
  rw [show (fun y => Real.log (P y + δ)) = Real.log ∘ (fun y => P y + δ) from rfl, this,
    Real.deriv_log, inner_smul_left, mgrad_inner F, ← mgrad_inner F, ← mgrad_inner F]
  have e : mgrad F (fun y => P y + δ) x = mgrad F P x := mgrad_add_const F hP δ x
  rw [e]
  simp
  
variable (hK : KerCanonical F V μ Kk) (hV : MSmooth F V)
  (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V) (hC : WeightedCutoffs F M)

include hK in
theorem semi_continuous_time (g : testSub F M) (x : M) :
    Continuous (fun s : ℝ => semi Kk s.toNNReal (g : M → ℝ) x) := by
  obtain ⟨_, _, C, hC⟩ := hK.smoothing (g : M → ℝ) g.2.1 g.2.2 0
  have h0 : semi Kk 0 (g : M → ℝ) = (g : M → ℝ) := by
    funext y
    have := hK.dynkin.2.2 (g : M → ℝ) g.2.1 g.2.2 y 0
    simpa [semi] using this
  have hL : ∀ z, |mgenerator F V (g : M → ℝ) z| ≤ max C 0 := fun z => by
    have := (hC 0 z).2
    rw [h0] at this
    exact this.trans (le_max_left _ _)
  have := (dynkin_lipschitz F hK.dynkin g.2.1 g.2.2 (le_max_right C 0) hL x).continuous
  exact this.comp continuous_real_toNNReal

include hK in
theorem bruijn_bounds (g : testSub F M) (hg0 : ∀ x, 0 ≤ (g : M → ℝ) x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ) x, 0 ≤ semi Kk s.toNNReal (g : M → ℝ) x ∧
      semi Kk s.toNNReal (g : M → ℝ) x ≤ C ∧
      |mgenerator F V (semi Kk s.toNNReal (g : M → ℝ)) x| ≤ C := by
  obtain ⟨_, _, C, hC⟩ := hK.smoothing (g : M → ℝ) g.2.1 g.2.2 0
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 (Classical.arbitrary M |> fun x => x)).1
  refine ⟨C, hC0, fun s x => ⟨semi_nonneg F hK hg0 _ x, ?_, (hC _ x).2⟩⟩
  exact (le_abs_self _).trans (hC _ x).1

include hK hV hIBP hReg hC in
/-- **de Bruijn**: `d/ds ∫ h_s log h_s = -∫ Γ(h_s)/h_s` for `s > 0`. -/
theorem entFun_hasDerivAt (g : testSub F M) (hg0 : ∀ x, 0 ≤ (g : M → ℝ) x) {δ : ℝ} (hδ : 0 < δ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (entFun Kk μ (g : M → ℝ) δ)
      (-∫ x, carre F (semi Kk t.toNNReal (g : M → ℝ)) (semi Kk t.toNNReal (g : M → ℝ)) x /
        (semi Kk t.toNNReal (g : M → ℝ) x + δ) ∂μ) t := by
  obtain ⟨C, hC0, hCb⟩ := bruijn_bounds F hK g hg0
  have hsm : ∀ s : ℝ, MSmooth F (semi Kk s.toNNReal (g : M → ℝ)) := fun s =>
    (hK.smoothing (g : M → ℝ) g.2.1 g.2.2 _).1
  have hgen : ∀ s : ℝ, mgenerator F V (semi Kk s.toNNReal (g : M → ℝ)) =
      semi Kk s.toNNReal (mgenerator F V (g : M → ℝ)) := fun s =>
    (hK.smoothing (g : M → ℝ) g.2.1 g.2.2 _).2.1
  have hpos : ∀ s : ℝ, ∀ y, 0 < semi Kk s.toNNReal (g : M → ℝ) y + δ := fun s y => by
    have := (hCb s y).1; linarith
  set B : ℝ := (|Real.log δ| + |Real.log (C + δ)| + 1) * C with hB
  have hlogcont : ∀ s : ℝ, Continuous (fun y => Real.log (semi Kk s.toNNReal (g : M → ℝ) y + δ)) :=
    fun s => Real.continuousOn_log.comp_continuous ((hsm s).continuous.add continuous_const)
      (fun y => (hpos s y).ne')
  have hLc : ∀ s : ℝ, Continuous (mgenerator F V (semi Kk s.toNNReal (g : M → ℝ))) := fun s =>
    (hReg.2.1 _ (hsm s)).continuous
  have hF_meas : ∀ s : ℝ, AEStronglyMeasurable (fun x => (semi Kk s.toNNReal (g : M → ℝ) x + δ) *
      Real.log (semi Kk s.toNNReal (g : M → ℝ) x + δ)) μ := fun s =>
    (((hsm s).continuous.add continuous_const).mul (hlogcont s)).aestronglyMeasurable
  have hbd : ∀ (s : ℝ) (x : M), |Real.log (semi Kk s.toNNReal (g : M → ℝ) x + δ) + 1| ≤
      |Real.log δ| + |Real.log (C + δ)| + 1 := fun s x => by
    have := abs_log_le_of_mem hδ (by linarith [(hCb s x).1] : δ ≤ semi Kk s.toNNReal (g : M → ℝ) x + δ)
      (by linarith [(hCb s x).2.1] : semi Kk s.toNNReal (g : M → ℝ) x + δ ≤ C + δ)
    exact (abs_add_le _ _).trans (by simp; linarith)
  have hdiff : ∀ x : M, ∀ s : ℝ, 0 < s → HasDerivAt (fun s : ℝ => (semi Kk s.toNNReal (g : M → ℝ) x + δ) *
      Real.log (semi Kk s.toNNReal (g : M → ℝ) x + δ))
      ((Real.log (semi Kk s.toNNReal (g : M → ℝ) x + δ) + 1) *
        mgenerator F V (semi Kk s.toNNReal (g : M → ℝ)) x) s := fun x s hs => by
    have d := (hasDerivAt_dynkin F hK.dynkin g.2.1 g.2.2 hV x hs).add_const δ
    have hl := d.log (hpos s x).ne'
    refine (d.mul hl).congr_deriv ?_
    rw [hgen s]
    have hne := (hpos s x).ne'
    have key : ∀ a l : ℝ, a + δ ≠ 0 →
        l * Real.log (a + δ) + (a + δ) * (l / (a + δ)) = (Real.log (a + δ) + 1) * l := by
      intro a l h
      field_simp
    exact key _ _ hne
  have hΘ : ∀ (s : ℝ) (x : M), |(semi Kk s.toNNReal (g : M → ℝ) x + δ) *
      Real.log (semi Kk s.toNNReal (g : M → ℝ) x + δ)| ≤
      (C + δ) * (|Real.log δ| + |Real.log (C + δ)|) := fun s x => by
    obtain ⟨h0, h1, _⟩ := hCb s x
    rw [abs_mul, abs_of_pos (hpos s x)]
    have := abs_log_le_of_mem hδ (by linarith : δ ≤ semi Kk s.toNNReal (g : M → ℝ) x + δ)
      (by linarith : semi Kk s.toNNReal (g : M → ℝ) x + δ ≤ C + δ)
    gcongr
  have hI := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (s : ℝ) (x : M) => (semi Kk s.toNNReal (g : M → ℝ) x + δ) *
      Real.log (semi Kk s.toNNReal (g : M → ℝ) x + δ))
    (F' := fun (s : ℝ) (x : M) => (Real.log (semi Kk s.toNNReal (g : M → ℝ) x + δ) + 1) *
      mgenerator F V (semi Kk s.toNNReal (g : M → ℝ)) x) (μ := μ) (x₀ := t)
    (s := Ioo (t / 2) (2 * t)) (Ioo_mem_nhds (by linarith) (by linarith)) (bound := fun _ => B)
    (Eventually.of_forall hF_meas) (Integrable.of_bound (hF_meas t) _ (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hΘ t x))
    ((((hlogcont t).add continuous_const).mul (hLc t)).aestronglyMeasurable)
    (ae_of_all _ fun x s _ => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (hbd s x) (hCb s x).2.2 (abs_nonneg _) (by positivity)))
    (integrable_const _)
    (ae_of_all _ fun x s hs => hdiff x s (by linarith [hs.1]))
  refine hI.2.congr_deriv ?_
  -- identification of the integral
  set P : M → ℝ := semi Kk t.toNNReal (g : M → ℝ) with hP
  have hPs : MSmooth F P := hsm t
  have hhs : MSmooth F (fun y => P y + δ) := hPs.add contMDiff_const
  have hpos' : ∀ y, 0 < P y + δ := hpos t
  have hu : MSmooth F (fun y => Real.log (P y + δ) + 1) := msmooth_log_add_one F hhs hpos'
  have hbdu : ∀ y, |Real.log (P y + δ) + 1| ≤ |Real.log δ| + |Real.log (C + δ)| + 1 := hbd t
  have hu2 : MemLp (fun y => Real.log (P y + δ) + 1) 2 μ :=
    MemLp.of_bound hu.continuous.aestronglyMeasurable _
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hbdu y)
  have hInS : InS F V μ P := (inS_semi F hK hReg g t.toNNReal).1
  have hGP : Integrable (fun x => carre F P P x) μ := integrable_carre_of_InS F hIBP hReg hC hInS
  have hcu : ∀ x, carre F (fun y => Real.log (P y + δ) + 1) (fun y => Real.log (P y + δ) + 1) x =
      ((P x + δ)⁻¹) ^ 2 * carre F P P x := fun x => by
    simp only [carre, mgrad_log_add_one F hPs hpos', real_inner_smul_left, real_inner_smul_right]
    ring
  have hGu : Integrable (fun x => carre F (fun y => Real.log (P y + δ) + 1)
      (fun y => Real.log (P y + δ) + 1) x) μ := by
    refine Integrable.mono' (hGP.const_mul (δ⁻¹ ^ 2)) ((hReg.1 _ _ hu hu).continuous.aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [hcu x, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (carre_nonneg F P x))]
    have : (P x + δ)⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ (by linarith [(hCb t x).1])
    have h0 : 0 ≤ (P x + δ)⁻¹ := (inv_pos.2 (hpos' x)).le
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 this 2) (carre_nonneg F P x)
  have hv : InS F V μ (fun y => P y + δ) := by
    refine InS.of_bounded F hReg hhs ⟨C + δ, fun x => ?_⟩ ⟨C, fun x => ?_⟩
    · rw [abs_of_pos (hpos' x)]; linarith [(hCb t x).2.1]
    · rw [funext (mgenerator_add_const F hPs δ)]; exact (hCb t x).2.2
  obtain ⟨_, hcross⟩ := integral_carre_cross F hIBP hReg hC hu hu2 hGu hv
  have hpt : ∀ x, carre F (fun y => Real.log (P y + δ) + 1) (fun y => P y + δ) x =
      carre F P P x / (P x + δ) := fun x => by
    simp only [carre, mgrad_log_add_one F hPs hpos', mgrad_add_const F hPs δ, real_inner_smul_left]
    rw [div_eq_inv_mul]
  have hpt2 : ∀ x, (Real.log (P x + δ) + 1) * mgenerator F V (semi Kk t.toNNReal (g : M → ℝ)) x =
      (Real.log (P x + δ) + 1) * mgenerator F V (fun y => P y + δ) x := fun x => by
    rw [mgenerator_add_const F hPs δ]
  simp only [hpt] at hcross
  rw [hcross, neg_neg]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [mgenerator_add_const F hPs δ x]

include hK in
/-- continuity of the entropy functional on `[0,∞)`. -/
theorem entFun_continuousOn (g : testSub F M) (hg0 : ∀ x, 0 ≤ (g : M → ℝ) x) {δ : ℝ}
    (hδ : 0 < δ) : ContinuousOn (entFun Kk μ (g : M → ℝ) δ) (Ici 0) := by
  obtain ⟨C, hC0, hC⟩ := bruijn_bounds F hK g hg0
  have hcont : Continuous (entFun Kk μ (g : M → ℝ) δ) := by
    unfold entFun
    refine continuous_of_dominated (bound := fun _ => (C + δ) * (|Real.log δ| + |Real.log (C + δ)|))
      (fun s => ?_) (fun s => Eventually.of_forall fun x => ?_) (integrable_const _)
      (Eventually.of_forall fun x => ?_)
    · have hs := (hK.smoothing (g : M → ℝ) g.2.1 g.2.2 s.toNNReal).1.continuous
      exact ((hs.add continuous_const).mul (Real.continuousOn_log.comp_continuous
        (hs.add continuous_const) (fun y => (by have := semi_nonneg F hK hg0 s.toNNReal y; exact (show (0:ℝ) < semi Kk s.toNNReal (g : M → ℝ) y + δ by linarith).ne')))).aestronglyMeasurable
    · obtain ⟨h0, h1, _⟩ := hC s x
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith)]
      have := abs_log_le_of_mem hδ (by linarith : δ ≤ semi Kk s.toNNReal (g : M → ℝ) x + δ)
        (by linarith : semi Kk s.toNNReal (g : M → ℝ) x + δ ≤ C + δ)
      gcongr
    · have hs := semi_continuous_time F hK g x
      have hp : ∀ s : ℝ, semi Kk s.toNNReal (g : M → ℝ) x + δ ≠ 0 := fun s => by
        have := semi_nonneg F hK hg0 s.toNNReal x
        exact (show (0:ℝ) < _ by linarith).ne'
      exact (hs.add continuous_const).mul (Real.continuousOn_log.comp_continuous
        (hs.add continuous_const) hp)
  exact hcont.continuousOn

end Bruijn

end CutoffRigidity.Riemann.Diff
