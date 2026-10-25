module

public import CutoffRigidity.Riemann.DiffBEClass
public import CutoffRigidity.Riemann.DiffBESemi3
public import CutoffRigidity.Riemann.DiffBESemi5

/-! # Differentiation of `A(s) = ∫ (K_s ζ) √(Γ(K_{t-s} f) + ε) dμ` (workstream BE, part C)

Abstract `Kk` with `KerCanonical F V μ Kk`.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Semi

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} {μ : Measure M} [IsFiniteMeasure μ] {Kk : ℝ≥0 → Kernel M M}

/-- `A(s) = ∫ (K_s ζ) · √(Γ(K_{t-s} f) + ε) dμ`. -/
noncomputable def Afun (Kk : ℝ≥0 → Kernel M M) (μ : Measure M) (t : ℝ) (f ζ : M → ℝ) (ε : ℝ)
    (s : ℝ) : ℝ :=
  ∫ x, semi Kk s.toNNReal ζ x *
    Real.sqrt (carre F (semi Kk (t - s).toNNReal f) (semi Kk (t - s).toNNReal f) x + ε) ∂μ

variable (hK : KerCanonical F V μ Kk) (hV : MSmooth F V)
  (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V) (hC : WeightedCutoffs F M)

include hK hReg in
/-- `K_r g ∈ 𝒮` for a test function `g`; also bounded; also `𝓛 (K_r g) = K_r (𝓛 g)` is again of
that type. -/
theorem inS_semi (g : testSub F M) (r : ℝ≥0) :
    InS F V μ (semi Kk r (g : M → ℝ)) ∧ InS F V μ (mgenerator F V (semi Kk r (g : M → ℝ))) ∧
    (∃ C, ∀ x, |semi Kk r (g : M → ℝ) x| ≤ C) := by
  have hg : MSmooth F (g : M → ℝ) := g.2.1
  have hgc : HasCompactSupport (g : M → ℝ) := g.2.2
  have hLg : MSmooth F (mgenerator F V (g : M → ℝ)) := hReg.2.1 _ hg
  have hLgc : HasCompactSupport (mgenerator F V (g : M → ℝ)) := hasCompactSupport_mgenerator F V hg hgc
  obtain ⟨C, hC0, hC⟩ := bdd_semi F hK hg hgc
  obtain ⟨C', hC0', hC'⟩ := bdd_semi F hK hLg hLgc
  refine ⟨InS.of_bounded F hReg (smooth_semi F hK hg hgc r) ⟨C, fun x => (hC r x).1⟩
    ⟨C, fun x => (hC r x).2⟩, ?_, ⟨C, fun x => (hC r x).1⟩⟩
  rw [gen_semi F hK hg hgc r]
  exact InS.of_bounded F hReg (smooth_semi F hK hLg hLgc r) ⟨C', fun x => (hC' r x).1⟩
    ⟨C', fun x => (hC' r x).2⟩

include hK in
/-- positivity of the semigroup. -/
theorem semi_nonneg {g : M → ℝ} (hg : ∀ x, 0 ≤ g x) (r : ℝ≥0) (x : M) : 0 ≤ semi Kk r g x :=
  integral_nonneg hg

include hK in
/-- invariance of `μ`: `∫ K_r g dμ = ∫ g dμ` for bounded measurable `g`. -/
theorem integral_semi {g : M → ℝ} (hg : Measurable g) (hb : ∃ C, ∀ x, |g x| ≤ C) (r : ℝ≥0) :
    ∫ x, semi Kk r g x ∂μ = ∫ x, g x ∂μ := by
  haveI := hK.markov r
  obtain ⟨C, hC⟩ := hb
  have hinv := hK.invariant r
  have hint : Integrable g (μ.bind (Kk r)) := by
    rw [hinv]
    exact Integrable.of_bound hg.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hC x)
  have h := Measure.comp_eq_comp_const_apply (κ := Kk r) (μ := μ)
  have h2 : (Kk r ∘ₖ Kernel.const Unit μ) () = μ.bind (Kk r) := h.symm
  have := Kernel.integral_comp (η := Kk r) (κ := Kernel.const Unit μ) (a := ()) (f := g)
    (by rw [h2]; exact hint)
  rw [h2, hinv] at this
  simpa [semi] using this.symm

include hK hV hIBP hReg hC in
/-- **Derivative of `A`** at `s ∈ (0,t)`. -/
theorem hasDerivAt_Afun (f ζ : testSub F M) {ε : ℝ} (hε : 0 < ε) {t s : ℝ} (hs : 0 < s)
    (hst : s < t) :
    HasDerivAt (Afun F Kk μ t (f : M → ℝ) (ζ : M → ℝ) ε)
      (∫ x, mgenerator F V (semi Kk s.toNNReal (ζ : M → ℝ)) x *
          Real.sqrt (carre F (semi Kk (t - s).toNNReal (f : M → ℝ))
            (semi Kk (t - s).toNNReal (f : M → ℝ)) x + ε) ∂μ -
        ∫ x, semi Kk s.toNNReal (ζ : M → ℝ) x *
          (carre F (semi Kk (t - s).toNNReal (f : M → ℝ))
              (mgenerator F V (semi Kk (t - s).toNNReal (f : M → ℝ))) x /
            Real.sqrt (carre F (semi Kk (t - s).toNNReal (f : M → ℝ))
              (semi Kk (t - s).toNNReal (f : M → ℝ)) x + ε)) ∂μ) s := by
  have hf : MSmooth F (f : M → ℝ) := f.2.1
  have hfc : HasCompactSupport (f : M → ℝ) := f.2.2
  have hζ : MSmooth F (ζ : M → ℝ) := ζ.2.1
  have hζc : HasCompactSupport (ζ : M → ℝ) := ζ.2.2
  have hr : 0 < t - s := by linarith
  obtain ⟨cu, hcu0, hcu⟩ := u_lip F hIBP hReg hC hK hV hf hfc hε
  obtain ⟨Cu, hCu⟩ := u_integrable F hIBP hReg hC hK hf hfc hε
  obtain ⟨K, hK0, hKb⟩ := G_deriv_bound F hIBP hReg hC hK hV hf hfc
  obtain ⟨Cph, hCph0, hph⟩ := phi_remainder F hK hV hζ hζc
  obtain ⟨Cb, hCb0, hCb⟩ := bdd_semi F hK hζ hζc
  obtain ⟨Cf, hCf0, hG⟩ := G_integrable F hIBP hReg hC hK hf hfc
  have hq := q_integrable F hIBP hReg hC hK hV hf hfc (t - s)
  have hw0 := smooth_semi F hK hf hfc (t - s).toNNReal
  have hLw0 : MSmooth F (mgenerator F V (semi Kk (t - s).toNNReal (f : M → ℝ))) :=
    msmooth_mgenerator F hV hw0
  have hD : MSmooth F (fun y => -1 * mgenerator F V (semi Kk (t - s).toNNReal (f : M → ℝ)) y) :=
    contMDiff_const.mul hLw0
  have hs0 : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hqc : Continuous (fun x => 2 * carre F
      (fun y => -1 * mgenerator F V (semi Kk (t - s).toNNReal (f : M → ℝ)) y)
      (semi Kk (t - s).toNNReal (f : M → ℝ)) x) :=
    continuous_const.mul (continuous_carre F hD hw0)
  have hden : ∀ x, 2 * Real.sqrt (carre F (semi Kk (t - s).toNNReal (f : M → ℝ))
      (semi Kk (t - s).toNNReal (f : M → ℝ)) x + ε) ≠ 0 := fun x =>
    (mul_pos two_pos (Real.sqrt_pos.2 (by
      have := carre_nonneg F (semi Kk (t - s).toNNReal (f : M → ℝ)) x
      linarith))).ne'
  have hdenc : Continuous (fun x => 2 * Real.sqrt (carre F (semi Kk (t - s).toNNReal (f : M → ℝ))
      (semi Kk (t - s).toNNReal (f : M → ℝ)) x + ε)) :=
    continuous_const.mul ((continuous_carre F hw0 hw0).add_const ε).sqrt
  have hsmall : ∀ δ > 0, ∀ᶠ h in 𝓝[≠] (0 : ℝ), h ≠ 0 ∧ |h| < δ := fun δ hδ => by
    have h1 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), h ≠ 0 := self_mem_nhdsWithin
    have h2 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h| < δ :=
      (Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun h hh => by simpa [Real.dist_eq] using hh⟩).filter_mono
        nhdsWithin_le_nhds
    exact h1.and h2
  have hδ0 : 0 < min s (t - s) := lt_min hs hr
  have hlimabs : Tendsto (fun h : ℝ => |h|) (𝓝[≠] 0) (𝓝 0) :=
    (continuous_abs.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
  have hlimK : ∀ c : ℝ, Tendsto (fun h : ℝ => c * |h|) (𝓝[≠] 0) (𝓝 0) := fun c => by
    simpa using hlimabs.const_mul c
  have hPm : ∀ s' : ℝ, AEStronglyMeasurable (fun x => semi Kk s'.toNNReal (ζ : M → ℝ) x) μ :=
    fun s' => (smooth_semi F hK hζ hζc s'.toNNReal).continuous.aestronglyMeasurable
  have hum : ∀ s' : ℝ, AEStronglyMeasurable (fun x => Real.sqrt (carre F
      (semi Kk (t - s').toNNReal (f : M → ℝ)) (semi Kk (t - s').toNNReal (f : M → ℝ)) x + ε)) μ :=
    fun s' => by
      have hw := smooth_semi F hK hf hfc (t - s').toNNReal
      exact ((continuous_carre F hw hw).add_const ε).sqrt.aestronglyMeasurable
  have hP'm : AEStronglyMeasurable (fun x => mgenerator F V (semi Kk s.toNNReal (ζ : M → ℝ)) x) μ :=
    (msmooth_mgenerator F hV (smooth_semi F hK hζ hζc s.toNNReal)).continuous.aestronglyMeasurable
  have hv : Integrable (fun x => 2 * carre F
      (fun y => -1 * mgenerator F V (semi Kk (t - s).toNNReal (f : M → ℝ)) y)
      (semi Kk (t - s).toNNReal (f : M → ℝ)) x /
      (2 * Real.sqrt (carre F (semi Kk (t - s).toNNReal (f : M → ℝ))
        (semi Kk (t - s).toNNReal (f : M → ℝ)) x + ε))) μ := by
    refine Integrable.mono' ((hq.const_mul 2).norm.div_const (2 * Real.sqrt ε))
      (hqc.div hdenc hden).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_div]
    refine div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by
      have := carre_nonneg F (semi Kk (t - s).toNNReal (f : M → ℝ)) x
      linarith)) (by norm_num)
  have hP : ∀ η > 0, ∀ᶠ h in 𝓝[≠] (0 : ℝ), ∀ x,
      |(semi Kk (s + h).toNNReal (ζ : M → ℝ) x - semi Kk s.toNNReal (ζ : M → ℝ) x) / h -
        mgenerator F V (semi Kk s.toNNReal (ζ : M → ℝ)) x| ≤ η := by
    intro η hη
    filter_upwards [hsmall (min (min s (t - s)) (η / (Cph + 1))) (lt_min hδ0 (by positivity))]
      with h ⟨hh, hlt⟩ x
    have hlt1 : |h| < min s (t - s) := lt_of_lt_of_le hlt (min_le_left _ _)
    have hlt2 : |h| < η / (Cph + 1) := lt_of_lt_of_le hlt (min_le_right _ _)
    have hsh : 0 < s + h := by
      have := neg_abs_le h; have := min_le_left s (t - s); linarith
    have := hph s h hs hsh hh x
    rw [div_eq_inv_mul]
    refine this.trans ?_
    have h3 : |h| * (Cph + 1) < η := (lt_div_iff₀ (by positivity)).1 hlt2
    nlinarith [abs_nonneg h]
  have hu1 : Tendsto (fun h : ℝ => ∫ x, |Real.sqrt (carre F (semi Kk (t - (s + h)).toNNReal (f : M → ℝ))
      (semi Kk (t - (s + h)).toNNReal (f : M → ℝ)) x + ε) - Real.sqrt (carre F
      (semi Kk (t - s).toNNReal (f : M → ℝ)) (semi Kk (t - s).toNNReal (f : M → ℝ)) x + ε)| ∂μ)
      (𝓝[≠] 0) (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun h => integral_nonneg fun x =>
      abs_nonneg _) (Filter.Eventually.of_forall fun h => ?_)
      (hlimK cu)
    have := hcu (t - s) (t - (s + h))
    have e : |t - (s + h) - (t - s)| = |h| := by rw [← abs_neg]; congr 1; ring
    rw [e] at this
    exact this
  have hlim : Tendsto (fun h : ℝ => ∫ x, |(carre F (semi Kk (t - (s + h)).toNNReal (f : M → ℝ))
        (semi Kk (t - (s + h)).toNNReal (f : M → ℝ)) x - carre F (semi Kk (t - s).toNNReal (f : M → ℝ))
          (semi Kk (t - s).toNNReal (f : M → ℝ)) x) / h -
      2 * carre F (fun y => -1 * mgenerator F V (semi Kk (t - s).toNNReal (f : M → ℝ)) y)
          (semi Kk (t - s).toNNReal (f : M → ℝ)) x| ∂μ) (𝓝[≠] 0) (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun h => integral_nonneg fun x =>
      abs_nonneg _) ?_ (hlimK K)
    filter_upwards [hsmall (min s (t - s)) hδ0] with h ⟨hh, hlt⟩
    have hts : 0 < t - (s + h) := by
      have := le_abs_self h; have := min_le_right s (t - s); linarith
    exact hKb (t - s) (t - (s + h)) h hr hts hh (by ring)
  have hu2 := sqrt_L1_deriv hε (fun h x => carre F (semi Kk (t - (s + h)).toNNReal (f : M → ℝ))
        (semi Kk (t - (s + h)).toNNReal (f : M → ℝ)) x)
      (fun x => carre F (semi Kk (t - s).toNNReal (f : M → ℝ))
        (semi Kk (t - s).toNNReal (f : M → ℝ)) x)
      (fun x => 2 * carre F (fun y => -1 * mgenerator F V (semi Kk (t - s).toNNReal (f : M → ℝ)) y)
        (semi Kk (t - s).toNNReal (f : M → ℝ)) x)
      (fun h => (continuous_carre F (smooth_semi F hK hf hfc _) (smooth_semi F hK hf hfc _)).aestronglyMeasurable)
      ((continuous_carre F hw0 hw0).aestronglyMeasurable)
      (fun h x => carre_nonneg F _ x) (fun x => carre_nonneg F _ x)
      (fun h => (hG _).1) (hG _).1 (hq.const_mul 2) hlim
  have main := hasDerivAt_integral_mul_L1 (μ := μ)
    (fun s' x => semi Kk s'.toNNReal (ζ : M → ℝ) x)
    (fun s' x => Real.sqrt (carre F (semi Kk (t - s').toNNReal (f : M → ℝ))
      (semi Kk (t - s').toNNReal (f : M → ℝ)) x + ε))
    (fun x => mgenerator F V (semi Kk s.toNNReal (ζ : M → ℝ)) x)
    (fun x => 2 * carre F (fun y => -1 * mgenerator F V (semi Kk (t - s).toNNReal (f : M → ℝ)) y)
      (semi Kk (t - s).toNNReal (f : M → ℝ)) x /
      (2 * Real.sqrt (carre F (semi Kk (t - s).toNNReal (f : M → ℝ))
        (semi Kk (t - s).toNNReal (f : M → ℝ)) x + ε))) s
    hPm hum Cb (fun s' x => (hCb _ x).1) (fun x => (hCb _ x).2) hP'm
    (fun s' => (hCu (t - s')).1) hv hP hu1 hu2
  unfold Afun
  convert main using 1
  rw [sub_eq_add_neg]
  congr 1
  rw [← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hc : carre F (fun y => -1 * mgenerator F V (semi Kk (t - s).toNNReal (f : M → ℝ)) y)
      (semi Kk (t - s).toNNReal (f : M → ℝ)) x =
      - carre F (semi Kk (t - s).toNNReal (f : M → ℝ))
        (mgenerator F V (semi Kk (t - s).toNNReal (f : M → ℝ))) x := by
    simp only [carre, mgrad_const_mul F (-1) hLw0, real_inner_smul_left]
    rw [real_inner_comm]; ring
  have hd := hden x
  beta_reduce
  rw [hc]
  field_simp


include hK hV hIBP hReg hC in
/-- `A` is continuous on `[0,t]`. -/
theorem continuousOn_Afun (f ζ : testSub F M) {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (Afun F Kk μ t (f : M → ℝ) (ζ : M → ℝ) ε) (Icc 0 t) := by
  obtain ⟨K, hK0, hKl⟩ := Afun_lip F hIBP hReg hC hK hV (f := (f : M → ℝ)) (ζ := (ζ : M → ℝ))
    f.2.1 f.2.2 ζ.2.1 ζ.2.2 hε
  have : LipschitzWith ⟨K, hK0⟩ (Afun F Kk μ t (f : M → ℝ) (ζ : M → ℝ) ε) := by
    refine LipschitzWith.of_dist_le_mul fun s s' => ?_
    rw [Real.dist_eq, Real.dist_eq, abs_sub_comm, abs_sub_comm s s']
    exact hKl t s s'
  exact this.continuous.continuousOn

end Semi

end CutoffRigidity.Riemann.Diff
