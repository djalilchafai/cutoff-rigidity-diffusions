module

public import CutoffRigidity.Statements
public import CutoffRigidity.Riemann.DiffSobolevRn2
public import CutoffRigidity.Riemann.DiffBridge
public import CutoffRigidity.Riemann.WitnessGeometry

/-! # `C²` uniqueness, stage 1: the resolvent of an `IsEuclideanDiffusion V` semigroup, `V ∈ C¹`

Flat-space (no manifold, no `MSmooth V`) replacement of the Riemannian resolvent calculus
(`DiffusionRegular`, `DiffBridge`): for `V ∈ C¹` and `P` with `IsEuclideanDiffusion V P` we show
* `s ↦ P_s f(x)` is Lipschitz for `f ∈ C_c^∞`;
* `s ↦ P_s h(x)` is continuous for every continuous compactly supported `h` (uniform approximation);
* resolvent form of Dynkin: `U_λ((λ - 𝓛) f)(x) = f(x)` for `f ∈ C_c^∞`, with `U_λ h = ∫₀^∞ e^{-λ s} P_s h(x) ds`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutCur

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

namespace C2U

variable {d : ℕ}

/-- The resolvent `U_λ h (x) = ∫₀^∞ e^{-λ s} (P_s h)(x) ds`. -/
noncomputable def resU (P : ℝ≥0 → Kernel (Rd d) (Rd d)) (lam : ℝ) (h : Rd d → ℝ) (x : Rd d) : ℝ :=
  ∫ s in Ioi (0 : ℝ), Real.exp (-lam * s) * ∫ y, h y ∂P s.toNNReal x

/-! ### The generator of a compactly supported smooth function -/

theorem continuous_gradient_of_contDiff_one {V : Rd d → ℝ} (hV : ContDiff ℝ 1 V) :
    Continuous (gradient V) :=
  (CutoffRigidity.Riemann.Witness.contDiff_gradient_rd (n := 0) hV (by norm_num)).continuous

theorem continuous_laplacian {f : Rd d → ℝ} (hf : ContDiff ℝ 2 f) : Continuous (laplacian f) := by
  unfold laplacian
  have h2 : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num) |>.continuous
  refine continuous_finsetSum _ fun i _ => ?_
  exact (h2.clm_apply continuous_const).clm_apply continuous_const

theorem hasCompactSupport_laplacian {f : Rd d → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (laplacian f) := by
  unfold laplacian
  have h2 : HasCompactSupport (fderiv ℝ (fderiv ℝ f)) := hfc.fderiv (𝕜 := ℝ) |>.fderiv (𝕜 := ℝ)
  refine h2.mono ?_
  intro z hz
  by_contra h
  simp only [Function.mem_support, not_not] at h
  exact hz (by simp [h])

theorem hasCompactSupport_gradient {f : Rd d → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (gradient f) := by
  have h1 : HasCompactSupport (fderiv ℝ f) := hfc.fderiv (𝕜 := ℝ)
  exact h1.comp_left (g := fun A : Rd d →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ (Rd d)).symm A) (by simp)

theorem continuous_generator {V f : Rd d → ℝ} (hV : ContDiff ℝ 1 V) (hf : ContDiff ℝ 2 f) :
    Continuous (generator V f) := by
  unfold generator
  have hg : Continuous (gradient f) :=
    (CutoffRigidity.Riemann.Witness.contDiff_gradient_rd (n := 0) hf (by norm_num)).continuous
  exact (continuous_laplacian hf).sub ((continuous_gradient_of_contDiff_one hV).inner hg)

theorem hasCompactSupport_generator {V f : Rd d → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (generator V f) := by
  unfold generator
  refine (hasCompactSupport_laplacian hfc).sub ?_
  refine (hasCompactSupport_gradient hfc).mono ?_
  intro z hz
  by_contra h
  simp only [Function.mem_support, not_not] at h
  exact hz (by simp [h])


/-! ### Dynkin regularity -/

section Dynkin

variable {V : Rd d → ℝ} {P : ℝ≥0 → Kernel (Rd d) (Rd d)}

theorem exists_abs_generator_le (hV : ContDiff ℝ 1 V) {f : Rd d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |generator V f z| ≤ C := by
  obtain ⟨C, hC⟩ := (continuous_generator hV (hf.of_le (by norm_cast))).bounded_above_of_compact_support
    (hasCompactSupport_generator hfc)
  exact ⟨max C 0, le_max_right _ _, fun z => (hC z).trans (le_max_left _ _)⟩

theorem dynkin_bound (hP : IsEuclideanDiffusion V P) {f : Rd d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) {C : ℝ} (hC : ∀ z, |generator V f z| ≤ C) (u : ℝ≥0) (y : Rd d) :
    |∫ z, f z ∂P u y - f y| ≤ C * u := by
  have h := hP.2.2 f hf hfc y u
  have hb : ‖∫ s in (0 : ℝ)..(u : ℝ), ∫ z, generator V f z ∂P s.toNNReal y‖ ≤
      C * |(u : ℝ) - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s _
    have : IsProbabilityMeasure (P s.toNNReal y) := (hP.1 _).isProbabilityMeasure y
    calc ‖∫ z, generator V f z ∂P s.toNNReal y‖
        ≤ C * (P s.toNNReal y).real univ :=
          norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hC)
      _ = C := by simp
  rw [h]
  simpa using hb

theorem dynkin_lipschitz_step (hP : IsEuclideanDiffusion V P) {f : Rd d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) {C : ℝ} (hC : ∀ z, |generator V f z| ≤ C) (x : Rd d)
    (t u : ℝ≥0) :
    |∫ z, f z ∂P (t + u) x - ∫ z, f z ∂P t x| ≤ C * u := by
  have hint : ∀ ν : Measure (Rd d), IsFiniteMeasure ν → Integrable f ν := fun ν _ =>
    hf.continuous.integrable_of_hasCompactSupport hfc
  have hcomp : P (t + u) = P u ∘ₖ P t := hP.2.1 t u
  have hI : Integrable f ((P u ∘ₖ P t) x) := by
    haveI : IsMarkovKernel (P u ∘ₖ P t) := by
      haveI := hP.1 u; haveI := hP.1 t; infer_instance
    exact hint _ inferInstance
  have h1 : ∫ z, f z ∂P (t + u) x = ∫ y, ∫ z, f z ∂P u y ∂P t x := by
    rw [hcomp]; exact ProbabilityTheory.Kernel.integral_comp hI
  have hg : Integrable (fun y => ∫ z, f z ∂P u y) (P t x) := hI.integral_comp
  haveI : IsProbabilityMeasure (P t x) := (hP.1 t).isProbabilityMeasure x
  have hf' : Integrable f (P t x) := hint _ inferInstance
  rw [h1, ← integral_sub hg hf']
  have := norm_integral_le_of_norm_le_const (μ := P t x)
    (f := fun y => ∫ z, f z ∂P u y - f y) (C := C * u)
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using dynkin_bound hP hf hfc hC u y)
  simpa using this

theorem dynkin_lipschitz (hP : IsEuclideanDiffusion V P) {f : Rd d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, |generator V f z| ≤ C)
    (x : Rd d) :
    LipschitzWith ⟨C, hC0⟩ (fun t : ℝ≥0 => ∫ z, f z ∂P t x) := by
  have key : ∀ s t : ℝ≥0, s ≤ t → dist (∫ z, f z ∂P s x) (∫ z, f z ∂P t x) ≤ C * dist s t := by
    intro s t hst
    obtain ⟨u, rfl⟩ : ∃ u, t = s + u := ⟨t - s, by simp [add_tsub_cancel_of_le hst]⟩
    rw [Real.dist_eq, abs_sub_comm]
    have := dynkin_lipschitz_step hP hf hfc hC x s u
    have hd : dist s (s + u) = u := by
      rw [NNReal.dist_eq]; simp [abs_of_nonneg]
    rw [hd]; exact this
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  rcases le_total s t with h | h
  · exact key s t h
  · rw [dist_comm, dist_comm s t]; exact key t s h

theorem continuous_semi_smooth (hP : IsEuclideanDiffusion V P) (hV : ContDiff ℝ 1 V)
    {f : Rd d → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (x : Rd d) :
    Continuous (fun t : ℝ≥0 => ∫ z, f z ∂P t x) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_generator_le hV hf hfc
  exact (dynkin_lipschitz hP hf hfc hC0 hC x).continuous

theorem abs_integral_le_of_bound (hP : IsEuclideanDiffusion V P) {h : Rd d → ℝ} {C : ℝ}
    (hb : ∀ y, |h y| ≤ C) (t : ℝ≥0) (x : Rd d) : |∫ y, h y ∂P t x| ≤ C := by
  haveI : IsProbabilityMeasure (P t x) := (hP.1 t).isProbabilityMeasure x
  have := norm_integral_le_of_norm_le_const (μ := P t x) (f := h) (C := C)
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hb y)
  simpa using this

/-- Continuity in time for continuous compactly supported functions, by uniform approximation by
`C_c^∞` functions. -/
theorem continuous_semi_cs (hP : IsEuclideanDiffusion V P) (hV : ContDiff ℝ 1 V)
    {h : Rd d → ℝ} (hh : Continuous h) (hhc : HasCompactSupport h) (x : Rd d) :
    Continuous (fun t : ℝ≥0 => ∫ z, h z ∂P t x) := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ y, R < ‖y‖ → h y = 0 := by
    obtain ⟨R, hR⟩ := hhc.isCompact.isBounded.exists_norm_le
    exact ⟨R, fun y hy => by
      by_contra hne
      exact absurd (hR y (subset_tsupport _ hne)) (not_le.2 hy)⟩
  have hloc : LocallyIntegrable h volume := hh.locallyIntegrable
  have hae : ∀ᵐ y ∂(volume : Measure (Rd d)), R < ‖y‖ → h y = 0 := Filter.Eventually.of_forall hR
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  set F : ℕ → ℝ≥0 → ℝ := fun n t => ∫ z, CutoffRigidity.Riemann.Diff.mol (ε n) (hεpos n) h z ∂P t x
    with hF
  have hFc : ∀ n, Continuous (F n) := fun n =>
    continuous_semi_smooth hP hV (CutoffRigidity.Riemann.Diff.mol_contDiff (ε n) (hεpos n) hloc)
      (CutoffRigidity.Riemann.Diff.mol_hasCompactSupport (ε n) (hεpos n) R hae) x
  have hunif : TendstoUniformly F (fun t => ∫ z, h z ∂P t x) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    obtain ⟨η, hη, hηε⟩ := CutoffRigidity.Riemann.Diff.mol_unif_close h hh hhc (half_pos hδ)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hη
    filter_upwards [eventually_ge_atTop N] with n hn t
    haveI : IsProbabilityMeasure (P t x) := (hP.1 t).isProbabilityMeasure x
    have hεn : ε n ≤ η := by
      have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      exact (this.trans hN.le)
    have hcl := hηε (ε n) (hεpos n) hεn
    have hint1 : Integrable h (P t x) := hh.integrable_of_hasCompactSupport hhc
    have hint2 : Integrable (CutoffRigidity.Riemann.Diff.mol (ε n) (hεpos n) h) (P t x) :=
      (CutoffRigidity.Riemann.Diff.mol_contDiff (ε n) (hεpos n) hloc).continuous.integrable_of_hasCompactSupport
        (CutoffRigidity.Riemann.Diff.mol_hasCompactSupport (ε n) (hεpos n) R hae)
    rw [Real.dist_eq, ← integral_sub hint1 hint2]
    have := abs_integral_le_of_bound hP (h := fun y => h y - CutoffRigidity.Riemann.Diff.mol (ε n) (hεpos n) h y)
      (C := δ / 2) (fun y => by rw [abs_sub_comm]; exact hcl y) t x
    exact lt_of_le_of_lt this (half_lt_self hδ)
  exact hunif.continuous (Eventually.of_forall hFc).frequently

theorem continuous_semi_cs_real (hP : IsEuclideanDiffusion V P) (hV : ContDiff ℝ 1 V)
    {h : Rd d → ℝ} (hh : Continuous h) (hhc : HasCompactSupport h) (x : Rd d) :
    Continuous (fun s : ℝ => ∫ z, h z ∂P s.toNNReal x) :=
  (continuous_semi_cs hP hV hh hhc x).comp continuous_real_toNNReal


theorem hasDerivAt_semi (hP : IsEuclideanDiffusion V P) (hV : ContDiff ℝ 1 V)
    {f : Rd d → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (x : Rd d) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ z, f z ∂P s.toNNReal x)
      (∫ z, generator V f z ∂P t.toNNReal x) t := by
  have hc := continuous_semi_cs_real hP hV (continuous_generator hV (hf.of_le (by norm_cast)))
    (hasCompactSupport_generator hfc) x
  have h1 := (hc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add (f x)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  have := hP.2.2 f hf hfc x s.toNNReal
  rw [this, Real.coe_toNNReal _ (le_of_lt hs)]

theorem resU_integrableOn (hP : IsEuclideanDiffusion V P) (hV : ContDiff ℝ 1 V)
    {h : Rd d → ℝ} (hh : Continuous h) (hhc : HasCompactSupport h) {lam : ℝ} (hlam : 0 < lam)
    (x : Rd d) :
    IntegrableOn (fun s : ℝ => Real.exp (-lam * s) * ∫ z, h z ∂P s.toNNReal x) (Ioi (0 : ℝ)) := by
  obtain ⟨C, hC⟩ := hh.bounded_above_of_compact_support hhc
  exact CutoffRigidity.Riemann.Diff.integrableOn_exp_mul_bdd (continuous_semi_cs_real hP hV hh hhc x)
    (fun s => abs_integral_le_of_bound hP (C := C) (fun y => by simpa [Real.norm_eq_abs] using hC y) _ x) hlam

/-- **Resolvent form of Dynkin's identity** (`C²` potential): `U_λ((λ - 𝓛) f)(x) = f(x)`. -/
theorem resU_dynkin (hP : IsEuclideanDiffusion V P) (hV : ContDiff ℝ 1 V) {lam : ℝ}
    (hlam : 0 < lam) {f : Rd d → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (x : Rd d) :
    resU P lam (fun y => lam * f y - generator V f y) x = f x := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_cast)
  have hLf : Continuous (generator V f) := continuous_generator hV hf2
  have hLfc : HasCompactSupport (generator V f) := hasCompactSupport_generator hfc
  set φ : ℝ → ℝ := fun s => ∫ z, f z ∂P s.toNNReal x with hφ
  set ψ : ℝ → ℝ := fun s => ∫ z, generator V f z ∂P s.toNNReal x with hψ
  have hφc : Continuous φ := continuous_semi_cs_real hP hV hf.continuous hfc x
  obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hfc
  have hφb : ∀ s, |φ s| ≤ C := fun s =>
    abs_integral_le_of_bound hP (C := C) (fun y => by simpa [Real.norm_eq_abs] using hC y) _ x
  have hint_f : ∀ s : ℝ, Integrable f (P s.toNNReal x) := fun s => by
    haveI : IsProbabilityMeasure (P s.toNNReal x) := (hP.1 _).isProbabilityMeasure x
    exact hf.continuous.integrable_of_hasCompactSupport hfc
  have hint_L : ∀ s : ℝ, Integrable (generator V f) (P s.toNNReal x) := fun s => by
    haveI : IsProbabilityMeasure (P s.toNNReal x) := (hP.1 _).isProbabilityMeasure x
    exact hLf.integrable_of_hasCompactSupport hLfc
  have hmix : ∀ s : ℝ, ∫ z, (lam * f z - generator V f z) ∂P s.toNNReal x = lam * φ s - ψ s := by
    intro s
    simp only [hφ, hψ]
    rw [integral_sub ((hint_f s).const_mul lam) (hint_L s), integral_const_mul]
  set G : ℝ → ℝ := fun s => -(Real.exp (-lam * s) * φ s) with hG
  have hGc : Continuous G := (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    hφc)).neg
  have hder : ∀ s ∈ Ioi (0 : ℝ), HasDerivAt G
      (Real.exp (-lam * s) * (lam * φ s - ψ s)) s := by
    intro s hs
    have hs' : (0 : ℝ) < s := hs
    have hφd : HasDerivAt φ (ψ s) s := hasDerivAt_semi hP hV hf hfc x hs'
    have he : HasDerivAt (fun s : ℝ => Real.exp (-lam * s)) (Real.exp (-lam * s) * (-lam)) s := by
      simpa using ((hasDerivAt_id s).const_mul (-lam)).exp
    have := (he.mul hφd).neg
    convert this using 1
    ring
  have hint : IntegrableOn (fun s : ℝ => Real.exp (-lam * s) * (lam * φ s - ψ s)) (Ioi (0 : ℝ)) := by
    have h1 := resU_integrableOn hP hV hf.continuous hfc hlam x
    have h2 := resU_integrableOn hP hV hLf hLfc hlam x
    have h3 : IntegrableOn (fun s : ℝ => lam * (Real.exp (-lam * s) * φ s) -
        Real.exp (-lam * s) * ψ s) (Ioi (0 : ℝ)) := (h1.const_mul lam).sub h2
    refine h3.congr_fun (fun s _ => ?_) measurableSet_Ioi
    ring
  have hlim : Tendsto G atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => C * Real.exp (-lam * s)) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hlam) : Tendsto (fun s : ℝ => -lam * s) atTop atBot))
      simpa using this.const_mul C
    refine squeeze_zero_norm (fun s => ?_) h1
    simp only [hG, norm_neg, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hφb s) (Real.exp_pos _).le
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hGc.continuousWithinAt hder hint hlim
  have hφ0 : φ 0 = f x := by
    have := hP.2.2 f hf hfc x 0
    simpa [hφ] using this
  have hG0 : G 0 = -f x := by simp [hG, hφ0]
  unfold resU
  simp_rw [hmix]
  rw [key, hG0]; ring

end Dynkin

end C2U

end CutCur
