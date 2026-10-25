module

public import CutoffRigidity.Riemann.DiffEig1

/-! # Eigenfunction identity in `L²` (workstream KER-EIG, A7)

Generic: Cauchy-Schwarz for the closed form `E` and extension of a weak eigen-equation from
`D` to `Q`.  Gaffney: smooth `L²` eigenfunctions of `𝓛` (any sign of the eigenvalue) lie in `Q`
(`mem_Q_of_eigen`), satisfy the weak equation, and (`eigen_semigroup`) are eigenvectors of `T_t`.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {S : DirFormData H} (T : DirFriedrichs S)

/-- Cauchy-Schwarz for the closed form. -/
theorem DirFriedrichs.E_sq_le {u v : H} (hu : u ∈ T.Q) (hv : v ∈ T.Q) :
    T.E u v ^ 2 ≤ T.E u u * T.E v v := by
  have key : ∀ t : ℝ, 0 ≤ T.E v v * (t * t) + 2 * T.E u v * t + T.E u u := by
    intro t
    have := T.E_nonneg (T.Q_add hu (T.Q_smul t hv))
    rw [T.E_add_left hu (T.Q_smul t hv) (T.Q_add hu (T.Q_smul t hv)),
      T.E_add_right hu hu (T.Q_smul t hv), T.E_add_right (T.Q_smul t hv) hu (T.Q_smul t hv),
      T.E_smul_left t hv hu, T.E_smul_right t hu hv, T.E_smul_left t hv (T.Q_smul t hv),
      T.E_smul_right t hv hv, T.E_comm hv hu] at this
    nlinarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

/-- A weak eigen-equation on `D` extends to `Q`. -/
theorem DirFriedrichs.E_eq_of_dense {u : H} (hu : u ∈ T.Q) (c : ℝ)
    (h : ∀ g : S.D, T.E u g = c * inner ℝ u (g : H)) :
    ∀ φ ∈ T.Q, T.E u φ = c * inner ℝ u φ := by
  intro φ hφ
  obtain ⟨g, hg, hgc⟩ := (T.mem_Q φ).1 hφ
  -- `E (φ - g m) → 0`
  have hsubQ : ∀ m, φ - (g m : H) ∈ T.Q := fun m => T.Q_sub hφ (T.coe_mem (g m))
  have hE0 : Tendsto (fun m => T.E (φ - (g m : H)) (φ - (g m : H))) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hgc (ε / 2) (by positivity)
    refine ⟨N, fun m hm => ?_⟩
    have hcauchy : S.EnCauchy (fun k => g k - g m) := by
      intro δ hδ
      obtain ⟨N', hN'⟩ := hgc δ hδ
      refine ⟨N', fun k hk l hl => ?_⟩
      rw [sub_sub_sub_cancel_right]
      exact hN' k hk l hl
    have hlim := T.E_lim (fun k => g k - g m) (fun k => g k - g m) (φ - (g m : H))
      (φ - (g m : H)) (by simpa using hg.sub_const (g m : H)) hcauchy
      (by simpa using hg.sub_const (g m : H)) hcauchy
    have hle : T.E (φ - (g m : H)) (φ - (g m : H)) ≤ ε / 2 := by
      refine le_of_tendsto hlim ?_
      filter_upwards [eventually_ge_atTop N] with k hk
      exact (hN k hk m hm).le
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (T.E_nonneg (hsubQ m))]
    linarith
  have hlim1 : Tendsto (fun m => T.E u (φ - (g m : H))) atTop (𝓝 0) := by
    have hsq : Tendsto (fun m => T.E u (φ - (g m : H)) ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero (fun m => sq_nonneg _) (fun m => T.E_sq_le hu (hsubQ m)) ?_
      simpa using hE0.const_mul (T.E u u)
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simp only [Real.sqrt_zero] at this
    have h5 : Tendsto (fun m => |T.E u (φ - (g m : H))|) atTop (𝓝 0) :=
      this.congr (fun m => Real.sqrt_sq_eq_abs _)
    exact (tendsto_zero_iff_abs_tendsto_zero _).2 h5
  have hlim2 : Tendsto (fun m => T.E u (g m : H)) atTop (𝓝 (T.E u φ)) := by
    have e : ∀ m, T.E u (g m : H) = T.E u φ - T.E u (φ - (g m : H)) := fun m => by
      rw [T.E_sub_right hu hφ (T.coe_mem (g m))]; ring
    simp only [e]
    simpa using (tendsto_const_nhds (x := T.E u φ)).sub hlim1
  have hlim3 : Tendsto (fun m => T.E u (g m : H)) atTop (𝓝 (c * inner ℝ u φ)) := by
    simp only [h]
    exact (tendsto_const_nhds.inner hg).const_mul c |>.congr (fun _ => rfl)
  exact tendsto_nhds_unique hlim2 hlim3

end Abstract

section Gaffney

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

include hV hμ in
/-- Caccioppoli inequality for an eigenfunction, any sign of the eigenvalue. -/
theorem caccioppoli' {f χ : M → ℝ} {ρ : ℝ} (hf : MSmooth F f)
    (hfL2 : Integrable (fun x => f x ^ 2) μ) (hL : ∀ x, mgenerator F V f x = -ρ * f x)
    (hχ : MSmooth F χ) (hχc : HasCompactSupport χ) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχg : ∀ x, ‖mgrad F χ x‖ ≤ 1) :
    ∫ x, χ x ^ 2 * carre F f f x ∂μ ≤ 2 * (|ρ| + 2) * ∫ x, f x ^ 2 ∂μ := by
  have hIBP := weightedIBP_of_isWeightedVolume F hV hμ
  have hReg : WeightedRegular F V := weightedRegular V hV
  have hG : MSmooth F (carre F f f) := hReg.1 f f hf hf
  have hχχ : MSmooth F (χ * χ) := hχ.mul hχ
  have hu : MSmooth F ((χ * χ) * f) := hχχ.mul hf
  have huc : HasCompactSupport ((χ * χ) * f) := (hχc.mul_right.mul_right)
  have hibp := hIBP ((χ * χ) * f) f hu hf huc
  have hpt : ∀ x, carre F ((χ * χ) * f) f x =
      χ x ^ 2 * carre F f f x + 2 * (f x * (χ x * carre F χ f x)) := by
    intro x
    rw [carre_mul_left F hχχ hf x, carre_mul_left F hχ hχ x]
    simp only [Pi.mul_apply]; ring
  have hrhs : -∫ x, ((χ * χ) * f) x * mgenerator F V f x ∂μ =
      ρ * ∫ x, χ x ^ 2 * f x ^ 2 ∂μ := by
    rw [← integral_const_mul, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply, hL x]; ring
  have hint_uf : Integrable (fun x => carre F ((χ * χ) * f) f x) μ :=
    integrable_of_cont_cs (hReg.1 _ _ hu hf).continuous (hasCompactSupport_carre F f huc)
  have hint_G : Integrable (fun x => χ x ^ 2 * carre F f f x) μ := by
    refine integrable_of_cont_cs ((hχ.continuous.pow 2).mul hG.continuous) ?_
    exact hcs_of_zero hχc (fun x hx => by simp [hx])
  have hint_f2 : Integrable (fun x => χ x ^ 2 * f x ^ 2) μ := by
    refine hfL2.mono' ((hχ.continuous.pow 2).mul (hf.continuous.pow 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    obtain ⟨h0, h1⟩ := hχ01 x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : χ x ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (f x)]
  have hpw : ∀ x, χ x ^ 2 * carre F f f x / 2 ≤ carre F ((χ * χ) * f) f x + 2 * f x ^ 2 := by
    intro x
    rw [hpt x]
    obtain ⟨h0, h1⟩ := hχ01 x
    set s := Real.sqrt (carre F f f x) with hs
    have hs2 : s ^ 2 = carre F f f x := Real.sq_sqrt (carre_nonneg F f x)
    have hgs : ‖mgrad F f x‖ = s := by
      rw [hs, carre_self_eq, Real.sqrt_sq (norm_nonneg _)]
    have hc : |carre F χ f x| ≤ s := by
      refine (abs_carre_le F χ f x).trans ?_
      rw [hgs]
      calc ‖mgrad F χ x‖ * s ≤ 1 * s := by gcongr; exact hχg x
        _ = s := one_mul s
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have habs : |f x * (χ x * carre F χ f x)| ≤ |f x| * (χ x * s) := by
      rw [abs_mul, abs_mul, abs_of_nonneg h0]
      gcongr
    have hlow := neg_abs_le (f x * (χ x * carre F χ f x))
    rw [← hs2]
    nlinarith [sq_nonneg (χ x * s - 2 * |f x|), sq_abs (f x)]
  have h1 : ∫ x, χ x ^ 2 * carre F f f x / 2 ∂μ ≤
      ∫ x, (carre F ((χ * χ) * f) f x + 2 * f x ^ 2) ∂μ :=
    integral_mono (hint_G.div_const 2) (hint_uf.add (hfL2.const_mul 2)) hpw
  have h2 : ∫ x, (carre F ((χ * χ) * f) f x + 2 * f x ^ 2) ∂μ =
      ∫ x, carre F ((χ * χ) * f) f x ∂μ + 2 * ∫ x, f x ^ 2 ∂μ := by
    rw [integral_add hint_uf (hfL2.const_mul 2), integral_const_mul]
  have h3 : ∫ x, χ x ^ 2 * f x ^ 2 ∂μ ≤ ∫ x, f x ^ 2 ∂μ := by
    refine integral_mono hint_f2 hfL2 fun x => ?_
    obtain ⟨h0, h1⟩ := hχ01 x
    have : χ x ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (f x)]
  have h3' : 0 ≤ ∫ x, χ x ^ 2 * f x ^ 2 ∂μ := integral_nonneg fun x => by positivity
  have h4 : ∫ x, χ x ^ 2 * carre F f f x / 2 ∂μ = (∫ x, χ x ^ 2 * carre F f f x ∂μ) / 2 := by
    rw [integral_div]
  rw [h4, h2, hibp, hrhs] at h1
  nlinarith [mul_le_mul_of_nonneg_left h3 (abs_nonneg ρ),
    mul_le_mul_of_nonneg_right (le_abs_self ρ) h3']

include hV hμ in
/-- **Gaffney**: a smooth `L²` eigenfunction of `𝓛` (any eigenvalue) lies in the form domain. -/
theorem mem_Q_of_eigen {c : ℝ} {ū : M → ℝ} (hū : MSmooth F ū) (hu2 : MemLp ū 2 μ)
    (hL : ∀ x, mgenerator F V ū x = -c * ū x) :
    hu2.toLp ū ∈ (diffT F hV hμ).Q := by
  obtain ⟨χ, hχ, hlim⟩ := weightedCutoffs_of_complete F (M := M)
  have hf2 : Integrable (fun x => ū x ^ 2) μ := hu2.integrable_sq
  have hχ1 : ∀ n x, ‖mgrad F (χ n) x‖ ≤ 1 := fun n x => by
    refine ((hχ n).2.2 x).2.2.trans ?_
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  set K := ∫ x, ū x ^ 2 ∂μ with hK
  set a : ℕ → testSub F M := fun n => ⟨χ n * ū, (hχ n).1.mul hū, (hχ n).2.1.mul_right⟩ with ha
  set w : ℕ → (diffFormData F hV hμ).D := fun n => ⟨testToL2 F μ (a n), a n, rfl⟩ with hw
  have hconv : Tendsto (fun n => ((w n : (diffFormData F hV hμ).D) : M →₂[μ] ℝ)) atTop
      (𝓝 (hu2.toLp ū)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq : ∀ n, ‖((w n : (diffFormData F hV hμ).D) : M →₂[μ] ℝ) - hu2.toLp ū‖ ^ 2 =
        ∫ x, (χ n x * ū x - ū x) ^ 2 ∂μ := by
      intro n
      rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub ((w n : M →₂[μ] ℝ)) (hu2.toLp ū), hu2.coeFn_toLp,
        coeFn_testToL2 F μ (a n)] with x h1 h2 h3
      rw [h1, Pi.sub_apply, h2]
      have : ((w n : M →₂[μ] ℝ) : M → ℝ) x = χ n x * ū x := h3
      rw [this]
      simp [sq]
    have hint : Tendsto (fun n => ∫ x, (χ n x * ū x - ū x) ^ 2 ∂μ) atTop (𝓝 0) := by
      have := tendsto_integral_of_dominated_convergence (μ := μ) (fun x => ū x ^ 2)
        (F := fun n x => (χ n x * ū x - ū x) ^ 2) (f := fun _ => 0)
        (fun n => (((hχ n).1.continuous.mul hū.continuous).sub hū.continuous).pow 2
          |>.aestronglyMeasurable)
        hf2 (fun n => Eventually.of_forall fun x => by
          obtain ⟨h1, h2, _⟩ := (hχ n).2.2 x
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          have : (χ n x * ū x - ū x) ^ 2 = (1 - χ n x) ^ 2 * ū x ^ 2 := by ring
          rw [this]
          have : (1 - χ n x) ^ 2 ≤ 1 := by nlinarith
          nlinarith [sq_nonneg (ū x)])
        (Eventually.of_forall fun x => by
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [hlim x] with n hn
          simp [hn])
      simpa using this
    have h2 : Tendsto (fun n => ‖((w n : (diffFormData F hV hμ).D) : M →₂[μ] ℝ) - hu2.toLp ū‖ ^ 2)
        atTop (𝓝 0) := by simpa [hsq] using hint
    have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
    simp only [Real.sqrt_zero] at h3
    refine h3.congr (fun n => ?_)
    simp [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)]
  -- energy bound
  have hbound : ∀ n, (diffFormData F hV hμ).en (w n) (w n) ≤ 4 * (|c| + 2) * K + 2 * K := by
    intro n
    have hen : (diffFormData F hV hμ).en (w n) (w n) =
        ∫ x, carre F (χ n * ū) (χ n * ū) x ∂μ := en_diffFormData F hV hμ (a n) (a n)
    rw [hen]
    have hcacc := caccioppoli' F hV hμ hū hf2 hL (hχ n).1 (hχ n).2.1
      (fun x => ⟨((hχ n).2.2 x).1, ((hχ n).2.2 x).2.1⟩) (hχ1 n)
    have hintG : Integrable (fun x => χ n x ^ 2 * carre F ū ū x) μ :=
      integrable_cutoff_sq_mul (hχ n).1.continuous (hχ n).2.1 (continuous_carre F hū hū)
    have hintH : Integrable (fun x => ū x ^ 2 * carre F (χ n) (χ n) x) μ :=
      ((hū.continuous.pow 2).mul (continuous_carre F (hχ n).1 (hχ n).1)).integrable_of_hasCompactSupport
        (hasCompactSupport_carre F (χ n) (hχ n).2.1).mul_left
    have hintL : Integrable (fun x => carre F (χ n * ū) (χ n * ū) x) μ :=
      CutCur.integrable_carre F ((hχ n).1.mul hū) ((hχ n).1.mul hū) ((hχ n).2.1.mul_right) μ
    have hpt : ∀ x, carre F (χ n * ū) (χ n * ū) x ≤
        2 * (χ n x ^ 2 * carre F ū ū x) + 2 * (ū x ^ 2 * carre F (χ n) (χ n) x) := by
      intro x
      rw [carre_self_eq, mgrad_mul F (hχ n).1 hū x, carre_self_eq, carre_self_eq]
      have h1 := norm_add_le (χ n x • mgrad F ū x) (ū x • mgrad F (χ n) x)
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at h1
      have h0 : 0 ≤ ‖χ n x • mgrad F ū x + ū x • mgrad F (χ n) x‖ := norm_nonneg _
      have e1 : (|χ n x| * ‖mgrad F ū x‖) ^ 2 = χ n x ^ 2 * ‖mgrad F ū x‖ ^ 2 := by
        rw [mul_pow, sq_abs]
      have e2 : (|ū x| * ‖mgrad F (χ n) x‖) ^ 2 = ū x ^ 2 * ‖mgrad F (χ n) x‖ ^ 2 := by
        rw [mul_pow, sq_abs]
      nlinarith [sq_nonneg (|χ n x| * ‖mgrad F ū x‖ - |ū x| * ‖mgrad F (χ n) x‖),
        sq_nonneg (‖χ n x • mgrad F ū x + ū x • mgrad F (χ n) x‖)]
    have hH : ∫ x, ū x ^ 2 * carre F (χ n) (χ n) x ∂μ ≤ K := by
      refine integral_mono hintH hf2 fun x => ?_
      have : carre F (χ n) (χ n) x ≤ 1 := by
        rw [carre_self_eq]
        have := hχ1 n x
        nlinarith [norm_nonneg (mgrad F (χ n) x)]
      nlinarith [sq_nonneg (ū x), carre_nonneg F (χ n) x]
    have h1 : ∫ x, carre F (χ n * ū) (χ n * ū) x ∂μ ≤
        ∫ x, (2 * (χ n x ^ 2 * carre F ū ū x) + 2 * (ū x ^ 2 * carre F (χ n) (χ n) x)) ∂μ :=
      integral_mono hintL ((hintG.const_mul 2).add (hintH.const_mul 2)) hpt
    rw [integral_add (hintG.const_mul 2) (hintH.const_mul 2), integral_const_mul,
      integral_const_mul] at h1
    nlinarith
  exact ((diffT F hV hμ).closed_of_bounded w _ hconv _ hbound).1

include hV hμ in
/-- **Weak eigen-equation** for a smooth `L²` eigenfunction: `E(uL, φ) = c ⟪uL, φ⟫` for all `φ ∈ Q`. -/
theorem weak_eigen_of_smooth {c : ℝ} {ū : M → ℝ} (hū : MSmooth F ū) (hu2 : MemLp ū 2 μ)
    (hL : ∀ x, mgenerator F V ū x = -c * ū x) :
    ∀ φ ∈ (diffT F hV hμ).Q, (diffT F hV hμ).E (hu2.toLp ū) φ = c * inner ℝ (hu2.toLp ū) φ := by
  have hQ := mem_Q_of_eigen F hV hμ hū hu2 hL
  refine (diffT F hV hμ).E_eq_of_dense hQ c ?_
  rintro ⟨_, f, rfl⟩
  show (diffT F hV hμ).E (hu2.toLp ū) (testToL2 F μ f) =
    c * inner ℝ (hu2.toLp ū) (testToL2 F μ f)
  rw [E_testFun_eq F hV hμ hQ f, inner_testToL2_right]
  have e1 : ∫ x, (hu2.toLp ū : M → ℝ) x * mgenerator F V (f : M → ℝ) x ∂μ =
      ∫ x, ū x * mgenerator F V (f : M → ℝ) x ∂μ :=
    integral_congr_ae (hu2.coeFn_toLp.mono fun x hx => by simp only [hx])
  have e2 : ∫ x, (hu2.toLp ū : M → ℝ) x * (f : M → ℝ) x ∂μ = ∫ x, ū x * (f : M → ℝ) x ∂μ :=
    integral_congr_ae (hu2.coeFn_toLp.mono fun x hx => by simp only [hx])
  rw [e1, e2, green_test F hV hμ hū f, ← integral_const_mul, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hL x]; ring

include hV hμ in
/-- **A7: eigenfunction identity in `L²`.**  A smooth `L²` function with `𝓛u = -c u` is an
eigenvector of the Friedrichs semigroup: `T_t u = e^{-ct} u`. -/
theorem eigen_semigroup {c : ℝ} {u : M → ℝ} (hū : MSmooth F u) (hu2 : MemLp u 2 μ)
    (hL : ∀ x, mgenerator F V u x = -c * u x) :
    ∃ uL : M →₂[μ] ℝ, (uL : M → ℝ) =ᵐ[μ] u ∧
      ∀ t : ℝ≥0, (diffFR F hV hμ).semigroup t uL = Real.exp (-c * t) • uL := by
  refine ⟨hu2.toLp u, hu2.coeFn_toLp, ?_⟩
  set uL := hu2.toLp u with huL
  have hQ : uL ∈ (diffT F hV hμ).Q := mem_Q_of_eigen F hV hμ hū hu2 hL
  have hW := weak_eigen_of_smooth F hV hμ hū hu2 hL
  have hself : (diffT F hV hμ).E uL uL = c * ‖uL‖ ^ 2 := by
    rw [hW uL hQ, real_inner_self_eq_norm_sq]
  have hnn := (diffT F hV hμ).E_nonneg hQ
  rw [hself] at hnn
  intro t
  by_cases hc : c < 0
  · have h0 : ‖uL‖ ^ 2 ≤ 0 := by
      by_contra h
      push Not at h
      nlinarith
    have : uL = 0 := norm_eq_zero.1 (by nlinarith [norm_nonneg uL, sq_nonneg ‖uL‖])
    rw [this]; simp
  · push Not at hc
    have h1c : 1 + c ≠ 0 := by linarith
    have hR := (diffFR F hV hμ).R_eigen_of_weak h1c (u := uL) hQ (fun φ => by
      rw [(diffFR F hV hμ).Eext_of_mem hQ φ.2 |>.symm]
      exact hW φ φ.2)
    exact (diffFR F hV hμ).semigroup_eigen hc hR t

end Gaffney

end CutoffRigidity.Riemann.Diff
