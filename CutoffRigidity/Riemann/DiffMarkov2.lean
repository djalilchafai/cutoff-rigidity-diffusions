module

public import CutoffRigidity.Riemann.DiffMarkov1

/-! # The constant `1` lies in the form domain (workstream DIR)

Via the Gaffney cutoffs `weightedCutoffs_of_complete`: `χₙ ∈ 𝒟`, `χₙ → 1` in `L²(μ)`,
`E(χₙ) ≤ μ(M)/(n+1)²`, hence `(χₙ)` is `E`-Cauchy.  So `1 ∈ Q`, `E(1,1) = 0`, `R_λ 1 = λ⁻¹ 1` and
the resolvent is sub-Markov (`resolvent_le_one`).
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section One

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]

theorem mgrad_sub' {f g : M → ℝ} (hf : MSmooth F f) (hg : MSmooth F g) (x : M) :
    mgrad F (fun y => f y - g y) x = mgrad F f x - mgrad F g x := by
  have e : (fun y => f y - g y) = fun y => f y + (-1) * g y := by
    funext y; ring
  have hg' : MSmooth F (fun y => -1 * g y) := contMDiff_const.mul hg
  rw [e, mgrad_add' F hf hg' x, mgrad_const_mul F (-1) hg x, sub_eq_add_neg, neg_smul, one_smul]

/-- The constant function `1` in `L²(μ)`. -/
noncomputable def oneL2 (μ : Measure M) [IsFiniteMeasure μ] : M →₂[μ] ℝ := Lp.const 2 μ (1 : ℝ)

theorem coeFn_oneL2 (μ : Measure M) [IsFiniteMeasure μ] :
    (oneL2 μ : M → ℝ) =ᵐ[μ] fun _ => (1 : ℝ) := Lp.coeFn_const 2 μ (1 : ℝ)

variable {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V) (T : DirFriedrichs (diffFormData F hV hμ))

include hV in
/-- If `‖∇ c‖ ≤ B` then `∫ Γ(c,c) ≤ B² μ(M)`. -/
theorem integral_carre_le (c : testSub F M) {B : ℝ} (hB : ∀ x, ‖mgrad F (c : M → ℝ) x‖ ≤ B) :
    ∫ x, carre F (c : M → ℝ) (c : M → ℝ) x ∂μ ≤ B ^ 2 * μ.real univ := by
  have h1 : ∫ x, carre F (c : M → ℝ) (c : M → ℝ) x ∂μ ≤ ∫ _x, B ^ 2 ∂μ := by
    refine integral_mono (integrable_carre F hV (μ := μ) c c) (integrable_const _) fun x => ?_
    rw [carre_self_eq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB x) 2
  simpa [mul_comm] using h1

include hV in
theorem integral_carre_nonneg (c : testSub F M) :
    0 ≤ ∫ x, carre F (c : M → ℝ) (c : M → ℝ) x ∂μ :=
  integral_nonneg fun x => carre_nonneg F _ x

/-- **`1` lies in the form domain, with zero energy.** -/
theorem one_mem_Q : oneL2 μ ∈ T.Q ∧ T.E (oneL2 μ) (oneL2 μ) = 0 := by
  obtain ⟨χ, hχ, hlim⟩ := weightedCutoffs_of_complete F (M := M)
  set a : ℕ → testSub F M := fun n => ⟨χ n, (hχ n).1, (hχ n).2.1⟩ with ha
  set f : ℕ → (diffFormData F hV hμ).D := fun n => ⟨testToL2 F μ (a n), a n, rfl⟩ with hf
  -- convergence in `L²`
  have hconv : Tendsto (fun n => ((f n : (diffFormData F hV hμ).D) : M →₂[μ] ℝ)) atTop
      (𝓝 (oneL2 μ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq : ∀ n, ‖((f n : (diffFormData F hV hμ).D) : M →₂[μ] ℝ) - oneL2 μ‖ ^ 2 =
        ∫ x, (χ n x - 1) ^ 2 ∂μ := by
      intro n
      rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub ((f n : M →₂[μ] ℝ)) (oneL2 μ), coeFn_oneL2 μ,
        coeFn_testToL2 F μ (a n)] with x h1 h2 h3
      rw [h1, Pi.sub_apply, h2]
      have : ((f n : M →₂[μ] ℝ) : M → ℝ) x = χ n x := h3
      rw [this]
      simp [sq]
    have hint : Tendsto (fun n => ∫ x, (χ n x - 1) ^ 2 ∂μ) atTop (𝓝 0) := by
      have := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1 : ℝ))
        (F := fun n x => (χ n x - 1) ^ 2) (f := fun _ => 0)
        (fun n => ((hχ n).1.continuous.sub continuous_const).pow 2 |>.aestronglyMeasurable)
        (integrable_const _) (fun n => Eventually.of_forall fun x => by
          obtain ⟨h1, h2, _⟩ := (hχ n).2.2 x
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          nlinarith)
        (Eventually.of_forall fun x => by
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [hlim x] with n hn
          simp [hn])
      simpa using this
    have h2 : Tendsto (fun n => ‖((f n : (diffFormData F hV hμ).D) : M →₂[μ] ℝ) - oneL2 μ‖ ^ 2)
        atTop (𝓝 0) := by simpa [hsq] using hint
    have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
    simp only [Real.sqrt_zero] at h3
    refine h3.congr (fun n => ?_)
    simp [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)]
  -- energy Cauchy
  have hdiff : ∀ m n, f m - f n = ⟨testToL2 F μ (a m - a n), a m - a n, rfl⟩ := by
    intro m n
    exact Subtype.ext (by simp [hf, map_sub])
  have hgradle : ∀ n x, ‖mgrad F (a n : M → ℝ) x‖ ≤ 1 / ((n : ℝ) + 1) := fun n x =>
    (hχ n).2.2 x |>.2.2
  have hendiff : ∀ m n, (diffFormData F hV hμ).en (f m - f n) (f m - f n) ≤
      (1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1)) ^ 2 * μ.real univ := by
    intro m n
    rw [hdiff, en_diffFormData F hV hμ]
    refine integral_carre_le F hV (μ := μ) (a m - a n) (fun x => ?_)
    have : mgrad F ((a m - a n : testSub F M) : M → ℝ) x = mgrad F (χ m) x - mgrad F (χ n) x :=
      mgrad_sub' F (hχ m).1 (hχ n).1 x
    rw [this]
    exact (norm_sub_le _ _).trans (add_le_add (hgradle m x) (hgradle n x))
  have hcau : (diffFormData F hV hμ).EnCauchy f := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (4 * μ.real univ / ε)
    refine ⟨N, fun m hm n hn => ?_⟩
    refine lt_of_le_of_lt (hendiff m n) ?_
    have h1 : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hm)
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hn)
    have hμr : 0 ≤ μ.real univ := measureReal_nonneg
    have h3 : (1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1)) ^ 2 ≤ (2 / ((N : ℝ) + 1)) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      have : 2 / ((N : ℝ) + 1) = 1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) := by ring
      rw [this]; exact add_le_add h1 h2
    have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    have h4 : (2 / ((N : ℝ) + 1)) ^ 2 ≤ 4 / ((N : ℝ) + 1) := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc (1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1)) ^ 2 * μ.real univ
        ≤ (4 / ((N : ℝ) + 1)) * μ.real univ := by
          exact mul_le_mul_of_nonneg_right (h3.trans h4) hμr
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hε] at hN
          nlinarith
  refine ⟨(T.mem_Q _).2 ⟨f, hconv, hcau⟩, ?_⟩
  have hlimE := T.E_lim f f (oneL2 μ) (oneL2 μ) hconv hcau hconv hcau
  have hen0 : Tendsto (fun n => (diffFormData F hV hμ).en (f n) (f n)) atTop (𝓝 0) := by
    have hup : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ 2 * μ.real univ) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (h0.pow 2).mul_const (μ.real univ)
    refine squeeze_zero (fun n => (diffFormData F hV hμ).en_nonneg _) (fun n => ?_) hup
    have : (diffFormData F hV hμ).en (f n) (f n) = ∫ x, carre F (a n : M → ℝ) (a n : M → ℝ) x ∂μ :=
      en_diffFormData F hV hμ (a n) (a n)
    rw [this]
    exact integral_carre_le F hV (μ := μ) (a n) (hgradle n)
  exact tendsto_nhds_unique hlimE hen0

theorem E_one_left {φ : M →₂[μ] ℝ} (hφ : φ ∈ T.Q) : T.E (oneL2 μ) φ = 0 :=
  T.E_eq_zero_of_self (one_mem_Q F hV hμ T).1 (one_mem_Q F hV hμ T).2 hφ

/-- `R_λ 1 = λ⁻¹ 1`. -/
theorem resolvent_one {lam : ℝ} (hlam : 0 < lam) {R : (M →₂[μ] ℝ) →L[ℝ] (M →₂[μ] ℝ)}
    (hR : DirResolvent T lam R) : R (oneL2 μ) = lam⁻¹ • oneL2 μ := by
  have h1 : (oneL2 μ) ∈ T.Q := (one_mem_Q F hV hμ T).1
  have hq : lam⁻¹ • oneL2 μ ∈ T.Q := T.Q_smul _ h1
  set u := R (oneL2 μ) - lam⁻¹ • oneL2 μ with hu
  have huQ : u ∈ T.Q := T.Q_sub (hR.mem _) hq
  have key : ∀ φ ∈ T.Q, T.E u φ + lam * inner ℝ u φ = 0 := by
    intro φ hφ
    have := hR.weak (oneL2 μ) φ hφ
    rw [hu, T.E_sub_left (hR.mem _) hq hφ, T.E_smul_left _ h1 hφ, E_one_left F hV hμ T hφ,
      inner_sub_left, real_inner_smul_left]
    have hl : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hlam.ne'
    rw [mul_sub, ← mul_assoc, hl, one_mul, mul_zero, sub_zero]
    linarith
  have h := key u huQ
  rw [real_inner_self_eq_norm_sq] at h
  have hE := T.E_nonneg huQ
  have : ‖u‖ ^ 2 ≤ 0 := by
    by_contra hc
    push Not at hc
    nlinarith
  have hu0 : ‖u‖ = 0 := by nlinarith [norm_nonneg u, sq_nonneg ‖u‖]
  exact sub_eq_zero.1 (norm_eq_zero.1 hu0)

/-- **Sub-Markov property of the resolvent**: `g ≤ 1` a.e. implies `λ R_λ g ≤ 1` a.e. -/
theorem resolvent_le_one {lam : ℝ} (hlam : 0 < lam) {R : (M →₂[μ] ℝ) →L[ℝ] (M →₂[μ] ℝ)}
    (hR : DirResolvent T lam R) (g : M →₂[μ] ℝ) (hg : g ≤ᵐ[μ] fun _ => (1 : ℝ)) :
    ∀ᵐ x ∂μ, lam * (R g) x ≤ 1 := by
  have hpos : 0 ≤ᵐ[μ] (oneL2 μ - g) := by
    filter_upwards [hg, Lp.coeFn_sub (oneL2 μ) g, coeFn_oneL2 μ] with x h1 h2 h3
    rw [Pi.zero_apply, h2, Pi.sub_apply, h3]
    linarith
  have h := resolvent_posPreserving F hV hμ T hlam hR _ hpos
  have e : R (oneL2 μ - g) = lam⁻¹ • oneL2 μ - R g := by
    rw [map_sub, resolvent_one F hV hμ T hlam hR]
  rw [e] at h
  filter_upwards [h, Lp.coeFn_sub (lam⁻¹ • oneL2 μ) (R g), Lp.coeFn_smul lam⁻¹ (oneL2 μ),
    coeFn_oneL2 μ] with x h1 h2 h3 h4
  rw [Pi.zero_apply, h2, Pi.sub_apply, h3, Pi.smul_apply, h4, smul_eq_mul] at h1
  have : lam * (lam⁻¹ * 1 - (R g) x) ≥ 0 := mul_nonneg hlam.le (by linarith)
  have hl : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hlam.ne'
  nlinarith

/-- Positivity preservation for `R_λ` (restated): `g ≥ 0` a.e. implies `R_λ g ≥ 0` a.e. -/
theorem resolvent_nonneg {lam : ℝ} (hlam : 0 < lam) {R : (M →₂[μ] ℝ) →L[ℝ] (M →₂[μ] ℝ)}
    (hR : DirResolvent T lam R) (g : M →₂[μ] ℝ) (hg : 0 ≤ᵐ[μ] g) : 0 ≤ᵐ[μ] R g :=
  resolvent_posPreserving F hV hμ T hlam hR g hg

end One

end CutoffRigidity.Riemann.Diff
