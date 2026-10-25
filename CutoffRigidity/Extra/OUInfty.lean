module

public import CutoffRigidity.Extra.OUMeanStart

/-! # `p = ∞` fails for the Ornstein–Uhlenbeck process (manuscript L407)

For `V = ρ|x|²/2 + c` and every `x₀`, every `t`, the `L^∞(μ)` distance of the law of `X_t^{x₀}`
to `μ` is at least `exp(ρ|x₀|²/2) - 1`. With `|x₀|² = c² n` this diverges, so the `L^∞` analogue of
(1.25) (limit `0` after the critical time) fails.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff

universe u

section Gaussian

variable {d : ℕ}

theorem stdGaussian_integrable_exp_inner (w : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun z => Real.exp (inner ℝ w z)) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  set L : StrongDual ℝ (EuclideanSpace ℝ (Fin d)) := innerSL ℝ w
  have hmap := IsGaussian.map_eq_gaussianReal (μ := stdGaussian (EuclideanSpace ℝ (Fin d))) L
  have h := integrable_exp_mul_gaussianReal (μ := ((stdGaussian (EuclideanSpace ℝ (Fin d)))[L]))
    (v := (Var[L; stdGaussian (EuclideanSpace ℝ (Fin d))]).toNNReal) 1
  rw [← hmap] at h
  rw [integrable_map_measure (by fun_prop) L.continuous.aemeasurable] at h
  simpa [L, Function.comp_def] using h

theorem stdGaussian_integral_exp_inner (w : EuclideanSpace ℝ (Fin d)) :
    ∫ z, Real.exp (inner ℝ w z) ∂stdGaussian (EuclideanSpace ℝ (Fin d)) =
      Real.exp (‖w‖ ^ 2 / 2) := by
  set L : StrongDual ℝ (EuclideanSpace ℝ (Fin d)) := innerSL ℝ w with hL
  have hnorm : ‖L‖ = ‖w‖ := by simp [L]
  have hmap := IsGaussian.map_eq_gaussianReal (μ := stdGaussian (EuclideanSpace ℝ (Fin d))) L
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian, hnorm] at hmap
  have hlaw : HasLaw L (gaussianReal 0 (‖w‖ ^ 2).toNNReal) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    ⟨L.continuous.aemeasurable, hmap⟩
  have h := mgf_gaussianReal hlaw 1
  unfold mgf at h
  simp only [one_mul, zero_add, mul_one, one_pow] at h
  rw [Real.coe_toNNReal _ (sq_nonneg _)] at h
  simpa [L] using h

/-- Domination by a multiple of the standard Gaussian bounds the exponential moments. -/
theorem affineGaussian_mgf_bound (m : EuclideanSpace ℝ (Fin d)) (s : ℝ) (K : ℝ) (hK : 0 ≤ K)
    (h : affineGaussian m s ≤ ENNReal.ofReal K • stdGaussian (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d)) :
    Real.exp (inner ℝ u m + s ^ 2 * ‖u‖ ^ 2 / 2) ≤ K * Real.exp (‖u‖ ^ 2 / 2) := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d)) with hγ
  have hint : Integrable (fun y : EuclideanSpace ℝ (Fin d) => Real.exp (inner ℝ u y))
      (affineGaussian m s) := by
    unfold affineGaussian
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    have := (stdGaussian_integrable_exp_inner (s • u)).const_mul (Real.exp (inner ℝ u m))
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [Function.comp_apply, inner_add_right, inner_smul_right, real_inner_smul_left,
      Real.exp_add]
  have hA : ∫ y, Real.exp (inner ℝ u y) ∂affineGaussian m s =
      Real.exp (inner ℝ u m + s ^ 2 * ‖u‖ ^ 2 / 2) := by
    unfold affineGaussian
    rw [integral_map (by fun_prop) (by fun_prop)]
    have : ∀ z : EuclideanSpace ℝ (Fin d), Real.exp (inner ℝ u (m + s • z)) =
        Real.exp (inner ℝ u m) * Real.exp (inner ℝ (s • u) z) := by
      intro z
      rw [← Real.exp_add, inner_add_right, inner_smul_right, real_inner_smul_left]
    simp_rw [this]
    rw [integral_const_mul, stdGaussian_integral_exp_inner, ← Real.exp_add, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
  have hl : ∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ u y)) ∂affineGaussian m s ≤
      ENNReal.ofReal K * ∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ u y)) ∂γ := by
    calc _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ u y)) ∂(ENNReal.ofReal K • γ) :=
          lintegral_mono' h le_rfl
      _ = _ := lintegral_smul_measure _ _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => (Real.exp_pos _).le),
    ← ofReal_integral_eq_lintegral_ofReal (stdGaussian_integrable_exp_inner u)
      (Eventually.of_forall fun _ => (Real.exp_pos _).le), hA,
    stdGaussian_integral_exp_inner, ← ENNReal.ofReal_mul hK,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hl
  exact hl

end Gaussian

section Domination

theorem relLp_top_dominated {α : Type*} [MeasurableSpace α] {ν μ : Measure α} [IsFiniteMeasure ν]
    [SigmaFinite μ] {M : ℝ} (hM : 0 ≤ M) (h : CutCur.relLp ν μ ⊤ ≤ ENNReal.ofReal M) :
    ν ≤ ENNReal.ofReal (1 + M) • μ := by
  classical
  unfold CutCur.relLp at h
  by_cases hac : ν ≪ μ
  · have hmeas : AEStronglyMeasurable (fun x => (ν.rnDeriv μ x).toReal - 1) μ :=
      ((Measure.measurable_rnDeriv ν μ).ennreal_toReal.sub measurable_const).aestronglyMeasurable
    rw [if_pos hac, eLpNorm_exponent_top hmeas] at h
    have hae := enorm_ae_le_eLpNormEssSup (fun x => (ν.rnDeriv μ x).toReal - 1) μ
    have hlt := Measure.rnDeriv_lt_top ν μ
    have hle : ν.rnDeriv μ ≤ᵐ[μ] fun _ => ENNReal.ofReal (1 + M) := by
      filter_upwards [hae, hlt] with x hx hx2
      have h1 : ‖(ν.rnDeriv μ x).toReal - 1‖ₑ ≤ ENNReal.ofReal M := hx.trans h
      rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hM] at h1
      rw [← ENNReal.ofReal_toReal hx2.ne]
      apply ENNReal.ofReal_le_ofReal
      have := (abs_le.mp (by simpa using h1)).2
      linarith
    calc ν = μ.withDensity (ν.rnDeriv μ) := (Measure.withDensity_rnDeriv_eq ν μ hac).symm
      _ ≤ μ.withDensity (fun _ => ENNReal.ofReal (1 + M)) := withDensity_mono hle
      _ = _ := by rw [withDensity_const]
  · rw [if_neg hac] at h
    exact absurd h (by simp)

end Domination


section Main

variable {d : ℕ}

/-- Quantitative failure of `L^∞`: the `L^∞(μ)` distance of the law of `X_t^{x₀}` to `μ` is at
least `exp(ρ|x₀|²/2) - 1`, for every time. -/
theorem ou_relLp_top_ge (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {c : ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω}
    {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hL : CutCur.IsLangevin (fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c) B P X)
    (x₀ : CutCur.Rd d) (t : ℝ≥0) :
    ENNReal.ofReal (Real.exp (ρ / 2 * ‖x₀‖ ^ 2) - 1) ≤
      CutCur.relLp (P.map (X x₀ t)) (CutCur.gibbs fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c) ⊤ := by
  set V := fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c with hV
  have hVc : ContDiff ℝ 2 V := hL.1
  have hp : IsProbabilityMeasure (CutCur.gibbs V) := hL.2.1
  have hp' : IsProbabilityMeasure (gibbsMeasure volume V) := hp
  obtain ⟨hgap, hess⟩ := ou_gap_rigid hd hρ hp
  have hB : IsEuclideanBrownian B P := isStdBrownian_iff.mp hL.2.2.1
  -- affine data
  let a : Fin d → CutCur.Rd d := fun i => Real.sqrt ρ • EuclideanSpace.single i (1 : ℝ)
  have heig : ∀ i x, langevinDifferentialOperator V
      (fun y => inner ℝ (a i) y + (fun _ : Fin d => (0 : ℝ)) i) x =
      -ρ * (inner ℝ (a i) x + (fun _ : Fin d => (0 : ℝ)) i) := by
    intro i
    refine (affine_eigenfunction_iff_drift V (a i) 0 ρ).mpr fun x => ?_
    rw [show gradient V x = ρ • x from gradient_ou ρ c x]
    simp only [a, real_inner_smul_right, add_zero]
  have horth : ∀ i j, ∫ x, (inner ℝ (a i) x + (fun _ : Fin d => (0 : ℝ)) i) *
      (inner ℝ (a j) x + (fun _ : Fin d => (0 : ℝ)) j) ∂gibbsMeasure volume V =
      if i = j then 1 else 0 := by
    intro i j
    have := (ou_first_eigenspace hd hρ hp).2.2.2 i j
    have e1 : ∀ x : CutCur.Rd d, inner ℝ (a i) x = Real.sqrt ρ * x i := fun x => by
      simp [a, real_inner_smul_left, EuclideanSpace.inner_single_left]
    have e2 : ∀ x : CutCur.Rd d, inner ℝ (a j) x = Real.sqrt ρ * x j := fun x => by
      simp [a, real_inner_smul_left, EuclideanSpace.inner_single_left]
    simp only [add_zero, e1, e2]
    exact this
  have hlaw := langevinKernel_map_affineEigenfunctionMap hB hVc ρ hρ.le hess a
    (fun _ => 0) ρ hρ heig hp' horth x₀ t
  have hgib := gibbsMeasure_map_affineEigenfunctionMap hVc a (fun _ => 0) ρ hρ heig hp' horth
  have hA : affineEigenfunctionMap a (fun _ : Fin d => (0 : ℝ)) = fun x => Real.sqrt ρ • x := by
    funext x
    ext i
    simp [affineEigenfunctionMap, a, EuclideanSpace.inner_single_left, real_inner_smul_left]
  rw [hA] at hlaw hgib
  have hν : P.map (X x₀ t) = langevinKernel V B P t x₀ :=
    IsLangevin.map_eq_langevinKernel hL ρ hρ.le hess x₀ t
  have hmk := langevinKernel_isMarkovKernel hB hVc ρ hρ.le hess t
  have hνp : IsProbabilityMeasure (langevinKernel V B P t x₀) := inferInstance
  rw [hν]
  by_contra hlt
  rw [not_le] at hlt
  set R := CutCur.relLp (langevinKernel V B P t x₀) (CutCur.gibbs V) ⊤ with hR
  have hRtop : R ≠ ⊤ := ne_top_of_lt hlt
  set M := R.toReal with hM
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hRM : R ≤ ENNReal.ofReal M := (ENNReal.ofReal_toReal hRtop).ge
  have hdom := relLp_top_dominated (ν := langevinKernel V B P t x₀) (μ := CutCur.gibbs V) hM0 hRM
  have hmeas : Measurable (fun x : CutCur.Rd d => Real.sqrt ρ • x) := by fun_prop
  have hdom' := Measure.map_mono hdom hmeas
  rw [Measure.map_smul] at hdom'
  change Measure.map _ (gibbsMeasure volume V) = _ at hgib
  rw [hlaw, show Measure.map (fun x => Real.sqrt ρ • x) (CutCur.gibbs V) = _ from hgib] at hdom'
  -- the exponential-moment test
  have hδsq : ouDecay ρ t ^ 2 = Real.exp (-2 * ρ * (t : ℝ)) := ouDecay_sq ρ t
  have hδne : ouDecay ρ t ≠ 0 := by
    intro h0
    have h3 : Real.exp (-2 * ρ * (t : ℝ)) = 0 := by rw [← hδsq, h0]; norm_num
    exact (Real.exp_pos _).ne' h3
  have hs2 : ouNoise ρ t ^ 2 = 1 - ouDecay ρ t ^ 2 := by
    rw [hδsq]; exact ouNoise_sq hρ.le t.coe_nonneg
  set δ := ouDecay ρ t with hδ
  have hbound := affineGaussian_mgf_bound (δ • (Real.sqrt ρ • x₀)) (ouNoise ρ t) (1 + M)
    (by linarith) hdom' ((δ⁻¹ * Real.sqrt ρ) • x₀)
  have hρs : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt hρ.le
  rw [hs2] at hbound
  have e1 : inner ℝ ((δ⁻¹ * Real.sqrt ρ) • x₀) (δ • (Real.sqrt ρ • x₀)) = ρ * ‖x₀‖ ^ 2 := by
    rw [inner_smul_right, inner_smul_right, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
    rw [hρs]
    ring
  have e2 : ‖(δ⁻¹ * Real.sqrt ρ) • x₀‖ ^ 2 = δ⁻¹ ^ 2 * ρ * ‖x₀‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_pow, hρs]
  rw [e1, e2] at hbound
  have hfinal : Real.exp (ρ / 2 * ‖x₀‖ ^ 2) ≤ 1 + M := by
    have hB' := (div_le_iff₀ (Real.exp_pos _)).mpr hbound
    rw [← Real.exp_sub] at hB'
    refine le_trans (le_of_eq ?_) hB'
    congr 1
    field_simp
    ring
  have hMlt : M < Real.exp (ρ / 2 * ‖x₀‖ ^ 2) - 1 := by
    have := ENNReal.toReal_strict_mono (ENNReal.ofReal_ne_top) hlt
    rwa [ENNReal.toReal_ofReal (by
      by_contra hneg
      rw [not_le] at hneg
      rw [ENNReal.ofReal_of_nonpos hneg.le] at hlt
      exact absurd hlt (not_lt_zero))] at this
  linarith
  · exact hmeas.aemeasurable

end Main

/-- **`p = ∞` fails for the Ornstein–Uhlenbeck process** (after (1.25)): for
`V⁽ⁿ⁾(x) = ρ|x|²/2 + c⁽ⁿ⁾` with `ρ > 0` and the balls `B(m, c√n)`, `c > 0`, the worst-case
`L^∞(μ)` distance `‖dμ_t/dμ - 1‖_{L^∞(μ)}` tends to `+∞` along every sequence of times
(in particular after the critical time), so the analogue of (1.25) with `p = ∞`
(limit `0` at `(1+ε)t_*`) fails. -/
theorem ou_lp_infty_fails {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] {ρ : ℝ} (hρ : 0 < ρ)
    {c' : ℕ → ℝ} {B : ∀ n, ℝ≥0 → Ω n → CutCur.Rd n} {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, CutCur.Rd n → ℝ≥0 → Ω n → CutCur.Rd n}
    (hL : ∀ n, 0 < n →
      CutCur.IsLangevin (fun x : CutCur.Rd n => ρ / 2 * ‖x‖ ^ 2 + c' n) (B n) (P n) (X n))
    {c : ℝ} (hc : 0 < c) :
    let V := fun n (x : CutCur.Rd n) => ρ / 2 * ‖x‖ ^ 2 + c' n
    let prof := fun n => CutCur.worst (P n) (X n) (CutCur.meanBall (V n) c)
      (CutCur.relLp · (CutCur.gibbs (V n)) ⊤)
    (∀ t : ℕ → ℝ, Tendsto (fun n => prof n (t n)) atTop (𝓝 ⊤)) ∧
      ¬ CutCur.HasCutoff prof (fun n => CutCur.criticalTime n (CutCur.spectralGap (V n))) ⊤ 0 := by
  intro V prof
  have hev : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hlow : ∀ n : ℕ, 0 < n → ∀ t : ℝ,
      ENNReal.ofReal (Real.exp (ρ / 2 * (c ^ 2 * n)) - 1) ≤ prof n t := by
    intro n hn t
    have hm : ∫ x, x ∂CutCur.gibbs (V n) = 0 := ou_mean_zero hn hρ (hL n hn).2.1
    set x₀ : CutCur.Rd n := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (c * Real.sqrt n) with hx₀
    have hnorm : ‖x₀‖ = c * Real.sqrt n := by
      simp [hx₀, PiLp.norm_single, abs_of_nonneg hc.le, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hmem : x₀ ∈ CutCur.meanBall (V n) c := by
      simp only [CutCur.meanBall, hm, Metric.mem_closedBall, dist_zero_right, hnorm]
      exact le_rfl
    have hsq : ‖x₀‖ ^ 2 = c ^ 2 * n := by
      rw [hnorm, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    have := ou_relLp_top_ge hn hρ (hL n hn) x₀ t.toNNReal
    rw [hsq] at this
    exact this.trans (le_iSup₂ (f := fun x₀ (_ : x₀ ∈ CutCur.meanBall (V n) c) =>
      CutCur.relLp ((P n).map (X n x₀ t.toNNReal)) (CutCur.gibbs (V n)) ⊤) x₀ hmem)
  have hgrow : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (ρ / 2 * (c ^ 2 * n)) - 1))
      atTop (𝓝 ⊤) := by
    refine ENNReal.tendsto_ofReal_atTop.comp ?_
    have h1 : Tendsto (fun n : ℕ => ρ / 2 * (c ^ 2 * n)) atTop atTop :=
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)).const_mul_atTop (by positivity)
    exact tendsto_atTop_add_const_right _ (-1) (Real.tendsto_exp_atTop.comp h1)
  have hall : ∀ t : ℕ → ℝ, Tendsto (fun n => prof n (t n)) atTop (𝓝 ⊤) := by
    intro t
    refine tendsto_nhds_top_mono hgrow ?_
    filter_upwards [hev] with n hn using hlow n hn (t n)
  refine ⟨hall, fun hcut => ?_⟩
  obtain ⟨-, ha⟩ := hcut (1 / 2) (by norm_num) (by norm_num)
  have := tendsto_nhds_unique ha (hall fun n : ℕ => (1 + 1 / 2) * CutCur.criticalTime n
    (CutCur.spectralGap (V n)))
  exact ENNReal.top_ne_zero this.symm

end CutoffRigidity.Paper
