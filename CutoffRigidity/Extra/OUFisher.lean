module

public import CutoffRigidity.GaussianDensity
public import CutoffRigidity.GaussianMoments
public import CutoffRigidity.GaussianEntropy
public import CutoffRigidity.SmoothFisherInformation
public import CutoffRigidity.VectorMehlerLaw
public import CutoffRigidity.Paper.CoreBridge
public import CutoffRigidity.Paper.FisherBridge
public import CutoffRigidity.Paper.SeqData

/-! # Fisher information along the Ornstein-Uhlenbeck process (manuscript, Section 4.1) -/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff

/-- Coordinate densities multiply for finite products of sigma-finite measures. -/
theorem pi_eq_withDensity_of_coordinates' (n : ℕ) (μ ν : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (f : Fin n → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (hμ : ∀ i, μ i = (ν i).withDensity (f i)) :
    Measure.pi μ = (Measure.pi ν).withDensity (fun x => ∏ i, f i (x i)) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    rw [← Pi.one_def, withDensity_one]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    apply e.measurableEmbedding.map_injective
    rw [(measurePreserving_piFinSuccAbove μ 0).map_eq]
    rw [map_withDensity_measurableEquiv e _ _ (by fun_prop)]
    rw [(measurePreserving_piFinSuccAbove ν 0).map_eq]
    simp only [Fin.succAbove_zero]
    rw [hμ 0, ih (fun i => μ i.succ) (fun i => ν i.succ)
      (fun i => f i.succ) (fun i => hf i.succ) (fun i => hμ i.succ)]
    rw [prod_withDensity (hf 0) (by fun_prop)]
    congr 1
    ext z
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Fin.prod_univ_succ]


/-- The product of the coordinate Gaussian densities, in closed form. -/
theorem prod_gaussianPDFReal_eq {n : ℕ} (m x : EuclideanSpace ℝ (Fin n)) (s : ℝ≥0) (hs : s ≠ 0) :
    ∏ i, gaussianPDFReal (m i) s (x i) =
      Real.exp (-(n / 2 : ℝ) * Real.log (2 * Real.pi * s) - ‖x - m‖ ^ 2 / (2 * s)) := by
  have hs' : (0 : ℝ) < s := by positivity
  have hp : (0 : ℝ) < 2 * Real.pi * s := by positivity
  simp only [gaussianPDFReal_def]
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum, Finset.card_univ,
    Fintype.card_fin, sub_eq_add_neg, Real.exp_add]
  congr 1
  · have h1 : (Real.sqrt (2 * Real.pi * s))⁻¹ = Real.exp (-(1 / 2 : ℝ) * Real.log (2 * Real.pi * s)) := by
      rw [← Real.exp_log (Real.sqrt_pos.mpr hp), Real.log_sqrt hp.le, ← Real.exp_neg]
      congr 1
      ring
    rw [h1, ← Real.exp_nat_mul]
    congr 1
    ring
  · congr 1
    rw [EuclideanSpace.real_norm_sq_eq, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [neg_div]

/-- The isotropic Gaussian `𝒩(m, s I_n)` has the explicit Lebesgue density. -/
theorem multivariateGaussian_smul_one_eq_withDensity {n : ℕ} (m : EuclideanSpace ℝ (Fin n))
    (s : ℝ≥0) (hs : s ≠ 0) :
    multivariateGaussian m ((s : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) =
      volume.withDensity fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal
        (Real.exp (-(n / 2 : ℝ) * Real.log (2 * Real.pi * s) - ‖x - m‖ ^ 2 / (2 * s))) := by
  have hmat : Matrix.diagonal (fun _ : Fin n => (s : ℝ)) = (s : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [← hmat, ← gaussian_pi_eq_multivariate m (fun _ => s)]
  have hpi := pi_eq_withDensity_of_coordinates' n (fun i => gaussianReal (m i) s)
    (fun _ : Fin n => (volume : Measure ℝ)) (fun i x => gaussianPDF (m i) s x)
    (fun i => measurable_gaussianPDF _ _) (fun i => gaussianReal_of_var_ne_zero _ hs)
  rw [hpi]
  change (((Measure.pi fun _ : Fin n => (volume : Measure ℝ)).withDensity _).map
    (MeasurableEquiv.toLp 2 (Fin n → ℝ))) = _
  rw [map_withDensity_measurableEquiv _ _ _ (by fun_prop)]
  have hv : (Measure.pi fun _ : Fin n => (volume : Measure ℝ)).map (MeasurableEquiv.toLp 2 (Fin n → ℝ)) =
      volume := (PiLp.volume_preserving_toLp (Fin n)).map_eq
  rw [hv]
  congr 1
  ext x
  simp only [gaussianPDF_def]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)]
  congr 1
  exact prod_gaussianPDFReal_eq m x s hs

section Fisher

variable {n : ℕ}

theorem gradient_norm_sq_sub (m x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y : EuclideanSpace ℝ (Fin n) => ‖y - m‖ ^ 2) x = (2 : ℝ) • (x - m) := by
  have hd : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => ‖y - m‖ ^ 2)
      (2 • (innerSL ℝ (x - m))) x := by
    have h := (hasStrictFDerivAt_norm_sq (x - m)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const m)
    exact h.congr_fderiv (by ext z; simp [two_smul])
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left, hd.fderiv, real_inner_smul_left]
  simp only [two_smul, inner_sub_left, add_apply, innerSL_apply_apply]
  ring

/-- The gradient of the quadratic potential, up to an additive constant. -/
theorem gradient_quadratic_add_const (ρ c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y : EuclideanSpace ℝ (Fin n) => ρ / 2 * ‖y‖ ^ 2 + c) x = ρ • x := by
  have h : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => ρ / 2 * ‖y‖ ^ 2 + c) x =
      fderiv ℝ (quadraticLangevinPotential ρ) x := by
    unfold quadraticLangevinPotential
    exact fderiv_add_const c
  rw [gradient, h, ← gradient, gradient_quadraticLangevinPotential]

/-- Fisher information of an isotropic Gaussian relative to a quadratic Gibbs measure: the score
`∇log(dν/dμ)(x) = ρ x - (x - m)/s` is integrated against `ν = 𝒩(m, s I)`. -/
theorem fisherInfo_gaussian_quadratic {ρ c : ℝ} (hρ : 0 < ρ)
    (hp : IsProbabilityMeasure (CutCur.gibbs fun y : CutCur.Rd n => ρ / 2 * ‖y‖ ^ 2 + c))
    (m : CutCur.Rd n) (s : ℝ≥0) (hs : s ≠ 0) :
    let V := fun y : CutCur.Rd n => ρ / 2 * ‖y‖ ^ 2 + c
    let u := fun y : CutCur.Rd n => V y - (n / 2 : ℝ) * Real.log (2 * Real.pi * s) - ‖y - m‖ ^ 2 / (2 * s)
    let ν := multivariateGaussian m ((s : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))
    ContDiff ℝ ∞ u ∧ (∀ y, gradient u y = (ρ • y - (s : ℝ)⁻¹ • (y - m))) ∧
      ν = (CutCur.gibbs V).withDensity (fun y => ENNReal.ofReal (Real.exp (u y))) ∧
      CutCur.fisherInfo V ν = ENNReal.ofReal (∫ y, ‖ρ • y - (s : ℝ)⁻¹ • (y - m)‖ ^ 2 ∂ν) := by
  intro V u ν
  have hs' : (0 : ℝ) < s := by positivity
  have hVs : ContDiff ℝ ∞ V := by
    have : ContDiff ℝ ∞ (fun y : CutCur.Rd n => ‖y‖ ^ 2) := contDiff_norm_sq ℝ
    exact (contDiff_const.mul this).add contDiff_const
  have hN : ContDiff ℝ ∞ (fun y : CutCur.Rd n => ‖y - m‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  have huS : ContDiff ℝ ∞ u := (hVs.sub contDiff_const).sub (hN.div_const _)
  have hgu : ∀ y, gradient u y = ρ • y - (s : ℝ)⁻¹ • (y - m) := by
    intro y
    have hNd : DifferentiableAt ℝ (fun y : CutCur.Rd n => ‖y - m‖ ^ 2) y :=
      (hN.differentiable (by simp)) y
    have hVd : DifferentiableAt ℝ V y := (hVs.differentiable (by simp)) y
    have hf : HasFDerivAt u (fderiv ℝ V y - (2 * (s : ℝ))⁻¹ • fderiv ℝ (fun y : CutCur.Rd n => ‖y - m‖ ^ 2) y) y := by
      have h := (hVd.hasFDerivAt.sub_const ((n / 2 : ℝ) * Real.log (2 * Real.pi * s))).sub
        (hNd.hasFDerivAt.const_mul ((2 * (s : ℝ))⁻¹))
      have hu' : u = fun y => V y - (n / 2 : ℝ) * Real.log (2 * Real.pi * s) -
          (2 * (s : ℝ))⁻¹ * ‖y - m‖ ^ 2 := by
        funext y; simp only [u, div_eq_inv_mul]
      rw [hu']
      convert h using 1
    apply ext_inner_right ℝ
    intro z
    rw [inner_gradient_left, hf.fderiv]
    simp only [sub_apply, smul_apply, smul_eq_mul]
    rw [← inner_gradient_left (f := V), ← inner_gradient_left (f := fun y : CutCur.Rd n => ‖y - m‖ ^ 2),
      gradient_norm_sq_sub, show V = fun y : CutCur.Rd n => ρ / 2 * ‖y‖ ^ 2 + c from rfl,
      gradient_quadratic_add_const, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left]
    field_simp
  have hν : ν = (CutCur.gibbs V).withDensity (fun y => ENNReal.ofReal (Real.exp (u y))) := by
    show multivariateGaussian m ((s : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) = (volume.withDensity
      fun x => ENNReal.ofReal (Real.exp (-V x))).withDensity _
    have hm1 : Measurable fun x : CutCur.Rd n => ENNReal.ofReal (Real.exp (-V x)) :=
      hVs.continuous.neg.rexp.measurable.ennreal_ofReal
    have hm2 : Measurable fun x : CutCur.Rd n => ENNReal.ofReal (Real.exp (u x)) :=
      huS.continuous.rexp.measurable.ennreal_ofReal
    rw [multivariateGaussian_smul_one_eq_withDensity m s hs,
      ← withDensity_mul _ hm1 hm2]
    congr 1
    funext y
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 2
    simp only [u]
    ring
  have hV2 : ContDiff ℝ 2 V := hVs.of_le (by simp)
  have hprob : IsProbabilityMeasure (gibbsMeasure volume V) := hp
  have hHess : ∀ x z : CutCur.Rd n, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z := by
    intro x z
    have h : fderiv ℝ V = fderiv ℝ (quadraticLangevinPotential ρ) := by
      funext y
      unfold quadraticLangevinPotential
      exact fderiv_add_const c
    rw [h, hessian_quadraticLangevinPotential]
  have hνprob : IsProbabilityMeasure ν := by infer_instance
  have hνe : ν = exponentialDensityMeasure (gibbsMeasure volume V) u := hν
  have hI : Integrable (fun y => ‖gradient u y‖ ^ 2) ν := by
    have hm : MemLp (fun y : CutCur.Rd n => ρ • y - (s : ℝ)⁻¹ • (y - m)) 2 ν := by
      have h1 : MemLp (id : CutCur.Rd n → CutCur.Rd n) 2 ν := IsGaussian.memLp_id ν 2 (by norm_num)
      have h2 := (h1.const_smul ρ).sub ((h1.sub (memLp_const m)).const_smul ((s : ℝ)⁻¹))
      exact h2
    have := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
    simpa only [hgu] using this
  refine ⟨huS, hgu, hν, ?_⟩
  have hνp' : IsProbabilityMeasure (exponentialDensityMeasure (gibbsMeasure volume V) u) := by
    rw [← hνe]; exact hνprob
  have hI' : Integrable (fun y => ‖gradient u y‖ ^ 2)
      (exponentialDensityMeasure (gibbsMeasure volume V) u) := by
    rw [← hνe]; exact hI
  have key' := relativeFisherInformation_exponential hV2 hprob (huS.of_le (by simp)) hνp' hI'
  have aux : ∀ ν' : Measure (CutCur.Rd n), ν' = exponentialDensityMeasure (gibbsMeasure volume V) u →
      ∀ [IsProbabilityMeasure ν'], relativeFisherInformation hV2 hprob ν' =
      ENNReal.ofReal (∫ x, ‖gradient u x‖ ^ 2 ∂ν') := by
    intro ν' h _
    subst h
    exact key'
  have key := aux ν hνe
  rw [fisherInfo_eq_relativeFisherInformation hV2 hprob ρ hρ hHess ν, key]
  simp only [hgu]

end Fisher

section OU

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- Mehler's formula for an actual Langevin solution of the quadratic potential. -/
theorem ou_law_of_isLangevin {ρ c : ℝ} (hρ : 0 < ρ)
    {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hL : CutCur.IsLangevin (fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c) B P X)
    (x₀ : CutCur.Rd d) {t : ℝ} (ht : 0 < t) :
    P.map (X x₀ t.toNNReal) = multivariateGaussian (Real.exp (-ρ * t) • x₀)
      (((1 - Real.exp (-2 * ρ * t)) / ρ) • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
  have hB := isStdBrownian_iff.mp hL.2.2.1
  have hX := hL.2.2.2 x₀
  have hg : gradient (fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c) = gradient (quadraticLangevinPotential ρ) := by
    funext x
    rw [gradient_quadratic_add_const, gradient_quadraticLangevinPotential]
  have hX' : CutCur.IsLangevinSolution (quadraticLangevinPotential ρ) B P x₀ (X x₀) := by
    unfold CutCur.IsLangevinSolution at hX ⊢
    simpa only [hg] using hX
  have hae := IsLangevinSolution.ae_eq_langevinProcess hB (contDiff_quadraticLangevinPotential ρ) ρ
    hρ.le (fun x z => (hessian_quadraticLangevinPotential ρ x z).ge) hX' t.toNNReal
  rw [Measure.map_congr hae]
  have hT : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht.le
  have h := quadratic_langevinSolution_vector_hasLaw hB ρ (Real.sqrt 2) t hρ ht.le x₀
  have hv : (Real.sqrt 2) ^ 2 * (1 - Real.exp (-2 * ρ * t)) / (2 * ρ) =
      (1 - Real.exp (-2 * ρ * t)) / ρ := by
    rw [Real.sq_sqrt (by norm_num)]
    field_simp
  rw [hv] at h
  have h2 := h.map_eq
  have h3 : P.map (langevinProcess (quadraticLangevinPotential ρ) B x₀ t.toNNReal) =
      P.map (fun w => langevinSolution (quadraticLangevinPotential ρ)
        (fun s : ℝ => Real.sqrt 2 • B s.toNNReal w) x₀ t) := by
    conv_rhs => rw [← hT]
    rfl
  rw [h3, h2]

/-- **Fisher information and the heat kernel (OU case, manuscript Section 4.1).**
For `V(x) = ρ|x|²/2 + c` (the constant `c` is forced by `μ = e^{-V}` being a probability
measure) and a Langevin solution `X` from `x₀`, for every `t > 0`:
the law `μ_t` of `X_t` is `𝒩(e^{-ρt}x₀, ((1-e^{-2ρt})/ρ) I_d)`; `μ_t` has a smooth log-density
`u = log dμ_t/dμ` with `∇u(x) = a_t x + b_t x₀`, where `a_t`, `b_t` depend neither on `d`
nor on `x₀`; and `I(μ_t | μ) = ρ d e^{-4ρt}/(1-e^{-2ρt}) + ρ² e^{-2ρt}|x₀|²`. -/
theorem ou_fisher_information {ρ c : ℝ} (hρ : 0 < ρ)
    {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hL : CutCur.IsLangevin (fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c) B P X)
    (x₀ : CutCur.Rd d) {t : ℝ} (ht : 0 < t) :
    let V := fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c
    let μt := P.map (X x₀ t.toNNReal)
    μt = multivariateGaussian (Real.exp (-ρ * t) • x₀)
        (((1 - Real.exp (-2 * ρ * t)) / ρ) • (1 : Matrix (Fin d) (Fin d) ℝ)) ∧
      (∃ u : CutCur.Rd d → ℝ, ContDiff ℝ ∞ u ∧
        μt = (CutCur.gibbs V).withDensity (fun x => ENNReal.ofReal (Real.exp (u x))) ∧
        (∀ᵐ x ∂CutCur.gibbs V, u x = Real.log (μt.rnDeriv (CutCur.gibbs V) x).toReal) ∧
        ∀ x, gradient u x = (ρ - ρ / (1 - Real.exp (-2 * ρ * t))) • x +
          (ρ * Real.exp (-ρ * t) / (1 - Real.exp (-2 * ρ * t))) • x₀) ∧
      CutCur.fisherInfo V μt = ENNReal.ofReal
        (ρ * d * Real.exp (-4 * ρ * t) / (1 - Real.exp (-2 * ρ * t)) +
          ρ ^ 2 * Real.exp (-2 * ρ * t) * ‖x₀‖ ^ 2) := by
  intro V μt
  have hlaw := ou_law_of_isLangevin hρ hL x₀ ht
  have hp : IsProbabilityMeasure (CutCur.gibbs V) := hL.2.1
  set r := Real.exp (-ρ * t) with hr
  set q := Real.exp (-2 * ρ * t) with hq
  have hr0 : 0 < r := Real.exp_pos _
  have hqr : q = r ^ 2 := by
    rw [hq, hr, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by rw [hq, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith)
  have h1q : 0 < 1 - q := by linarith
  have hsv : 0 < (1 - q) / ρ := by positivity
  let s : ℝ≥0 := Real.toNNReal ((1 - q) / ρ)
  have hs : (s : ℝ) = (1 - q) / ρ := Real.coe_toNNReal _ hsv.le
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; linarith
  obtain ⟨hu, hgrad, hν, hF⟩ := fisherInfo_gaussian_quadratic hρ hp (r • x₀) s hs0
  have hlaw' : μt = multivariateGaussian (r • x₀) ((s : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
    rw [hs]; exact hlaw
  have hμe : μt = (CutCur.gibbs V).withDensity (fun y => ENNReal.ofReal (Real.exp
      (V y - (d / 2 : ℝ) * Real.log (2 * Real.pi * s) - ‖y - r • x₀‖ ^ 2 / (2 * s)))) :=
    hlaw'.trans hν
  refine ⟨hlaw, ⟨_, hu, hμe, ?_, ?_⟩, ?_⟩
  · have : IsProbabilityMeasure (gibbsMeasure volume V) := hp
    have hu' := llr_exponentialDensityMeasure (μ := gibbsMeasure volume V)
      (u := fun y => V y - (d / 2 : ℝ) * Real.log (2 * Real.pi * s) - ‖y - r • x₀‖ ^ 2 / (2 * s))
      (by exact (hu.continuous.measurable))
    filter_upwards [hu'] with x hx
    rw [hμe]
    exact hx.symm
  · intro x
    rw [hgrad x, hs, inv_div]
    have h1q' : (1 - q) ≠ 0 := h1q.ne'
    have hρ' : ρ ≠ 0 := hρ.ne'
    ext i
    simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    field_simp
    ring
  · rw [hlaw', hF]
    congr 1
    set S : ℝ := (s : ℝ)⁻¹ with hS
    have hSv : S = ρ / (1 - q) := by rw [hS, hs, inv_div]
    have h1q' : (1 - q) ≠ 0 := h1q.ne'
    have hρ' : ρ ≠ 0 := hρ.ne'
    set a' : ℝ := ρ - S with ha'
    have ha0 : a' ≠ 0 := by
      have : a' = -(ρ * q / (1 - q)) := by rw [ha', hSv]; field_simp; ring
      rw [this]
      exact neg_ne_zero.mpr (by positivity)
    set cc : CutCur.Rd d := (-(S * r / a')) • x₀ with hcc
    have hpt : ∀ y : CutCur.Rd d, ‖ρ • y - S • (y - r • x₀)‖ ^ 2 = a' ^ 2 * ‖y - cc‖ ^ 2 := by
      intro y
      have : ρ • y - S • (y - r • x₀) = a' • (y - cc) := by
        rw [hcc]
        ext i
        simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        field_simp
        rw [ha']
        ring
      rw [this, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    simp_rw [hpt]
    rw [integral_const_mul, gaussian_second_moment_about _ _ _
      (Matrix.PosSemidef.one.smul (by positivity))]
    have hnorm : ‖r • x₀ - cc‖ ^ 2 = (r * (1 + S / a')) ^ 2 * ‖x₀‖ ^ 2 := by
      have : r • x₀ - cc = (r * (1 + S / a')) • x₀ := by
        rw [hcc]
        ext i
        simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        ring
      rw [this, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have htr : Matrix.trace ((s : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)) = d * s := by
      simp [Matrix.trace]
    rw [hnorm, htr, hs]
    have hq4 : Real.exp (-4 * ρ * t) = q ^ 2 := by
      rw [hq, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hq4]
    have hsub : a' = -(ρ * q / (1 - q)) := by rw [ha', hSv]; field_simp; ring
    have hq' : q ≠ 0 := hq0.ne'
    rw [hsub, hSv]
    rw [hqr] at *
    field_simp
    ring

end OU

end CutoffRigidity.Paper
