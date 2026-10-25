module

public import CutoffRigidity.Extra.OptimalConstants
public import CutoffRigidity.Extra.Dynamics
public import CutoffRigidity.Extra.NoBmChain

/-! # Brownian-free optimal constants, extremal functions, Talagrand and logarithmic Sobolev

The statements of `optimal_lsi_twice_pi`, `optimal_constants_extremal` and `talagrand_logSobolev`
of the Challenge without the Brownian-motion carrier (`Ω`, `B`, `P`, `hB`, resp. `Ω`, `B`, `P`, `X`,
`hL`).  The proofs use the project's Euclidean machinery with the single Brownian-dependent leaf
`logSobolev_regularized_compact_square` replaced by `NoBm.logSobolev_regularized_compact_square_nobm`,
proved from the analytic Bakry-Emery semigroup of the Riemannian development (flat `ℝ^d`) plus
mollification of the potential and of the test functions.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal ContDiff Topology

variable {d : ℕ}

open CutCur (entropyOf IsTestFunction optimalPI optimalLSI)

section Validity

variable {V : CutCur.Rd d → ℝ}

/-- LSI with constant `2/ρ` on test functions, from the curvature condition. -/
theorem lsi_valid_nobm (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (CutCur.gibbs V))
    (hR : CutCur.RigidCurvature V) {f : CutCur.Rd d → ℝ} (hf : IsTestFunction f) :
    entropyOf (CutCur.gibbs V) (fun x => f x ^ 2) ≤
      2 * (CutCur.spectralGap V)⁻¹ * ∫ x, ‖gradient f x‖ ^ 2 ∂CutCur.gibbs V := by
  have hd := pos_dim_of_rigidCurvature hp hR
  have hρ := hR.1
  have hp' : IsProbabilityMeasure (gibbsMeasure volume V) := hp
  set μ := CutCur.gibbs V with hμ
  set ρ := CutCur.spectralGap V with hρdef
  set E := ∫ x, ‖gradient f x‖ ^ 2 ∂μ with hE
  set A := ∫ x, f x ^ 2 ∂μ with hA
  have hE0 : 0 ≤ E := integral_nonneg fun x => sq_nonneg _
  have hv : Integrable (fun x => f x ^ 2) μ := hf.integrable_of_bounded μ (F := fun t => t ^ 2) (by fun_prop)
  have hu : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ :=
    hf.integrable_of_bounded μ (F := fun t => t ^ 2 * Real.log (t ^ 2))
      (Real.continuous_mul_log.comp (continuous_pow 2))
  have hA0 : 0 ≤ A := integral_nonneg fun x => sq_nonneg _
  rcases hA0.eq_or_lt with hA00 | hApos
  · -- `f = 0` almost everywhere
    have hz : (fun x => f x ^ 2) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hv).mp hA00.symm
    have hu0 : ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ = 0 :=
      integral_eq_zero_of_ae (hz.mono fun x hx => by simp at hx ⊢; simp [hx])
    have : entropyOf μ (fun x => f x ^ 2) = 0 := by
      unfold entropyOf; rw [hu0, ← hA, ← hA00]; simp
    rw [this]; positivity
  · set c := (Real.sqrt A)⁻¹ with hc
    have hc2 : c ^ 2 = A⁻¹ := by rw [hc, inv_pow, Real.sq_sqrt hA0]
    have hgT : IsTestFunction (fun x => 0 + c * f x) := hf.affine 0 c
    obtain ⟨M, hM⟩ := hgT.2.1
    obtain ⟨L, hL⟩ := hgT.2.2
    have hnorm : ∫ x, (0 + c * f x) ^ 2 ∂μ = 1 := by
      have : ∀ x, (0 + c * f x) ^ 2 = c ^ 2 * f x ^ 2 := fun x => by ring
      simp_rw [this]
      rw [integral_const_mul, hc2, ← hA]; field_simp
    have hlsi0 := CutoffRigidity.logSobolev_normalized_bounded_lipschitz_nobm (V := V) (f := fun x => 0 + c * f x)
      hV hp' hd ρ hρ hR.2 hL M (fun x => by simpa [Real.norm_eq_abs] using hM x) hnorm
    have hlsi : ∫ x, InformationTheory.klFun ((0 + c * f x) ^ 2) ∂μ ≤
        2 / ρ * ∫ x, ‖gradient (fun x => 0 + c * f x) x‖ ^ 2 ∂μ := hlsi0
    have hgrad : ∫ x, ‖gradient (fun x => 0 + c * f x) x‖ ^ 2 ∂μ = A⁻¹ * E := by
      rw [hE, ← hc2, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      have hd' : DifferentiableAt ℝ f x := (hf.1.differentiable (by simp)) x
      show ‖gradient (fun x => 0 + c * f x) x‖ ^ 2 = c ^ 2 * ‖gradient f x‖ ^ 2
      rw [gradient_affine hd', norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hkl : ∫ x, InformationTheory.klFun ((0 + c * f x) ^ 2) ∂μ =
        A⁻¹ * entropyOf μ (fun x => f x ^ 2) := by
      have hpt : ∀ x, InformationTheory.klFun ((0 + c * f x) ^ 2) =
          A⁻¹ * (f x ^ 2 * Real.log (f x ^ 2)) + (A⁻¹ * Real.log A⁻¹) * f x ^ 2 + 1 -
            A⁻¹ * f x ^ 2 := by
        intro x
        rw [InformationTheory.klFun_apply]
        have e : (0 + c * f x) ^ 2 = A⁻¹ * f x ^ 2 := by rw [← hc2]; ring
        rw [e]
        by_cases hx : f x = 0
        · simp [hx]
        · rw [Real.log_mul (inv_ne_zero hApos.ne') (pow_ne_zero 2 hx)]; ring
      rw [integral_congr_ae (Eventually.of_forall hpt),
        integral_comb (μ := μ) (u := fun x => f x ^ 2 * Real.log (f x ^ 2))
          (v := fun x => f x ^ 2) hu hv]
      unfold entropyOf
      rw [← hA, Real.log_inv]
      field_simp
      ring
    have hkl' := hlsi
    rw [hkl, hgrad] at hkl'
    have : entropyOf μ (fun x => f x ^ 2) ≤ 2 / ρ * E := by
      have hAi : 0 < A⁻¹ := inv_pos.mpr hApos
      rw [mul_left_comm] at hkl'
      exact (mul_le_mul_iff_right₀ hAi).mp hkl'
    calc _ ≤ 2 / ρ * E := this
      _ = _ := by rw [div_eq_mul_inv]


/-- Under rigidity and with a Brownian motion, the optimal LSI constant is `2/λ₁`. -/
theorem optimalLSI_eq_nobm (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (CutCur.gibbs V)) (hR : CutCur.RigidCurvature V) :
    optimalLSI V = 2 * (CutCur.spectralGap V)⁻¹ := by
  refine IsLeast.csInf_eq ⟨⟨by have := hR.1; positivity, fun f hf => lsi_valid_nobm hV hp hR hf⟩, ?_⟩
  rintro C ⟨hC0, hC⟩
  have h2 := inv_spectralGap_le_of_pi (V := V) hR.1 (C := C / 2) (by positivity) (fun f hf => by
    have := pi_of_lsi (μ := CutCur.gibbs V) hC hf
    linarith)
  linarith

end Validity

/-- **Optimal constants** (manuscript subsection "Optimal constants"): under rigidity
(`Hess V ≥ λ₁ I`, `λ₁ > 0`), the optimal Poincaré constant is `1/λ₁` and the optimal
logarithmic Sobolev constant is twice the optimal Poincaré constant. -/
theorem optimal_lsi_twice_pi_nobm {d : ℕ} {V : CutCur.Rd d → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (CutCur.gibbs V))
    (hR : CutCur.RigidCurvature V) :
    optimalPI V = (CutCur.spectralGap V)⁻¹ ∧ optimalLSI V = 2 * optimalPI V := by
  rw [optimalPI_eq hV hp hR]
  exact ⟨rfl, optimalLSI_eq_nobm hV hp hR⟩

set_option maxHeartbeats 1000000 in
/-- **Extremal functions** (manuscript subsection "Optimal constants"): in the convex-interaction
setting `V = ρ|x|²/2 + W`, the function `x ↦ x₁+⋯+x_d` is extremal for the Poincaré inequality
(equality with the optimal constant), and `x ↦ e^{α(x₁+⋯+x_d)}` is extremal for the logarithmic
Sobolev inequality (equality with the optimal constant), for every real `α`. -/
theorem optimal_constants_extremal_nobm (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ)
    {W : CutCur.Rd d → ℝ} (hW : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ univ W)
    (hinv : ∀ x (s : ℝ), W (x + s • CutCur.diagonal d) = W x)
    (hp : IsProbabilityMeasure (CutCur.gibbs fun x => ρ / 2 * ‖x‖ ^ 2 + W x)) :
    let V := fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + W x
    let h := fun x : CutCur.Rd d => ∑ i, x i
    optimalPI V = ρ⁻¹ ∧ optimalLSI V = 2 * optimalPI V ∧
    (MemLp h 2 (CutCur.gibbs V) ∧ 0 < variance h (CutCur.gibbs V) ∧
      variance h (CutCur.gibbs V) =
        optimalPI V * ∫ x, ‖gradient h x‖ ^ 2 ∂CutCur.gibbs V) ∧
    ∀ α : ℝ,
      Integrable (fun x => Real.exp (α * h x) ^ 2) (CutCur.gibbs V) ∧
      Integrable (fun x => Real.exp (α * h x) ^ 2 * Real.log (Real.exp (α * h x) ^ 2))
        (CutCur.gibbs V) ∧
      Integrable (fun x => ‖gradient (fun y => Real.exp (α * h y)) x‖ ^ 2) (CutCur.gibbs V) ∧
      (α ≠ 0 → 0 < ∫ x, ‖gradient (fun y => Real.exp (α * h y)) x‖ ^ 2 ∂CutCur.gibbs V) ∧
      entropyOf (CutCur.gibbs V) (fun x => Real.exp (α * h x) ^ 2) =
        optimalLSI V * ∫ x, ‖gradient (fun y => Real.exp (α * h y)) x‖ ^ 2 ∂CutCur.gibbs V := by
  intro V h
  obtain ⟨⟨hgap, heig⟩, ⟨-, hprod⟩, hrig⟩ := convex_interaction hd hρ hW hconv hinv hp
  have hVc : ContDiff ℝ 2 V := (contDiff_const.mul (contDiff_norm_sq ℝ)).add hW
  have hPI : optimalPI V = ρ⁻¹ := by rw [optimalPI_eq hVc hp hrig, hgap]
  have hLSI : optimalLSI V = 2 * optimalPI V := by
    rw [optimalLSI_eq_nobm hVc hp hrig, hPI, hgap]
  set μ := CutCur.gibbs V with hμ
  set u : CutCur.Rd d := (Real.sqrt d)⁻¹ • CutCur.diagonal d with hu
  set π := fun x : CutCur.Rd d => x - inner ℝ u x • u with hπ
  have hπc : Continuous π := by fun_prop
  have hL := law_inner_eq_gaussian (μ := μ) (ρ := ρ) (u := u) (π := π) hπc hprod
  set σ : ℝ≥0 := ρ⁻¹.toNNReal with hσ
  have hσρ : (σ : ℝ) = ρ⁻¹ := by rw [hσ]; exact Real.coe_toNNReal _ (inv_nonneg.mpr hρ.le)
  set t : CutCur.Rd d → ℝ := fun x => inner ℝ u x with ht
  have htc : Continuous t := by fun_prop
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hht : ∀ x, h x = Real.sqrt d * t x := fun x => sum_eq_sqrt_mul_inner hd x
  have hsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt (by positivity)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hint : ∀ {G : ℝ → ℝ}, Integrable G (gaussianReal 0 σ) →
      Integrable (fun x => G (t x)) μ := fun {G} hG => by
    have hG' : Integrable G (μ.map t) := by rw [hL]; exact hG
    exact (integrable_map_measure hG'.aestronglyMeasurable htc.aemeasurable).mp hG'
  have hintg : ∀ (G : ℝ → ℝ), Continuous G →
      ∫ x, G (t x) ∂μ = ∫ s, G s ∂gaussianReal 0 σ := fun G hG => by
    rw [← hL, integral_map htc.aemeasurable hG.aestronglyMeasurable]
  have hexp2 : ∀ y : ℝ, Real.exp y ^ 2 = Real.exp (2 * y) := fun y => by
    rw [← Real.exp_nat_mul]; norm_num
  have hvar : variance h μ = d * ρ⁻¹ := by
    have hh : h = (fun s => Real.sqrt d * s) ∘ t := funext hht
    have h1 := variance_map (μ := μ) (X := fun s : ℝ => Real.sqrt d * s) (Y := t)
      (by rw [hL]; fun_prop) htc.aemeasurable
    rw [hL] at h1
    have h2 := variance_const_mul (Real.sqrt d) id (gaussianReal 0 σ)
    have h3 := variance_id_gaussianReal (μ := 0) (v := σ)
    rw [hh, ← h1]
    show variance (fun y => Real.sqrt d * id y) (gaussianReal 0 σ) = _
    rw [h2, h3, hsq, hσρ]
  have hgradh : ∫ x, ‖gradient h x‖ ^ 2 ∂μ = d := by
    have : ∀ x, ‖gradient h x‖ ^ 2 = d := fun x => by
      rw [show gradient h x = CutCur.diagonal d from gradient_sum x, norm_sq_diagonal]
    simp_rw [this]; simp
  refine ⟨hPI, hLSI, ⟨heig.2.1, ?_, ?_⟩, fun α => ?_⟩
  · rw [hvar]; positivity
  · rw [hvar, hgradh, hPI]; ring
  · set a := α * Real.sqrt d with ha
    set b := 2 * a with hb
    obtain ⟨hI0, hI1, hZ0, hY0⟩ := gaussian_exp_moments σ b
    have e1 : ∀ x, Real.exp (α * h x) ^ 2 = Real.exp (b * t x) := fun x => by
      rw [hexp2, hht]; congr 1; simp only [hb, ha]; ring
    have e2 : ∀ x, Real.exp (α * h x) ^ 2 * Real.log (Real.exp (α * h x) ^ 2) =
        b * (t x * Real.exp (b * t x)) := fun x => by
      rw [e1, Real.log_exp]; ring
    have hdiff : ∀ x, DifferentiableAt ℝ h x := fun x => by
      have hhd : (fun y : CutCur.Rd d => ∑ i, y i) = ⇑(innerSL ℝ (CutCur.diagonal d)) :=
        funext fun y => (inner_diagonalDirection y).symm
      show DifferentiableAt ℝ (fun y : CutCur.Rd d => ∑ i, y i) x
      rw [hhd]; exact (innerSL ℝ _).differentiableAt
    have e3 : ∀ x, ‖gradient (fun y => Real.exp (α * h y)) x‖ ^ 2 =
        α ^ 2 * d * Real.exp (b * t x) := fun x => by
      rw [CutoffRigidity.gradient_exp_mul_at (hdiff x) α, gradient_sum x, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs, norm_sq_diagonal, mul_pow, e1]
      ring
    have hZ : ∫ x, Real.exp (b * t x) ∂μ = Real.exp (σ * b ^ 2 / 2) :=
      (hintg (fun s => Real.exp (b * s)) (by fun_prop)).trans hZ0
    have hY : ∫ x, t x * Real.exp (b * t x) ∂μ = σ * b * Real.exp (σ * b ^ 2 / 2) :=
      (hintg (fun s => s * Real.exp (b * s)) (by fun_prop)).trans hY0
    have hE1 : ∫ x, Real.exp (α * h x) ^ 2 ∂μ = Real.exp (σ * b ^ 2 / 2) := by
      simp_rw [e1]; exact hZ
    have hE2 : ∫ x, Real.exp (α * h x) ^ 2 * Real.log (Real.exp (α * h x) ^ 2) ∂μ =
        b * (σ * b * Real.exp (σ * b ^ 2 / 2)) := by
      simp_rw [e2]; rw [integral_const_mul, hY]
    have hE3 : ∫ x, ‖gradient (fun y => Real.exp (α * h y)) x‖ ^ 2 ∂μ =
        α ^ 2 * d * Real.exp (σ * b ^ 2 / 2) := by
      simp_rw [e3]; rw [integral_const_mul, hZ]
    have hi0 : Integrable (fun x => Real.exp (b * t x)) μ :=
      hint (G := fun s => Real.exp (b * s)) hI0
    refine ⟨hi0.congr (Eventually.of_forall fun x => (e1 x).symm),
      ((hint (G := fun s => s * Real.exp (b * s)) hI1).const_mul b).congr (Eventually.of_forall fun x => (e2 x).symm),
      (hi0.const_mul (α ^ 2 * d)).congr (Eventually.of_forall fun x => (e3 x).symm),
      fun hα => ?_, ?_⟩
    · rw [hE3]; positivity
    · show (∫ x, Real.exp (α * h x) ^ 2 * Real.log (Real.exp (α * h x) ^ 2) ∂μ) -
        (∫ x, Real.exp (α * h x) ^ 2 ∂μ) * Real.log (∫ x, Real.exp (α * h x) ^ 2 ∂μ) = _
      rw [hE2, hE1, hE3, hLSI, hPI, Real.log_exp, hσρ]
      have hb2 : b ^ 2 = 4 * α ^ 2 * d := by
        calc b ^ 2 = 4 * α ^ 2 * Real.sqrt d ^ 2 := by rw [hb, ha]; ring
          _ = _ := by rw [hsq]
      have : b * (ρ⁻¹ * b * Real.exp (ρ⁻¹ * b ^ 2 / 2)) -
          Real.exp (ρ⁻¹ * b ^ 2 / 2) * (ρ⁻¹ * b ^ 2 / 2) =
          ρ⁻¹ * b ^ 2 * Real.exp (ρ⁻¹ * b ^ 2 / 2) / 2 := by ring
      rw [this, hb2]; ring


/-- **Talagrand** `ρ W₂(ν,μ)² ≤ 2 H(ν | μ)` and **logarithmic Sobolev** `H(ν | μ) ≤ I(ν | μ)/(2ρ)`
(eq. LSI) under `Hess V ≥ ρ I`, for every initial probability law, without any Brownian carrier. -/
theorem talagrand_logSobolev_nobm {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (CutCur.gibbs V)) (hd : 0 < d)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν] :
    ENNReal.ofReal ρ * CutCur.wasserstein2 ν (CutCur.gibbs V) ^ 2 ≤
        2 * InformationTheory.klDiv ν (CutCur.gibbs V) ∧
      InformationTheory.klDiv ν (CutCur.gibbs V) ≤ CutCur.fisherInfo V ν / ENNReal.ofReal (2 * ρ) := by
  have hp' : IsProbabilityMeasure (gibbsMeasure volume V) := hp
  refine ⟨?_, ?_⟩
  · rw [wasserstein2_sq]
    exact curvature_mul_squaredWasserstein_le_two_klDiv_nobm hV hp' hd ρ hρ hHess ν
  · rw [fisherInfo_eq_relativeFisherInformation hV hp' ρ hρ hHess ν]
    exact logSobolev_relativeFisherInformation_nobm hV hp' hd ρ hρ hHess ν

/-- Challenge statement `optimal_lsi_twice_pi` (no Brownian carrier). -/
alias optimal_lsi_twice_pi := optimal_lsi_twice_pi_nobm

/-- Challenge statement `optimal_constants_extremal` (no Brownian carrier). -/
alias optimal_constants_extremal := optimal_constants_extremal_nobm

/-- Challenge statement `talagrand_logSobolev` (no Brownian carrier). -/
alias talagrand_logSobolev := talagrand_logSobolev_nobm

end CutoffRigidity.Paper
