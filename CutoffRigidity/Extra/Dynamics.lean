module

public import CutoffRigidity.Paper.FisherBridge
public import CutoffRigidity.Paper.InformationCutoff
public import CutoffRigidity.LangevinInformationUpperBounds
public import CutoffRigidity.LangevinInformationEvolution
public import CutoffRigidity.LangevinFisherEntropyEndpoint
public import CutoffRigidity.LangevinEntropyRegularization
public import CutoffRigidity.LangevinKernel
public import CutoffRigidity.Talagrand
public import CutoffRigidity.LogSobolev
public import CutoffRigidity.Pinsker

/-! # Wasserstein contraction, entropy decay and regularization, Pinsker, Talagrand, LSI

The load-bearing analytic facts of the proofs of Theorem 1.1 and Corollary 1.4, for an
arbitrary initial law `ν`: `Law(X_t) = ∫ Law(X_t^x) ν(dx)`, written
`ν.bind fun x => P.map (X x t)`.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The mixture of the laws of the solutions is the library kernel applied to `ν`. -/
theorem law_bind_eq_comp {V : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω}
    {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d} (hL : CutCur.IsLangevin V B P X)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) (t : ℝ≥0) :
    ν.bind (fun x => P.map (X x t)) = langevinKernel V B P t ∘ₘ ν := by
  have : (fun x => P.map (X x t)) = ⇑(langevinKernel V B P t) :=
    funext fun x => IsLangevin.map_eq_langevinKernel hL ρ hρ hHess x t
  rw [this]

/-- Starting from a Dirac mass the mixture is the law of the solution. -/
theorem law_bind_dirac {V : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω}
    {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d} (hL : CutCur.IsLangevin V B P X)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : CutCur.Rd d) (t : ℝ≥0) :
    (Measure.dirac x₀).bind (fun x => P.map (X x t)) = P.map (X x₀ t) := by
  have hB := isStdBrownian_iff.mp hL.2.2.1
  have : (fun x => P.map (X x t)) = ⇑(langevinKernel V B P t) :=
    funext fun x => IsLangevin.map_eq_langevinKernel hL ρ hρ hHess x t
  rw [this, Measure.dirac_bind (Kernel.measurable _)]
  exact (IsLangevin.map_eq_langevinKernel hL ρ hρ hHess x₀ t).symm

/-- **Pinsker / Csiszár–Kullback–Pinsker** (eq. CKP): `TV(μ,ν)² ≤ H(ν | μ)/2`. -/
theorem pinsker_tvDist {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (CutCur.tvDist ν μ ^ 2) ≤ klDiv ν μ / 2 := by
  rw [tvDist_eq_totalVariationDistance]
  exact totalVariationDistance_sq_le_klDiv ν μ

/-- **Talagrand** `ρ W₂(ν,μ)² ≤ 2 H(ν | μ)` and **logarithmic Sobolev** `H(ν | μ) ≤ I(ν | μ)/(2ρ)`
(eq. LSI) under `Hess V ≥ ρ I`, for every initial probability law. -/
theorem talagrand_logSobolev_carrier {V : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω}
    {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d} (hL : CutCur.IsLangevin V B P X) (hd : 0 < d)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν] :
    ENNReal.ofReal ρ * CutCur.wasserstein2 ν (CutCur.gibbs V) ^ 2 ≤
        2 * klDiv ν (CutCur.gibbs V) ∧
      klDiv ν (CutCur.gibbs V) ≤ CutCur.fisherInfo V ν / ENNReal.ofReal (2 * ρ) := by
  have hB := isStdBrownian_iff.mp hL.2.2.1
  have hp : IsProbabilityMeasure (gibbsMeasure volume V) := hL.2.1
  refine ⟨?_, ?_⟩
  · rw [wasserstein2_sq]
    exact curvature_mul_squaredWasserstein_le_two_klDiv hB hL.1 hp hd ρ hρ hHess ν
  · rw [fisherInfo_eq_relativeFisherInformation hL.1 hp ρ hρ hHess ν]
    exact logSobolev_relativeFisherInformation hB hL.1 hp hd ρ hρ hHess ν

/-- **Wasserstein contraction for arbitrary initial laws**:
`W₂(Law X_t, Law Y_t) ≤ e^{-ρt} W₂(Law X₀, Law Y₀)` under `Hess V ≥ ρ I`, `ρ ≥ 0`. -/
theorem langevin_w2_contraction {V : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d}
    {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hL : CutCur.IsLangevin V B P X) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν₁ ν₂ : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (t : ℝ≥0) :
    CutCur.wasserstein2 (ν₁.bind fun x => P.map (X x t)) (ν₂.bind fun x => P.map (X x t)) ≤
      ENNReal.ofReal (Real.exp (-ρ * t)) * CutCur.wasserstein2 ν₁ ν₂ := by
  have hB := isStdBrownian_iff.mp hL.2.2.1
  rw [law_bind_eq_comp hL hρ hHess, law_bind_eq_comp hL hρ hHess]
  simp only [wasserstein2_eq_rpow]
  have h := squaredWasserstein_langevinKernel_comp_le hB hL.1 ρ hρ hHess t ν₁ ν₂
  calc _ ≤ (ENNReal.ofReal (Real.exp (-2 * ρ * t)) * squaredWasserstein ν₁ ν₂) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_nonneg
        (Real.exp_pos _).le (by norm_num)]
      congr 2
      rw [← Real.exp_mul]
      congr 1
      ring

/-- **Entropy decay and regularization** (eq. expdecH, eq. HWsmallt, eq. HtWX0, CKP, Fisher
information; manuscript proof of Corollary 1.4) under `Hess V ≥ ρ I`, `ρ > 0`, for an arbitrary
initial law `ν`, `μ_t := Law(X_t) = ν.bind fun x => P.map (X x t)`. -/
theorem langevin_entropy_decay {V : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d}
    {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hL : CutCur.IsLangevin V B P X) (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν] :
    let H := fun t : ℝ≥0 => klDiv (ν.bind fun x => P.map (X x t)) (CutCur.gibbs V)
    let I := fun t : ℝ≥0 => CutCur.fisherInfo V (ν.bind fun x => P.map (X x t))
    let W := CutCur.wasserstein2 ν (CutCur.gibbs V) ^ 2
    (∀ s t : ℝ≥0, s ≤ t → H t ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - s))) * H s) ∧
      (∀ t : ℝ≥0, 0 < t →
        H t ≤ ENNReal.ofReal (ρ * Real.exp (-2 * ρ * t) / (1 - Real.exp (-2 * ρ * t))) * W ∧
        ENNReal.ofReal (ρ * Real.exp (-2 * ρ * t) / (1 - Real.exp (-2 * ρ * t))) * W ≤
          ENNReal.ofReal (1 / (2 * (t : ℝ))) * W) ∧
      (∀ t : ℝ≥0, 1 ≤ t →
        2 * H t ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 1))) * W ∧
        ENNReal.ofReal (CutCur.tvDist (ν.bind fun x => P.map (X x t)) (CutCur.gibbs V) ^ 2) ≤
          ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 1)) / 4) * W) ∧
      (∀ s t : ℝ≥0, s ≤ t → I t ≤ I s) ∧
      (∀ s t : ℝ≥0, 0 < t → I (s + t) ≤ H s / ENNReal.ofReal t) ∧
      (∀ t₀ t₁ : ℝ≥0, 1 ≤ t₀ → t₀ < t₁ →
        I t₁ ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t₀ : ℝ) - 1)) / (2 * ((t₁ : ℝ) - t₀))) * W) := by
  intro H I W
  have hB := isStdBrownian_iff.mp hL.2.2.1
  have hV := hL.1
  have hp : IsProbabilityMeasure (gibbsMeasure volume V) := hL.2.1
  have hρ0 := hρ.le
  have hlaw := law_bind_eq_comp hL hρ0 hHess ν
  have hmk : ∀ t : ℝ≥0, IsMarkovKernel (langevinKernel V B P t) := fun t =>
    langevinKernel_isMarkovKernel hB hV ρ hρ0 hHess t
  have hWeq : W = squaredWasserstein ν (gibbsMeasure volume V) := by
    simp only [W]
    rw [wasserstein2_sq]
    exact rfl
  have hHeq : ∀ t, H t = klDiv (langevinKernel V B P t ∘ₘ ν) (gibbsMeasure volume V) := by
    intro t
    simp only [H]
    rw [hlaw]
    exact rfl
  have hIeq : ∀ t, I t = relativeFisherInformation hV hp (langevinKernel V B P t ∘ₘ ν) := by
    intro t
    simp only [I]
    rw [hlaw]
    let := hmk t
    have : IsProbabilityMeasure (langevinKernel V B P t ∘ₘ ν) := inferInstance
    exact fisherInfo_eq_relativeFisherInformation hV hp ρ hρ hHess _
  have hent_add := langevinKernel_entropy_contraction_add hB hV hp hd ρ hρ hHess ν
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t hst
    have h := hent_add s (t - s)
    rw [add_tsub_cancel_of_le hst, NNReal.coe_sub hst] at h
    rw [hHeq, hHeq]
    convert h using 4
  · intro t ht
    have htR : (0 : ℝ) < t := by exact_mod_cast ht
    have h := klDiv_langevinKernel_le_squaredWasserstein hB hV hp ρ hρ hHess ν t htR
    simp only [Real.toNNReal_coe] at h
    have hden : 0 < Real.exp (2 * ρ * t) - 1 :=
      sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
    have hcoef : ρ * Real.exp (-2 * ρ * t) / (1 - Real.exp (-2 * ρ * t)) =
        ρ / (Real.exp (2 * ρ * t) - 1) := by
      have h1 : Real.exp (-2 * ρ * t) * Real.exp (2 * ρ * t) = 1 := by
        rw [← Real.exp_add]; simp
      have h2 : 0 < Real.exp (2 * ρ * t) := Real.exp_pos _
      have h3 : 1 - Real.exp (-2 * ρ * t) = Real.exp (-2 * ρ * t) * (Real.exp (2 * ρ * t) - 1) := by
        nlinarith [h1]
      rw [h3]
      have : Real.exp (-2 * ρ * t) ≠ 0 := (Real.exp_pos _).ne'
      field_simp
    refine ⟨?_, ?_⟩
    · rw [hHeq, hWeq, hcoef]
      refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
      rw [div_le_div_iff₀ (mul_pos (by norm_num) hden) hden]
      nlinarith [hρ]
    · rw [hcoef]
      refine mul_le_mul' ?_ le_rfl
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_div_iff₀ hden (mul_pos (by norm_num) htR)]
      have hh := Real.add_one_le_exp (2 * ρ * t)
      nlinarith
  · intro t ht
    have h := klDiv_langevinKernel_le_exp_transport hB hV hp hd ρ hρ hHess ν t ht
    rw [hHeq, hWeq]
    constructor
    · calc 2 * klDiv (langevinKernel V B P t ∘ₘ ν) (gibbsMeasure volume V)
          ≤ 2 * (ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 1)) / 2) *
            squaredWasserstein ν (gibbsMeasure volume V)) := mul_le_mul' le_rfl h
        _ = _ := by
          rw [← mul_assoc]
          congr 1
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
    · have hKL : ENNReal.ofReal (CutCur.tvDist (langevinKernel V B P t ∘ₘ ν)
          (gibbsMeasure volume V) ^ 2) ≤ klDiv (langevinKernel V B P t ∘ₘ ν)
          (gibbsMeasure volume V) / 2 := by
        let := hmk t
        have := pinsker_tvDist (gibbsMeasure volume V) (langevinKernel V B P t ∘ₘ ν)
        exact this
      rw [hlaw t]
      refine hKL.trans ?_
      calc klDiv (langevinKernel V B P t ∘ₘ ν) (gibbsMeasure volume V) / 2
          ≤ (ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 1)) / 2) *
            squaredWasserstein ν (gibbsMeasure volume V)) / 2 := ENNReal.div_le_div_right h 2
        _ = _ := by
          have h4 : ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 1)) / 4) =
              ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 1)) / 2) * 2⁻¹ := by
            rw [show Real.exp (-2 * ρ * ((t : ℝ) - 1)) / 4 =
              Real.exp (-2 * ρ * ((t : ℝ) - 1)) / 2 * 2⁻¹ by ring,
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by norm_num)]
            simp
          rw [h4, div_eq_mul_inv]
          ring
  · intro s t hst
    rw [hIeq, hIeq]
    let := hmk s
    let := hmk t
    exact relativeFisherInformation_langevinKernel_antitone hB hV hp ρ hρ hHess ν s t hst
  · intro s t ht
    rw [hIeq, hHeq]
    let := hmk (s + t)
    have h := langevinKernel_fisher_entropy_endpoint_add hB hV hp ρ hρ hHess ν s t ht
    exact h
  · intro t₀ t₁ h1 h01
    have hΔ : (0 : ℝ) < (t₁ : ℝ) - t₀ := sub_pos.mpr (by exact_mod_cast h01)
    have hΔ' : 0 < t₁ - t₀ := tsub_pos_of_lt h01
    have h := langevinKernel_fisher_entropy_endpoint_add hB hV hp ρ hρ hHess ν t₀ (t₁ - t₀) hΔ'
    rw [add_tsub_cancel_of_le h01.le] at h
    have hE := klDiv_langevinKernel_le_exp_transport hB hV hp hd ρ hρ hHess ν t₀ h1
    rw [hIeq, hWeq]
    let := hmk t₁
    refine h.trans ?_
    calc _ ≤ (ENNReal.ofReal (Real.exp (-2 * ρ * ((t₀ : ℝ) - 1)) / 2) *
          squaredWasserstein ν (gibbsMeasure volume V)) / ENNReal.ofReal ((t₁ - t₀ : ℝ≥0) : ℝ) :=
          ENNReal.div_le_div_right hE _
      _ = _ := by
        rw [NNReal.coe_sub h01.le, div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos hΔ,
          mul_right_comm, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp

end CutoffRigidity.Paper
