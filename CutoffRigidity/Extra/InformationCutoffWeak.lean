module

public import CutoffRigidity.Paper.CarrierDefs
public import CutoffRigidity.Paper.InformationCutoff

/-! # Remark 3.5 (weaker assumption): `λ₁ = d^{o(1)}` suffices in Corollary 1.4

In the regularization step of the proof of Corollary 1.4 the time `1` is replaced by the time
`T = 1/λ₁`.  This produces a prefactor `λ₁` for the entropy, `λ₁²` for the Fisher information
(and `√λ₁` for total variation through Pinsker).  The critical time `t* = log d / (2 λ₁)`
satisfies `λ₁ t* = (log d)/2`, so the shifted exponent `2 λ₁ ((1+ε) t* - T)` is still
`(1+ε) log d - 2`, independently of the size of `λ₁`.  The lower bounds (before `t*`) only use
`liminf λ₁ > 0` and are taken from the existing development.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology ENNReal NNReal Asymptotics

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ### Regularization at an arbitrary time `T > 0` -/

theorem klDiv_langevinKernel_le_exp_transport_shift
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hdim : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] (T : ℝ) (hT : 0 < T) (t : NNReal)
    (ht : T ≤ t) :
    klDiv (langevinKernel V B P t ∘ₘ ν) (gibbsMeasure volume V) ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - T)) / (2 * T)) *
        squaredWasserstein ν (gibbsMeasure volume V) := by
  have hTt : T.toNNReal ≤ t := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hT.le]; exact ht
  have hh := langevinKernel_entropy_contraction_add hB hV hp hdim ρ hρ hHess ν T.toNNReal
    (t - T.toNNReal)
  have he : T.toNNReal + (t - T.toNNReal) = t := add_tsub_cancel_of_le hTt
  rw [he, NNReal.coe_sub hTt, Real.coe_toNNReal _ hT.le] at hh
  have hr := klDiv_langevinKernel_le_squaredWasserstein_div_time hB hV hp ρ hρ hHess ν T hT
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - T))) *
        klDiv (langevinKernel V B P T.toNNReal ∘ₘ ν) (gibbsMeasure volume V) := hh
    _ ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - T))) *
        (ENNReal.ofReal (1 / (2 * T)) * squaredWasserstein ν (gibbsMeasure volume V)) :=
      mul_le_mul' le_rfl hr
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      congr 2
      ring

theorem relativeFisherInformation_langevinKernel_le_exp_transport_shift
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] (T : ℝ) (hT : 0 < T) (t : NNReal)
    (ht : 2 * T ≤ t) :
    letI := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
    relativeFisherInformation hV hp (langevinKernel V B P t ∘ₘ ν) ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 2 * T)) / (2 * T ^ 2)) *
        squaredWasserstein ν (gibbsMeasure volume V) := by
  have hT' : (0 : NNReal) < T.toNNReal := Real.toNNReal_pos.mpr hT
  have hcoe : ((T.toNNReal : NNReal) : ℝ) = T := Real.coe_toNNReal _ hT.le
  have h2 : T.toNNReal + T.toNNReal ≤ t := by
    rw [← NNReal.coe_le_coe, NNReal.coe_add, hcoe]; linarith
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T.toNNReal
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess (T.toNNReal + T.toNNReal)
  have hstep := langevinKernel_fisher_entropy_endpoint_add hB hV hp ρ hρ hHess ν T.toNNReal
    T.toNNReal hT'
  rw [hcoe] at hstep
  have hr := klDiv_langevinKernel_le_squaredWasserstein_div_time hB hV hp ρ hρ hHess ν T hT
  have hd := relativeFisherInformation_langevinKernel_le hB hV hp ρ hρ hHess
    (langevinKernel V B P (T.toNNReal + T.toNNReal) ∘ₘ ν) (t - (T.toNNReal + T.toNNReal))
  have he : (T.toNNReal + T.toNNReal) + (t - (T.toNNReal + T.toNNReal)) = t :=
    add_tsub_cancel_of_le h2
  have hc : relativeFisherInformation hV hp (langevinKernel V B P t ∘ₘ ν) ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 2 * T))) *
        relativeFisherInformation hV hp
          (langevinKernel V B P (T.toNNReal + T.toNNReal) ∘ₘ ν) := by
    have := hd
    simp only [Measure.comp_assoc, langevinKernel_comp hB hV ρ hρ.le hHess, he,
      NNReal.coe_sub h2, NNReal.coe_add, hcoe] at this
    have e : (t : ℝ) - (T + T) = (t : ℝ) - 2 * T := by ring
    rw [e] at this
    exact this
  have hK : relativeFisherInformation hV hp
      (langevinKernel V B P (T.toNNReal + T.toNNReal) ∘ₘ ν) ≤
      ENNReal.ofReal (1 / (2 * T ^ 2)) * squaredWasserstein ν (gibbsMeasure volume V) := by
    refine hstep.trans ?_
    calc _ ≤ (ENNReal.ofReal (1 / (2 * T)) * squaredWasserstein ν (gibbsMeasure volume V)) /
          ENNReal.ofReal T := ENNReal.div_le_div_right hr _
      _ = _ := by
        rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos hT, mul_right_comm,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp
  calc
    _ ≤ _ := hc
    _ ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 2 * T))) *
        (ENNReal.ofReal (1 / (2 * T ^ 2)) * squaredWasserstein ν (gibbsMeasure volume V)) :=
      mul_le_mul' le_rfl hK
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      congr 2
      ring

/-! ### Set profiles on mean balls -/

theorem spectralSetKL_upper_shift
    (D : SpectralInformationLowerData Ω d) (hd : 0 < d) (S : Set E) (B : ℝ)
    (hCost : ∀ x ∈ S, squaredWasserstein (Measure.dirac x) (gibbsMeasure volume D.potential) ≤
      ENNReal.ofReal B) {T t : ℝ} (hT : 0 < T) (ht : T ≤ t) :
    projectedSetKL (spectralInformationToAffine D) S t ≤
      ENNReal.ofReal (Real.exp (-2 * D.rate * (t - T)) / (2 * T) * B) := by
  let := D.probability
  apply iSup_le
  intro x
  have hh := klDiv_langevinKernel_le_exp_transport_shift D.brownian D.smooth D.probability hd
    D.rate D.rate_pos D.hessian (Measure.dirac (x : E)) T hT t.toNNReal (by
      rw [Real.coe_toNNReal _ (by linarith : 0 ≤ t)]; exact ht)
  rw [langevinKernel_comp_dirac, Real.coe_toNNReal _ (by linarith : 0 ≤ t)] at hh
  apply hh.trans
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (-2 * D.rate * (t - T)) / (2 * T))]
  exact mul_le_mul' le_rfl (hCost x x.property)

theorem spectralSetFisher_upper_shift
    (D : SpectralInformationLowerData Ω d) (S : Set E) (B : ℝ)
    (hCost : ∀ x ∈ S, squaredWasserstein (Measure.dirac x) (gibbsMeasure volume D.potential) ≤
      ENNReal.ofReal B) {T t : ℝ} (hT : 0 < T) (ht : 2 * T ≤ t) :
    spectralSetFisher D S t ≤
      ENNReal.ofReal (Real.exp (-2 * D.rate * (t - 2 * T)) / (2 * T ^ 2) * B) := by
  let := D.probability
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.rate D.rate_pos.le D.hessian
    t.toNNReal
  apply iSup_le
  intro x
  have hh := relativeFisherInformation_langevinKernel_le_exp_transport_shift D.brownian D.smooth
    D.probability D.rate D.rate_pos D.hessian (Measure.dirac (x : E)) T hT t.toNNReal
    (by rw [Real.coe_toNNReal _ (by linarith : 0 ≤ t)]; exact ht)
  simp only [langevinKernel_comp_dirac, Real.coe_toNNReal _ (by linarith : 0 ≤ t)] at hh
  apply hh.trans
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (-2 * D.rate * (t - 2 * T)) / (2 * T ^ 2))]
  exact mul_le_mul' le_rfl (hCost x x.property)

theorem meanBallKL_upper_shift (D : SpectralInformationLowerData Ω d) (hd : 0 < d)
    {c t : ℝ} (hc : 0 ≤ c) (ht : 1 / D.rate ≤ t) :
    meanBallKL D c t ≤ ENNReal.ofReal (Real.exp (-2 * D.rate * t + 2) / 2 *
      ((c ^ 2 * D.rate + 1) * d)) := by
  have hρ := D.rate_pos
  have hT : 0 < 1 / D.rate := by positivity
  have hh := spectralSetKL_upper_shift D hd _ ((c ^ 2 + D.rate⁻¹) * d)
    (fun x hx => spectral_mean_ball_initial_transport_bound D hd hc x hx) hT ht
  change meanBallKL D c t ≤ _ at hh
  convert hh using 2
  field_simp
  ring_nf

theorem meanBallFisher_upper_shift (D : SpectralInformationLowerData Ω d) (hd : 0 < d)
    {c t : ℝ} (hc : 0 ≤ c) (ht : 2 / D.rate ≤ t) :
    meanBallFisher D c t ≤ ENNReal.ofReal (Real.exp (-2 * D.rate * t + 4) / 2 *
      ((c ^ 2 * D.rate ^ 2 + D.rate) * d)) := by
  have hρ := D.rate_pos
  have hT : 0 < 1 / D.rate := by positivity
  have hh := spectralSetFisher_upper_shift D _ ((c ^ 2 + D.rate⁻¹) * d)
    (fun x hx => spectral_mean_ball_initial_transport_bound D hd hc x hx) hT
    (t := t) (by rw [show 2 * (1 / D.rate) = 2 / D.rate by ring]; exact ht)
  change meanBallFisher D c t ≤ _ at hh
  convert hh using 2
  field_simp
  ring_nf

/-! ### Scalar absorption -/

theorem weak_scalar_decay {ρ : ℕ → ℝ} (hρ : ∀ n, 0 < ρ n)
    (hsub : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ρ n ≤ (n : ℝ) ^ δ)
    {c ε σ : ℝ} (hε : 0 < ε) (k : ℕ) (hk : 1 ≤ k) (hk2 : k ≤ 2) :
    Tendsto (fun n : ℕ => Real.exp (-2 * ρ n * ((1 + ε) * criticalTime n (ρ n)) + σ) / 2 *
      ((c ^ 2 * ρ n ^ k + ρ n ^ (k - 1)) * n)) atTop (𝓝 0) := by
  have hL : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => Real.exp (σ) / 2 * ((c ^ 2 + 1) *
      Real.exp (-(ε / 2) * Real.log (n : ℝ)))) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => Real.exp (-(ε / 2) * Real.log (n : ℝ))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (hL.const_mul_atTop_of_neg (by linarith : -(ε / 2) < 0))
    simpa using (this.const_mul (c ^ 2 + 1)).const_mul (Real.exp σ / 2)
  refine squeeze_zero' ?_ ?_ hlim
  · exact Eventually.of_forall fun n => by
      have := hρ n
      positivity
  · filter_upwards [hsub (ε / 4) (by positivity), eventually_ge_atTop 1] with n hn hn1
    have hρn := hρ n
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    set L := Real.log (n : ℝ) with hLdef
    have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hn1)
    have hrpow : (n : ℝ) ^ (ε / 4) = Real.exp (ε / 4 * L) := by
      rw [Real.rpow_def_of_pos hn0, hLdef]; congr 1; ring
    rw [hrpow] at hn
    have hct : -2 * ρ n * ((1 + ε) * criticalTime n (ρ n)) = -(1 + ε) * L := by
      unfold criticalTime
      rw [hLdef]
      field_simp
    rw [hct]
    have hnexp : (n : ℝ) = Real.exp L := (Real.exp_log hn0).symm
    have h1 : 1 ≤ Real.exp (ε / 4 * L) := Real.one_le_exp (by positivity)
    have hkey : (c ^ 2 * ρ n ^ k + ρ n ^ (k - 1)) ≤ (c ^ 2 + 1) * Real.exp (ε / 2 * L) := by
      have e1 : ρ n ≤ Real.exp (ε / 4 * L) := hn
      have e2 : Real.exp (ε / 2 * L) = Real.exp (ε / 4 * L) * Real.exp (ε / 4 * L) := by
        rw [← Real.exp_add]; ring_nf
      have e3 : ρ n ^ 2 ≤ Real.exp (ε / 2 * L) := by
        rw [e2, sq]; exact mul_le_mul e1 e1 hρn.le (by linarith)
      have e4 : 1 ≤ Real.exp (ε / 2 * L) := Real.one_le_exp (by positivity)
      have e5 : ρ n ≤ Real.exp (ε / 2 * L) := by
        rw [e2]; nlinarith
      have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
      interval_cases k
      · simp only [pow_one, Nat.sub_self, pow_zero]
        nlinarith
      · simp only [Nat.add_one_sub_one, pow_one]
        nlinarith
    calc Real.exp (-(1 + ε) * L + σ) / 2 * ((c ^ 2 * ρ n ^ k + ρ n ^ (k - 1)) * n)
        ≤ Real.exp (-(1 + ε) * L + σ) / 2 * (((c ^ 2 + 1) * Real.exp (ε / 2 * L)) * n) := by
          gcongr
      _ = Real.exp σ / 2 * ((c ^ 2 + 1) * Real.exp (-(ε / 2) * L)) := by
          rw [hnexp]
          have : Real.exp (-(1 + ε) * L + σ) * Real.exp (ε / 2 * L) * Real.exp L =
              Real.exp σ * Real.exp (-(ε / 2) * L) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
          rw [← hnexp] at this ⊢
          rw [hnexp] at this ⊢
          nlinarith [this]


/-! ### After the critical time, under `λ₁ = d^{o(1)}` -/

theorem weak_time_ge {ρ : ℕ → ℝ} (hρ : ∀ n, 0 < ρ n) {ε : ℝ} (hε : 0 < ε) {a : ℝ} :
    ∀ᶠ n : ℕ in atTop, a / ρ n ≤ (1 + ε) * criticalTime n (ρ n) := by
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (max (2 * a) 0)] with n hn
  have h0 := hρ n
  have hn' : max (2 * a) 0 ≤ Real.log n := hn
  have hl : 2 * a ≤ Real.log n := le_trans (le_max_left _ _) hn'
  have hl0 : 0 ≤ Real.log n := le_trans (le_max_right _ _) hn'
  unfold criticalTime
  rw [div_le_iff₀ h0]
  have h3 : (1 + ε) * (Real.log n / (2 * ρ n)) * ρ n = (1 + ε) * Real.log n / 2 := by
    field_simp
  rw [h3]
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω]

theorem meanBall_entropy_after_cutoff_weak
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hsub : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, (D n).rate ≤ (n : ℝ) ^ δ) :
    Tendsto (fun n => meanBallKL (D n) c ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) := by
  have hdec := weak_scalar_decay (ρ := fun n => (D n).rate) (fun n => (D n).rate_pos) hsub
    (c := c) (σ := 2) hε 1 le_rfl (by norm_num)
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hdec
  simp only [ENNReal.ofReal_zero, Function.comp_def] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => bot_le) ?_
  filter_upwards [weak_time_ge (fun n => (D n).rate_pos) hε (a := 1), eventually_ge_atTop 1]
    with n ht hn
  exact meanBallKL_upper_shift (D n) (by omega) hc ht |>.trans (by simp)

theorem meanBallFisher_after_cutoff_weak
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hsub : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, (D n).rate ≤ (n : ℝ) ^ δ) :
    Tendsto (fun n => meanBallFisher (D n) c ((1 + ε) * criticalTime n (D n).rate)) atTop
      (𝓝 0) := by
  have hdec := weak_scalar_decay (ρ := fun n => (D n).rate) (fun n => (D n).rate_pos) hsub
    (c := c) (σ := 4) hε 2 (by norm_num) le_rfl
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hdec
  simp only [ENNReal.ofReal_zero, Function.comp_def] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => bot_le) ?_
  filter_upwards [weak_time_ge (fun n => (D n).rate_pos) hε (a := 2), eventually_ge_atTop 1]
    with n ht hn
  exact meanBallFisher_upper_shift (D n) (by omega) hc ht |>.trans (by simp)

theorem meanBall_totalVariation_after_cutoff_weak
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hsub : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, (D n).rate ≤ (n : ℝ) ^ δ) :
    Tendsto (fun n => meanBallTV (D n) c ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) := by
  apply projectedSetTV_tendsto_zero_of_KL (fun n => spectralInformationToAffine (D n))
    (fun n => Metric.closedBall (∫ y, y ∂gibbsMeasure volume (D n).potential) (c * Real.sqrt n))
    (fun n => ⟨∫ y, y ∂gibbsMeasure volume (D n).potential, by
      rw [Metric.mem_closedBall, dist_self]
      exact mul_nonneg hc (Real.sqrt_nonneg (n : ℝ))⟩)
    (fun n => (1 + ε) * criticalTime n (D n).rate)
  exact meanBall_entropy_after_cutoff_weak D hc hε hsub

/-- Remark 3.5 at the level of library data: all six limits under `liminf λ₁ > 0` and
`λ₁ = d^{o(1)}`. -/
theorem meanBall_information_cutoff_weak
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop)
    (hsub : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, (D n).rate ≤ (n : ℝ) ^ δ) :
    Tendsto (fun n => meanBallKL (D n) c ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 ⊤) ∧
    Tendsto (fun n => meanBallKL (D n) c ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) ∧
    Tendsto (fun n => meanBallTV (D n) c ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 1) ∧
    Tendsto (fun n => meanBallTV (D n) c ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) ∧
    Tendsto (fun n => meanBallFisher (D n) c ((1 - ε) * criticalTime n (D n).rate)) atTop
      (𝓝 ⊤) ∧
    Tendsto (fun n => meanBallFisher (D n) c ((1 + ε) * criticalTime n (D n).rate)) atTop
      (𝓝 0) :=
  ⟨meanBall_entropy_before_cutoff D hc hε hε1 hliminf,
    meanBall_entropy_after_cutoff_weak D hc.le hε hsub,
    meanBall_totalVariation_before_cutoff D hc hε hε1 hliminf,
    meanBall_totalVariation_after_cutoff_weak D hc.le hε hsub,
    meanBallFisher_before_cutoff D hc hε hε1 hliminf,
    meanBallFisher_after_cutoff_weak D hc.le hε hsub⟩

end CutoffRigidity

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped ENNReal NNReal Topology Asymptotics

/-- **Remark 3.5** (weaker assumption): Corollary 1.4 holds with `λ₁⁽ⁿ⁾ = o(log n)` replaced by
`λ₁⁽ⁿ⁾ = n^{o(1)}`. -/
theorem information_cutoff_weak_carrier {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {V : ∀ n, CutCur.Rd n → ℝ} {B : ∀ n, ℝ≥0 → Ω n → CutCur.Rd n} {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, CutCur.Rd n → ℝ≥0 → Ω n → CutCur.Rd n}
    (h : CutCur.IsRigidSequence V B P X)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, CutCur.spectralGap (V n) ≤ (n : ℝ) ^ ε)
    {c : ℝ} (hc : 0 < c) :
    let t := fun n => CutCur.criticalTime n (CutCur.spectralGap (V n))
    let S := fun n => CutCur.meanBall (V n) c
    CutCur.HasCutoff (fun n => CutCur.worst (P n) (X n) (S n) (CutCur.fisherInfo (V n))) t ⊤ 0 ∧
    CutCur.HasCutoff (fun n => CutCur.worst (P n) (X n) (S n)
      (InformationTheory.klDiv · (CutCur.gibbs (V n)))) t ⊤ 0 ∧
    CutCur.HasCutoff (fun n => CutCur.worst (P n) (X n) (S n)
      (fun ν => .ofReal (CutCur.tvDist ν (CutCur.gibbs (V n))))) t 1 0 := by
  intro t S
  obtain ⟨Ω', _, D, hD, hliminf, hcrit, -⟩ := exists_seqData_rigid h
  have hev : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hsub : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, (D n).rate ≤ (n : ℝ) ^ δ := by
    intro δ hδ
    filter_upwards [hsmall δ hδ, hev] with n hn hn0
    rw [(hD n hn0).1]; exact hn
  have prof : ∀ {δ : ∀ n, Measure (CutCur.Rd n) → ℝ≥0∞} {Q : ℕ → ℝ → ℝ≥0∞},
      (∀ n, 0 < n → ∀ s : ℝ, CutCur.worst (P n) (X n) (S n) (δ n) s = Q n s) →
      ∀ (a : ℝ≥0∞) (σ : ℝ),
        Tendsto (fun n => Q n (σ * criticalTime n (D n).rate)) atTop (𝓝 a) →
        Tendsto (fun n => CutCur.worst (P n) (X n) (S n) (δ n) (σ * t n)) atTop (𝓝 a) := by
    intro δ Q hQ a σ hlim
    refine hlim.congr' ?_
    filter_upwards [hev] with n hn
    rw [hQ n hn, ← hcrit n hn]
  have hK : ∀ n, 0 < n → ∀ s : ℝ, CutCur.worst (P n) (X n) (S n)
      (InformationTheory.klDiv · (CutCur.gibbs (V n))) s = meanBallKL (D n) c s := by
    intro n hn s
    obtain ⟨hr, hpot, hk⟩ := hD n hn
    have := worst_kl_eq (D n) c (P := P n) (X := X n) hk s
    rwa [hpot] at this
  have hF : ∀ n, 0 < n → ∀ s : ℝ, CutCur.worst (P n) (X n) (S n) (CutCur.fisherInfo (V n)) s =
      meanBallFisher (D n) c s := by
    intro n hn s
    obtain ⟨hr, hpot, hk⟩ := hD n hn
    have := worst_fisher_eq (D n) c (P := P n) (X := X n) hk s
    rwa [hpot] at this
  have hT : ∀ n, 0 < n → ∀ s : ℝ, CutCur.worst (P n) (X n) (S n)
      (fun ν => .ofReal (CutCur.tvDist ν (CutCur.gibbs (V n)))) s =
        ENNReal.ofReal (meanBallTV (D n) c s) := by
    intro n hn s
    obtain ⟨hr, hpot, hk⟩ := hD n hn
    have := worst_tv_eq (D n) c hc.le (P := P n) (X := X n) hk s
    rwa [hpot] at this
  have hTv : ∀ {a : ℝ}, ∀ {u : ℕ → ℝ}, Tendsto u atTop (𝓝 a) →
      Tendsto (fun n => ENNReal.ofReal (u n)) atTop (𝓝 (ENNReal.ofReal a)) :=
    fun hu => (ENNReal.continuous_ofReal.tendsto _).comp hu
  refine ⟨fun ε hε0 hε1 => ?_, fun ε hε0 hε1 => ?_, fun ε hε0 hε1 => ?_⟩ <;>
    obtain ⟨hKb, hKa, hTb, hTa, hFb, hFa⟩ :=
      meanBall_information_cutoff_weak D hc hε0 hε1 hliminf hsub
  · exact ⟨prof hF _ _ hFb, prof hF _ _ hFa⟩
  · exact ⟨prof hK _ _ hKb, prof hK _ _ hKa⟩
  · have h1 := hTv hTb
    have h2 := hTv hTa
    rw [ENNReal.ofReal_one] at h1
    rw [ENNReal.ofReal_zero] at h2
    exact ⟨prof hT _ _ h1, prof hT _ _ h2⟩

end CutoffRigidity.Paper
