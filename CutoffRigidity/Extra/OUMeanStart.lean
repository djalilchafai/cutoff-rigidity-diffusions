module

public import CutoffRigidity.Paper.CarrierDefs
public import CutoffRigidity.Extra.OUEigen
public import CutoffRigidity.Paper.WassersteinCutoff
public import CutoffRigidity.AffineProjectedDistances
public import CutoffRigidity.OUKernel

/-! # OU started from the mean: Wasserstein cutoff at `log d/(4λ₁)` (manuscript L197-202)

For `V = ρ|x|²/2 + c` and the initial condition `S = {m}`, `m = 0` the mean of `μ`, the squared
Wasserstein distance is exactly `d (1 - √(1 - e^{-2ρt}))²/ρ`, which has a cutoff at
`log d/(4ρ)`; in particular there is no cutoff at `log d/(2ρ)`, so `c > 0` is essential in
Corollary 1.3.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff

universe u

section Core

variable {d : ℕ}

/-- For the quadratic potential: gap, rigid curvature, and the affine eigenfunction data. -/
theorem ou_gap_rigid (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {c : ℝ}
    (hp : IsProbabilityMeasure (CutCur.gibbs fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c)) :
    CutCur.spectralGap (fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c) = ρ ∧
      ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤
        fderiv ℝ (fderiv ℝ (fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c)) x z z := by
  have hCI := convex_interaction hd hρ (W := fun _ => c) contDiff_const
    (convexOn_const c convex_univ) (fun _ _ => rfl) hp
  exact ⟨hCI.1.1, hCI.2.1.1⟩

/-- The mean of the Gaussian-type measure `e^{-ρ|x|²/2 - c}` is `0`. -/
theorem ou_mean_zero (_hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {c : ℝ}
    (hp : IsProbabilityMeasure (CutCur.gibbs fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c)) :
    ∫ x, x ∂CutCur.gibbs (fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c) = 0 := by
  set V := fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c with hV
  have hVc : ContDiff ℝ 2 V := by
    have : ContDiff ℝ 2 (fun x : CutCur.Rd d => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
    exact (this.const_smul (ρ / 2)).add contDiff_const
  have hp' : IsProbabilityMeasure (gibbsMeasure volume V) := hp
  by_cases hi : Integrable (fun x : CutCur.Rd d => x) (CutCur.gibbs V)
  · ext i
    have h1 : ∫ x : CutCur.Rd d, x i ∂CutCur.gibbs V = (∫ x, x ∂CutCur.gibbs V) i :=
      (EuclideanSpace.proj i : CutCur.Rd d →L[ℝ] ℝ).integral_comp_comm hi
    have heig : ∀ x, langevinDifferentialOperator V
        (fun y => inner ℝ (Real.sqrt ρ • EuclideanSpace.single i (1 : ℝ)) y + 0) x =
        -ρ * (inner ℝ (Real.sqrt ρ • EuclideanSpace.single i (1 : ℝ)) x + 0) := by
      refine (affine_eigenfunction_iff_drift V _ 0 ρ).mpr fun x => ?_
      rw [show gradient V x = ρ • x from gradient_ou ρ c x, real_inner_smul_right, add_zero]
    have hm := affine_eigenfunction_mean_zero V (hVc.differentiable (by norm_num))
      (Real.sqrt ρ • EuclideanSpace.single i (1 : ℝ))
      (by
        intro h0
        have := congrArg (fun v : CutCur.Rd d => v i) h0
        simp [(Real.sqrt_pos.mpr hρ).ne'] at this) 0 ρ hρ heig hp'
    have e := congrFun (coord_eq ρ i)
    have hm' : ∫ x, Real.sqrt ρ * x i ∂CutCur.gibbs V = 0 := by
      rw [show (fun x : CutCur.Rd d => Real.sqrt ρ * x i) = _ from coord_eq ρ i]
      exact hm
    rw [integral_const_mul] at hm'
    have := (mul_eq_zero.mp hm').resolve_left (Real.sqrt_pos.mpr hρ).ne'
    rw [← h1, this]
    rfl
  · exact integral_undef hi

/-- Exact squared Wasserstein distance of `X_t^{0}` to equilibrium for the quadratic potential. -/
theorem ou_squaredWasserstein_zero (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {c : ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω}
    {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hL : CutCur.IsLangevin (fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c) B P X) (t : ℝ≥0) :
    squaredWasserstein (P.map (X 0 t)) (CutCur.gibbs fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c) =
      ENNReal.ofReal (d * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * t))) ^ 2 / ρ) := by
  set V := fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c with hV
  have hVc : ContDiff ℝ 2 V := hL.1
  have hp : IsProbabilityMeasure (CutCur.gibbs V) := hL.2.1
  have hp' : IsProbabilityMeasure (gibbsMeasure volume V) := hp
  obtain ⟨hgap, hess⟩ := ou_gap_rigid hd hρ hp
  have hB : IsEuclideanBrownian B P := isStdBrownian_iff.mp hL.2.2.1
  -- the affine data
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
    (fun _ => 0) ρ hρ heig hp' horth 0 t
  have hgib := gibbsMeasure_map_affineEigenfunctionMap hVc a (fun _ => 0) ρ hρ heig hp' horth
  have hA : affineEigenfunctionMap a (fun _ : Fin d => (0 : ℝ)) = fun x => Real.sqrt ρ • x := by
    funext x
    ext i
    simp [affineEigenfunctionMap, a, EuclideanSpace.inner_single_left, real_inner_smul_left]
  rw [hA] at hlaw hgib
  have hν : P.map (X 0 t) = langevinKernel V B P t 0 :=
    IsLangevin.map_eq_langevinKernel hL ρ hρ.le hess 0 t
  have hmk := langevinKernel_isMarkovKernel hB hVc ρ hρ.le hess t
  have hνp : IsProbabilityMeasure (langevinKernel V B P t 0) := inferInstance
  rw [hν]
  show squaredWasserstein _ (gibbsMeasure volume V) = _
  -- transport costs through the dilation
  set K : ℝ≥0 := ⟨Real.sqrt ρ, Real.sqrt_nonneg ρ⟩ with hK
  have hKpos : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hLip : LipschitzWith K (fun x : CutCur.Rd d => Real.sqrt ρ • x) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hKpos]
    rfl
  set K' : ℝ≥0 := ⟨(Real.sqrt ρ)⁻¹, inv_nonneg.mpr (Real.sqrt_nonneg ρ)⟩ with hK'
  have hLip' : LipschitzWith K' (fun x : CutCur.Rd d => (Real.sqrt ρ)⁻¹ • x) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hKpos)]
    rfl
  have hid : (fun x : CutCur.Rd d => (Real.sqrt ρ)⁻¹ • x) ∘ (fun x => Real.sqrt ρ • x) = id := by
    funext x; simp [smul_smul, hKpos.ne']
  have hmeas : Measurable (fun x : CutCur.Rd d => Real.sqrt ρ • x) := by fun_prop
  have hmeas' : Measurable (fun x : CutCur.Rd d => (Real.sqrt ρ)⁻¹ • x) := by fun_prop
  have hexp : squaredWasserstein
      ((langevinKernel V B P t 0).map (fun x => Real.sqrt ρ • x))
      ((gibbsMeasure volume V).map (fun x => Real.sqrt ρ • x)) =
      ENNReal.ofReal (d * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * t))) ^ 2) := by
    rw [hlaw, hgib, squaredWasserstein_ouLaw]
    have : (Real.sqrt ρ • (0 : CutCur.Rd d)) = 0 := smul_zero _
    simp [this]
  have hupper : squaredWasserstein (langevinKernel V B P t 0) (gibbsMeasure volume V) ≤
      ENNReal.ofReal ρ⁻¹ *
        ENNReal.ofReal (d * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * t))) ^ 2) := by
    have h := squaredWasserstein_map_le
      ((langevinKernel V B P t 0).map (fun x => Real.sqrt ρ • x))
      ((gibbsMeasure volume V).map (fun x => Real.sqrt ρ • x)) hLip'
    rw [hexp, Measure.map_map hmeas' hmeas, Measure.map_map hmeas' hmeas, hid,
      Measure.map_id, Measure.map_id] at h
    have hfac : (K' : ℝ≥0∞) ^ 2 = ENNReal.ofReal ρ⁻¹ := by
      rw [show (K' : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt ρ)⁻¹ from
        (ENNReal.ofReal_coe_nnreal (p := K')).symm,
        ← ENNReal.ofReal_pow (inv_nonneg.mpr (Real.sqrt_nonneg ρ)), inv_pow, Real.sq_sqrt hρ.le]
    rw [hfac] at h
    exact h
  have hlower : ENNReal.ofReal (d * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * t))) ^ 2) ≤
      ENNReal.ofReal ρ * squaredWasserstein (langevinKernel V B P t 0) (gibbsMeasure volume V) := by
    have h := squaredWasserstein_map_le (langevinKernel V B P t 0) (gibbsMeasure volume V) hLip
    rw [hexp] at h
    have hfac : (K : ℝ≥0∞) ^ 2 = ENNReal.ofReal ρ := by
      rw [show (K : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt ρ) from
        (ENNReal.ofReal_coe_nnreal (p := K)).symm,
        ← ENNReal.ofReal_pow (Real.sqrt_nonneg ρ), Real.sq_sqrt hρ.le]
    rw [hfac] at h
    exact h
  have hr : ENNReal.ofReal (d * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * t))) ^ 2 / ρ) =
      ENNReal.ofReal ρ⁻¹ *
        ENNReal.ofReal (d * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * t))) ^ 2) := by
    rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.mpr hρ.le)]
  rw [hr]
  refine le_antisymm hupper ?_
  have h2 : ENNReal.ofReal ρ⁻¹ *
      ENNReal.ofReal (d * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * t))) ^ 2) ≤
      ENNReal.ofReal ρ⁻¹ * (ENNReal.ofReal ρ *
        squaredWasserstein (langevinKernel V B P t 0) (gibbsMeasure volume V)) := by gcongr
  have hc : ENNReal.ofReal ρ⁻¹ * ENNReal.ofReal ρ = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hρ.le), inv_mul_cancel₀ hρ.ne', ENNReal.ofReal_one]
  rw [← mul_assoc, hc, one_mul] at h2
  exact h2

end Core

section Asymptotics

theorem one_sub_sqrt_bounds {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    q / 2 ≤ 1 - Real.sqrt (1 - q) ∧ 1 - Real.sqrt (1 - q) ≤ q := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 - q by linarith)
  have hn := Real.sqrt_nonneg (1 - q)
  constructor
  · nlinarith [sq_nonneg (Real.sqrt (1 - q) - (1 - q / 2))]
  · have : 1 - q ≤ Real.sqrt (1 - q) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith
    linarith

/-- `w_n(s) = n (1 - √(1 - e^{-2ρs}))² / ρ`: the exact squared distance from the mean. -/
noncomputable def ouMeanW (ρ : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  n * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * s))) ^ 2 / ρ

theorem ouMeanW_exp_bounds {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 ≤ s) :
    (n : ℝ) * Real.exp (-2 * ρ * s) ^ 2 / (4 * ρ) ≤ ouMeanW ρ n s ∧
      ouMeanW ρ n s ≤ (n : ℝ) * Real.exp (-2 * ρ * s) ^ 2 / ρ := by
  have h0 : 0 ≤ Real.exp (-2 * ρ * s) := (Real.exp_pos _).le
  have h1 : Real.exp (-2 * ρ * s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  obtain ⟨hb1, hb2⟩ := one_sub_sqrt_bounds h0 h1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold ouMeanW
  set q := Real.exp (-2 * ρ * s)
  have hu0 : 0 ≤ 1 - Real.sqrt (1 - q) := by linarith [h0]
  constructor
  · rw [show (n : ℝ) * q ^ 2 / (4 * ρ) = n * (q / 2) ^ 2 / ρ by field_simp; ring]
    gcongr
  · gcongr

theorem exp_at_time {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ} (hn : 0 < n) (a : ℝ) :
    (n : ℝ) * Real.exp (-2 * ρ * (a * Real.log n / (4 * ρ))) ^ 2 =
      Real.exp ((1 - a) * Real.log n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have key : ∀ L : ℝ, (n : ℝ) = Real.exp L →
      (n : ℝ) * Real.exp (-2 * ρ * (a * L / (4 * ρ))) ^ 2 = Real.exp ((1 - a) * L) := by
    intro L hL
    rw [hL, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  exact key _ (Real.exp_log hn').symm

theorem ouMeanW_tendsto_atTop {ρ a : ℝ} (hρ : 0 < ρ) (ha : a < 1) (ha0 : 0 ≤ a) :
    Tendsto (fun n : ℕ => ouMeanW ρ n (a * Real.log n / (4 * ρ))) atTop atTop := by
  have hL : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => Real.exp ((1 - a) * Real.log n) / (4 * ρ)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (hL.const_mul_atTop (by linarith))).atTop_div_const (by positivity)
  refine tendsto_atTop_mono' _ ?_ h1
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : 0 < n := by omega
  have hs : 0 ≤ a * Real.log n / (4 * ρ) := by
    have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    positivity
  have := (ouMeanW_exp_bounds hρ hn0 hs).1
  rwa [show (n : ℝ) * Real.exp (-2 * ρ * (a * Real.log n / (4 * ρ))) ^ 2 =
    Real.exp ((1 - a) * Real.log n) from exp_at_time hρ hn0 a] at this

theorem ouMeanW_tendsto_zero {ρ a : ℝ} (hρ : 0 < ρ) (ha : 1 < a) :
    Tendsto (fun n : ℕ => ouMeanW ρ n (a * Real.log n / (4 * ρ))) atTop (𝓝 0) := by
  have hL : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => Real.exp ((1 - a) * Real.log n) / ρ) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp (hL.const_mul_atTop_of_neg (by linarith : 1 - a < 0)))
    simpa using this.div_const ρ
  refine squeeze_zero' ?_ ?_ h1
  · filter_upwards [eventually_ge_atTop 1] with n hn
    unfold ouMeanW; positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : 0 < n := by omega
    have hs : 0 ≤ a * Real.log n / (4 * ρ) := by
      have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
      have : 0 ≤ a := by linarith
      positivity
    have := (ouMeanW_exp_bounds hρ hn0 hs).2
    rwa [show (n : ℝ) * Real.exp (-2 * ρ * (a * Real.log n / (4 * ρ))) ^ 2 =
      Real.exp ((1 - a) * Real.log n) from exp_at_time hρ hn0 a] at this

end Asymptotics

/-- **OU started from the mean** (after Corollary 1.3): for `V⁽ⁿ⁾(x) = ρ|x|²/2 + c⁽ⁿ⁾` with
`ρ > 0` independent of `n` (so `λ₁⁽ⁿ⁾ = ρ`) and the single initial condition `S⁽ⁿ⁾ = {m⁽ⁿ⁾}`, `m⁽ⁿ⁾`
the mean of `μ⁽ⁿ⁾`, the Wasserstein distance has a cutoff at `log n/(4λ₁)`, and there is no
cutoff at the critical time `log n/(2λ₁)` of Corollary 1.3 (so `c > 0` is essential there). -/
theorem ou_mean_start_cutoff_carrier {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] {ρ : ℝ} (hρ : 0 < ρ)
    {c : ℕ → ℝ} {B : ∀ n, ℝ≥0 → Ω n → CutCur.Rd n} {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, CutCur.Rd n → ℝ≥0 → Ω n → CutCur.Rd n}
    (hL : ∀ n, 0 < n →
      CutCur.IsLangevin (fun x : CutCur.Rd n => ρ / 2 * ‖x‖ ^ 2 + c n) (B n) (P n) (X n)) :
    let V := fun n (x : CutCur.Rd n) => ρ / 2 * ‖x‖ ^ 2 + c n
    let prof := fun n => CutCur.worst (P n) (X n) {∫ x, x ∂CutCur.gibbs (V n)}
      (CutCur.wasserstein2 · (CutCur.gibbs (V n)))
    CutCur.HasCutoff prof (fun n => Real.log n / (4 * CutCur.spectralGap (V n))) ⊤ 0 ∧
      ¬ CutCur.HasCutoff prof (fun n => CutCur.criticalTime n (CutCur.spectralGap (V n))) ⊤ 0 := by
  intro V prof
  have hev : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hgap : ∀ n, 0 < n → CutCur.spectralGap (V n) = ρ := fun n hn =>
    (ou_gap_rigid hn hρ (hL n hn).2.1).1
  have hprof : ∀ n, 0 < n → ∀ s : ℝ, 0 ≤ s →
      prof n s = ENNReal.ofReal (Real.sqrt (ouMeanW ρ n s)) := by
    intro n hn s hs
    have hm : ∫ x, x ∂CutCur.gibbs (V n) = 0 := ou_mean_zero hn hρ (hL n hn).2.1
    simp only [prof, CutCur.worst, hm, Set.mem_singleton_iff, iSup_iSup_eq_left]
    rw [wasserstein2_eq_rpow, ou_squaredWasserstein_zero hn hρ (hL n hn),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 1
    simp only [Real.coe_toNNReal _ hs]
    exact (Real.sqrt_eq_rpow (ouMeanW ρ n s)).symm
  have hLg : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnn : ∀ n : ℕ, 0 ≤ Real.log n / (4 * ρ) := fun n => by
    have := Real.log_natCast_nonneg n
    positivity
  -- limits of the profile at the times `a log n / (4ρ)`
  have htop : ∀ a : ℝ, 0 ≤ a → a < 1 →
      Tendsto (fun n : ℕ => prof n (a * Real.log n / (4 * ρ))) atTop (𝓝 ⊤) := by
    intro a ha0 ha
    have h := ENNReal.tendsto_ofReal_atTop.comp
      (Real.tendsto_sqrt_atTop.comp (ouMeanW_tendsto_atTop hρ ha ha0))
    refine h.congr' ?_
    filter_upwards [hev] with n hn
    rw [hprof n hn _ (by have := Real.log_natCast_nonneg n; positivity)]
    rfl
  have hzero : ∀ a : ℝ, 1 < a →
      Tendsto (fun n : ℕ => prof n (a * Real.log n / (4 * ρ))) atTop (𝓝 0) := by
    intro a ha
    have h1 := (Real.continuous_sqrt.tendsto 0).comp (ouMeanW_tendsto_zero hρ ha)
    rw [Real.sqrt_zero] at h1
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp h1
    rw [ENNReal.ofReal_zero] at h
    refine h.congr' ?_
    filter_upwards [hev] with n hn
    rw [hprof n hn _ (by have : 0 ≤ a := by linarith
                         have := Real.log_natCast_nonneg n; positivity)]
    rfl
  constructor
  · intro ε h0 h1
    have e : ∀ b : ℝ, ∀ᶠ n : ℕ in atTop,
        b * (Real.log n / (4 * CutCur.spectralGap (V n))) = b * Real.log n / (4 * ρ) := by
      intro b
      filter_upwards [hev] with n hn
      rw [hgap n hn, mul_div_assoc]
    constructor
    · refine (htop (1 - ε) (by linarith) (by linarith)).congr' ?_
      filter_upwards [e (1 - ε)] with n hn
      rw [hn]
    · refine (hzero (1 + ε) (by linarith)).congr' ?_
      filter_upwards [e (1 + ε)] with n hn
      rw [hn]
  · intro hcut
    obtain ⟨hb, -⟩ := hcut (1 / 4) (by norm_num) (by norm_num)
    have h2 := hzero (3 / 2) (by norm_num)
    have heq : ∀ᶠ n : ℕ in atTop,
        prof n ((1 - 1 / 4) * CutCur.criticalTime n (CutCur.spectralGap (V n))) =
          prof n (3 / 2 * Real.log n / (4 * ρ)) := by
      filter_upwards [hev] with n hn
      rw [hgap n hn]
      congr 1
      simp only [CutCur.criticalTime]
      field_simp
      ring
    have := tendsto_nhds_unique (hb.congr' heq) h2
    exact ENNReal.top_ne_zero this

end CutoffRigidity.Paper
