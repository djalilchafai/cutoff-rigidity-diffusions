module

public import Mathlib

/-! # One-dimensional regularisation of the logarithmic interaction

`sp u = log (1 + e^u)` (softplus).  For `ε > 0` and `β ≥ 0`,
`G ε β t = -β log (ε sp (t/ε)) + log (1 + e^{-t/ε})` is a smooth convex function with
`exp (-G ε β t) = (ε sp (t/ε))^β / (1 + e^{-t/ε})`; as `ε → 0` this tends to `t^β 1_{t>0}`.
-/

@[expose] public section

open Real Filter Topology

namespace CutoffRigidity.Dyson

noncomputable def sp (u : ℝ) : ℝ := Real.log (1 + Real.exp u)
noncomputable def sg (u : ℝ) : ℝ := Real.exp u / (1 + Real.exp u)

theorem sp_pos (u : ℝ) : 0 < sp u := Real.log_pos (by linarith [Real.exp_pos u])

theorem hasDerivAt_sp (u : ℝ) : HasDerivAt sp (sg u) u := by
  have h := ((Real.hasDerivAt_exp u).const_add 1).log (by positivity)
  exact h

theorem hasDerivAt_sg (u : ℝ) : HasDerivAt sg (sg u * (1 - sg u)) u := by
  have h : HasDerivAt (fun u => Real.exp u / (1 + Real.exp u))
      ((Real.exp u * (1 + Real.exp u) - Real.exp u * Real.exp u) / (1 + Real.exp u) ^ 2) u :=
    HasDerivAt.fun_div (Real.hasDerivAt_exp u) ((Real.hasDerivAt_exp u).const_add 1) (by positivity)
  have e : sg u * (1 - sg u) =
      (Real.exp u * (1 + Real.exp u) - Real.exp u * Real.exp u) / (1 + Real.exp u) ^ 2 := by
    have : (1 + Real.exp u) ≠ 0 := by positivity
    unfold sg; field_simp
  rw [e]; exact h

theorem sg_pos (u : ℝ) : 0 < sg u := by unfold sg; positivity
theorem sg_lt_one (u : ℝ) : sg u < 1 := by
  unfold sg; rw [div_lt_one (by positivity)]; linarith

theorem sp_le_exp (u : ℝ) : sp u ≤ Real.exp u := by
  have := Real.log_le_sub_one_of_pos (x := 1 + Real.exp u) (by positivity)
  unfold sp; linarith

theorem sp_le_abs_add_one (u : ℝ) : sp u ≤ |u| + 1 := by
  unfold sp
  have h2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  rcases le_total u 0 with hu | hu
  · have : Real.log (1 + Real.exp u) ≤ Real.log 2 :=
      Real.log_le_log (by positivity) (by linarith [Real.exp_le_one_iff.2 hu])
    linarith [abs_nonneg u]
  · have h1 : Real.log (1 + Real.exp u) ≤ Real.log (2 * Real.exp u) :=
      Real.log_le_log (by positivity) (by linarith [Real.one_le_exp hu])
    rw [Real.log_mul (by norm_num) (Real.exp_pos u).ne', Real.log_exp] at h1
    rw [abs_of_nonneg hu]; linarith

theorem sp_sub_le {u : ℝ} (hu : 0 ≤ u) : sp u - u ≤ 1 := by
  have := sp_le_abs_add_one u
  rw [abs_of_nonneg hu] at this; linarith

/-- `A u = -log (sp u)` is convex: `sp` is log-concave. -/
theorem convexOn_neg_log_sp : ConvexOn ℝ Set.univ fun u => -Real.log (sp u) := by
  have hd (u : ℝ) : HasDerivAt (fun u => -Real.log (sp u)) (-(sg u / sp u)) u :=
    ((hasDerivAt_sp u).log (sp_pos u).ne').neg
  have hder : deriv (fun u => -Real.log (sp u)) = fun u => -(sg u / sp u) :=
    funext fun u => (hd u).deriv
  have hd2 (u : ℝ) : HasDerivAt (fun u => -(sg u / sp u))
      (-((sg u * (1 - sg u) * sp u - sg u * sg u) / sp u ^ 2)) u :=
    ((hasDerivAt_sg u).div (hasDerivAt_sp u) (sp_pos u).ne').neg
  refine convexOn_univ_of_deriv2_nonneg (fun u => (hd u).differentiableAt) ?_ fun u => ?_
  · rw [hder]; exact fun u => (hd2 u).differentiableAt
  · simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    rw [hder, (hd2 u).deriv]
    have hsp := sp_pos u
    have h1 : sg u * (1 - sg u) * sp u ≤ sg u * sg u := by
      have : (1 - sg u) * sp u ≤ sg u := by
        have e : 1 - sg u = 1 / (1 + Real.exp u) := by unfold sg; field_simp; ring
        rw [e, one_div_mul_eq_div, div_le_iff₀ (by positivity)]
        unfold sg
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith [sp_le_exp u, Real.exp_pos u]
      nlinarith [sg_pos u]
    have : 0 ≤ (sg u * sg u - sg u * (1 - sg u) * sp u) / sp u ^ 2 := by
      apply div_nonneg <;> nlinarith [sq_nonneg (sp u)]
    linarith [show -((sg u * (1 - sg u) * sp u - sg u * sg u) / sp u ^ 2) =
      (sg u * sg u - sg u * (1 - sg u) * sp u) / sp u ^ 2 by ring]

theorem convexOn_sp : ConvexOn ℝ Set.univ sp := by
  have hder : deriv sp = sg := funext fun u => (hasDerivAt_sp u).deriv
  refine convexOn_univ_of_deriv2_nonneg (fun u => (hasDerivAt_sp u).differentiableAt) ?_ fun u => ?_
  · rw [hder]; exact fun u => (hasDerivAt_sg u).differentiableAt
  · simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    rw [hder, (hasDerivAt_sg u).deriv]
    exact mul_nonneg (sg_pos u).le (by linarith [sg_lt_one u])


theorem le_sp (u : ℝ) : u ≤ sp u := by
  unfold sp
  calc u = Real.log (Real.exp u) := (Real.log_exp u).symm
    _ ≤ _ := Real.log_le_log (Real.exp_pos u) (by linarith)

theorem contDiff_sp : ContDiff ℝ ⊤ sp := by
  unfold sp
  exact ContDiff.log (by fun_prop) (fun u => by positivity)

/-- The regularised interaction `G ε β`. -/
noncomputable def Ge (ε β t : ℝ) : ℝ :=
  -β * Real.log (ε * sp (t / ε)) + Real.log (1 + Real.exp (-t / ε))

/-- The regularised Boltzmann weight `exp (- G ε β)`. -/
noncomputable def qe (ε β t : ℝ) : ℝ :=
  (ε * sp (t / ε)) ^ β / (1 + Real.exp (-t / ε))

theorem exp_neg_Ge {ε : ℝ} (hε : 0 < ε) (β t : ℝ) : Real.exp (-Ge ε β t) = qe ε β t := by
  have ha : 0 < ε * sp (t / ε) := mul_pos hε (sp_pos _)
  have hb : 0 < 1 + Real.exp (-t / ε) := by positivity
  unfold Ge qe
  have e : -(-β * Real.log (ε * sp (t / ε)) + Real.log (1 + Real.exp (-t / ε))) =
      Real.log (ε * sp (t / ε)) * β - Real.log (1 + Real.exp (-t / ε)) := by ring
  rw [e, Real.exp_sub, Real.exp_log hb, ← Real.rpow_def_of_pos ha]

theorem contDiff_Ge {ε : ℝ} (hε : 0 < ε) (β : ℝ) : ContDiff ℝ ⊤ (Ge ε β) := by
  unfold Ge
  have h1 : ContDiff ℝ ⊤ fun t : ℝ => ε * sp (t / ε) :=
    contDiff_const.mul (contDiff_sp.comp (contDiff_id.div_const ε))
  refine (contDiff_const.mul (ContDiff.log h1 fun t => (mul_pos hε (sp_pos _)).ne')).add ?_
  exact ContDiff.log (by fun_prop) (fun t => by positivity)

theorem convexOn_Ge {ε : ℝ} (hε : 0 < ε) {β : ℝ} (hβ : 0 ≤ β) : ConvexOn ℝ Set.univ (Ge ε β) := by
  let L1 : ℝ →ₗ[ℝ] ℝ := ε⁻¹ • LinearMap.id
  let L2 : ℝ →ₗ[ℝ] ℝ := (-ε⁻¹) • LinearMap.id
  have hA := ((convexOn_neg_log_sp.comp_linearMap L1).smul hβ)
  have hB := convexOn_sp.comp_linearMap L2
  rw [Set.preimage_univ] at hA hB
  have hC := (hA.add hB).add_const (-β * Real.log ε)
  convert hC using 1
  ext t
  have hs := sp_pos (t / ε)
  simp only [Ge, Pi.add_apply, Function.comp_apply, L1, L2, LinearMap.smul_apply,
    LinearMap.id_apply, smul_eq_mul]
  rw [Real.log_mul hε.ne' (sp_pos _).ne']
  have e1 : ε⁻¹ * t = t / ε := by rw [div_eq_inv_mul]
  have e2 : -ε⁻¹ * t = -t / ε := by rw [neg_div, neg_mul, div_eq_inv_mul]
  rw [e1, e2]
  simp only [sp]
  ring

theorem qe_nonneg {ε : ℝ} (hε : 0 < ε) (β t : ℝ) : 0 ≤ qe ε β t := by
  unfold qe
  have ha : 0 < ε * sp (t / ε) := mul_pos hε (sp_pos _)
  positivity

theorem eps_sp_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (t : ℝ) : ε * sp (t / ε) ≤ |t| + 1 := by
  have h := sp_le_abs_add_one (t / ε)
  have : |t / ε| = |t| / ε := by rw [abs_div, abs_of_pos hε]
  rw [this] at h
  calc ε * sp (t / ε) ≤ ε * (|t| / ε + 1) := by gcongr
    _ = |t| + ε := by field_simp
    _ ≤ _ := by linarith

theorem qe_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {β : ℝ} (hβ : 0 ≤ β) (t : ℝ) :
    qe ε β t ≤ (|t| + 1) ^ β := by
  unfold qe
  have ha : 0 < ε * sp (t / ε) := mul_pos hε (sp_pos _)
  have hb : 1 ≤ 1 + Real.exp (-t / ε) := by linarith [Real.exp_pos (-t / ε)]
  calc (ε * sp (t / ε)) ^ β / (1 + Real.exp (-t / ε)) ≤ (ε * sp (t / ε)) ^ β := by
        apply div_le_self (by positivity) hb
    _ ≤ _ := Real.rpow_le_rpow ha.le (eps_sp_le hε hε1 t) hβ

theorem qe_le_exp {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {β : ℝ} (hβ : 0 ≤ β) (t : ℝ) :
    qe ε β t ≤ (|t| + 1) ^ β * Real.exp (t / ε) := by
  unfold qe
  have ha : 0 < ε * sp (t / ε) := mul_pos hε (sp_pos _)
  have h1 : (ε * sp (t / ε)) ^ β ≤ (|t| + 1) ^ β := Real.rpow_le_rpow ha.le (eps_sp_le hε hε1 t) hβ
  have h2 : (1 + Real.exp (-t / ε))⁻¹ ≤ Real.exp (t / ε) := by
    have : Real.exp (t / ε) = (Real.exp (-t / ε))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [this]
    exact inv_anti₀ (Real.exp_pos _) (by linarith)
  rw [div_eq_mul_inv]
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

theorem tendsto_div_atTop {t : ℝ} (ht : 0 < t) :
    Tendsto (fun ε : ℝ => t / ε) (𝓝[>] 0) atTop := by
  simpa [div_eq_mul_inv] using
    (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop ht

theorem tendsto_qe_pos {t : ℝ} (ht : 0 < t) (β : ℝ) :
    Tendsto (fun ε => qe ε β t) (𝓝[>] 0) (𝓝 (t ^ β)) := by
  have h1 : Tendsto (fun ε : ℝ => ε * sp (t / ε)) (𝓝[>] 0) (𝓝 t) := by
    have hlow : ∀ᶠ ε in 𝓝[>] (0 : ℝ), t ≤ ε * sp (t / ε) := by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have := le_sp (t / ε)
      calc t = ε * (t / ε) := by field_simp
        _ ≤ _ := by gcongr
    have hup : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * sp (t / ε) ≤ t + ε := by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have := sp_sub_le (div_pos ht hε).le
      calc ε * sp (t / ε) ≤ ε * (t / ε + 1) := by gcongr; linarith
        _ = t + ε := by field_simp
    have hε0 : Tendsto (fun ε : ℝ => t + ε) (𝓝[>] 0) (𝓝 t) := by
      have : Tendsto (fun ε : ℝ => t + ε) (𝓝 0) (𝓝 (t + 0)) := tendsto_const_nhds.add tendsto_id
      simpa using this.mono_left nhdsWithin_le_nhds
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hε0 hlow hup
  have h2 : Tendsto (fun ε : ℝ => 1 + Real.exp (-t / ε)) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun ε : ℝ => Real.exp (-(t / ε))) (𝓝[>] 0) (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_div_atTop ht)
    simpa [neg_div] using (tendsto_const_nhds (x := (1 : ℝ))).add this
  have h3 := (h1.rpow_const (p := β) (Or.inl ht.ne')).div h2 one_ne_zero
  have e : (fun ε : ℝ => qe ε β t) = ((fun a => (a * sp (t / a)) ^ β) / fun ε => 1 + Real.exp (-t / ε)) := rfl
  rw [e]; simpa using h3

theorem tendsto_qe_neg {t : ℝ} (ht : t < 0) {β : ℝ} (hβ : 0 ≤ β) :
    Tendsto (fun ε => qe ε β t) (𝓝[>] 0) (𝓝 0) := by
  have hdiv : Tendsto (fun ε : ℝ => t / ε) (𝓝[>] 0) atBot := by
    have := tendsto_div_atTop (neg_pos.2 ht)
    simpa [neg_div, Function.comp_def] using tendsto_neg_atTop_atBot.comp this
  have hexp : Tendsto (fun ε : ℝ => (|t| + 1) ^ β * Real.exp (t / ε)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hdiv).const_mul ((|t| + 1) ^ β)
  refine squeeze_zero' ?_ ?_ hexp
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) using qe_nonneg hε β t
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
    exact qe_le_exp hε.1 hε.2.le hβ t

end CutoffRigidity.Dyson
