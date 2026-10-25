module

public import CutoffRigidity.Paper.CarrierDefs
public import CutoffRigidity.Paper.ProductCondition
public import CutoffRigidity.Paper.InformationCutoff

/-! # Mixing time of a rigid sequence (manuscript L349, L387-393)

Under the hypotheses of Corollary 1.4, the total variation mixing time from the balls
`B(m, c√n)` is `(log n/(2λ₁))(1+o(1))`, and the product condition `λ₁ t_mix → ∞` holds
together with `t_mix → ∞`.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology Asymptotics

universe u

/-- **Mixing time of rigid sequences** (introduction, after Corollary 1.6, and Section
"Product condition"): under the hypotheses of Corollary 1.4 and for every `η ∈ (0,1)`, the total
variation mixing time `t₀⁽ⁿ⁾` from the balls `B(m, c√n)` is finite for large `n` and is
`(log n/(2λ₁))(1+o(1))`; moreover `λ₁⁽ⁿ⁾ t₀⁽ⁿ⁾ → ∞` (so the product condition of Theorem 1.7
holds) and `t₀⁽ⁿ⁾ → ∞`. -/
theorem mixing_time_rigid_carrier {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    {V : ∀ n, CutCur.Rd n → ℝ} {B : ∀ n, ℝ≥0 → Ω n → CutCur.Rd n} {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, CutCur.Rd n → ℝ≥0 → Ω n → CutCur.Rd n}
    (h : CutCur.IsRigidSequence V B P X)
    (hsmall : (fun n => CutCur.spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n))
    {c : ℝ} (hc : 0 < c) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    let t₀ := fun n => CutCur.mixingTime (P n) (X n) (CutCur.gibbs (V n))
      (CutCur.meanBall (V n) c) η
    (∀ᶠ n in atTop, t₀ n < ⊤) ∧
      Tendsto (fun n => (t₀ n).toReal / CutCur.criticalTime n (CutCur.spectralGap (V n)))
        atTop (𝓝 1) ∧
      Tendsto (fun n => CutCur.spectralGap (V n) * (t₀ n).toReal) atTop atTop ∧
      Tendsto (fun n => (t₀ n).toReal) atTop atTop := by
  intro t₀
  have hinfo := information_cutoff_carrier h hsmall hc
  have hTV := hinfo.2.2
  obtain ⟨Ω', _, D, hD, -⟩ := exists_seqData_rigid h
  have hev : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  let C : ∀ n : ℕ, CurvedLangevinData Ω' n := fun n =>
    { potential := (D n).potential, smooth := (D n).smooth, probability := (D n).probability,
      driver := (D n).driver, noiseLaw := (D n).noiseLaw, brownian := (D n).brownian,
      curvature := (D n).rate, curvature_pos := (D n).rate_pos, hessian := (D n).hessian }
  let S : ∀ n : ℕ, Set (CutCur.Rd n) := fun n => CutCur.meanBall (V n) c
  have hSne : ∀ n, (S n).Nonempty := fun n =>
    ⟨_, Metric.mem_closedBall_self (mul_nonneg hc.le (Real.sqrt_nonneg _))⟩
  have hpot : ∀ n, 0 < n → (C n).potential = V n := fun n hn => (hD n hn).2.1
  have hk : ∀ n, 0 < n → ∀ (s : ℝ≥0) (x : CutCur.Rd n),
      langevinKernel (C n).potential (C n).driver (C n).noiseLaw s x = (P n).map (X n x s) :=
    fun n hn s x => (hD n hn).2.2 s x
  have hgap : ∀ n, 0 < n → 0 < CutCur.spectralGap (V n) := fun n hn => by
    rw [← (hD n hn).1]; exact (D n).rate_pos
  have hmix : ∀ n, 0 < n → t₀ n = curvedMixingTime (C n) (S n) η := fun n hn => by
    have := mixingTime_eq_curved (C n) (hSne n) (hk n hn) hη.le
    rw [hpot n hn] at this
    exact this
  -- the TV profile of the statement surface is the curved TV profile
  have hprof : ∀ n, 0 < n → ∀ s : ℝ, CutCur.worst (P n) (X n) (S n)
      (fun ν => ENNReal.ofReal (CutCur.tvDist ν (CutCur.gibbs (V n)))) s =
        ENNReal.ofReal (curvedTVProfile (C n) (S n) s) := fun n hn s => by
    have := worst_tv_curved (C n) (hSne n) (hk n hn) s
    rw [hpot n hn] at this
    exact this
  set t : ℕ → ℝ := fun n => CutCur.criticalTime n (CutCur.spectralGap (V n)) with ht
  have htpos : ∀ᶠ n : ℕ in atTop, 0 < t n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have h1 : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast hn)
    have := hgap n (by omega)
    simp only [ht, CutCur.criticalTime]
    positivity
  -- real-valued limits of the curved profile
  have hreal : ∀ ε : ℝ, 0 < ε → ε < 1 →
      Tendsto (fun n => curvedTVProfile (C n) (S n) ((1 - ε) * t n)) atTop (𝓝 1) ∧
      Tendsto (fun n => curvedTVProfile (C n) (S n) ((1 + ε) * t n)) atTop (𝓝 0) := by
    intro ε h0 h1
    obtain ⟨hb, ha⟩ := hTV ε h0 h1
    have conv : ∀ {a : ℝ} {u : ℕ → ℝ}, (∀ᶠ n in atTop, 0 ≤ u n) →
        Tendsto (fun n => ENNReal.ofReal (u n)) atTop (𝓝 (ENNReal.ofReal a)) → 0 ≤ a →
        Tendsto u atTop (𝓝 a) := by
      intro a u hu hlim ha0
      have := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hlim
      rw [ENNReal.toReal_ofReal ha0] at this
      refine this.congr' ?_
      filter_upwards [hu] with n hn
      simp [Function.comp, ENNReal.toReal_ofReal hn]
    have hnn : ∀ s : ℕ → ℝ, ∀ᶠ n in atTop, 0 ≤ curvedTVProfile (C n) (S n) (s n) := by
      intro s
      filter_upwards with n
      exact curvedTVProfile_nonneg (C n) (hSne n) _
    refine ⟨conv (hnn _) ?_ zero_le_one, conv (hnn _) ?_ le_rfl⟩
    · rw [ENNReal.ofReal_one]
      refine hb.congr' ?_
      filter_upwards [hev] with n hn using hprof n hn _
    · rw [ENNReal.ofReal_zero]
      refine ha.congr' ?_
      filter_upwards [hev] with n hn using hprof n hn _
  -- two-sided bound on the mixing time
  have hsandwich : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n in atTop,
      t₀ n < ⊤ ∧ (1 - ε) * t n ≤ (t₀ n).toReal ∧ (t₀ n).toReal ≤ (1 + ε) * t n := by
    intro ε h0 h1
    obtain ⟨hb, ha⟩ := hreal ε h0 h1
    have hb' : ∀ᶠ n in atTop, η < curvedTVProfile (C n) (S n) ((1 - ε) * t n) :=
      hb.eventually (lt_mem_nhds hη1)
    have ha' : ∀ᶠ n in atTop, curvedTVProfile (C n) (S n) ((1 + ε) * t n) ≤ η :=
      ha.eventually (ge_mem_nhds hη)
    filter_upwards [hb', ha', htpos, hev] with n hbn han htn hn
    have hupper : curvedMixingTime (C n) (S n) η ≤ (((1 + ε) * t n).toNNReal : ℝ≥0∞) := by
      refine kernelTVMixingTime_le_of_profile_le _ _ _ _ _ ?_
      exact han
    have hfin : curvedMixingTime (C n) (S n) η ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top hupper
    have hnn : 0 ≤ (1 + ε) * t n := by positivity
    refine ⟨by rw [hmix n hn]; exact lt_top_iff_ne_top.mpr hfin, ?_, ?_⟩
    · rw [hmix n hn]
      by_contra hlt
      replace hlt := not_le.mp hlt
      have := curvedTVProfile_le_after_mixing (C n) (S n) (hSne n) η _ hfin hlt
      exact absurd hbn (not_lt.mpr this)
    · rw [hmix n hn]
      have := ENNReal.toReal_mono ENNReal.coe_ne_top hupper
      simpa [Real.coe_toNNReal _ hnn] using this
  have hfinal : ∀ᶠ n in atTop, t₀ n < ⊤ := by
    filter_upwards [hsandwich (1/2) (by norm_num) (by norm_num)] with n hn using hn.1
  have hratio : Tendsto (fun n => (t₀ n).toReal / t n) atTop (𝓝 1) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      have hε : 0 < min ((1 - a) / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
      have hε1 : min ((1 - a) / 2) (1 / 2) < 1 :=
        lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      filter_upwards [hsandwich _ hε hε1, htpos] with n hn htn
      rw [lt_div_iff₀ htn]
      have := hn.2.1
      have hm : min ((1 - a) / 2) (1 / 2) ≤ (1 - a) / 2 := min_le_left _ _
      nlinarith
    · intro b hb
      have hε : 0 < min ((b - 1) / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
      have hε1 : min ((b - 1) / 2) (1 / 2) < 1 :=
        lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      filter_upwards [hsandwich _ hε hε1, htpos] with n hn htn
      rw [div_lt_iff₀ htn]
      have := hn.2.2
      have hm : min ((b - 1) / 2) (1 / 2) ≤ (b - 1) / 2 := min_le_left _ _
      nlinarith
  refine ⟨hfinal, hratio, ?_, ?_⟩
  · -- λ t₀ = (log n / 2) * (t₀ / t)
    have hlog : Tendsto (fun n : ℕ => Real.log n / 2) atTop atTop :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
    have := hlog.atTop_mul_pos one_pos hratio
    refine this.congr' ?_
    filter_upwards [htpos, eventually_ge_atTop 2] with n htn hn
    have := hgap n (by omega)
    have hl : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast hn)
    simp only [ht, CutCur.criticalTime] at htn ⊢
    field_simp
  · have htinf : Tendsto t atTop atTop := by
      have h1 : Tendsto (fun n : ℕ => CutCur.spectralGap (V n) / Real.log n) atTop (𝓝 0) :=
        hsmall.tendsto_div_nhds_zero
      have h2 : Tendsto (fun n : ℕ => CutCur.spectralGap (V n) / Real.log n) atTop (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨h1, ?_⟩
        filter_upwards [eventually_ge_atTop 2] with n hn
        have := hgap n (by omega)
        have hl : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast hn)
        exact div_pos this hl
      have h3 := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).comp h2
      have h4 := h3.atTop_div_const (r := 2) (by norm_num)
      refine h4.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with n hn
      have := hgap n (by omega)
      have hl : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast hn)
      simp only [ht, CutCur.criticalTime, Function.comp]
      field_simp
    have := htinf.atTop_mul_pos one_pos hratio
    refine this.congr' ?_
    filter_upwards [htpos] with n htn
    field_simp

end CutoffRigidity.Paper
