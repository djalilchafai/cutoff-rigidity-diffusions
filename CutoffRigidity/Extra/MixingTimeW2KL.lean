module

public import CutoffRigidity.Statements
public import CutoffRigidity.Extra.MixingTime
public import CutoffRigidity.Extra.Dynamics
public import CutoffRigidity.Paper.WassersteinCutoff
public import CutoffRigidity.Paper.InformationCutoff

/-! # Wasserstein and entropy mixing times of a rigid sequence (manuscript L349)

For rigid curved diffusions the mixing times in Wasserstein distance and in relative entropy from
the balls `B(m, c√n)` are `(log n/(2λ₁))(1+o(1))`, for every threshold `η > 0`. The definitions
`CutCur.mixingTimeW2`, `CutCur.mixingTimeKL` are defined in `Challenge.lean`.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped ENNReal NNReal Topology Asymptotics

namespace CutoffRigidity.Paper

/-- generic mixing time of a profile `f : ℝ≥0 → ℝ≥0∞` -/
noncomputable def profileMixing (f : ℝ≥0 → ℝ≥0∞) (η : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (u : ℝ≥0) (_ : f u ≤ η), (u : ℝ≥0∞)

theorem profileMixing_le {f : ℝ≥0 → ℝ≥0∞} {η : ℝ≥0∞} {u : ℝ≥0} (h : f u ≤ η) :
    profileMixing f η ≤ u := iInf₂_le u h

theorem le_profileMixing {f : ℝ≥0 → ℝ≥0∞} (hf : Antitone f) {η : ℝ≥0∞} {u : ℝ≥0} (h : η < f u) :
    (u : ℝ≥0∞) ≤ profileMixing f η := by
  refine le_iInf₂ fun v hv => ?_
  by_contra hlt
  have : v ≤ u := by exact_mod_cast (not_le.mp hlt).le
  exact absurd (hf this |>.trans hv) (not_le.mpr h)

theorem mixing_ratio_of_cutoff {f : ℕ → ℝ≥0 → ℝ≥0∞} (hanti : ∀ᶠ n in atTop, Antitone (f n))
    {t : ℕ → ℝ} (htpos : ∀ᶠ n in atTop, 0 < t n) {η : ℝ≥0∞} (hη0 : 0 < η) (hηtop : η ≠ ⊤)
    (hcut : ∀ ε : ℝ, 0 < ε → ε < 1 →
      Tendsto (fun n => f n (((1 - ε) * t n).toNNReal)) atTop (𝓝 ⊤) ∧
      Tendsto (fun n => f n (((1 + ε) * t n).toNNReal)) atTop (𝓝 0)) :
    (∀ᶠ n in atTop, profileMixing (f n) η < ⊤) ∧
      Tendsto (fun n => (profileMixing (f n) η).toReal / t n) atTop (𝓝 1) := by
  have hsandwich : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n in atTop,
      profileMixing (f n) η < ⊤ ∧ (1 - ε) * t n ≤ (profileMixing (f n) η).toReal ∧
        (profileMixing (f n) η).toReal ≤ (1 + ε) * t n := by
    intro ε h0 h1
    obtain ⟨hb, ha⟩ := hcut ε h0 h1
    have hb' := hb.eventually (lt_mem_nhds (lt_top_iff_ne_top.mpr hηtop))
    have ha' := ha.eventually (ge_mem_nhds hη0)
    filter_upwards [hb', ha', htpos, hanti] with n hbn han htn hant
    have hupper : profileMixing (f n) η ≤ (((1 + ε) * t n).toNNReal : ℝ≥0∞) :=
      profileMixing_le han
    have hfin : profileMixing (f n) η ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hupper
    have hnn : 0 ≤ (1 + ε) * t n := by positivity
    refine ⟨lt_top_iff_ne_top.mpr hfin, ?_, ?_⟩
    · have hlow := le_profileMixing hant hbn
      have := ENNReal.toReal_mono hfin hlow
      have hnn' : 0 ≤ (1 - ε) * t n := mul_nonneg (by linarith) htn.le
      simpa [Real.coe_toNNReal _ hnn'] using this
    · have := ENNReal.toReal_mono ENNReal.coe_ne_top hupper
      simpa [Real.coe_toNNReal _ hnn] using this
  refine ⟨?_, ?_⟩
  · filter_upwards [hsandwich (1/2) (by norm_num) (by norm_num)] with n hn using hn.1
  · rw [tendsto_order]
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

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- worst-case KL profile is nonincreasing in time -/
theorem worst_klDiv_antitone {V : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω}
    {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d} (hL : CutCur.IsLangevin V B P X) (hd : 0 < d)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (S : Set (CutCur.Rd d)) :
    Antitone (fun u : ℝ≥0 => CutCur.worst P X S (fun ν => klDiv ν (CutCur.gibbs V)) (u : ℝ)) := by
  intro u u' h
  simp only [CutCur.worst, Real.toNNReal_coe]
  refine iSup₂_mono fun x hx => ?_
  have hB := isStdBrownian_iff.mp hL.2.2.1
  have hp : IsProbabilityMeasure (gibbsMeasure volume V) := hL.2.1
  have hk := fun t => IsLangevin.map_eq_langevinKernel hL ρ hρ.le hHess x t
  have := langevinKernel_entropy_contraction_add hB hL.1 hp hd ρ hρ hHess (Measure.dirac x) u (u' - u)
  rw [add_tsub_cancel_of_le h] at this
  have e1 : ∀ s, langevinKernel V B P s ∘ₘ Measure.dirac x = P.map (X x s) := fun s => by
    exact (law_bind_eq_comp hL hρ.le hHess (Measure.dirac x) s).symm.trans
      (law_bind_dirac hL hρ.le hHess x s)
  rw [e1, e1] at this
  exact this.trans (by
    calc _ ≤ 1 * _ := mul_le_mul' (ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (by
            have := NNReal.coe_nonneg (u' - u); nlinarith))) le_rfl
      _ = _ := one_mul _)

/-- worst-case W2 profile is nonincreasing in time -/
theorem worst_w2_antitone {V : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω}
    {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d} (hL : CutCur.IsLangevin V B P X)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (S : Set (CutCur.Rd d)) :
    Antitone (fun u : ℝ≥0 => CutCur.worst P X S (fun ν => CutCur.wasserstein2 ν (CutCur.gibbs V)) (u : ℝ)) := by
  intro u u' h
  simp only [CutCur.worst, Real.toNNReal_coe]
  refine iSup₂_mono fun x hx => ?_
  have hB := isStdBrownian_iff.mp hL.2.2.1
  have hp : IsProbabilityMeasure (gibbsMeasure volume V) := hL.2.1
  have hmk : ∀ t : ℝ≥0, IsMarkovKernel (langevinKernel V B P t) := fun t =>
    langevinKernel_isMarkovKernel hB hL.1 ρ hρ.le hHess t
  have hg : IsProbabilityMeasure (CutCur.gibbs V) := hp
  have hu : IsProbabilityMeasure (P.map (X x u)) := by
    rw [IsLangevin.map_eq_langevinKernel hL ρ hρ.le hHess x u]; exact (hmk u).isProbabilityMeasure x
  have hs := langevin_w2_contraction hL hρ.le hHess (P.map (X x u)) (CutCur.gibbs V) (u' - u)
  have hinv : (CutCur.gibbs V).bind (fun y => P.map (X y (u' - u))) = CutCur.gibbs V := by
    rw [law_bind_eq_comp hL hρ.le hHess]
    exact langevinKernel_gibbs_invariant hB hL.1 hp ρ hρ hHess (u' - u)
  have hchain : (P.map (X x u)).bind (fun y => P.map (X y (u' - u))) = P.map (X x u') := by
    rw [law_bind_eq_comp hL hρ.le hHess, IsLangevin.map_eq_langevinKernel hL ρ hρ.le hHess x u,
      IsLangevin.map_eq_langevinKernel hL ρ hρ.le hHess x u', ← Kernel.comp_apply,
      langevinKernel_comp hB hL.1 ρ hρ.le hHess u (u' - u), add_tsub_cancel_of_le h]
  rw [hinv, hchain] at hs
  refine hs.trans ?_
  calc _ ≤ 1 * _ := mul_le_mul' (ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (by
            have := NNReal.coe_nonneg (u' - u); nlinarith))) le_rfl
      _ = _ := one_mul _

end CutoffRigidity.Paper

namespace CutoffRigidity.Paper

universe u

/-- Common tail: from the ratio limit to the product condition and divergence. -/
theorem mixing_tail {V : ∀ n, CutCur.Rd n → ℝ} {t₀ : ℕ → ℝ≥0∞}
    (hgap : ∀ n, 0 < n → 0 < CutCur.spectralGap (V n))
    (hratio : Tendsto (fun n => (t₀ n).toReal / CutCur.criticalTime n (CutCur.spectralGap (V n)))
      atTop (𝓝 1)) :
    Tendsto (fun n => CutCur.spectralGap (V n) * (t₀ n).toReal) atTop atTop ∧
    ((fun n => CutCur.spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n) →
      Tendsto (fun n => (t₀ n).toReal) atTop atTop) := by
  set t : ℕ → ℝ := fun n => CutCur.criticalTime n (CutCur.spectralGap (V n)) with ht
  change Tendsto (fun n => (t₀ n).toReal / t n) atTop (𝓝 1) at hratio
  have htpos : ∀ᶠ n : ℕ in atTop, 0 < t n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have h1 : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast hn)
    have := hgap n (by omega)
    simp only [ht, CutCur.criticalTime]
    positivity
  refine ⟨?_, fun hsmall => ?_⟩
  · have hlog : Tendsto (fun n : ℕ => Real.log n / 2) atTop atTop :=
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

/-- **Wasserstein mixing time of rigid sequences** (manuscript L349, Corollary 1.3): for every
`η > 0`, the Wasserstein mixing time `t₀⁽ⁿ⁾` from the balls `B(m, c√n)` is finite for large `n` and
is `(log n/(2λ₁))(1+o(1))`; moreover `λ₁⁽ⁿ⁾ t₀⁽ⁿ⁾ → ∞`, and `t₀⁽ⁿ⁾ → ∞` when
`λ₁⁽ⁿ⁾ = o(log n)`. -/
theorem mixing_time_w2_rigid {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    {V : ∀ n, CutCur.Rd n → ℝ} {B : ∀ n, ℝ≥0 → Ω n → CutCur.Rd n} {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, CutCur.Rd n → ℝ≥0 → Ω n → CutCur.Rd n}
    (h : CutCur.IsRigidSequence V B P X) {c : ℝ} (hc : 0 < c) {η : ℝ} (hη : 0 < η) :
    let t₀ := fun n => CutCur.mixingTimeW2 (P n) (X n) (CutCur.gibbs (V n))
      (CutCur.meanBall (V n) c) η
    (∀ᶠ n in atTop, t₀ n < ⊤) ∧
      Tendsto (fun n => (t₀ n).toReal / CutCur.criticalTime n (CutCur.spectralGap (V n)))
        atTop (𝓝 1) ∧
      Tendsto (fun n => CutCur.spectralGap (V n) * (t₀ n).toReal) atTop atTop ∧
      ((fun n => CutCur.spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n) →
        Tendsto (fun n => (t₀ n).toReal) atTop atTop) := by
  intro t₀
  have hcut := wasserstein_cutoff h hc
  have hgap : ∀ n, 0 < n → 0 < CutCur.spectralGap (V n) := fun n hn => (h.1 n hn).2.1
  have htpos : ∀ᶠ n in atTop, 0 < CutCur.criticalTime n (CutCur.spectralGap (V n)) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have h1 : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast hn)
    have := hgap n (by omega)
    unfold CutCur.criticalTime; positivity
  have hmono : ∀ᶠ n in atTop, Antitone (fun u : ℝ≥0 => CutCur.worst (P n) (X n)
      (CutCur.meanBall (V n) c) (fun ν => CutCur.wasserstein2 ν (CutCur.gibbs (V n))) (u : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact worst_w2_antitone (h.1 n hn).1 (hgap n hn) (fun x z => (h.1 n hn).2.2 x z)
      (CutCur.meanBall (V n) c)
  have key := mixing_ratio_of_cutoff (f := fun n u => CutCur.worst (P n) (X n)
      (CutCur.meanBall (V n) c) (fun ν => CutCur.wasserstein2 ν (CutCur.gibbs (V n))) (u : ℝ))
      hmono htpos (η := ENNReal.ofReal η) (by simpa using hη) ENNReal.ofReal_ne_top (by
    intro ε h0 h1
    obtain ⟨hb, ha⟩ := hcut ε h0 h1
    constructor
    · refine hb.congr' ?_
      filter_upwards [htpos] with n hn
      rw [Real.coe_toNNReal _ (by nlinarith)]
    · refine ha.congr' ?_
      filter_upwards [htpos] with n hn
      rw [Real.coe_toNNReal _ (by nlinarith)])
  have tail := mixing_tail (t₀ := t₀) hgap key.2
  exact ⟨key.1, key.2, tail.1, tail.2⟩

/-- **Entropy mixing time of rigid sequences** (manuscript L349, Corollary 1.4): under the
hypotheses of Corollary 1.4 and for every `η > 0`, the relative entropy mixing time `t₀⁽ⁿ⁾` from
the balls `B(m, c√n)` is finite for large `n` and is `(log n/(2λ₁))(1+o(1))`; moreover
`λ₁⁽ⁿ⁾ t₀⁽ⁿ⁾ → ∞` and `t₀⁽ⁿ⁾ → ∞`. -/
theorem mixing_time_kl_rigid {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    {V : ∀ n, CutCur.Rd n → ℝ} {B : ∀ n, ℝ≥0 → Ω n → CutCur.Rd n} {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, CutCur.Rd n → ℝ≥0 → Ω n → CutCur.Rd n}
    (h : CutCur.IsRigidSequence V B P X)
    (hsmall : (fun n => CutCur.spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n))
    {c : ℝ} (hc : 0 < c) {η : ℝ} (hη : 0 < η) :
    let t₀ := fun n => CutCur.mixingTimeKL (P n) (X n) (CutCur.gibbs (V n))
      (CutCur.meanBall (V n) c) η
    (∀ᶠ n in atTop, t₀ n < ⊤) ∧
      Tendsto (fun n => (t₀ n).toReal / CutCur.criticalTime n (CutCur.spectralGap (V n)))
        atTop (𝓝 1) ∧
      Tendsto (fun n => CutCur.spectralGap (V n) * (t₀ n).toReal) atTop atTop ∧
      Tendsto (fun n => (t₀ n).toReal) atTop atTop := by
  intro t₀
  have hcut := (information_cutoff h hsmall hc).2.1
  have hgap : ∀ n, 0 < n → 0 < CutCur.spectralGap (V n) := fun n hn => (h.1 n hn).2.1
  have htpos : ∀ᶠ n in atTop, 0 < CutCur.criticalTime n (CutCur.spectralGap (V n)) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have h1 : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast hn)
    have := hgap n (by omega)
    unfold CutCur.criticalTime; positivity
  have hmono : ∀ᶠ n in atTop, Antitone (fun u : ℝ≥0 => CutCur.worst (P n) (X n)
      (CutCur.meanBall (V n) c) (fun ν => InformationTheory.klDiv ν (CutCur.gibbs (V n))) (u : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact worst_klDiv_antitone (h.1 n hn).1 hn (hgap n hn) (fun x z => (h.1 n hn).2.2 x z)
      (CutCur.meanBall (V n) c)
  have key := mixing_ratio_of_cutoff (f := fun n u => CutCur.worst (P n) (X n)
      (CutCur.meanBall (V n) c) (fun ν => InformationTheory.klDiv ν (CutCur.gibbs (V n))) (u : ℝ))
      hmono htpos (η := ENNReal.ofReal η) (by simpa using hη) ENNReal.ofReal_ne_top (by
    intro ε h0 h1
    obtain ⟨hb, ha⟩ := hcut ε h0 h1
    constructor
    · refine hb.congr' ?_
      filter_upwards [htpos] with n hn
      rw [Real.coe_toNNReal _ (by nlinarith)]
    · refine ha.congr' ?_
      filter_upwards [htpos] with n hn
      rw [Real.coe_toNNReal _ (by nlinarith)])
  have tail := mixing_tail (t₀ := t₀) hgap key.2
  exact ⟨key.1, key.2, tail.1, tail.2 hsmall⟩

end CutoffRigidity.Paper

