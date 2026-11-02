module

public import CutoffRigidity.Extra.GaussIso16

/-! # Isoperimetry for sets (stage 7d): the comparison argument

`n : ℝ → ℝ` nondecreasing, right-continuous, `n ≤ 1`, satisfying the finite-increment inequality (FS) derived
from Bobkov's inequality, with `Φ(a) ≤ n(0)`. Then `Φ(a + c r) ≤ n(r)` for `r ≥ 0`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal

set_option linter.unusedSectionVars false

namespace CutoffRigidity.GaussIso

/-- Local extension step of the comparison argument. -/
lemma comparison_local {n : ℝ → ℝ} (hmono : Monotone n) (hrc : ∀ r, ContinuousWithinAt n (Ici r) r)
    {c : ℝ} (hc : 0 < c) {a : ℝ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hFS : ∀ r, 0 ≤ r → ∀ s, 0 < s → ∀ η, 0 < η → ∃ N, n r ≤ N ∧ N ≤ n (r + s) ∧
      gI N ≤ (gφ 0 + c⁻¹ * (1 + η) / s) * (n (r + s) - n r))
    {t : ℝ} (ht : 0 ≤ t) (hwt : gΦ (a + c * (1 - ε) * t) ≤ n t) :
    ∃ δ > 0, ∀ s, 0 < s → s < δ → gΦ (a + c * (1 - ε) * (t + s)) ≤ n (t + s) := by
  set lam : ℝ := c * (1 - ε) with hlam
  have hlam0 : 0 < lam := by positivity [sub_pos.2 hε1]
  set w : ℝ → ℝ := fun u => gΦ (a + lam * u) with hw
  have hwd : ∀ u, HasDerivAt w (gφ (a + lam * u) * lam) u := fun u => by
    have h1 : HasDerivAt (fun u : ℝ => a + lam * u) lam u := by
      simpa using ((hasDerivAt_id u).const_mul lam).const_add a
    exact (hasDerivAt_gΦ (a + lam * u)).comp u h1
  rcases lt_or_eq_of_le hwt with hlt | heq
  · -- strict: continuity of w
    have hcont : ContinuousAt w t := (hwd t).continuousAt
    have : ∀ᶠ u in 𝓝 t, w u < n t := hcont.eventually (gt_mem_nhds hlt)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 this
    refine ⟨δ, hδ, fun s hs hsδ => ?_⟩
    have := hδ' (y := t + s) (by rw [Real.dist_eq]; simp [abs_of_pos hs, hsδ])
    exact (this.le).trans (hmono (by linarith))
  · -- equality case
    set m : ℝ := n t with hm
    have hwt' : gΦ (a + lam * t) = m := heq
    have hm01 : m ∈ Ioo (0:ℝ) 1 := by rw [← hwt']; exact gΦ_mem _
    set xs : ℝ := a + lam * t with hxs
    have hφs : 0 < gφ xs := gφ_pos _
    have hη : 0 < ε / 2 := by positivity
    have hFSt : ∀ s, 0 < s → ∃ N, n t ≤ N ∧ N ≤ n (t + s) ∧
        gI N ≤ (gφ 0 + c⁻¹ * (1 + ε / 2) / s) * (n (t + s) - n t) := fun s hs => hFS t ht s hs (ε / 2) hη
    choose! N hN using hFSt
    -- n (t + s) → m as s → 0+
    have hnlim : Tendsto (fun s => n (t + s)) (𝓝[>] 0) (𝓝 m) := by
      have h1 : Tendsto (fun s : ℝ => t + s) (𝓝[>] 0) (𝓝[Ici t] t) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have : Tendsto (fun s : ℝ => t + s) (𝓝 0) (𝓝 (t + 0)) := (continuous_const.add continuous_id).tendsto 0
          simpa using this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs using le_add_of_nonneg_right (le_of_lt hs)
      exact (hrc t).tendsto.comp h1
    have hNlim : Tendsto N (𝓝[>] 0) (𝓝 m) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hnlim ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with s hs using (hN s hs).1
      · filter_upwards [self_mem_nhdsWithin] with s hs using (hN s hs).2.1
    have hgIlim : Tendsto (fun s => gI (N s)) (𝓝[>] 0) (𝓝 (gφ xs)) := by
      have h1 : Tendsto gI (𝓝 m) (𝓝 (gI m)) := (hasDerivAt_gI hm01).continuousAt.tendsto
      have e : gI m = gφ xs := by
        rw [gI_of_mem hm01, ← hwt', gQ_gΦ]
      rw [← e]
      exact h1.comp hNlim
    set η : ℝ := ε / 2 with hη'
    have hRlim : Tendsto (fun s => gI (N s) / (gφ 0 * s + c⁻¹ * (1 + η))) (𝓝[>] 0)
        (𝓝 (gφ xs / (c⁻¹ * (1 + η)))) := by
      have hden : Tendsto (fun s : ℝ => gφ 0 * s + c⁻¹ * (1 + η)) (𝓝[>] 0) (𝓝 (gφ 0 * 0 + c⁻¹ * (1 + η))) :=
        ((continuous_const.mul continuous_id).add continuous_const).tendsto 0 |>.mono_left nhdsWithin_le_nhds
      have hne : (gφ 0 * 0 + c⁻¹ * (1 + η)) ≠ 0 := by
        have : 0 < c⁻¹ * (1 + η) := by positivity
        simpa using this.ne'
      have := hgIlim.div hden hne
      rw [mul_zero, zero_add] at this
      exact this
    have hslope : Tendsto (fun s : ℝ => s⁻¹ • (w (t + s) - w t)) (𝓝[>] 0) (𝓝 (gφ xs * lam)) :=
      (hwd t).tendsto_slope_zero_right
    have hlt : gφ xs * lam < gφ xs / (c⁻¹ * (1 + η)) := by
      have e : gφ xs / (c⁻¹ * (1 + η)) = gφ xs * c / (1 + η) := by field_simp
      rw [e, hlam, lt_div_iff₀ (by positivity)]
      have : (1 - ε) * (1 + η) < 1 := by
        rw [hη']; nlinarith
      nlinarith [mul_pos hφs hc]
    have hev := (hslope.eventually_lt hRlim hlt)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    refine ⟨u, hu, fun s hs hsu => ?_⟩
    have hs' := hsub ⟨hs, hsu⟩
    simp only [mem_setOf_eq, smul_eq_mul] at hs'
    have h1 := (hN s hs)
    have hden : 0 < gφ 0 * s + c⁻¹ * (1 + η) := by
      have := gφ_pos 0; positivity
    have h2 : s * (gI (N s) / (gφ 0 * s + c⁻¹ * (1 + η))) ≤ n (t + s) - n t := by
      rw [mul_div_assoc', div_le_iff₀ hden]
      have := h1.2.2
      have e : (gφ 0 + c⁻¹ * (1 + η) / s) = (gφ 0 * s + c⁻¹ * (1 + η)) / s := by field_simp
      rw [e] at this
      calc s * gI (N s) ≤ s * (((gφ 0 * s + c⁻¹ * (1 + η)) / s) * (n (t + s) - n t)) :=
            mul_le_mul_of_nonneg_left this hs.le
        _ = (n (t + s) - n t) * (gφ 0 * s + c⁻¹ * (1 + η)) := by field_simp
    have h3 : w (t + s) - w t < s * (gI (N s) / (gφ 0 * s + c⁻¹ * (1 + η))) := by
      have := (inv_mul_lt_iff₀ hs).1 hs'
      linarith
    have : w (t + s) < n (t + s) := by
      have : w t = n t := heq
      linarith
    exact this.le


/-- **Comparison principle** (real induction). -/
theorem comparison {n : ℝ → ℝ} (hmono : Monotone n) (hrc : ∀ r, ContinuousWithinAt n (Ici r) r)
    {c : ℝ} (hc : 0 < c) {a : ℝ} (h0 : gΦ a ≤ n 0)
    (hFS : ∀ r, 0 ≤ r → ∀ s, 0 < s → ∀ η, 0 < η → ∃ N, n r ≤ N ∧ N ≤ n (r + s) ∧
      gI N ≤ (gφ 0 + c⁻¹ * (1 + η) / s) * (n (r + s) - n r)) :
    ∀ r, 0 ≤ r → gΦ (a + c * r) ≤ n r := by
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t, 0 ≤ t → gΦ (a + c * (1 - ε) * t) ≤ n t := by
    intro ε hε0 hε1
    by_contra hcon
    simp only [not_forall, not_le] at hcon
    obtain ⟨t1, ht1, hbad⟩ := hcon
    let P : ℝ → Prop := fun t => gΦ (a + c * (1 - ε) * t) ≤ n t
    let S : Set ℝ := {t | 0 ≤ t ∧ ∀ t' ∈ Icc 0 t, P t'}
    have hP0 : P 0 := by simpa [P] using h0
    have h0S : (0:ℝ) ∈ S := ⟨le_rfl, fun t' ht' => by
      have : t' = 0 := le_antisymm ht'.2 ht'.1
      rw [this]; exact hP0⟩
    have hbdd : BddAbove S := ⟨t1, fun t ht => by
      by_contra hlt
      rw [not_le] at hlt
      exact absurd (ht.2 t1 ⟨ht1, hlt.le⟩) (not_le.2 hbad)⟩
    set ts := sSup S with hts
    have hts0 : 0 ≤ ts := le_csSup hbdd h0S
    have hPlt : ∀ t', 0 ≤ t' → t' < ts → P t' := by
      intro t' ht' hlt
      obtain ⟨t, htS, htt⟩ := (lt_csSup_iff hbdd ⟨0, h0S⟩).1 hlt
      exact htS.2 t' ⟨ht', htt.le⟩
    have hPts : P ts := by
      rcases hts0.eq_or_lt with h | h
      · rw [← h]; exact hP0
      · have hcont : Tendsto (fun u => gΦ (a + c * (1 - ε) * u)) (𝓝[<] ts) (𝓝 (gΦ (a + c * (1 - ε) * ts))) :=
          (continuous_gΦ.comp (by fun_prop : Continuous fun u : ℝ => a + c * (1 - ε) * u)).continuousAt.tendsto.mono_left
            nhdsWithin_le_nhds
        refine le_of_tendsto hcont ?_
        filter_upwards [Ioo_mem_nhdsLT h] with u hu
        exact (hPlt u hu.1.le hu.2).trans (hmono hu.2.le)
    obtain ⟨δ, hδ, hloc⟩ := comparison_local hmono hrc hc hε0 hε1 hFS hts0 hPts
    have hin : ts + δ / 2 ∈ S := by
      refine ⟨by linarith, fun t' ht' => ?_⟩
      rcases le_or_gt t' ts with h | h
      · rcases h.eq_or_lt with h' | h'
        · rw [h']; exact hPts
        · exact hPlt t' ht'.1 h'
      · have := hloc (t' - ts) (by linarith) (by linarith [ht'.2])
        simpa [P] using this
    have := le_csSup hbdd hin
    linarith
  intro r hr
  have hlim : Tendsto (fun ε : ℝ => gΦ (a + c * (1 - ε) * r)) (𝓝[>] 0) (𝓝 (gΦ (a + c * r))) := by
    have : Continuous fun ε : ℝ => gΦ (a + c * (1 - ε) * r) :=
      continuous_gΦ.comp (by fun_prop)
    have h := this.tendsto 0
    simp only [sub_zero, mul_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
  exact key ε hε.1 hε.2 r hr

end CutoffRigidity.GaussIso
