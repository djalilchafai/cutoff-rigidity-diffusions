module

public import CutoffRigidity.Riemann.DiffKuwada1

/-! # Interpolation along a `C^1` curve: the Dini step -/

@[expose] public section

open Bundle MeasureTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Pure

theorem young_aux {c g0 v S ρ0 K κ : ℝ} (hK : 0 < K) (hκ : 0 < κ) (hv : 0 ≤ v) (hS : 0 ≤ S)
    (hg : 0 ≤ g0) (h4 : g0 ^ 2 ≤ c ^ 2 * S) (hρ : ρ0 * (2 * K) = v + κ) :
    g0 * v - ρ0 / 2 * S ≤ c ^ 2 * K * v := by
  have hρpos : 0 < ρ0 := by
    have : 0 < ρ0 * (2 * K) := by rw [hρ]; linarith
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith
  rcases eq_or_ne c 0 with h | h
  · subst h
    have : g0 = 0 := by nlinarith
    subst this
    nlinarith [mul_nonneg hρpos.le hS]
  · have hc : 0 < c ^ 2 := by positivity
    have h1 : c ^ 2 * (g0 * v) - ρ0 / 2 * g0 ^ 2 ≤ c ^ 4 * v ^ 2 / (2 * ρ0) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (ρ0 * g0 - c ^ 2 * v)]
    have h2 : c ^ 4 * v ^ 2 / (2 * ρ0) ≤ c ^ 4 * K * v := by
      rw [div_le_iff₀ (by positivity)]
      have : v ^ 2 ≤ K * v * (2 * ρ0) := by
        have : K * v * (2 * ρ0) = v * (v + κ) := by rw [← hρ]; ring
        rw [this]; nlinarith [mul_nonneg hv hκ.le]
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ c ^ 4)]
    have h3 : c ^ 2 * (g0 * v - ρ0 / 2 * S) ≤ c ^ 2 * (c ^ 2 * K * v) := by
      nlinarith [mul_le_mul_of_nonneg_left h4 hρpos.le]
    exact le_of_mul_le_mul_left h3 hc

end Pure

section Dini

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

include F

theorem curve_dini_step {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 γ)
    {c κ K : ℝ} (hK : 0 < K) (hκ : 0 < κ) {W Sg : ℝ → M → ℝ}
    (h1 : ∀ r, 0 < r → MSmooth F (W r))
    (h4 : ∀ r, 0 < r → ∀ y, ‖mgrad F (W r) y‖ ^ 2 ≤ c ^ 2 * Sg r y)
    (h5 : ∀ r, 0 < r → ∀ y, 0 ≤ Sg r y ∧ ∀ s, r < s →
      (W s y - W r y) / (s - r) ≤ -(1 / 2) * (r / s) * Sg r y)
    {r : ℝ → ℝ}
    (hr : ∀ τ, HasDerivAt r ((‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1‖ + κ) / (2 * K)) τ)
    (hmono : ∀ τ σ, τ < σ → r τ < r σ) {η r0 L C3 : ℝ} (hη : 0 ≤ η) (hr0 : 0 < r0)
    (hrr : ∀ τ ∈ Icc η 1, r0 ≤ r τ ∧ r τ ≤ 1)
    (hL : ∀ τ ∈ Icc η 1, ∀ σ ∈ Icc η 1, |r σ - r τ| ≤ L * |σ - τ|)
    (hC3 : ∀ r s, r0 ≤ r → r ≤ 1 → r0 ≤ s → s ≤ 1 → ∀ τ ∈ Icc (0:ℝ) 1,
      ‖mgrad F (W r) (γ τ) - mgrad F (W s) (γ τ)‖ ≤ C3 * |r - s|) :
    ∀ x ∈ Ico η 1, ∀ a, c ^ 2 * K * ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ x 1‖ < a →
      ∀ᶠ z in 𝓝[>] x, slope (fun τ => W (r τ) (γ τ)) x z < a := by
  intro x hx a ha
  set v : ℝ → ℝ := fun τ => ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1‖ with hvdef
  have hvc : Continuous v := continuous_speed F hγ
  have hrc : Continuous r := continuous_iff_continuousAt.2 fun τ => (hr τ).continuousAt
  have hxI : x ∈ Icc η 1 := ⟨hx.1, hx.2.le⟩
  have hrx := hrr x hxI
  have rxpos : 0 < r x := lt_of_lt_of_le hr0 hrx.1
  have hSn := (h5 (r x) rxpos (γ x)).1
  set S := Sg (r x) (γ x) with hSdef
  set g : ℝ → ℝ := fun s => ‖mgrad F (W (r x)) (γ s)‖ with hgdef
  have hf : Continuous (fun s => g s * v s) :=
    ((continuous_norm_mgrad F (h1 (r x) rxpos)).comp hγ.continuous).mul hvc
  set ρ0 : ℝ := (v x + κ) / (2 * K) with hρ0
  have hρ : ρ0 * (2 * K) = v x + κ := div_mul_cancel₀ _ (by positivity)
  have hA : g x * v x - ρ0 / 2 * S ≤ c ^ 2 * K * v x :=
    young_aux hK hκ (norm_nonneg _) hSn (norm_nonneg _) (h4 (r x) rxpos (γ x)) hρ
  have hvnn : 0 ≤ v x := norm_nonneg _
  have hρpos : 0 < ρ0 := by positivity
  set ε : ℝ := (a - c ^ 2 * K * v x) / 3 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  -- second bracket
  have hT : Tendsto (fun z => (r x / r z) * ((r z - r x) / (z - x))) (𝓝[>] x) (𝓝 ρ0) := by
    have hs := (hasDerivAt_iff_tendsto_slope.1 (hr x)).mono_left (nhdsGT_le_nhdsNE x)
    have hs' : Tendsto (fun z => (r z - r x) / (z - x)) (𝓝[>] x) (𝓝 ρ0) := by
      refine hs.congr (fun z => ?_)
      rw [slope_def_field]
    have hrz : Tendsto r (𝓝[>] x) (𝓝 (r x)) := (hrc.tendsto x).mono_left nhdsWithin_le_nhds
    have := (tendsto_const_nhds (x := r x)).div hrz rxpos.ne'
    rw [div_self rxpos.ne'] at this
    simpa using this.mul hs'
  have hT2 : ∀ᶠ z in 𝓝[>] x,
      -(1 / 2) * S * ((r x / r z) * ((r z - r x) / (z - x))) < -(ρ0 / 2) * S + ε := by
    have := hT.const_mul (-(1 / 2) * S)
    refine this.eventually (eventually_lt_nhds ?_)
    nlinarith
  -- first bracket
  obtain ⟨δ1, hδ1, hδ1'⟩ : ∃ δ1 > 0, ∀ s, dist s x < δ1 →
      g s * v s < g x * v x + ε / 2 ∧ v s < v x + 1 := by
    have e1 : ∀ᶠ s in 𝓝 x, g s * v s < g x * v x + ε / 2 :=
      hf.continuousAt.eventually (eventually_lt_nhds (by linarith))
    have e2 : ∀ᶠ s in 𝓝 x, v s < v x + 1 :=
      hvc.continuousAt.eventually (eventually_lt_nhds (by linarith))
    exact Metric.eventually_nhds_iff.1 (e1.and e2)
  set T : ℝ := |C3| * |L| * (v x + 1) with hTdef
  have hT0 : 0 ≤ T := by positivity
  set δ2 : ℝ := ε / (2 * (T + 1)) with hδ2
  have hδ2pos : 0 < δ2 := by positivity
  have hδ2T : δ2 * T ≤ ε / 2 := by
    have : δ2 * (T + 1) = ε / 2 := by rw [hδ2]; field_simp
    nlinarith
  set δ : ℝ := min (min δ1 δ2) (1 - x) with hδdef
  have hδpos : 0 < δ := lt_min (lt_min hδ1 hδ2pos) (by linarith [hx.2])
  have hE1 : ∀ z ∈ Ioo x (x + δ), W (r z) (γ z) - W (r z) (γ x) ≤ (g x * v x + ε) * (z - x) := by
    intro z hz
    have hz1 : z - x < δ1 := by
      have := min_le_left (min δ1 δ2) (1 - x); have := min_le_left δ1 δ2; linarith [hz.2]
    have hz2 : z - x < δ2 := by
      have := min_le_left (min δ1 δ2) (1 - x); have := min_le_right δ1 δ2; linarith [hz.2]
    have hz3 : z ≤ 1 := by
      have := min_le_right (min δ1 δ2) (1 - x); linarith [hz.2]
    have hzI : z ∈ Icc η 1 := ⟨by linarith [hx.1, hz.1], hz3⟩
    have hrz := hrr z hzI
    have hrzpos : 0 < r z := lt_of_lt_of_le hr0 hrz.1
    have hLz : |r z - r x| ≤ |L| * (z - x) := by
      have := hL x hxI z hzI
      rw [abs_of_pos (sub_pos.2 hz.1)] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sub_pos.2 hz.1).le)
    refine curve_mvt F hγ (h1 (r z) hrzpos) hz.1.le ?_
    intro s hs
    have hsI : s ∈ Icc η 1 := ⟨by linarith [hx.1, hs.1], hs.2.trans hz3⟩
    have hs0 : s ∈ Icc (0:ℝ) 1 := ⟨hη.trans hsI.1, hsI.2⟩
    have hsd : dist s x < δ1 := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]; linarith [hs.2]
    obtain ⟨hs1, hs2⟩ := hδ1' s hsd
    have hv0 : 0 ≤ v s := norm_nonneg _
    have hnorm : ‖mgrad F (W (r z)) (γ s)‖ ≤ g s + |C3| * |L| * (z - x) := by
      have h3 := hC3 (r z) (r x) hrz.1 hrz.2 hrx.1 hrx.2 s hs0
      have : ‖mgrad F (W (r z)) (γ s)‖ ≤
          ‖mgrad F (W (r x)) (γ s)‖ + ‖mgrad F (W (r z)) (γ s) - mgrad F (W (r x)) (γ s)‖ := by
        have := norm_le_insert' (mgrad F (W (r z)) (γ s)) (mgrad F (W (r x)) (γ s))
        linarith [norm_sub_rev (mgrad F (W (r z)) (γ s)) (mgrad F (W (r x)) (γ s))]
      calc _ ≤ g s + C3 * |r z - r x| := by
            have := hC3 (r z) (r x) hrz.1 hrz.2 hrx.1 hrx.2 s hs0
            simp only [hgdef]; linarith
        _ ≤ g s + |C3| * (|L| * (z - x)) := by
            exact add_le_add_right (le_trans
              (mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hLz (abs_nonneg _))) _
        _ = _ := by ring
    have hzx : z - x ≤ δ2 := hz2.le
    calc ‖mgrad F (W (r z)) (γ s)‖ * ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ s 1‖
        ≤ (g s + |C3| * |L| * (z - x)) * v s :=
          mul_le_mul_of_nonneg_right hnorm hv0
      _ = g s * v s + |C3| * |L| * (z - x) * v s := by ring
      _ ≤ g s * v s + |C3| * |L| * δ2 * (v x + 1) := by
          gcongr
      _ ≤ (g x * v x + ε / 2) + ε / 2 := by
          have : |C3| * |L| * δ2 * (v x + 1) = δ2 * T := by rw [hTdef]; ring
          rw [this]; linarith
      _ = g x * v x + ε := by ring
  filter_upwards [Ioo_mem_nhdsGT (show x < x + δ by linarith), hT2] with z hz hz2
  have hz3 : z ≤ 1 := by
    have := min_le_right (min δ1 δ2) (1 - x); linarith [hz.2]
  have hzI : z ∈ Icc η 1 := ⟨by linarith [hx.1, hz.1], hz3⟩
  have hzx : 0 < z - x := sub_pos.2 hz.1
  have hlt : r x < r z := hmono x z hz.1
  have hb2 := ((h5 (r x) rxpos (γ x)).2 (r z) hlt)
  rw [div_le_iff₀ (sub_pos.2 hlt)] at hb2
  have hrzpos : 0 < r z := by linarith
  have hb1 := hE1 z hz
  have hb3 : -(1 / 2) * S * ((r x / r z) * ((r z - r x) / (z - x))) * (z - x)
      < (-(ρ0 / 2) * S + ε) * (z - x) := mul_lt_mul_of_pos_right hz2 hzx
  have hb4 : -(1 / 2) * S * ((r x / r z) * ((r z - r x) / (z - x))) * (z - x)
      = -(1 / 2) * (r x / r z) * S * (r z - r x) := by
    field_simp
  rw [slope_def_field, div_lt_iff₀ hzx]
  have hA' : (g x * v x + ε + (-(ρ0 / 2) * S + ε)) * (z - x) ≤ (c ^ 2 * K * v x + 2 * ε) * (z - x) :=
    mul_le_mul_of_nonneg_right (by linarith) hzx.le
  have : (c ^ 2 * K * v x + 2 * ε) * (z - x) < a * (z - x) :=
    mul_lt_mul_of_pos_right (by rw [hεdef]; linarith) hzx
  nlinarith

end Dini

end CutoffRigidity.Riemann.Diff
