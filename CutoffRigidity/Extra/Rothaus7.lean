module

public import Mathlib
public import CutoffRigidity.Extra.Rothaus6

/-! # Rothaus remark (stage 7): the asymptotics of the entropy at a large constant

For `m_n → ∞` and `g_n → h` in `L²` and in the Orlicz sense, `∫ m_n² ψ (g_n/m_n) → 2 ∫ h²`, and
`Ent((g + m)²) ≤ ∫ m² ψ (g/m)` (Gibbs-type bound at the constant `m²`).
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace CutoffRigidity.Rothaus

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Pointwise domination of the scaled integrand. -/
theorem scaled_le {m g : ℝ} (hm : 1 ≤ m) : m ^ 2 * ψ (g / m) ≤ 32 * g ^ 2 + 9 * Θ g := by
  have hm0 : 0 < m := by linarith
  have hΘ := Θ_nonneg g
  by_cases h : |g / m| ≤ 1 / 2
  · have h1 := ψ_le_small h
    have hg : m ^ 2 * (g / m) ^ 2 = g ^ 2 := by field_simp
    have h3 : |g / m| ^ 3 ≤ (g / m) ^ 2 * (1 / 2) := by
      have : |g / m| ^ 3 = (g / m) ^ 2 * |g / m| := by rw [← sq_abs (g / m)]; ring
      rw [this]; exact mul_le_mul_of_nonneg_left h (sq_nonneg _)
    have h4 : m ^ 2 * ψ (g / m) ≤ m ^ 2 * (2 * (g / m) ^ 2 + 10 * ((g / m) ^ 2 * (1 / 2))) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg m)
    have : m ^ 2 * (2 * (g / m) ^ 2 + 10 * ((g / m) ^ 2 * (1 / 2))) = 7 * g ^ 2 := by
      rw [← hg]; ring
    nlinarith [sq_nonneg g]
  · have h1 := ψ_le_large (le_of_lt (not_le.1 h))
    have h2 : m ^ 2 * (32 * (g / m) ^ 2 + 9 * Θ (g / m)) ≤ 32 * g ^ 2 + 9 * Θ g := by
      have e1 : m ^ 2 * (g / m) ^ 2 = g ^ 2 := by field_simp
      have e2 : m ^ 2 * Θ (g / m) = g ^ 2 * Real.log (1 + (g / m) ^ 2) := by
        unfold Θ; rw [← e1]; ring
      have e3 : Real.log (1 + (g / m) ^ 2) ≤ Real.log (1 + g ^ 2) := by
        refine Real.log_le_log (by positivity) ?_
        have : (g / m) ^ 2 ≤ g ^ 2 := by
          rw [div_pow]
          exact div_le_self (sq_nonneg g) (by nlinarith)
        linarith
      have e4 : m ^ 2 * Θ (g / m) ≤ Θ g := by
        rw [e2]; unfold Θ
        exact mul_le_mul_of_nonneg_left e3 (sq_nonneg g)
      nlinarith
    calc m ^ 2 * ψ (g / m) ≤ m ^ 2 * (32 * (g / m) ^ 2 + 9 * Θ (g / m)) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg m)
      _ ≤ _ := h2

theorem scaled_nonneg (m g : ℝ) : 0 ≤ m ^ 2 * ψ (g / m) := mul_nonneg (sq_nonneg m) (ψ_nonneg _)

/-- Pointwise approximation of the scaled integrand by `2 g²`. -/
theorem scaled_sub {m g : ℝ} (hm : 0 < m) (hg : |g| ≤ m / 2) : |m ^ 2 * ψ (g / m) - 2 * g ^ 2| ≤ 10 * |g| ^ 3 / m := by
  have h : |g / m| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hm, div_le_iff₀ hm]; linarith
  have h1 := ψ_sub_small h
  have e : m ^ 2 * ψ (g / m) - 2 * g ^ 2 = m ^ 2 * (ψ (g / m) - 2 * (g / m) ^ 2) := by
    field_simp
  rw [e, abs_mul, abs_of_nonneg (sq_nonneg m)]
  calc m ^ 2 * |ψ (g / m) - 2 * (g / m) ^ 2| ≤ m ^ 2 * (10 * |g / m| ^ 3) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg m)
    _ = 10 * |g| ^ 3 / m := by
        rw [abs_div, abs_of_pos hm]; field_simp

/-- Convergence of the scaled integrals. -/
theorem tendsto_scaled [IsFiniteMeasure μ] {g : ℕ → X → ℝ} {h : X → ℝ} {m : ℕ → ℝ}
    (hg : ∀ n, MemLp (g n) 2 μ) (hΘg : ∀ n, Integrable (fun x => Θ (g n x)) μ)
    (hh : MemLp h 2 μ) (hΘh : Integrable (fun x => Θ (h x)) μ)
    (hm1 : ∀ n, 1 ≤ m n) (hm : Tendsto m atTop atTop)
    (hL2 : Tendsto (fun n => ∫ x, (g n x - h x) ^ 2 ∂μ) atTop (𝓝 0))
    (hΘ : Tendsto (fun n => ∫ x, |Θ (g n x) - Θ (h x)| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, m n ^ 2 * ψ (g n x / m n) ∂μ) atTop (𝓝 (∫ x, 2 * h x ^ 2 ∂μ)) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hL2' : Tendsto (fun n => ∫ x, (g (ns n) x - h x) ^ 2 ∂μ) atTop (𝓝 0) := hL2.comp hns
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_sq (fun n => hg (ns n)) hh hL2').exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  set k : ℕ → ℕ := fun i => ns (ms i) with hk
  have hkt : Tendsto k atTop atTop := hns.comp hms.tendsto_atTop
  have hL2k : Tendsto (fun i => ∫ x, (g (k i) x - h x) ^ 2 ∂μ) atTop (𝓝 0) := hL2.comp hkt
  have hΘk : Tendsto (fun i => ∫ x, |Θ (g (k i) x) - Θ (h x)| ∂μ) atTop (𝓝 0) := hΘ.comp hkt
  have hmk : Tendsto (fun i => m (k i)) atTop atTop := hm.comp hkt
  have hsq := sq_L1_tendsto (fun i => hg (k i)) hh hL2k
  set B : ℕ → X → ℝ := fun i x => 32 * g (k i) x ^ 2 + 9 * Θ (g (k i) x) with hB
  set b : X → ℝ := fun x => 32 * h x ^ 2 + 9 * Θ (h x) with hb
  have hBi : ∀ i, Integrable (B i) μ := fun i =>
    ((hg (k i)).integrable_sq.const_mul 32).add ((hΘg (k i)).const_mul 9)
  have hbi : Integrable b μ := (hh.integrable_sq.const_mul 32).add (hΘh.const_mul 9)
  have hψc : Continuous ψ := by
    unfold ψ
    have : Continuous fun t : ℝ => (1 + t) ^ 2 * Real.log ((1 + t) ^ 2) :=
      (Real.continuous_mul_log.comp (by fun_prop : Continuous fun t : ℝ => (1 + t) ^ 2))
    exact (this.sub (by fun_prop)).add continuous_const
  refine tendsto_integral_of_dominated_L1 (B := B) (b := b) (fun i => ?_) hbi hBi
    (fun i => Eventually.of_forall fun x => ?_) ?_ ?_ ?_
  · exact (hψc.comp_aestronglyMeasurable ((continuous_id.div_const (m (k i))).comp_aestronglyMeasurable
      (hg (k i)).aestronglyMeasurable)).const_mul _
  · rw [abs_of_nonneg (scaled_nonneg _ _)]
    exact scaled_le (hm1 _)
  · filter_upwards [hae] with x hx
    obtain ⟨R, hR⟩ := hx.norm.bddAbove_range
    have hR' : ∀ i, |g (k i) x| ≤ R := fun i => hR ⟨i, rfl⟩
    have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR' 0)
    have hev : ∀ᶠ i in atTop, 2 * R ≤ m (k i) := hmk.eventually_ge_atTop _
    have hdiff : Tendsto (fun i => m (k i) ^ 2 * ψ (g (k i) x / m (k i)) - 2 * g (k i) x ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ (tendsto_const_nhds.div_atTop hmk : Tendsto (fun i => 10 * R ^ 3 / m (k i)) atTop (𝓝 0))
      filter_upwards [hev] with i hi
      have hm0 : 0 < m (k i) := by linarith [hm1 (k i)]
      rw [Real.norm_eq_abs]
      refine (scaled_sub hm0 (by linarith [hR' i])).trans ?_
      refine div_le_div_of_nonneg_right ?_ hm0.le
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hR' i) 3) (by norm_num)
    have h1 : Tendsto (fun i => 2 * g (k i) x ^ 2) atTop (𝓝 (2 * h x ^ 2)) := (hx.pow 2).const_mul 2
    simpa using hdiff.add h1
  · filter_upwards [hae] with x hx
    have h1 : Tendsto (fun i => g (k i) x ^ 2) atTop (𝓝 (h x ^ 2)) := hx.pow 2
    have h2 : Tendsto (fun i => Θ (g (k i) x)) atTop (𝓝 (Θ (h x))) := (continuous_Θ.tendsto _).comp hx
    exact (h1.const_mul 32).add (h2.const_mul 9)
  · have hbound : ∀ i, ∫ x, |B i x - b x| ∂μ ≤ 32 * ∫ x, |g (k i) x ^ 2 - h x ^ 2| ∂μ +
        9 * ∫ x, |Θ (g (k i) x) - Θ (h x)| ∂μ := by
      intro i
      have hi1 : Integrable (fun x => |g (k i) x ^ 2 - h x ^ 2|) μ :=
        ((hg (k i)).integrable_sq.sub hh.integrable_sq).abs
      have hi2 : Integrable (fun x => |Θ (g (k i) x) - Θ (h x)|) μ := ((hΘg _).sub hΘh).abs
      calc ∫ x, |B i x - b x| ∂μ ≤ ∫ x, (32 * |g (k i) x ^ 2 - h x ^ 2| + 9 * |Θ (g (k i) x) - Θ (h x)|) ∂μ := by
            refine integral_mono ((hBi i).sub hbi).abs ((hi1.const_mul 32).add (hi2.const_mul 9)) fun x => ?_
            simp only [hB, hb]
            have : 32 * g (k i) x ^ 2 + 9 * Θ (g (k i) x) - (32 * h x ^ 2 + 9 * Θ (h x)) =
                32 * (g (k i) x ^ 2 - h x ^ 2) + 9 * (Θ (g (k i) x) - Θ (h x)) := by ring
            rw [this]
            calc _ ≤ |32 * (g (k i) x ^ 2 - h x ^ 2)| + |9 * (Θ (g (k i) x) - Θ (h x))| := abs_add_le _ _
              _ = _ := by rw [abs_mul, abs_mul]; norm_num
        _ = _ := by rw [integral_add (hi1.const_mul 32) (hi2.const_mul 9), integral_const_mul, integral_const_mul]
    refine squeeze_zero (fun i => integral_nonneg fun x => abs_nonneg _) hbound ?_
    simpa using (hsq.const_mul 32).add (hΘk.const_mul 9)

end CutoffRigidity.Rothaus
