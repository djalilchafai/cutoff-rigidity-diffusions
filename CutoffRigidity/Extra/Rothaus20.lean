module

public import Mathlib
public import CutoffRigidity.Extra.Rothaus19

/-! # Rothaus remark (stage 20): `L¹` convergence of `Θ(f_n)` from a.e. convergence and a uniform `L^{2+δ}` bound -/

@[expose] public section

open MeasureTheory Filter Topology Real

namespace CutoffRigidity.Rothaus

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem aesm_tail [IsFiniteMeasure μ] {f : X → ℝ} (hf : AEStronglyMeasurable f μ) (R : ℝ) :
    AEStronglyMeasurable (fun x => if R < |f x| then Θ (f x) else 0) μ := by
  have hm : Measurable (fun t : ℝ => if R < |t| then Θ t else 0) :=
    Measurable.ite (measurableSet_lt measurable_const (continuous_abs.measurable)) continuous_Θ.measurable
      measurable_const
  exact (hm.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable

theorem tail_integrable [IsFiniteMeasure μ] {f : X → ℝ} (hf : AEStronglyMeasurable f μ)
    (hΘ : Integrable (fun x => Θ (f x)) μ) (R : ℝ) :
    Integrable (fun x => if R < |f x| then Θ (f x) else 0) μ := by
  refine Integrable.mono' hΘ (aesm_tail hf R) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  split_ifs
  · rw [abs_of_nonneg (Θ_nonneg _)]
  · simpa using Θ_nonneg _

theorem tendsto_L1_Θ [IsFiniteMeasure μ] {δ K : ℝ} (hδ : 0 < δ) {f : ℕ → X → ℝ} {h : X → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hΘf : ∀ n, Integrable (fun x => Θ (f n x)) μ)
    (hmom : ∀ n, Integrable (fun x => |f n x| ^ (2 + δ)) μ)
    (hK : ∀ n, ∫ x, |f n x| ^ (2 + δ) ∂μ ≤ K)
    (hh : AEStronglyMeasurable h μ) (hΘh : Integrable (fun x => Θ (h x)) μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (h x))) :
    Tendsto (fun n => ∫ x, |Θ (f n x) - Θ (h x)| ∂μ) atTop (𝓝 0) := by
  set c0 : ℝ := 1 + 4 / δ with hc0
  have hc0pos : 0 < c0 := by positivity
  set K' : ℝ := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  -- tails of the sequence
  have htail_f : ∀ (n : ℕ) (R : ℝ), 1 ≤ R →
      ∫ x, (if R < |f n x| then Θ (f n x) else 0) ∂μ ≤ c0 * R ^ (-(δ / 2)) * K' := by
    intro n R hR
    have hpt : ∀ x, (if R < |f n x| then Θ (f n x) else 0) ≤ c0 * R ^ (-(δ / 2)) * |f n x| ^ (2 + δ) := by
      intro x
      split_ifs with h1
      · exact Θ_tail_le hδ hR h1
      · have : 0 ≤ |f n x| ^ (2 + δ) := by positivity
        have : 0 < R ^ (-(δ / 2)) := Real.rpow_pos_of_pos (by linarith) _
        positivity
    calc ∫ x, (if R < |f n x| then Θ (f n x) else 0) ∂μ
        ≤ ∫ x, c0 * R ^ (-(δ / 2)) * |f n x| ^ (2 + δ) ∂μ :=
          integral_mono (tail_integrable (hf n) (hΘf n) R) ((hmom n).const_mul _) hpt
      _ = c0 * R ^ (-(δ / 2)) * ∫ x, |f n x| ^ (2 + δ) ∂μ := integral_const_mul _ _
      _ ≤ c0 * R ^ (-(δ / 2)) * K' := by
          refine mul_le_mul_of_nonneg_left ((hK n).trans (le_max_left _ _)) ?_
          have : 0 < R ^ (-(δ / 2)) := Real.rpow_pos_of_pos (by linarith) _
          positivity
  -- tail of the limit
  have htail_h : Tendsto (fun j : ℕ => ∫ x, (if ((j : ℝ) + 1) < |h x| then Θ (h x) else 0) ∂μ) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun (j : ℕ) x => if ((j : ℝ) + 1) < |h x| then Θ (h x) else 0) (f := fun _ => (0 : ℝ))
      (fun x => Θ (h x)) (fun j => aesm_tail hh _) hΘh
      (fun j => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        split_ifs
        · rw [abs_of_nonneg (Θ_nonneg _)]
        · simpa using Θ_nonneg _)
      (Eventually.of_forall fun x => by
        have : ∀ᶠ j : ℕ in atTop, ¬ (((j : ℝ) + 1) < |h x|) := by
          obtain ⟨N, hN⟩ := exists_nat_ge |h x|
          filter_upwards [eventually_ge_atTop N] with j hj
          have : (N : ℝ) ≤ j := by exact_mod_cast hj
          intro hlt; linarith
        exact tendsto_const_nhds.congr' (by
          filter_upwards [this] with j hj
          simp [hj]))
    simpa using this
  -- clamped part
  have hclamp : ∀ R : ℝ, 0 ≤ R → Tendsto (fun n => ∫ x, |Θ (clampR R (f n x)) - Θ (clampR R (h x))| ∂μ)
      atTop (𝓝 0) := by
    intro R hR
    have := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n x => |Θ (clampR R (f n x)) - Θ (clampR R (h x))|) (f := fun _ => (0 : ℝ))
      (fun _ => 2 * Θ R) (fun n => ((continuous_Θ.comp (continuous_clampR R)).comp_aestronglyMeasurable (hf n)).sub
        ((continuous_Θ.comp (continuous_clampR R)).comp_aestronglyMeasurable hh) |>.norm.congr (by
          exact Eventually.of_forall fun x => by simp [Real.norm_eq_abs]))
      (integrable_const _)
      (fun n => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_abs]
        have h1 : Θ (clampR R (f n x)) ≤ Θ R := Θ_mono (by rw [abs_of_nonneg hR]; exact abs_clampR_le R _ hR)
        have h2 : Θ (clampR R (h x)) ≤ Θ R := Θ_mono (by rw [abs_of_nonneg hR]; exact abs_clampR_le R _ hR)
        rw [abs_le]
        constructor <;> linarith [Θ_nonneg (clampR R (f n x)), Θ_nonneg (clampR R (h x))])
      (by
        filter_upwards [hae] with x hx
        have : Tendsto (fun n => Θ (clampR R (f n x))) atTop (𝓝 (Θ (clampR R (h x)))) :=
          (continuous_Θ.comp (continuous_clampR R)).tendsto _ |>.comp hx
        simpa using (this.sub_const (Θ (clampR R (h x)))).abs)
    simpa using this
  -- conclusion
  rw [Metric.tendsto_atTop]
  intro η hη
  have hs : Tendsto (fun j : ℕ => c0 * ((j : ℝ) + 1) ^ (-(δ / 2)) * K') atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => ((j : ℝ) + 1) ^ (-(δ / 2))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by positivity : 0 < δ / 2)).comp
        (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    simpa using (h1.const_mul c0).mul_const K'
  obtain ⟨j, hj1, hj2⟩ := ((hs.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < η / 3))).and
    (htail_h.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < η / 3)))).exists
  set R : ℝ := (j : ℝ) + 1 with hRdef
  have hR1 : 1 ≤ R := by rw [hRdef]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hclamp R (by linarith)) (η / 3) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hcl := hN n hn
  rw [Real.dist_eq, sub_zero] at hcl ⊢
  have hint : ∀ x, 0 ≤ |Θ (f n x) - Θ (h x)| := fun x => abs_nonneg _
  have hI : 0 ≤ ∫ x, |Θ (f n x) - Θ (h x)| ∂μ := integral_nonneg hint
  rw [abs_of_nonneg hI]
  have hcl0 : 0 ≤ ∫ x, |Θ (clampR R (f n x)) - Θ (clampR R (h x))| ∂μ := integral_nonneg fun x => abs_nonneg _
  rw [abs_of_nonneg hcl0] at hcl
  have i1 : Integrable (fun x => |Θ (clampR R (f n x)) - Θ (clampR R (h x))|) μ := by
    refine Integrable.mono' (integrable_const (2 * Θ R)) ?_ (Eventually.of_forall fun x => ?_)
    · exact (((continuous_Θ.comp (continuous_clampR R)).comp_aestronglyMeasurable (hf n)).sub
        ((continuous_Θ.comp (continuous_clampR R)).comp_aestronglyMeasurable hh)).norm.congr
        (Eventually.of_forall fun x => by simp [Real.norm_eq_abs])
    · have hR0 : (0 : ℝ) ≤ R := by linarith
      rw [Real.norm_eq_abs, abs_abs]
      have h1 : Θ (clampR R (f n x)) ≤ Θ R := Θ_mono (by rw [abs_of_nonneg hR0]; exact abs_clampR_le R _ hR0)
      have h2 : Θ (clampR R (h x)) ≤ Θ R := Θ_mono (by rw [abs_of_nonneg hR0]; exact abs_clampR_le R _ hR0)
      rw [abs_le]
      constructor <;> linarith [Θ_nonneg (clampR R (f n x)), Θ_nonneg (clampR R (h x))]
  have i2 := tail_integrable (hf n) (hΘf n) R
  have i3 := tail_integrable hh hΘh R
  have hmain : ∫ x, |Θ (f n x) - Θ (h x)| ∂μ ≤
      ∫ x, (|Θ (clampR R (f n x)) - Θ (clampR R (h x))| + (if R < |f n x| then Θ (f n x) else 0) +
        (if R < |h x| then Θ (h x) else 0)) ∂μ :=
    integral_mono ((hΘf n).sub hΘh).abs ((i1.add i2).add i3)
      fun x => abs_Θ_sub_le (by linarith) _ _
  have e1 := integral_add (i1.add i2) i3
  have e2 := integral_add i1 i2
  simp only [Pi.add_apply] at e1 e2
  rw [e1, e2] at hmain
  have h4 := htail_f n R hR1
  linarith

end CutoffRigidity.Rothaus
