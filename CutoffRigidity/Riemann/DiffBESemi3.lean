module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Two abstract L¹-differentiation lemmas

* `sqrt_L1_deriv`: `√(G + ε)` is differentiable in L¹ along L¹-differentiable nonnegative families.
* `hasDerivAt_integral_mul_L1`: product rule `d/ds ∫ P_s u_s` for `P` uniformly differentiable
  and `u` differentiable in L¹.
-/

@[expose] public section

open MeasureTheory Filter Set Topology
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

/-- Pointwise estimate behind `sqrt_L1_deriv` (`a = √(G_h+ε)`, `b = √(G+ε)`, `s = √ε`). -/
lemma sqrtL1_pt {s a b δ q h K : ℝ} (hs : 0 < s) (ha : s ≤ a) (hb : s ≤ b)
    (hδ : a ^ 2 - b ^ 2 = δ) (hK : 0 ≤ K) :
    |(a - b) / h - q / (2 * b)| ≤
      1 / (2 * s) * |δ / h - q| + K / (8 * s ^ 3) * |δ| + 1 / (2 * s) * max (|q| - K) 0 := by
  have hb0 : 0 < b := lt_of_lt_of_le hs hb
  have hab : 0 < a + b := by linarith
  have e1 : (a - b) / h - q / (2 * b)
      = (δ / h - q) * (1 / (a + b)) + q * (1 / (a + b) - 1 / (2 * b)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv δ h]
    set t := h⁻¹
    rw [← hδ]; field_simp; ring
  have e2 : 1 / (a + b) - 1 / (2 * b) = -δ / (2 * b * (a + b) ^ 2) := by
    rw [← hδ]; field_simp; ring
  have hbh0 : 0 ≤ 1 / (a + b) := by positivity
  have hbh : 1 / (a + b) ≤ 1 / (2 * s) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have hb' : 1 / (2 * b) ≤ 1 / (2 * s) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have hb'0 : 0 ≤ 1 / (2 * b) := by positivity
  have d1 : |1 / (a + b) - 1 / (2 * b)| ≤ 1 / (2 * s) := by
    rw [abs_sub_le_iff]; constructor <;> linarith
  have d2 : |1 / (a + b) - 1 / (2 * b)| ≤ |δ| / (8 * s ^ 3) := by
    rw [e2, abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2 * b * (a + b) ^ 2)]
    apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
    have h1 : 2 * s ≤ a + b := by linarith
    have h2 : (2 * s) ^ 2 ≤ (a + b) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    nlinarith [mul_le_mul hb h2 (by positivity) hb0.le]
  rw [e1]
  have hq : |q| ≤ K + max (|q| - K) 0 := by
    have := le_max_left (|q| - K) 0; linarith
  have hm : 0 ≤ max (|q| - K) 0 := le_max_right _ _
  set D := |1 / (a + b) - 1 / (2 * b)|
  have hD : 0 ≤ D := abs_nonneg _
  calc _ ≤ |(δ / h - q) * (1 / (a + b))| + |q * (1 / (a + b) - 1 / (2 * b))| := abs_add_le _ _
    _ = |δ / h - q| * (1 / (a + b)) + |q| * D := by
        rw [abs_mul, abs_mul, abs_of_nonneg hbh0]
    _ ≤ |δ / h - q| * (1 / (2 * s)) + (K + max (|q| - K) 0) * D := by
        gcongr
    _ = |δ / h - q| * (1 / (2 * s)) + K * D + max (|q| - K) 0 * D := by ring
    _ ≤ |δ / h - q| * (1 / (2 * s)) + K * (|δ| / (8 * s ^ 3)) + max (|q| - K) 0 * (1 / (2 * s)) := by
        gcongr
    _ = _ := by ring


section AbstractL1
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

/-- `∫ (|q| - n)⁺ → 0`. -/
lemma sqrtL1_tail_tendsto {q : α → ℝ} (hq : Integrable q μ) :
    Tendsto (fun n : ℕ => ∫ x, max (|q x| - n) 0 ∂μ) atTop (𝓝 0) := by
  have := tendsto_integral_of_dominated_convergence (μ := μ) (f := fun _ => (0:ℝ))
    (fun x => |q x|) (F := fun (n : ℕ) x => max (|q x| - n) 0) (fun n => ?_) hq.abs
    (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · simpa using this
  · exact (by fun_prop : Continuous fun y : ℝ => max (|y| - n) 0).comp_aestronglyMeasurable hq.1
  · rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) (abs_nonneg _)
  · obtain ⟨N, hN⟩ := exists_nat_ge |q x|
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have : (N:ℝ) ≤ n := by exact_mod_cast hn
    exact (max_eq_right (by linarith)).symm

lemma sqrtL1_integrable_tail {q : α → ℝ} (hq : Integrable q μ) (K : ℝ) (hK : 0 ≤ K) :
    Integrable (fun x => max (|q x| - K) 0) μ := by
  refine hq.abs.mono' ((by fun_prop : Continuous fun y : ℝ => max (|y| - K) 0).comp_aestronglyMeasurable hq.1)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith) (abs_nonneg _)

/-- the nonlinearity `sqrt(G+ε)` is differentiable in L¹ along L¹-differentiable nonnegative families.

Compared with the original statement, the integrability hypotheses `hGhi`, `hG0i` were added: they
are necessary (with `Gh h` non-integrable the Bochner integral in `hlim` is `0`, and e.g.
`G0 = q = 0`, `Gh h x = 1/x` on `(0,1)` gives a counterexample) and available to the consumer. -/
theorem sqrt_L1_deriv {ε : ℝ} (hε : 0 < ε) (Gh : ℝ → α → ℝ) (G0 q : α → ℝ)
    (hGh : ∀ h, AEStronglyMeasurable (Gh h) μ) (hG0 : AEStronglyMeasurable G0 μ)
    (hGh0 : ∀ h x, 0 ≤ Gh h x) (hG00 : ∀ x, 0 ≤ G0 x)
    (hGhi : ∀ h, Integrable (Gh h) μ) (hG0i : Integrable G0 μ)
    (hq : Integrable q μ)
    (hlim : Tendsto (fun h : ℝ => ∫ x, |(Gh h x - G0 x) / h - q x| ∂μ) (𝓝[≠] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => ∫ x, |(Real.sqrt (Gh h x + ε) - Real.sqrt (G0 x + ε)) / h
        - q x / (2 * Real.sqrt (G0 x + ε))| ∂μ) (𝓝[≠] 0) (𝓝 0) := by
  set s := Real.sqrt ε with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 hε
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨N, hN⟩ := ((sqrtL1_tail_tendsto hq).eventually
    (gt_mem_nhds (by positivity : (0:ℝ) < η * s))).exists
  set K : ℝ := (N : ℝ)
  have hK : 0 ≤ K := Nat.cast_nonneg N
  set M := ∫ x, |q x| ∂μ
  set A := fun h : ℝ => ∫ x, |(Gh h x - G0 x) / h - q x| ∂μ
  have hg : Tendsto (fun h : ℝ => 1 / (2 * s) * A h + K / (8 * s ^ 3) * (|h| * (A h + M)))
      (𝓝[≠] 0) (𝓝 (1 / (2 * s) * 0 + K / (8 * s ^ 3) * (|(0:ℝ)| * (0 + M)))) := by
    have habs : Tendsto (fun h : ℝ => |h|) (𝓝[≠] 0) (𝓝 (|(0:ℝ)|)) :=
      tendsto_nhdsWithin_of_tendsto_nhds (continuous_abs.tendsto 0)
    exact (hlim.const_mul _).add ((habs.mul (hlim.add_const M)).const_mul _)
  simp only [abs_zero, zero_mul, mul_zero, add_zero] at hg
  filter_upwards [hg.eventually (gt_mem_nhds (by positivity : (0:ℝ) < η / 2)),
    self_mem_nhdsWithin] with h hgh hh0
  have hh0 : h ≠ 0 := hh0
  have iQ : Integrable (fun x => |(Gh h x - G0 x) / h - q x|) μ :=
    ((((hGhi h).sub hG0i).div_const h).sub hq).abs
  have iD : Integrable (fun x => |Gh h x - G0 x|) μ := ((hGhi h).sub hG0i).abs
  have iT := sqrtL1_integrable_tail hq K hK
  have hD : ∫ x, |Gh h x - G0 x| ∂μ ≤ |h| * (A h + M) := by
    calc ∫ x, |Gh h x - G0 x| ∂μ ≤ ∫ x, |h| * (|(Gh h x - G0 x) / h - q x| + |q x|) ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
            ((iQ.add hq.abs).const_mul _) (Eventually.of_forall fun x => ?_)
          have : Gh h x - G0 x = h * (((Gh h x - G0 x) / h - q x) + q x) := by
            field_simp; ring
          calc |Gh h x - G0 x| = |h * (((Gh h x - G0 x) / h - q x) + q x)| := congrArg _ this
            _ = |h| * |((Gh h x - G0 x) / h - q x) + q x| := abs_mul _ _
            _ ≤ _ := mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg h)
      _ = |h| * (A h + M) := by rw [integral_const_mul, integral_add iQ hq.abs]
  have hmain : ∫ x, |(Real.sqrt (Gh h x + ε) - Real.sqrt (G0 x + ε)) / h
        - q x / (2 * Real.sqrt (G0 x + ε))| ∂μ
      ≤ 1 / (2 * s) * A h + K / (8 * s ^ 3) * ∫ x, |Gh h x - G0 x| ∂μ
        + 1 / (2 * s) * ∫ x, max (|q x| - K) 0 ∂μ := by
    calc _ ≤ ∫ x, (1 / (2 * s) * |(Gh h x - G0 x) / h - q x| + K / (8 * s ^ 3) * |Gh h x - G0 x|
          + 1 / (2 * s) * max (|q x| - K) 0) ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
            (((iQ.const_mul _).add (iD.const_mul _)).add (iT.const_mul _))
            (Eventually.of_forall fun x => ?_)
          refine sqrtL1_pt hs (Real.sqrt_le_sqrt (by linarith [hGh0 h x]))
            (Real.sqrt_le_sqrt (by linarith [hG00 x])) ?_ hK
          rw [Real.sq_sqrt (by linarith [hGh0 h x]), Real.sq_sqrt (by linarith [hG00 x])]; ring
      _ = _ := by
          have k1 : Integrable (fun x => 1 / (2 * s) * |(Gh h x - G0 x) / h - q x|) μ :=
            iQ.const_mul _
          have k2 : Integrable (fun x => K / (8 * s ^ 3) * |Gh h x - G0 x|) μ := iD.const_mul _
          have k3 : Integrable (fun x => 1 / (2 * s) * max (|q x| - K) 0) μ := iT.const_mul _
          have k12 : Integrable (fun x => 1 / (2 * s) * |(Gh h x - G0 x) / h - q x|
            + K / (8 * s ^ 3) * |Gh h x - G0 x|) μ := k1.add k2
          rw [integral_add k12 k3, integral_add k1 k2, integral_const_mul,
            integral_const_mul, integral_const_mul]
  have hTN : 1 / (2 * s) * ∫ x, max (|q x| - K) 0 ∂μ < η / 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ (by positivity)]
    nlinarith
  have hpos : 0 ≤ ∫ x, |(Real.sqrt (Gh h x + ε) - Real.sqrt (G0 x + ε)) / h
        - q x / (2 * Real.sqrt (G0 x + ε))| ∂μ := integral_nonneg fun x => abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hpos]
  have : K / (8 * s ^ 3) * ∫ x, |Gh h x - G0 x| ∂μ ≤ K / (8 * s ^ 3) * (|h| * (A h + M)) :=
    mul_le_mul_of_nonneg_left hD (by positivity)
  linarith

/-- product rule `d/ds ∫ P_s u_s = ∫ P' u_{s₀} + ∫ P_{s₀} v` at `s₀`, `P` uniformly differentiable and
`u` differentiable in L¹. -/
theorem hasDerivAt_integral_mul_L1 (Ph u : ℝ → α → ℝ) (P' v : α → ℝ) (s₀ : ℝ)
    (hPm : ∀ s, AEStronglyMeasurable (Ph s) μ) (hum : ∀ s, AEStronglyMeasurable (u s) μ)
    (C : ℝ) (hC : ∀ s x, |Ph s x| ≤ C)
    (hP' : ∀ x, |P' x| ≤ C)
    (hP'm : AEStronglyMeasurable P' μ)
    (hui : ∀ s, Integrable (u s) μ) (hv : Integrable v μ)
    (hP : ∀ η > 0, ∀ᶠ h in 𝓝[≠] (0:ℝ), ∀ x, |(Ph (s₀ + h) x - Ph s₀ x) / h - P' x| ≤ η)
    (hu1 : Tendsto (fun h : ℝ => ∫ x, |u (s₀ + h) x - u s₀ x| ∂μ) (𝓝[≠] 0) (𝓝 0))
    (hu2 : Tendsto (fun h : ℝ => ∫ x, |(u (s₀ + h) x - u s₀ x) / h - v x| ∂μ) (𝓝[≠] 0) (𝓝 0)) :
    HasDerivAt (fun s => ∫ x, Ph s x * u s x ∂μ) (∫ x, P' x * u s₀ x ∂μ + ∫ x, Ph s₀ x * v x ∂μ) s₀ := by
  rw [hasDerivAt_iff_tendsto_slope_zero, Metric.tendsto_nhds]
  intro ε hε
  set M := ∫ x, |u s₀ x| ∂μ
  have hM : 0 ≤ M := integral_nonneg fun x => abs_nonneg _
  have hη : 0 < ε / (2 * (M + 1)) := by positivity
  have hCC : Tendsto (fun h : ℝ => C * ∫ x, |u (s₀ + h) x - u s₀ x| ∂μ
      + C * ∫ x, |(u (s₀ + h) x - u s₀ x) / h - v x| ∂μ) (𝓝[≠] 0) (𝓝 (C * 0 + C * 0)) :=
    (hu1.const_mul C).add (hu2.const_mul C)
  simp only [mul_zero, add_zero] at hCC
  have bdd : ∀ s, ∀ᵐ x ∂μ, ‖Ph s x‖ ≤ C := fun s => Eventually.of_forall fun x => hC s x
  filter_upwards [hP _ hη, hu1.eventually (gt_mem_nhds one_pos),
    hCC.eventually (gt_mem_nhds (by positivity : (0:ℝ) < ε / 2)), self_mem_nhdsWithin]
    with h hPh hA1 hA hh0
  have hh0 : h ≠ 0 := hh0
  set u1 := u (s₀ + h)
  set u0 := u s₀
  set P1 := Ph (s₀ + h)
  set P0 := Ph s₀
  have i1 : Integrable (fun x => P1 x * u1 x) μ := (hui _).bdd_mul (hPm _) (bdd _)
  have i0 : Integrable (fun x => P0 x * u0 x) μ := (hui _).bdd_mul (hPm _) (bdd _)
  have iP : Integrable (fun x => P' x * u0 x) μ :=
    (hui _).bdd_mul hP'm (Eventually.of_forall fun x => hP' x)
  have iV : Integrable (fun x => P0 x * v x) μ := hv.bdd_mul (hPm _) (bdd _)
  have iA1 : Integrable (fun x => |u1 x - u0 x|) μ := ((hui _).sub (hui _)).abs
  have iA2 : Integrable (fun x => |(u1 x - u0 x) / h - v x|) μ :=
    ((((hui _).sub (hui _)).div_const h).sub hv).abs
  set E := fun x => ((P1 x - P0 x) / h - P' x) * u1 x + P' x * (u1 x - u0 x)
    + P0 x * ((u1 x - u0 x) / h - v x)
  have hE : h⁻¹ • ((∫ x, P1 x * u1 x ∂μ) - ∫ x, P0 x * u0 x ∂μ)
      - (∫ x, P' x * u0 x ∂μ + ∫ x, P0 x * v x ∂μ) = ∫ x, E x ∂μ := by
    have : E = fun x => h⁻¹ * (P1 x * u1 x - P0 x * u0 x) - (P' x * u0 x + P0 x * v x) := by
      funext x; simp only [E]; field_simp; ring
    have j1 : Integrable (fun x => h⁻¹ * (P1 x * u1 x - P0 x * u0 x)) μ := (i1.sub i0).const_mul _
    have j2 : Integrable (fun x => P' x * u0 x + P0 x * v x) μ := iP.add iV
    simp only [this]
    rw [integral_sub j1 j2, integral_const_mul,
      integral_sub i1 i0, integral_add iP iV, smul_eq_mul]
  have hEb : ∫ x, |E x| ∂μ ≤ ε / (2 * (M + 1)) * ((∫ x, |u1 x - u0 x| ∂μ) + M)
      + (C * ∫ x, |u1 x - u0 x| ∂μ + C * ∫ x, |(u1 x - u0 x) / h - v x| ∂μ) := by
    calc ∫ x, |E x| ∂μ ≤ ∫ x, (ε / (2 * (M + 1)) * (|u1 x - u0 x| + |u0 x|)
          + (C * |u1 x - u0 x| + C * |(u1 x - u0 x) / h - v x|)) ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
            (((iA1.add (hui _).abs).const_mul _).add ((iA1.const_mul _).add (iA2.const_mul _)))
            (Eventually.of_forall fun x => ?_)
          simp only [E]
          have h1 : |u1 x| ≤ |u1 x - u0 x| + |u0 x| := by
            simpa using abs_add_le (u1 x - u0 x) (u0 x)
          calc _ ≤ |((P1 x - P0 x) / h - P' x) * u1 x| + |P' x * (u1 x - u0 x)|
                + |P0 x * ((u1 x - u0 x) / h - v x)| := abs_add_three _ _ _
            _ = |(P1 x - P0 x) / h - P' x| * |u1 x| + |P' x| * |u1 x - u0 x|
                + |P0 x| * |(u1 x - u0 x) / h - v x| := by rw [abs_mul, abs_mul, abs_mul]
            _ ≤ _ := by
                have a1 := mul_le_mul (hPh x) h1 (abs_nonneg _) hη.le
                have a2 := mul_le_mul_of_nonneg_right (hP' x) (abs_nonneg (u1 x - u0 x))
                have a3 := mul_le_mul_of_nonneg_right (hC s₀ x)
                  (abs_nonneg ((u1 x - u0 x) / h - v x))
                linarith
      _ = _ := by
          have iU : Integrable (fun x => |u0 x|) μ := (hui _).abs
          have k1 : Integrable (fun x => |u1 x - u0 x| + |u0 x|) μ := iA1.add iU
          have k2 : Integrable (fun x => ε / (2 * (M + 1)) * (|u1 x - u0 x| + |u0 x|)) μ :=
            k1.const_mul _
          have k3 : Integrable (fun x => C * |u1 x - u0 x|) μ := iA1.const_mul _
          have k4 : Integrable (fun x => C * |(u1 x - u0 x) / h - v x|) μ := iA2.const_mul _
          have k5 : Integrable (fun x => C * |u1 x - u0 x| + C * |(u1 x - u0 x) / h - v x|) μ :=
            k3.add k4
          rw [integral_add k2 k5, integral_const_mul, integral_add iA1 iU, integral_add k3 k4,
            integral_const_mul, integral_const_mul]
  rw [Real.dist_eq, hE]
  have hη2 : ε / (2 * (M + 1)) * ((∫ x, |u1 x - u0 x| ∂μ) + M) ≤ ε / 2 := by
    calc _ ≤ ε / (2 * (M + 1)) * (1 + M) := by gcongr
      _ = ε / 2 := by field_simp; ring
  calc |∫ x, E x ∂μ| ≤ ∫ x, |E x| ∂μ := abs_integral_le_integral_abs
    _ < ε := by linarith

end AbstractL1

end CutoffRigidity.Riemann.Diff
