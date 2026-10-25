module

public import CutoffRigidity.LangevinInitialDerivative

/-! # Genuine C¹ initial-point dependence of the fixed-noise Langevin flow

The continuous Hessian is uniformly continuous on compact path tubes.
Comparing true variational evolutions by Volterra stability proves continuity
of the actual initial-point derivative. No Lipschitz Hessian is assumed.
-/

public section

namespace CutoffRigidity

open Set Metric MeasureTheory
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem exists_langevin_variation_fderiv {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w : ℝ → E} (hw : Continuous w) (x : E) {T : ℝ} (hT : 0 ≤ T) :
    ∃ J : ℝ → E →L[ℝ] E, J 0 = ContinuousLinearMap.id ℝ E ∧
      ContinuousOn J (Icc 0 T) ∧
      (∀ s ∈ Icc 0 T, HasDerivWithinAt J
        (-(fderiv ℝ (gradient V) (langevinSolution V w x s)).comp (J s)) (Icc 0 T) s) ∧
      (∀ s ∈ Icc 0 T, J s = fderiv ℝ (fun y => langevinSolution V w y s) x) ∧
      ∀ s ∈ Icc 0 T, ‖J s‖ ≤ 1 := by
  let A := fun s => fderiv ℝ (gradient V) (langevinSolution V w x s)
  have hA : ContinuousOn A (Icc 0 T) :=
    continuousOn_langevinSolution_linearization hV ρ hρ hHess hw x hT
  have hpos (s : ℝ) (_hs : s ∈ Icc 0 T) (z : E) : 0 ≤ inner ℝ z (A s z) := by
    have hh := hHess (langevinSolution V w x s) z
    have hd := (hV.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
    rw [← inner_fderiv_gradient_apply (hd _)] at hh
    rw [real_inner_comm]
    exact (mul_nonneg hρ (sq_nonneg _)).trans hh
  obtain ⟨J, hJ0, hJC, hJD⟩ := exists_linear_variation_on_finite_interval A hT hA hpos
  have hEq (s : ℝ) (hs : s ∈ Icc 0 T) : J s = fderiv ℝ (fun y => langevinSolution V w y s) x := by
    apply Eq.symm
    apply HasFDerivAt.fderiv
    apply hasFDerivAt_langevinSolution_of_variational_equation hV ρ hρ hHess hw x J hs.1 hJ0
      (hJC.mono (fun r hr => ⟨hr.1, hr.2.trans hs.2⟩))
    intro r hr
    exact (hJD r ⟨hr.1.le, hr.2.le.trans hs.2⟩).hasDerivAt
      (Icc_mem_nhds hr.1 (hr.2.trans_le hs.2))
  refine ⟨J, hJ0, hJC, hJD, hEq, ?_⟩
  intro s hs
  rw [hEq s hs]
  apply (norm_fderiv_langevinSolution_initial_point_le hV ρ hρ hHess hw hs.1 x).trans
  simpa only [Real.exp_zero] using Real.exp_le_exp.mpr
    (show -ρ * s ≤ 0 by nlinarith [mul_nonneg hρ hs.1])

/-- The actual fixed-noise initial-point derivative is continuous, under
precisely the source C² potential and Hessian assumptions. -/
theorem continuous_fderiv_langevinSolution_initial_point {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w : ℝ → E} (hw : Continuous w) {T : ℝ} (hT : 0 ≤ T) :
    Continuous (fun x => fderiv ℝ (fun y => langevinSolution V w y T) x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨J, hJ0, hJC, hJD, hJEq, hJn⟩ := exists_langevin_variation_fderiv hV ρ hρ hHess hw x hT
  let X := fun s => langevinSolution V w x s
  let A := fun s => fderiv ℝ (gradient V) (X s)
  have hX := langevinSolution_isLangevinPathOn hV ρ hρ hHess hw x hT
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hX.1
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_langevinSolution_linearization hV ρ hρ hHess hw x hT)
  let K := max K₀ 0
  let M := Real.exp ((2 * K + 1) * T / 2)
  have hM : 0 < M := Real.exp_pos _
  have hG := contDiff_one_gradient_of_contDiff_two hV
  have hUC := (isCompact_closedBall (0 : E) (R + 1)).uniformContinuousOn_of_continuous
    (hG.continuous_fderiv one_ne_zero).continuousOn
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  let e := ε / (2 * M)
  have he : 0 < e := div_pos hε (mul_pos (by norm_num) hM)
  obtain ⟨η, hη, hηbound⟩ := Metric.uniformContinuousOn_iff.mp hUC e he
  let δ := min 1 (η / 2)
  have hδ : 0 < δ := lt_min zero_lt_one (half_pos hη)
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  have hyx : ‖y - x‖ < δ := by simpa only [dist_eq_norm] using hy
  obtain ⟨Q, hQ0, hQC, hQD, hQEq, hQn⟩ := exists_langevin_variation_fderiv hV ρ hρ hHess hw y hT
  let Y := fun s => langevinSolution V w y s
  let B := fun s => fderiv ℝ (gradient V) (Y s)
  have hΔ (s : ℝ) (hs : s ∈ Icc 0 T) : ‖Y s - X s‖ ≤ ‖y - x‖ := by
    have hh := langevinSolution_initial_point_contraction hV ρ hρ hHess hw y x hs.1
    have hexp : Real.exp (-ρ * s) ≤ 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr
        (show -ρ * s ≤ 0 by nlinarith [mul_nonneg hρ hs.1])
    exact hh.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp (norm_nonneg _))
  have hAB (s : ℝ) (hs : s ∈ Icc 0 T) : ‖B s - A s‖ ≤ e := by
    have hxR : ‖X s‖ ≤ R := hR s hs
    have hxS : X s ∈ closedBall (0 : E) (R + 1) := by
      rw [mem_closedBall, dist_zero_right]
      linarith
    have hyS : Y s ∈ closedBall (0 : E) (R + 1) := by
      rw [mem_closedBall, dist_zero_right]
      have hn := norm_le_norm_sub_add (Y s) (X s)
      have hh := hΔ s hs
      have hδ1 : δ ≤ 1 := min_le_left _ _
      linarith
    have hd : dist (Y s) (X s) < η := by
      rw [dist_eq_norm]
      have hδη : δ ≤ η / 2 := min_le_right _ _
      linarith [hΔ s hs]
    simpa only [dist_eq_norm, B, A] using (hηbound (Y s) hyS (X s) hxS hd).le
  have hOp : ‖Q T - J T‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (half_pos hε).le
    intro z
    let Z := fun s => Q s z - J s z
    let Z' := fun s => -(B s (Q s z)) + A s (J s z)
    have hZC : ContinuousOn Z (Icc 0 T) :=
      (hQC.clm_apply continuousOn_const).sub (hJC.clm_apply continuousOn_const)
    have hZ0 : Z 0 = 0 := by simp only [Z, hQ0, hJ0, ContinuousLinearMap.id_apply, sub_self]
    have hZD (s : ℝ) (hs : s ∈ Ioo 0 T) : HasDerivAt Z (Z' s) s := by
      have hdQ := ((hQD s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)).clm_apply (hasDerivAt_const s z)
      have hdJ := ((hJD s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)).clm_apply (hasDerivAt_const s z)
      convert! hdQ.sub hdJ using 1
      simp only [map_zero, add_zero, ContinuousLinearMap.comp_apply, neg_apply]
      dsimp only [Z', B, A, X, Y]
      abel
    have hb (s : ℝ) (hs : s ∈ Ioo 0 T) : ‖Z' s‖ ≤ K * ‖Z s‖ + e * ‖z‖ := by
      have hs' : s ∈ Icc 0 T := Ioo_subset_Icc_self hs
      have heq : Z' s = -(A s (Z s)) - (B s - A s) (Q s z) := by
        dsimp only [Z', Z]
        simp only [map_sub, sub_apply]
        abel
      have hAK : ‖A s‖ ≤ K := (hK₀ s hs').trans (le_max_left _ _)
      have hQz : ‖Q s z‖ ≤ ‖z‖ := (Q s).le_opNorm z |>.trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (hQn s hs') (norm_nonneg z))
      rw [heq]
      calc
        _ ≤ ‖A s (Z s)‖ + ‖(B s - A s) (Q s z)‖ := by
          simpa only [norm_neg] using (norm_sub_le (-(A s (Z s))) ((B s - A s) (Q s z)))
        _ ≤ K * ‖Z s‖ + e * ‖z‖ := add_le_add
          (((A s).le_opNorm _).trans (mul_le_mul_of_nonneg_right hAK (norm_nonneg _)))
          ((((B s - A s).le_opNorm _).trans
            (mul_le_mul (hAB s hs') hQz (norm_nonneg _) he.le)))
    have hh := zero_initial_volterra_stability (le_max_right K₀ 0) (mul_nonneg he.le (norm_nonneg z)) hT
      hZC hZ0 hZD hb
    have heM : e * M = ε / 2 := by dsimp [e]; field_simp
    change ‖Q T z - J T z‖ ≤ (ε / 2) * ‖z‖
    calc
      _ ≤ (e * ‖z‖) * M := hh
      _ = _ := by rw [mul_right_comm, heM]
  rw [dist_eq_norm, ← hQEq T ⟨hT, le_rfl⟩, ← hJEq T ⟨hT, le_rfl⟩]
  exact hOp.trans_lt (half_lt_self hε)

/-- True C¹ spatial regularity of every finite-time fixed-noise flow. -/
theorem contDiff_one_langevinSolution_initial_point {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w : ℝ → E} (hw : Continuous w) {T : ℝ} (hT : 0 ≤ T) :
    ContDiff ℝ 1 (fun x => langevinSolution V w x T) :=
  contDiff_one_iff_fderiv.mpr ⟨differentiable_langevinSolution_initial_point hV ρ hρ hHess hw hT,
    continuous_fderiv_langevinSolution_initial_point hV ρ hρ hHess hw hT⟩

end CutoffRigidity
