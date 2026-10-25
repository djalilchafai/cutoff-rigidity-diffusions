module

public import CutoffRigidity.LangevinSolution

/-!
# Quantitative dependence on the actual driving path

For two actual Langevin integral-equation solutions, removing their respective
continuous noise increments gives a differentiable difference. A Lipschitz bound
for the actual potential gradient on a shared set then controls the difference
by the initial displacement and uniform noise displacement.

This file starts with a deterministic estimate; continuity and measurability
of the selected solution in a continuous-path topology require the subsequent
verification that such bounds hold locally uniformly in the inputs.
-/

public section

open Set
open scoped NNReal

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Quantitative dependence of actual solutions on their continuous driving
paths, under a concrete shared gradient Lipschitz bound. -/
theorem langevin_noise_difference_bound
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) {w v X Y : ℝ → E} {x₀ y₀ : E}
    {T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 ≤ δ)
    (hw : ContinuousOn w (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hX : IsLangevinPathOn V w x₀ X T) (hY : IsLangevinPathOn V v y₀ Y T)
    {S : Set E} {K : ℝ≥0} (hLip : LipschitzOnWith K (gradient V) S)
    (hXS : MapsTo X (Icc 0 T) S) (hYS : MapsTo Y (Icc 0 T) S)
    (hnoise : ∀ s ∈ Icc 0 T, ‖(w s - w 0) - (v s - v 0)‖ ≤ δ) :
    ‖X T - Y T‖ ≤ Real.exp ((K + 1) * T) * (‖x₀ - y₀‖ + K * δ) + δ := by
  let Z : ℝ → E := fun s => (X s - (w s - w 0)) - (Y s - (v s - v 0))
  let Z' : ℝ → E := fun s => -gradient V (X s) + gradient V (Y s)
  have hZcont : ContinuousOn Z (Icc 0 T) :=
    (hX.1.sub (hw.sub continuousOn_const)).sub (hY.1.sub (hv.sub continuousOn_const))
  have hZd (s : ℝ) (hs : s ∈ Ioo 0 T) : HasDerivAt Z (Z' s) s := by
    convert (langevin_compensated_hasDerivAt hV hX hs).sub
      (langevin_compensated_hasDerivAt hV hY hs) using 1
    simp only [Z', sub_neg_eq_add]
  have hZ₀ : Z 0 = x₀ - y₀ := by
    simp only [Z, sub_self, sub_zero, hX.initial hT, hY.initial hT]
  have hnorm (s : ℝ) (hs : s ∈ Icc 0 T) : ‖X s - Y s‖ ≤ ‖Z s‖ + δ := by
    have heq : X s - Y s = Z s + ((w s - w 0) - (v s - v 0)) := by dsimp [Z]; abel
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (hnoise s hs))
  have hYoung (s : ℝ) (hs : s ∈ Ioo 0 T) :
      2 * inner ℝ (Z s) (Z' s) ≤ 2 * (K + 1) * (‖Z s‖ ^ 2 + (K * δ) ^ 2) := by
    have hs' : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le⟩
    have hgrad : ‖Z' s‖ ≤ K * (‖Z s‖ + δ) := by
      have heq : Z' s = -(gradient V (X s) - gradient V (Y s)) := by dsimp [Z']; abel
      rw [heq, norm_neg]
      exact (hLip.norm_sub_le (hXS hs') (hYS hs')).trans
        (mul_le_mul_of_nonneg_left (hnorm s hs') K.2)
    have hinner := real_inner_le_norm (Z s) (Z' s)
    have hmul := mul_le_mul_of_nonneg_left hgrad (norm_nonneg (Z s))
    have hK : (0 : ℝ) ≤ K := K.2
    have hKC : 0 ≤ (K : ℝ) * (K * δ) ^ 2 := mul_nonneg hK (sq_nonneg _)
    nlinarith [sq_nonneg (‖Z s‖ - K * δ), sq_nonneg ‖Z s‖, sq_nonneg (K * δ)]
  have henergy := exponential_decay_of_deriv_le
    (f := fun s => ‖Z s‖ ^ 2 + (K * δ) ^ 2)
    (f' := fun s => 2 * inner ℝ (Z s) (Z' s)) (rate := -(2 * (K + 1))) hT
    ((hZcont.norm.pow 2).add_const _)
    (fun s hs => (hZd s hs).norm_sq.add_const _)
    (fun s hs => by simpa only [neg_neg] using hYoung s hs)
  rw [neg_neg] at henergy
  change ‖Z T‖ ^ 2 + (K * δ) ^ 2 ≤
    Real.exp (2 * (K + 1) * T) * (‖Z 0‖ ^ 2 + (K * δ) ^ 2) at henergy
  rw [hZ₀] at henergy
  have hKδ : (0 : ℝ) ≤ K * δ := mul_nonneg K.2 hδ
  have hexp : Real.exp ((K + 1) * T) ^ 2 = Real.exp (2 * (K + 1) * T) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hZnorm : ‖Z T‖ ≤ Real.exp ((K + 1) * T) * (‖x₀ - y₀‖ + K * δ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _)
      (add_nonneg (norm_nonneg _) hKδ))).mp
    rw [mul_pow, hexp]
    have hsq : ‖x₀ - y₀‖ ^ 2 + (K * δ) ^ 2 ≤ (‖x₀ - y₀‖ + K * δ) ^ 2 := by
      nlinarith [norm_nonneg (x₀ - y₀)]
    have hmul := mul_le_mul_of_nonneg_left hsq (Real.exp_nonneg (2 * (K + 1) * T))
    nlinarith [sq_nonneg (K * δ)]
  exact (hnorm T ⟨hT, le_rfl⟩).trans (add_le_add hZnorm le_rfl)

/-- A uniform displacement of the raw driving paths controls their increments
by twice that displacement, including different values at time zero. -/
theorem langevin_raw_noise_difference_bound
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) {w v X Y : ℝ → E} {x₀ y₀ : E}
    {T η : ℝ} (hT : 0 ≤ T) (hη : 0 ≤ η)
    (hw : ContinuousOn w (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hX : IsLangevinPathOn V w x₀ X T) (hY : IsLangevinPathOn V v y₀ Y T)
    {S : Set E} {K : ℝ≥0} (hLip : LipschitzOnWith K (gradient V) S)
    (hXS : MapsTo X (Icc 0 T) S) (hYS : MapsTo Y (Icc 0 T) S)
    (hnoise : ∀ s ∈ Icc 0 T, ‖w s - v s‖ ≤ η) :
    ‖X T - Y T‖ ≤ Real.exp ((K + 1) * T) * (‖x₀ - y₀‖ + K * (2 * η)) + 2 * η := by
  apply langevin_noise_difference_bound hV hT (by positivity) hw hv hX hY hLip hXS hYS
  intro s hs
  have heq : (w s - w 0) - (v s - v 0) = (w s - v s) - (w 0 - v 0) := by abel
  rw [heq]
  have h := norm_sub_le (w s - v s) (w 0 - v 0)
  linarith [hnoise s hs, hnoise 0 ⟨le_rfl, hT⟩]

/-- The same concrete estimate applies to the canonical selected solutions,
whose actual existence and integral equations are supplied by proved theorems. -/
theorem langevinSolution_noise_difference_bound [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w v : ℝ → E} (hw : Continuous w) (hv : Continuous v) (x₀ y₀ : E)
    {T η : ℝ} (hT : 0 ≤ T) (hη : 0 ≤ η)
    {S : Set E} {K : ℝ≥0} (hLip : LipschitzOnWith K (gradient V) S)
    (hXS : MapsTo (langevinSolution V w x₀) (Icc 0 T) S)
    (hYS : MapsTo (langevinSolution V v y₀) (Icc 0 T) S)
    (hnoise : ∀ s ∈ Icc 0 T, ‖w s - v s‖ ≤ η) :
    ‖langevinSolution V w x₀ T - langevinSolution V v y₀ T‖ ≤
      Real.exp ((K + 1) * T) * (‖x₀ - y₀‖ + K * (2 * η)) + 2 * η :=
  langevin_raw_noise_difference_bound hV hT hη hw.continuousOn hv.continuousOn
    (langevinSolution_isLangevinPathOn hV rate hrate hHess hw x₀ hT)
    (langevinSolution_isLangevinPathOn hV rate hrate hHess hv y₀ hT)
    hLip hXS hYS hnoise

end CutoffRigidity
