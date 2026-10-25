module
public import CutoffRigidity.LangevinContinuity
public import Mathlib.Topology.MetricSpace.Antilipschitz

/-! # Actual inverse distance bounds for synchronous localized Langevin flow

Cancellation of the shared additive noise gives a differentiable difference.
A concrete gradient Lipschitz bound along both paths gives a lower distance
bound by the signed scalar integrating-factor argument. C² regularity derives
the needed Lipschitz constant on every compact Euclidean ball.
-/
public section
namespace CutoffRigidity
open Set Metric Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The squared distance cannot collapse faster than the local drift
Lipschitz rate, for two actual paths driven by the same noise. -/
theorem langevin_same_noise_norm_sq_lower_bound
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) {w X Y : ℝ → E} {x₀ y₀ : E} {T : ℝ}
    (hT : 0 ≤ T) (hX : IsLangevinPathOn V w x₀ X T) (hY : IsLangevinPathOn V w y₀ Y T)
    {K : NNReal} {S : Set E} (hLip : LipschitzOnWith K (gradient V) S)
    (hXS : MapsTo X (Icc 0 T) S) (hYS : MapsTo Y (Icc 0 T) S) :
    Real.exp (-2 * K * T) * ‖x₀ - y₀‖ ^ 2 ≤ ‖X T - Y T‖ ^ 2 := by
  let Z : ℝ → E := fun s => X s - Y s
  let Z' : ℝ → E := fun s => -gradient V (X s) + gradient V (Y s)
  have hZd (s : ℝ) (hs : s ∈ Ioo 0 T) : HasDerivAt Z (Z' s) s :=
    langevin_same_noise_difference_hasDerivAt hV hX hY hs
  have hinner (s : ℝ) (hs : s ∈ Ioo 0 T) : -(K : ℝ) * ‖Z s‖ ^ 2 ≤ inner ℝ (Z s) (Z' s) := by
    have hs' : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le⟩
    have hgrad : ‖Z' s‖ ≤ K * ‖Z s‖ := by
      have heq : Z' s = -(gradient V (X s) - gradient V (Y s)) := by dsimp [Z']; abel
      rw [heq, norm_neg]
      exact hLip.norm_sub_le (hXS hs') (hYS hs')
    have hi := neg_le_of_abs_le (abs_real_inner_le_norm (Z s) (Z' s))
    have hm := mul_le_mul_of_nonneg_left hgrad (norm_nonneg (Z s))
    nlinarith only [hi, hm]
  have he := exponential_decay_of_deriv_le
    (f := fun s => -(‖Z s‖ ^ 2)) (f' := fun s => -(2 * inner ℝ (Z s) (Z' s)))
    (rate := 2 * K) hT ((hX.1.sub hY.1).norm.pow 2 |>.neg)
    (fun s hs => (hZd s hs).norm_sq.neg)
    (fun s hs => by have hi := hinner s hs; nlinarith only [hi])
  have hZ0 : Z 0 = x₀ - y₀ := by dsimp [Z]; rw [hX.initial hT, hY.initial hT]
  rw [hZ0] at he
  change -‖X T - Y T‖ ^ 2 ≤ Real.exp (-(2 * K) * T) * (-‖x₀ - y₀‖ ^ 2) at he
  have hex : -(2 * (K : ℝ)) * T = -2 * K * T := by ring
  rw [hex] at he
  nlinarith only [he]

/-- The actual local inverse Lipschitz lower bound. -/
theorem langevin_same_noise_norm_lower_bound
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) {w X Y : ℝ → E} {x₀ y₀ : E} {T : ℝ}
    (hT : 0 ≤ T) (hX : IsLangevinPathOn V w x₀ X T) (hY : IsLangevinPathOn V w y₀ Y T)
    {K : NNReal} {S : Set E} (hLip : LipschitzOnWith K (gradient V) S)
    (hXS : MapsTo X (Icc 0 T) S) (hYS : MapsTo Y (Icc 0 T) S) :
    Real.exp (-(K : ℝ) * T) * ‖x₀ - y₀‖ ≤ ‖X T - Y T‖ := by
  have he := langevin_same_noise_norm_sq_lower_bound hV hT hX hY hLip hXS hYS
  have hex : Real.exp (-(K : ℝ) * T) ^ 2 = Real.exp (-2 * K * T) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply (sq_le_sq₀ (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
  simpa only [mul_pow, hex] using he

/-- Equivalently, the actual flow has an inverse Lipschitz estimate on any
set of initial points whose trajectories stay in the common local region. -/
theorem langevin_same_noise_inverse_bound
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) {w X Y : ℝ → E} {x₀ y₀ : E} {T : ℝ}
    (hT : 0 ≤ T) (hX : IsLangevinPathOn V w x₀ X T) (hY : IsLangevinPathOn V w y₀ Y T)
    {K : NNReal} {S : Set E} (hLip : LipschitzOnWith K (gradient V) S)
    (hXS : MapsTo X (Icc 0 T) S) (hYS : MapsTo Y (Icc 0 T) S) :
    ‖x₀ - y₀‖ ≤ Real.exp ((K : ℝ) * T) * ‖X T - Y T‖ := by
  have hh := mul_le_mul_of_nonneg_left
    (langevin_same_noise_norm_lower_bound hV hT hX hY hLip hXS hYS)
    (Real.exp_nonneg ((K : ℝ) * T))
  have heq : Real.exp ((K : ℝ) * T) * (Real.exp (-(K : ℝ) * T) * ‖x₀ - y₀‖) = ‖x₀ - y₀‖ := by
    rw [← mul_assoc, ← Real.exp_add]
    simp only [neg_mul, add_neg_cancel, Real.exp_zero, one_mul]
  exact heq ▸ hh

/-- C² regularity gives an actual gradient Lipschitz constant on each
compact ball; no local drift regularity is assumed separately. -/
theorem exists_gradient_lipschitz_closedBall [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (R : ℝ) :
    ∃ K : NNReal, LipschitzOnWith K (gradient V) (closedBall (0 : E) R) := by
  let Riesz : (E →L[ℝ] ℝ) →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hgrad : ContDiff ℝ 1 (gradient V) :=
    Riesz.contDiff.comp (hV.fderiv_right (m := 1) (by norm_num))
  exact hgrad.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : E) R) (isCompact_closedBall (0 : E) R)

/-- Uniform inverse estimate for every pair of actual solutions staying
in a given compact ball, with the constant derived from the C² potential. -/
theorem langevin_inverse_bound_on_closedBall [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (R : ℝ) :
    ∃ K : NNReal, ∀ {w X Y : ℝ → E} {x₀ y₀ : E} {T : ℝ},
      0 ≤ T → IsLangevinPathOn V w x₀ X T → IsLangevinPathOn V w y₀ Y T →
      MapsTo X (Icc 0 T) (closedBall (0 : E) R) → MapsTo Y (Icc 0 T) (closedBall (0 : E) R) →
      ‖x₀ - y₀‖ ≤ Real.exp ((K : ℝ) * T) * ‖X T - Y T‖ := by
  obtain ⟨K, hK⟩ := exists_gradient_lipschitz_closedBall hV R
  exact ⟨K, fun hT hX hY hXS hYS => langevin_same_noise_inverse_bound hV hT hX hY hK hXS hYS⟩

/-- Initial points whose actual trajectories stay inside the localization ball. -/
@[expose] noncomputable def langevinStayingSet (V : E → ℝ) (w : ℝ → E) (T R : ℝ) : Set E :=
  {x | MapsTo (langevinSolution V w x) (Icc 0 T) (closedBall (0 : E) R)}

/-- Actual selected flow restricted to trajectories staying in a compact ball
is inverse Lipschitz, with a constant obtained solely from the C² potential. -/
theorem langevinSolution_antilipschitz_stayingSet [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (R : ℝ) :
    ∃ K : NNReal, ∀ (w : ℝ → E), Continuous w → ∀ (T : ℝ), 0 ≤ T →
      AntilipschitzWith (⟨Real.exp ((K : ℝ) * T), Real.exp_nonneg _⟩ : NNReal)
        (fun x : langevinStayingSet V w T R => langevinSolution V w x T) := by
  obtain ⟨K, hK⟩ := exists_gradient_lipschitz_closedBall hV R
  refine ⟨K, fun w hw T hT => AntilipschitzWith.of_le_mul_dist ?_⟩
  intro x y
  change dist (x : E) (y : E) ≤ Real.exp ((K : ℝ) * T) *
    dist (langevinSolution V w x T) (langevinSolution V w y T)
  simp only [dist_eq_norm]
  exact langevin_same_noise_inverse_bound hV hT
    (langevinSolution_isLangevinPathOn hV rate hrate hHess hw x hT)
    (langevinSolution_isLangevinPathOn hV rate hrate hHess hw y hT) hK x.property y.property

/-- The localization set is genuinely closed, by actual continuous dependence
on the initial state at every nonnegative evaluation time. -/
theorem isClosed_langevinStayingSet [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w : ℝ → E} (hw : Continuous w) (T R : ℝ) :
    IsClosed (langevinStayingSet V w T R) := by
  let wc : C(ℝ, E) := ⟨w, hw⟩
  have heq : langevinStayingSet V w T R =
      ⋂ s : Icc 0 T, (fun x : E => langevinSolution V w x s) ⁻¹' closedBall (0 : E) R := by
    ext x
    simp only [langevinStayingSet, MapsTo, mem_ofPred_eq, mem_iInter, mem_preimage, Subtype.forall]
  rw [heq]
  apply isClosed_iInter
  intro s
  have hc : Continuous (fun x : E => langevinSolution V w x s) :=
    (langevinSolution_evaluation_continuous hV rate hrate hHess s.property.1).comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : E => wc)))
  exact isClosed_closedBall.preimage hc

end CutoffRigidity
