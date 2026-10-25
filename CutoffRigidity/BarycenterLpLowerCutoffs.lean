module
public import CutoffRigidity.EntropyLpBound
public import CutoffRigidity.BarycenterLpCutoffs

/-! # Genuine Lᵖ lower cutoffs for every p>1

Actual entropy divergence forces divergence of every finite density Lᵖ
error above one, through the proved RN power bound.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem tendsto_ennreal_top_of_power_budget
    {H L : ℕ → ENNReal} {C : ENNReal} (hC : C ≠ ⊤) {p : ℝ} (hp : 0 ≤ p)
    (hH : Tendsto H atTop (𝓝 ⊤))
    (hBound : ∀ n, H n ≤ C*(L n+1)^p+1) : Tendsto L atTop (𝓝 ⊤) := by
  apply ENNReal.tendsto_nhds_top
  intro N
  have hFin : C*((N:ENNReal)+1)^p+1 < ⊤ := by
    apply ENNReal.add_lt_top.mpr
    exact ⟨ENNReal.mul_lt_top hC.lt_top
      (ENNReal.rpow_ne_top_of_nonneg hp (by finiteness)).lt_top,by norm_num⟩
  filter_upwards [(tendsto_order.mp hH).1 _ hFin] with n hn
  by_contra hh
  have hLn : L n ≤ (N:ENNReal) := le_of_not_gt hh
  have hb : H n ≤ C*((N:ENNReal)+1)^p+1 := (hBound n).trans
    (add_le_add (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (add_le_add hLn le_rfl) hp)) le_rfl)
  exact (not_lt_of_ge hb) hn

/-- Actual entropy profile control by any actual relative Lᵖ profile. -/
theorem projectedSetKL_le_spectralSetLp_rpow_add
    (D : SpectralInformationLowerData Ω d) (S : Set E) (t : ℝ) {p : ℝ} (hp : 1 < p) :
    projectedSetKL (spectralInformationToAffine D) S t ≤
      ENNReal.ofReal (1/(p-1))*(spectralSetLp D S (ENNReal.ofReal p) t+1)^p+1 := by
  let := D.probability
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.rate D.rate_pos.le D.hessian t.toNNReal
  apply iSup_le
  intro x
  change InformationTheory.klDiv (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
    (gibbsMeasure volume D.potential) ≤ _
  apply (klDiv_le_relativeLpDistance_rpow_add _ _ hp).trans
  apply add_le_add _ le_rfl
  apply mul_le_mul' le_rfl
  apply ENNReal.rpow_le_rpow _ (zero_lt_one.trans hp).le
  apply add_le_add _ le_rfl
  exact le_iSup (fun y : S => relativeLpDistance
    (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal y)
    (gibbsMeasure volume D.potential) (ENNReal.ofReal p)) x

/-- Every finite exponent above one has the actual mean-ball lower cutoff. -/
theorem meanBall_Lp_before_cutoff_gt_one
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε p : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1) (hp : 1 < p)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n => meanBallLp (D n) c (ENNReal.ofReal p)
      ((1-ε)*criticalTime n (D n).rate)) atTop (𝓝 ⊤) := by
  apply tendsto_ennreal_top_of_power_budget ENNReal.ofReal_ne_top (zero_lt_one.trans hp).le
    (meanBall_entropy_before_cutoff D hc hε hε1 hliminf)
  intro n
  exact projectedSetKL_le_spectralSetLp_rpow_add (D n) _ _ hp

/-- The identical actual lower transfer on interaction cubes. -/
theorem convexCube_Lp_before_cutoff_gt_one
    (D : ∀ n : ℕ, ConvexInteractionCubeData Ω n) {c ε p : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1) (hp : 1 < p)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n => convexCubeLp (D n) c (ENNReal.ofReal p)
      ((1-ε)*criticalTime n (D n).rate)) atTop (𝓝 ⊤) := by
  apply tendsto_ennreal_top_of_power_budget ENNReal.ofReal_ne_top (zero_lt_one.trans hp).le
    (convexCube_entropy_before_cutoff D hc hε hε1 hliminf)
  intro n
  exact projectedSetKL_le_spectralSetLp_rpow_add (cubeSpectralData (D n)) _ _ hp

end CutoffRigidity
