module
public import CutoffRigidity.ProductConditionProfiles

/-! # The written entropy lower bound under the curvature product condition

The true threshold infimum supplies the intermediate TV lower bound.
Genuine Pinsker and actual entropy contraction amplify it backwards to an
exponentially diverging entropy profile. No cutoff estimate is a premise.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 650000 in
theorem curvedEntropyProfile_before_mixing_lower
    (D : CurvedLangevinData Ω d) (hd : 0 < d) (S : Set E) (hS : S.Nonempty)
    (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) (hε1 : ε < 1)
    (hfin : curvedMixingTime D S η ≠ ⊤) (ht0 : 0 < curvedCriticalTime D S η) :
    ENNReal.ofReal (2*η^2*Real.exp (ε*D.curvature*curvedCriticalTime D S η)) ≤
      curvedEntropyProfile D S ((1-ε)*curvedCriticalTime D S η) := by
  let t0 := curvedCriticalTime D S η
  let a := (1-ε)*t0
  let b := (1-ε/2)*t0
  have ha : 0 ≤ a := by dsimp [a,t0]; positivity
  have hab : a ≤ b := by dsimp [a,b]; nlinarith
  have hb0 : 0 ≤ b := by dsimp [b]; nlinarith
  have hbt : b < t0 := by dsimp [b]; nlinarith
  have hTV := curvedTVProfile_gt_before_mixing D S η b hfin hb0 hbt
  have hLower := curvedEntropyProfile_ge_of_tv_ge D S hS b η hη.le hTV.le
  have hContract := curvedEntropyProfile_le_of_le D hd S a b ha hab
  have hBound := hLower.trans hContract
  have htime : -2*D.curvature*(b-a) = -(ε*D.curvature*t0) := by dsimp [a,b]; ring
  rw [htime] at hBound
  have hh := mul_le_mul_of_nonneg_left hBound (show (0:ENNReal) ≤ ENNReal.ofReal (Real.exp (ε*D.curvature*t0)) from bot_le)
  have hcancel : ENNReal.ofReal (Real.exp (ε*D.curvature*t0))*
      ENNReal.ofReal (Real.exp (-(ε*D.curvature*t0)))=1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),← Real.exp_add]
    simp
  rw [← mul_assoc,hcancel,one_mul] at hh
  convert! hh using 1
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  congr 1
  ring

/-- The source curvature product condition forces the actual critical time
to be positive eventually, even when the curvature varies with dimension. -/
theorem productCondition_criticalTime_eventually_pos
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    (D : ∀ n : ℕ, CurvedLangevinData (Ξ n) n)
    (S : ∀ n : ℕ, Set (EuclideanSpace ℝ (Fin n))) (η : ℝ)
    (hprod : Tendsto (fun n => (D n).curvature*curvedCriticalTime (D n) (S n) η) atTop atTop) :
    ∀ᶠ n in atTop, 0 < curvedCriticalTime (D n) (S n) η := by
  filter_upwards [hprod.eventually (eventually_gt_atTop (0:ℝ))] with n hn
  exact (mul_pos_iff.mp hn).resolve_right (fun h => not_lt_of_ge (D n).curvature_pos.le h.1) |>.2

/-- Actual entropy diverges before the genuine mixing time under exactly
the source curvature product condition. -/
theorem productCondition_entropy_before_cutoff
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    (D : ∀ n : ℕ, CurvedLangevinData (Ξ n) n)
    (S : ∀ n : ℕ, Set (EuclideanSpace ℝ (Fin n))) (hS : ∀ n, (S n).Nonempty)
    (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) (hε1 : ε < 1)
    (hfinite : ∀ᶠ n in atTop, curvedMixingTime (D n) (S n) η < ⊤)
    (hprod : Tendsto (fun n => (D n).curvature*curvedCriticalTime (D n) (S n) η) atTop atTop) :
    Tendsto (fun n => curvedEntropyProfile (D n) (S n)
      ((1-ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 ⊤) := by
  have hscale : Tendsto (fun n => 2*η^2*Real.exp (ε*(D n).curvature*curvedCriticalTime (D n) (S n) η))
      atTop atTop := by
    have hh := Real.tendsto_exp_atTop.comp (hprod.const_mul_atTop hε)
    have hh' := hh.const_mul_atTop (by positivity : 0 < 2*η^2)
    simpa only [Function.comp_def,mul_assoc] using hh'
  have hENN := ENNReal.tendsto_ofReal_atTop.comp hscale
  apply tendsto_nhds_top_mono hENN
  filter_upwards [hfinite,productCondition_criticalTime_eventually_pos D S η hprod,eventually_ge_atTop 1] with n hfin ht hn
  exact curvedEntropyProfile_before_mixing_lower (D n) (by omega) (S n) (hS n) η ε hη hε hε1 hfin.ne ht

end CutoffRigidity
