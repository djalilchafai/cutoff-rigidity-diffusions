module
public import CutoffRigidity.LangevinSalezWindow
public import CutoffRigidity.ProductConditionUpperTransfer

/-! # Actual information cutoffs from the curvature product condition

The critical time is the genuine worst-state TV threshold infimum.
Salez's derived entropy window, actual entropy contraction and Pinsker give
both TV cutoffs and the entropy upper cutoff. All time shifts are the ones
in the written source argument; strict post-threshold times avoid assuming
threshold attainment for an arbitrary initial set.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def productAfterEntropyConstant (η ε : ℝ) : ℝ :=
  1/(1-η)+2/((1-η)^2*Real.log ((1+ε/2)/(1+ε/4)))

@[expose] noncomputable def productBeforeEntropyConstant (δ ε : ℝ) : ℝ :=
  1/δ+2/(δ^2*Real.log ((1-ε/2)/(1-ε)))

set_option maxHeartbeats 650000 in
/-- The genuine uniform finite entropy input just after the actual mixing
threshold; its constant depends only on the two fixed precision parameters. -/
theorem curvedEntropyProfile_after_window_bound
    (D : CurvedLangevinData Ω d) (S : Set E) (hS : S.Nonempty)
    (η ε : ℝ) (hη : 0 < η) (hη1 : η < 1) (hε : 0 < ε)
    (hfin : curvedMixingTime D S η ≠ ⊤) (ht0 : 0 < curvedCriticalTime D S η) :
    curvedEntropyProfile D S ((1+ε/2)*curvedCriticalTime D S η) ≤
      ENNReal.ofReal (productAfterEntropyConstant η ε) := by
  let t0 := curvedCriticalTime D S η
  let a := (1+ε/4)*t0
  let b := (1+ε/2)*t0
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a < b := by dsimp [a,b]; nlinarith
  have hta : t0 < a := by dsimp [a]; nlinarith
  have hTV := curvedTVProfile_le_after_mixing D S hS η a hfin hta
  have hh := curvedEntropyProfile_window_bound D S hS a b η ha hab hη hη1 hTV
  have hr : b/a=(1+ε/2)/(1+ε/4) := by
    dsimp [a,b]
    rw [mul_div_mul_right _ _ ht0.ne']
  rw [hr] at hh
  exact hh

theorem productCondition_entropy_after_cutoff
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    (D : ∀ n : ℕ, CurvedLangevinData (Ξ n) n)
    (S : ∀ n : ℕ, Set (EuclideanSpace ℝ (Fin n))) (hS : ∀ n, (S n).Nonempty)
    (η ε : ℝ) (hη : 0 < η) (hη1 : η < 1) (hε : 0 < ε)
    (hfinite : ∀ᶠ n in atTop, curvedMixingTime (D n) (S n) η < ⊤)
    (hprod : Tendsto (fun n => (D n).curvature*curvedCriticalTime (D n) (S n) η) atTop atTop) :
    Tendsto (fun n => curvedEntropyProfile (D n) (S n)
      ((1+ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 0) := by
  apply curvedEntropyProfiles_tendsto_zero_of_uniform_earlier_bound D S
    (fun n => (1+ε/2)*curvedCriticalTime (D n) (S n) η)
    (fun n => (1+ε)*curvedCriticalTime (D n) (S n) η) (productAfterEntropyConstant η ε)
  · exact Eventually.of_forall (fun n => mul_nonneg (by positivity) ENNReal.toReal_nonneg)
  · exact Eventually.of_forall (fun n => by
      have hh : 0 ≤ curvedCriticalTime (D n) (S n) η := ENNReal.toReal_nonneg
      nlinarith)
  · filter_upwards [hfinite,productCondition_criticalTime_eventually_pos D S η hprod] with n hn ht
    exact curvedEntropyProfile_after_window_bound (D n) (S n) (hS n) η ε hη hη1 hε hn.ne ht
  · have hh := hprod.const_mul_atTop (by positivity : 0 < ε/2)
    convert! hh using 1
    funext n
    ring

theorem productCondition_totalVariation_after_cutoff
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    (D : ∀ n : ℕ, CurvedLangevinData (Ξ n) n)
    (S : ∀ n : ℕ, Set (EuclideanSpace ℝ (Fin n))) (hS : ∀ n, (S n).Nonempty)
    (η ε : ℝ) (hη : 0 < η) (hη1 : η < 1) (hε : 0 < ε)
    (hfinite : ∀ᶠ n in atTop, curvedMixingTime (D n) (S n) η < ⊤)
    (hprod : Tendsto (fun n => (D n).curvature*curvedCriticalTime (D n) (S n) η) atTop atTop) :
    Tendsto (fun n => curvedTVProfile (D n) (S n)
      ((1+ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 0) :=
  curvedTVProfile_tendsto_zero_of_entropy D S hS _
    (productCondition_entropy_after_cutoff D S hS η ε hη hη1 hε hfinite hprod)

set_option maxHeartbeats 650000 in
/-- The written pre-mixing contradiction: a TV bound away from one would
force entropy below the actual defining mixing threshold at an earlier time. -/
theorem curvedTVProfile_before_gt_of_small_entropy_budget
    (D : CurvedLangevinData Ω d) (hd : 0 < d) (S : Set E) (hS : S.Nonempty)
    (η ε δ : ℝ) (hη : 0 < η) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfin : curvedMixingTime D S η ≠ ⊤) (ht0 : 0 < curvedCriticalTime D S η)
    (hbudget : ENNReal.ofReal (productBeforeEntropyConstant δ ε *
      Real.exp (-(ε/2)*(D.curvature*curvedCriticalTime D S η))) < ENNReal.ofReal (2*η^2)) :
    1-δ < curvedTVProfile D S ((1-ε)*curvedCriticalTime D S η) := by
  by_contra hnot
  have hTV := le_of_not_gt hnot
  let t0 := curvedCriticalTime D S η
  let a := (1-ε)*t0
  let b := (1-ε/2)*t0
  let c := (1-ε/4)*t0
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a < b := by dsimp [a,b]; nlinarith
  have hbc : b ≤ c := by dsimp [b,c]; nlinarith
  have hb : 0 ≤ b := ha.le.trans hab.le
  have hc : 0 ≤ c := hb.trans hbc
  have hct : c < t0 := by dsimp [c]; nlinarith
  have hwindow := curvedEntropyProfile_window_bound D S hS a b (1-δ) ha hab (sub_pos.mpr hδ1) (by linarith) hTV
  have hr : b/a=(1-ε/2)/(1-ε) := by
    dsimp [a,b]
    rw [mul_div_mul_right _ _ ht0.ne']
  rw [hr,sub_sub_cancel] at hwindow
  have hwindow' : curvedEntropyProfile D S b ≤ ENNReal.ofReal (productBeforeEntropyConstant δ ε) := hwindow
  have hupper := curvedEntropyProfile_decay_bound D hd S b c (productBeforeEntropyConstant δ ε) hb hbc hwindow'
  have he : -2*D.curvature*(c-b)=-(ε/2)*(D.curvature*t0) := by dsimp [b,c]; ring
  rw [he] at hupper
  have hTVc := curvedTVProfile_gt_before_mixing D S η c hfin hc hct
  have hlower := curvedEntropyProfile_ge_of_tv_ge D S hS c η hη.le hTVc.le
  exact not_lt_of_ge (hlower.trans hupper) hbudget

theorem productCondition_totalVariation_before_threshold
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    (D : ∀ n : ℕ, CurvedLangevinData (Ξ n) n)
    (S : ∀ n : ℕ, Set (EuclideanSpace ℝ (Fin n))) (hS : ∀ n, (S n).Nonempty)
    (η ε δ : ℝ) (hη : 0 < η) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfinite : ∀ᶠ n in atTop, curvedMixingTime (D n) (S n) η < ⊤)
    (hprod : Tendsto (fun n => (D n).curvature*curvedCriticalTime (D n) (S n) η) atTop atTop) :
    ∀ᶠ n in atTop, 1-δ < curvedTVProfile (D n) (S n)
      ((1-ε)*curvedCriticalTime (D n) (S n) η) := by
  have hlim := productCondition_exp_decay hprod (ε/2) (productBeforeEntropyConstant δ ε) (by positivity)
  have hp : (0:ENNReal) < ENNReal.ofReal (2*η^2) := ENNReal.ofReal_pos.mpr (by positivity)
  filter_upwards [hfinite,productCondition_criticalTime_eventually_pos D S η hprod,
    hlim.eventually (eventually_lt_nhds hp),eventually_ge_atTop 1] with n hfin ht hb hn
  exact curvedTVProfile_before_gt_of_small_entropy_budget (D n) (by omega) (S n) (hS n) η ε δ hη hε hε1 hδ hδ1 hfin.ne ht hb

theorem productCondition_totalVariation_before_cutoff
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    (D : ∀ n : ℕ, CurvedLangevinData (Ξ n) n)
    (S : ∀ n : ℕ, Set (EuclideanSpace ℝ (Fin n))) (hS : ∀ n, (S n).Nonempty)
    (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) (hε1 : ε < 1)
    (hfinite : ∀ᶠ n in atTop, curvedMixingTime (D n) (S n) η < ⊤)
    (hprod : Tendsto (fun n => (D n).curvature*curvedCriticalTime (D n) (S n) η) atTop atTop) :
    Tendsto (fun n => curvedTVProfile (D n) (S n)
      ((1-ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro q hq
    by_cases hq0 : q < 0
    · exact Eventually.of_forall (fun n => hq0.trans_le (curvedTVProfile_nonneg (D n) (hS n) _))
    · have hq0' : 0 ≤ q := le_of_not_gt hq0
      have hδ : 0 < (1-q)/2 := by linarith
      have hδ1 : (1-q)/2 < 1 := by linarith
      filter_upwards [productCondition_totalVariation_before_threshold D S hS η ε ((1-q)/2) hη hε hε1 hδ hδ1 hfinite hprod]
        with n hn
      linarith
  · intro q hq
    exact Eventually.of_forall (fun n => (curvedTVProfile_le_one (D n) (hS n) _).trans_lt hq)

theorem productCondition_fisher_after_cutoff
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    (D : ∀ n : ℕ, CurvedLangevinData (Ξ n) n)
    (S : ∀ n : ℕ, Set (EuclideanSpace ℝ (Fin n))) (hS : ∀ n, (S n).Nonempty)
    (η ε : ℝ) (hη : 0 < η) (hη1 : η < 1) (hε : 0 < ε)
    (hfinite : ∀ᶠ n in atTop, curvedMixingTime (D n) (S n) η < ⊤)
    (ht0 : Tendsto (fun n => curvedCriticalTime (D n) (S n) η) atTop atTop) :
    Tendsto (fun n => curvedFisherProfile (D n) (S n)
      ((1+ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 0) := by
  apply productCondition_fisher_after_of_window_bound D S η ε (productAfterEntropyConstant η ε) hε ht0
  filter_upwards [hfinite,ht0.eventually (eventually_gt_atTop (0:ℝ))] with n hn ht
  exact curvedEntropyProfile_after_window_bound (D n) (S n) (hS n) η ε hη hη1 hε hn.ne ht

end CutoffRigidity
