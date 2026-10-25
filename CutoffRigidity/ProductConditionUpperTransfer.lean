module
public import CutoffRigidity.ProductConditionAsymptotics

/-! # Actual information-profile transfer after the mixing window

These composition lemmas combine a finite earlier entropy bound with the
proved diffusion estimates. The finite earlier bound is supplied by the
separate genuine Salez window theorem in the final source application.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem curvedEntropyProfile_decay_bound (D : CurvedLangevinData Ω d) (hd : 0 < d)
    (S : Set E) (s t M : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (hM : curvedEntropyProfile D S s ≤ ENNReal.ofReal M) :
    curvedEntropyProfile D S t ≤ ENNReal.ofReal (M*Real.exp (-2*D.curvature*(t-s))) := by
  apply (curvedEntropyProfile_le_of_le D hd S s t hs hst).trans
  have hh := mul_le_mul_of_nonneg_left hM
    (show (0:ENNReal) ≤ ENNReal.ofReal (Real.exp (-2*D.curvature*(t-s))) from bot_le)
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)] at hh
  simpa only [mul_comm] using hh

theorem curvedEntropyProfiles_tendsto_zero_of_uniform_earlier_bound
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    (D : ∀ n : ℕ, CurvedLangevinData (Ξ n) n)
    (S : ∀ n : ℕ, Set (EuclideanSpace ℝ (Fin n))) (s t : ℕ → ℝ) (M : ℝ)
    (hs : ∀ᶠ n in atTop, 0 ≤ s n) (hst : ∀ᶠ n in atTop, s n ≤ t n)
    (hM : ∀ᶠ n in atTop, curvedEntropyProfile (D n) (S n) (s n) ≤ ENNReal.ofReal M)
    (hgap : Tendsto (fun n => (D n).curvature*(t n-s n)) atTop atTop) :
    Tendsto (fun n => curvedEntropyProfile (D n) (S n) (t n)) atTop (𝓝 0) := by
  have hlim := productCondition_exp_decay hgap 2 M (by norm_num)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [hs,hst,hM,eventually_ge_atTop 1] with n hsn hstn hMn hn
  simpa only [mul_assoc] using curvedEntropyProfile_decay_bound (D n) (by omega) (S n) (s n) (t n) M hsn hstn hMn

theorem curvedFisherProfile_bound_of_earlier_entropy
    (D : CurvedLangevinData Ω d) (S : Set E) (s t M : ℝ) (hs : 0 ≤ s) (hst : s < t)
    (hM : curvedEntropyProfile D S s ≤ ENNReal.ofReal M) :
    curvedFisherProfile D S t ≤ ENNReal.ofReal (M/(t-s)) := by
  have hh := curvedFisherProfile_add_le_entropy_div D S s (t-s) hs (sub_pos.mpr hst)
  rw [add_sub_cancel] at hh
  apply hh.trans
  rw [ENNReal.ofReal_div_of_pos (sub_pos.mpr hst),div_eq_mul_inv,div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hM (show (0:ENNReal) ≤ (ENNReal.ofReal (t-s))⁻¹ from bot_le)

theorem productCondition_fisher_after_of_window_bound
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    (D : ∀ n : ℕ, CurvedLangevinData (Ξ n) n)
    (S : ∀ n : ℕ, Set (EuclideanSpace ℝ (Fin n)))
    (η ε M : ℝ) (hε : 0 < ε)
    (ht0 : Tendsto (fun n => curvedCriticalTime (D n) (S n) η) atTop atTop)
    (hM : ∀ᶠ n in atTop, curvedEntropyProfile (D n) (S n)
      ((1+ε/2)*curvedCriticalTime (D n) (S n) η) ≤ ENNReal.ofReal M) :
    Tendsto (fun n => curvedFisherProfile (D n) (S n)
      ((1+ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 0) := by
  have hlim := productCondition_reciprocal_time_decay ht0 (ε/2) M (by positivity)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [hM,ht0.eventually (eventually_gt_atTop (0:ℝ))] with n hMn hn
  have hs : 0 ≤ (1+ε/2)*curvedCriticalTime (D n) (S n) η := by positivity
  have hst : (1+ε/2)*curvedCriticalTime (D n) (S n) η < (1+ε)*curvedCriticalTime (D n) (S n) η := by nlinarith
  have hh := curvedFisherProfile_bound_of_earlier_entropy (D n) (S n)
    ((1+ε/2)*curvedCriticalTime (D n) (S n) η) ((1+ε)*curvedCriticalTime (D n) (S n) η) M hs hst hMn
  have he : (1+ε)*curvedCriticalTime (D n) (S n) η -
      (1+ε/2)*curvedCriticalTime (D n) (S n) η = (ε/2)*curvedCriticalTime (D n) (S n) η := by ring
  rw [he] at hh
  exact hh

end CutoffRigidity
