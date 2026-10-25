module
public import CutoffRigidity.ProductConditionTheorem

/-! # The unsquared Wasserstein distance cutoff

The supremum is taken over genuine square roots of coupling costs. The
positive-power order isomorphism proves equality with the square root of
the already controlled squared-distance supremum, including infinite values.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Set
open scoped Topology ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

@[expose] noncomputable def curvedWassersteinProfile
    (D : CurvedLangevinData Ω d) (S : Set (EuclideanSpace ℝ (Fin d))) (t : ℝ) : ENNReal :=
  ⨆ x : S, (squaredWasserstein (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
    (gibbsMeasure volume D.potential)) ^ (1/2:ℝ)

theorem curvedWassersteinProfile_eq_rpow
    (D : CurvedLangevinData Ω d) (S : Set (EuclideanSpace ℝ (Fin d))) (t : ℝ) :
    curvedWassersteinProfile D S t = curvedWassersteinSqProfile D S t ^ (1/2:ℝ) := by
  exact ((ENNReal.orderIsoRpow (1/2:ℝ) (by norm_num)).map_iSup
    (fun x : S => squaredWasserstein (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
      (gibbsMeasure volume D.potential))).symm

/-- The source W₂ cutoff in its literal unsquared form. -/
theorem curvature_product_condition_wasserstein_distance
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    (D : ∀ n : ℕ, CurvedLangevinData (Ξ n) n)
    (S : ∀ n : ℕ, Set (EuclideanSpace ℝ (Fin n))) (hS : ∀ n, (S n).Nonempty)
    (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hfinite : ∀ᶠ n in atTop, curvedMixingTime (D n) (S n) η < ⊤)
    (hprod : Tendsto (fun n => (D n).curvature*curvedCriticalTime (D n) (S n) η) atTop atTop)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).curvature) atTop)
    (ht0 : Tendsto (fun n => curvedCriticalTime (D n) (S n) η) atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      Tendsto (fun n => curvedWassersteinProfile (D n) (S n) ((1-ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 ⊤) ∧
      Tendsto (fun n => curvedWassersteinProfile (D n) (S n) ((1+ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 0) := by
  intro ε hε hε1
  obtain ⟨hb,ha⟩ := curvature_product_condition_wasserstein D S hS η hη hη1 hfinite hprod hliminf ht0 ε hε hε1
  constructor
  · simpa only [curvedWassersteinProfile_eq_rpow,ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ)<1/2)]
      using hb.ennrpow_const (1/2:ℝ)
  · simpa only [curvedWassersteinProfile_eq_rpow,ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ)<1/2)]
      using ha.ennrpow_const (1/2:ℝ)

end CutoffRigidity
