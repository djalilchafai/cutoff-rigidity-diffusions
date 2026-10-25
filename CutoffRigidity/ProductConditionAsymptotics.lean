module
public import CutoffRigidity.ProductConditionEnergyLower

/-! # The written product-condition asymptotic comparisons

Exponential curvature-product decay and reciprocal mixing-time decay are
ordinary scalar limits. Actual Pinsker then passes genuine set entropy
convergence to genuine set TV convergence.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω]

theorem productCondition_exp_decay {p : ℕ → ℝ}
    (hp : Tendsto p atTop atTop) (ε C : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => ENNReal.ofReal (C*Real.exp (-ε*p n))) atTop (𝓝 0) := by
  have hneg := tendsto_neg_atTop_atBot.comp (hp.const_mul_atTop hε)
  have hh := (Real.tendsto_exp_atBot.comp hneg).const_mul C
  have hh' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh
  simpa only [neg_mul,Function.comp_def,mul_zero,ENNReal.ofReal_zero] using hh'

theorem productCondition_reciprocal_time_decay {t : ℕ → ℝ}
    (ht : Tendsto t atTop atTop) (ε C : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => ENNReal.ofReal (C/(ε*t n))) atTop (𝓝 0) := by
  have hh := (tendsto_inv_atTop_zero.comp (ht.const_mul_atTop hε)).const_mul C
  have hh' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh
  simpa only [div_eq_mul_inv,Function.comp_def,mul_zero,ENNReal.ofReal_zero] using hh'

theorem curvedTVProfile_tendsto_zero_of_entropy
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    (D : ∀ n : ℕ, CurvedLangevinData (Ξ n) n)
    (S : ∀ n : ℕ, Set (EuclideanSpace ℝ (Fin n))) (hS : ∀ n, (S n).Nonempty)
    (t : ℕ → ℝ)
    (hKL : Tendsto (fun n => curvedEntropyProfile (D n) (S n) (t n)) atTop (𝓝 0)) :
    Tendsto (fun n => curvedTVProfile (D n) (S n) (t n)) atTop (𝓝 0) := by
  have hfinite : ∀ᶠ n in atTop, curvedEntropyProfile (D n) (S n) (t n) ≠ ⊤ := by
    have he := hKL.eventually (eventually_lt_nhds (by norm_num : (0:ENNReal)<1))
    exact he.mono (fun n hn => ne_top_of_lt hn)
  have hreal := (ENNReal.continuousAt_toReal (by simp : (0:ENNReal) ≠ ⊤)).tendsto.comp hKL
  have hsqrt := (hreal.div_const 2).sqrt
  simp only [ENNReal.toReal_zero,zero_div,Real.sqrt_zero,Function.comp_def] at hsqrt
  apply squeeze_zero' (Eventually.of_forall (fun n => curvedTVProfile_nonneg (D n) (hS n) (t n))) _ hsqrt
  filter_upwards [hfinite] with n hn
  exact curvedTVProfile_le_sqrt_entropy (D n) (S n) (hS n) (t n) hn

end CutoffRigidity
