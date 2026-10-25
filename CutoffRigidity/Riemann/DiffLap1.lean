module

public import CutoffRigidity.Riemann.DiffFrResolvent
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Laplace transform of the semigroup: `R_λ g = ∫₀^∞ e^{-λ s} T_s g ds`

Proof: with `g' = (1+(λ-1)R)⁻¹ g` and `w = R g' = R_λ g`, the function
`Ψ(s) = e^{-λ s} T_s w` is continuous on `[0,∞)`, tends to `0`, and has derivative
`-e^{-λ s} T_s g` for `s > 0`; hence `∫₀^∞ e^{-λ s} T_s g = Ψ(0) = w`.
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped NNReal InnerProductSpace

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

open Cx

namespace FormData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (S : FormData H)

lemma norm_semigroup_apply_le' (t : ℝ≥0) (g : H) : ‖S.semigroup t g‖ ≤ ‖g‖ := by
  simpa using (S.semigroup t).le_of_opNorm_le (S.norm_semigroup_le t) g

lemma integrableOn_laplace {lam : ℝ} (hlam : 0 < lam) (g : H) :
    IntegrableOn (fun s : ℝ => Real.exp (-lam * s) • S.semigroup s.toNNReal g) (Ioi 0) := by
  have hc : Continuous fun s : ℝ => Real.exp (-lam * s) • S.semigroup s.toNNReal g := by
    have h1 : Continuous fun s : ℝ => S.semigroup s.toNNReal g :=
      (S.continuous_semigroup_apply g).comp continuous_real_toNNReal
    fun_prop
  have hint : IntegrableOn (fun s : ℝ => ‖g‖ * Real.exp (-lam * s)) (Ioi 0) := by
    exact (exp_neg_integrableOn_Ioi 0 hlam).const_mul ‖g‖
  refine Integrable.mono' hint hc.aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s _ => ?_)
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
  exact mul_le_mul_of_nonneg_right (S.norm_semigroup_apply_le' _ g) (Real.exp_pos _).le

theorem resolvent_eq_laplace {lam : ℝ} (hlam : 0 < lam) (g : H) :
    S.resolvent lam g = ∫ s in Set.Ioi (0:ℝ), Real.exp (-lam * s) • S.semigroup s.toNNReal g := by
  set g' : H := rcfc (fun r : ℝ => 1 / (1 + (lam - 1) * r)) S.R g with hg'
  have hgg : ((lam - 1) • S.R + 1) g' = g := by
    have := congrArg (fun T : H →L[ℝ] H => T g) (S.M_mul_inv hlam)
    simpa [hg'] using this
  set w : H := S.R g' with hw
  have hwr : S.resolvent lam g = w := by
    rw [S.resolvent_eq_R_mul hlam]; rfl
  have hgw : lam • w + (g' - w) = g := by
    have h : ((lam - 1) • S.R + 1) g' = (lam - 1) • w + g' := by simp [hw]
    rw [← hgg, h]; module
  let Ψ : ℝ → H := fun s => Real.exp (-lam * s) • S.semigroup s.toNNReal w
  have hderiv : ∀ t ∈ Ioi (0:ℝ), HasDerivAt Ψ
      (-(Real.exp (-lam * t) • S.semigroup t.toNNReal g)) t := by
    intro t ht
    have ht' : 0 < t := ht
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-lam * s)) (Real.exp (-lam * t) * (-lam)) t := by
      have := ((hasDerivAt_id t).const_mul (-lam)).exp
      simpa using this
    have h2 := S.hasDerivAt_semigroup ht' g'
    have h3 := h1.smul h2
    convert h3 using 1
    rw [← hgw, map_add, map_sub, ← hw]
    simp only [map_smul, smul_add, smul_neg, smul_sub]
    simp only [mul_comm (Real.exp _) (-lam), smul_smul, neg_mul]
    module
  have hcont : ContinuousWithinAt Ψ (Ici 0) 0 := by
    have h1 : Continuous fun s : ℝ => S.semigroup s.toNNReal w :=
      (S.continuous_semigroup_apply w).comp continuous_real_toNNReal
    exact (by fun_prop : Continuous Ψ).continuousWithinAt
  have hlim : Tendsto Ψ atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : Tendsto (fun s : ℝ => ‖w‖ * Real.exp (-lam * s)) atTop (𝓝 0) := by
      have : Tendsto (fun s : ℝ => Real.exp (-lam * s)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
      simpa using this.const_mul ‖w‖
    refine squeeze_zero (fun _ => norm_nonneg _) (fun s => ?_) hb
    show ‖Real.exp (-lam * s) • S.semigroup s.toNNReal w‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
    exact mul_le_mul_of_nonneg_right (S.norm_semigroup_apply_le' _ w) (Real.exp_pos _).le
  have hint := S.integrableOn_laplace hlam g
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint.neg hlim
  have h0 : Ψ 0 = w := by simp [Ψ, S.semigroup_zero]
  rw [h0, zero_sub, integral_neg] at key
  rw [hwr]
  exact (neg_injective (by simpa using key)).symm

theorem inner_resolvent_eq_laplace {lam : ℝ} (hlam : 0 < lam) (g φ : H) :
    ⟪S.resolvent lam g, φ⟫_ℝ =
      ∫ s in Set.Ioi (0:ℝ), Real.exp (-lam * s) * ⟪S.semigroup s.toNNReal g, φ⟫_ℝ := by
  rw [S.resolvent_eq_laplace hlam g, real_inner_comm, ← integral_inner (S.integrableOn_laplace hlam g)]
  simp [inner_smul_right, real_inner_comm]

end FormData

end CutoffRigidity.Riemann.Diff
