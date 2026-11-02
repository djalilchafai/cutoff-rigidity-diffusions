module

public import Mathlib
public import CutoffRigidity.Extra.Rothaus13

/-! # Rothaus remark (stage 14): Poincaré inequality on finite irreducible spaces -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace CutoffRigidity.Rothaus

section Finite

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] (μ : Measure X)
  [IsProbabilityMeasure μ]

/-- Poincaré inequality for the finite Dirichlet form under irreducibility. -/
theorem finite_PI (w : X → X → ℝ) (hw : ∀ x y, 0 ≤ w x y) (hπ : ∀ x, 0 < μ.real {x})
    (hconn : ∀ f : X → ℝ, ∑ x, ∑ y, w x y * (f x - f y) ^ 2 = 0 → ∀ x y, f x = f y) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ f : X → ℝ, variance f μ ≤ P * ∑ x, ∑ y, w x y * (f x - f y) ^ 2 := by
  set π : X → ℝ := fun x => μ.real {x} with hπdef
  have hsum : ∑ x, π x = 1 := sum_real_singleton μ
  set E : (X → ℝ) → ℝ := fun f => ∑ x, ∑ y, w x y * (f x - f y) ^ 2 with hE
  have hE0 : ∀ f, 0 ≤ E f := fun f =>
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => mul_nonneg (hw x y) (sq_nonneg _)
  have hEc : Continuous E := by
    refine continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun y _ => ?_
    exact continuous_const.mul (((continuous_apply x).sub (continuous_apply y)).pow 2)
  set S : Set (X → ℝ) := {f | ∑ x, π x * f x = 0 ∧ ∑ x, π x * f x ^ 2 = 1} with hS
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have c1 : Continuous fun f : X → ℝ => ∑ x, π x * f x :=
        continuous_finsetSum _ fun x _ => continuous_const.mul (continuous_apply x)
      have c2 : Continuous fun f : X → ℝ => ∑ x, π x * f x ^ 2 :=
        continuous_finsetSum _ fun x _ => continuous_const.mul ((continuous_apply x).pow 2)
      exact (isClosed_eq c1 continuous_const).inter (isClosed_eq c2 continuous_const)
    · rw [isBounded_iff_forall_norm_le]
      refine ⟨∑ x, (1 + 1 / π x), fun f hf => ?_⟩
      rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun x _ => by have := hπ x; positivity)]
      intro x
      have h1 : π x * f x ^ 2 ≤ 1 := by
        rw [← hf.2]
        exact Finset.single_le_sum (f := fun y => π y * f y ^ 2) (fun y _ => mul_nonneg (hπ y).le (sq_nonneg _))
          (Finset.mem_univ x)
      have h2 : f x ^ 2 ≤ 1 / π x := by
        rw [le_div_iff₀ (hπ x)]; linarith
      have h3 : ‖f x‖ ≤ 1 + 1 / π x := by
        rw [Real.norm_eq_abs]
        nlinarith [sq_abs (f x), abs_nonneg (f x), sq_nonneg (|f x| - 1)]
      exact h3.trans (Finset.single_le_sum (f := fun y => 1 + 1 / π y)
        (fun y _ => by have := hπ y; positivity) (Finset.mem_univ x))
  have key : ∀ f : X → ℝ, 0 < variance f μ → ∃ g ∈ S, E f = variance f μ * E g := by
    intro f hv
    set v := variance f μ with hvdef
    obtain ⟨m, hm⟩ : ∃ m, m = ∑ x, π x * f x := ⟨_, rfl⟩
    have hvf : v = ∑ x, π x * f x ^ 2 - m ^ 2 := by rw [hvdef, variance_finite μ f, hm]
    have hv2 : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv.le
    refine ⟨(1 / Real.sqrt v) • fun x => f x + -m, ⟨?_, ?_⟩, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      have e : ∀ x, π x * (1 / Real.sqrt v * (f x + -m)) =
          1 / Real.sqrt v * (π x * f x) - 1 / Real.sqrt v * m * π x := fun x => by ring
      simp_rw [e]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hm, hsum]; ring
    · simp only [Pi.smul_apply, smul_eq_mul]
      have e : ∀ x, π x * (1 / Real.sqrt v * (f x + -m)) ^ 2 =
          (1 / Real.sqrt v) ^ 2 * (π x * f x ^ 2) - 2 * (1 / Real.sqrt v) ^ 2 * m * (π x * f x)
            + (1 / Real.sqrt v) ^ 2 * m ^ 2 * π x := fun x => by ring
      simp_rw [e]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        ← hm, hsum, div_pow, hv2]
      field_simp
      linarith
    · have h1 : E ((1 / Real.sqrt v) • fun x => f x + -m) = (1 / Real.sqrt v) ^ 2 * E f := by
        have := (finiteForm μ w hw).E_smul (1 / Real.sqrt v) (fun x => f x + -m) trivial
        simp only [finiteForm_E] at this
        have h2 := (finiteForm μ w hw).E_add_const (-m) f trivial
        simp only [finiteForm_E] at h2
        rw [hE]; simp only
        rw [this, h2]
      rw [h1, div_pow, Real.sq_sqrt hv.le]
      field_simp
  by_cases hSne : S.Nonempty
  · obtain ⟨f₀, hf₀, hmin⟩ := hSc.exists_isMinOn hSne hEc.continuousOn
    have hne : Nonempty X := by
      by_contra hX
      rw [not_nonempty_iff] at hX
      simp at hsum
    have hlam : 0 < E f₀ := by
      rcases (hE0 f₀).eq_or_lt with h0 | h0
      · exfalso
        have hc := hconn f₀ h0.symm
        obtain ⟨x₀⟩ := hne
        have e1 : ∑ x, π x * f₀ x = f₀ x₀ := by
          have : ∀ x, π x * f₀ x = π x * f₀ x₀ := fun x => by rw [hc x x₀]
          simp_rw [this]; rw [← Finset.sum_mul, hsum]; simp
        have e2 : f₀ x₀ = 0 := by rw [← e1]; exact hf₀.1
        have e3 : ∑ x, π x * f₀ x ^ 2 = 0 := by
          have : ∀ x, π x * f₀ x ^ 2 = 0 := fun x => by rw [hc x x₀, e2]; simp
          simp_rw [this]; simp
        linarith [hf₀.2]
      · exact h0
    refine ⟨1 / E f₀, by positivity, fun f => ?_⟩
    rcases (variance_nonneg f μ).eq_or_lt with hv | hv
    · rw [← hv]; exact mul_nonneg (by positivity) (hE0 f)
    · obtain ⟨g, hg, hEg⟩ := key f hv
      have h1 : E f₀ ≤ E g := hmin hg
      show variance f μ ≤ 1 / E f₀ * E f
      rw [hEg, one_div_mul_eq_div, le_div_iff₀ hlam]
      nlinarith
  · refine ⟨0, le_rfl, fun f => ?_⟩
    rcases (variance_nonneg f μ).eq_or_lt with hv | hv
    · rw [← hv]; simp
    · obtain ⟨g, hg, -⟩ := key f hv
      exact absurd ⟨g, hg⟩ hSne

end Finite

end CutoffRigidity.Rothaus
