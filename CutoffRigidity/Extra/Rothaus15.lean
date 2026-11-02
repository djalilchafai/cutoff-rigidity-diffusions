module

public import Mathlib
public import CutoffRigidity.Extra.Rothaus14

/-! # Rothaus remark (stage 15): the discrete Rothaus alternative

For an irreducible finite Dirichlet form on a finite probability space with full support, `Form.Compact` holds, so
`C_LSI > 2 C_PI` implies the existence of an LSI extremal function (discrete version of the Rothaus alternative, cf. Saloff-Coste,
Lectures on finite Markov chains, Th. 2.2.3).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace CutoffRigidity.Rothaus

section Finite

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] (μ : Measure X)
  [IsProbabilityMeasure μ]

theorem finite_compact (w : X → X → ℝ) (hw : ∀ x y, 0 ≤ w x y) (hπ : ∀ x, 0 < μ.real {x})
    (hP : ∃ P : ℝ, 0 ≤ P ∧ ∀ f : X → ℝ, variance f μ ≤ P * ∑ x, ∑ y, w x y * (f x - f y) ^ 2) :
    (finiteForm μ w hw).Compact := by
  obtain ⟨P, hP0, hPI⟩ := hP
  intro B g _ hmean hB
  set E : (X → ℝ) → ℝ := fun f => ∑ x, ∑ y, w x y * (f x - f y) ^ 2 with hE
  have hEc : Continuous E := by
    refine continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun y _ => ?_
    exact continuous_const.mul (((continuous_apply x).sub (continuous_apply y)).pow 2)
  have hB' : ∀ n, E (g n) ≤ B := hB
  -- uniform bound
  have hsq : ∀ n, ∑ x, μ.real {x} * g n x ^ 2 ≤ P * B := by
    intro n
    have h1 := hPI (g n)
    rw [variance_finite μ] at h1
    have h2 : ∑ x, μ.real {x} * g n x = 0 := by rw [← integral_finite]; exact hmean n
    rw [h2] at h1
    have : P * E (g n) ≤ P * B := mul_le_mul_of_nonneg_left (hB' n) hP0
    simp only [hE] at this
    nlinarith
  have hbd : ∀ n x, ‖g n x‖ ≤ 1 + P * B / μ.real {x} := by
    intro n x
    have h1 : μ.real {x} * g n x ^ 2 ≤ P * B := by
      refine le_trans ?_ (hsq n)
      exact Finset.single_le_sum (f := fun y => μ.real {y} * g n y ^ 2)
        (fun y _ => mul_nonneg (hπ y).le (sq_nonneg _)) (Finset.mem_univ x)
    have h2 : g n x ^ 2 ≤ P * B / μ.real {x} := by
      rw [le_div_iff₀ (hπ x)]; linarith
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (g n x), abs_nonneg (g n x), sq_nonneg (|g n x| - 1)]
  have hboundedset : Bornology.IsBounded (Set.range g) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨∑ x, |1 + P * B / μ.real {x}|, ?_⟩
    rintro _ ⟨n, rfl⟩
    rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun x _ => abs_nonneg _)]
    intro x
    refine (hbd n x).trans ?_
    refine le_trans (le_abs_self _) ?_
    exact Finset.single_le_sum (f := fun y => |1 + P * B / μ.real {y}|) (fun y _ => abs_nonneg _)
      (Finset.mem_univ x)
  obtain ⟨h, -, φ, hφ, htend⟩ := tendsto_subseq_of_bounded hboundedset (fun n => Set.mem_range_self n)
  have hpt : ∀ x, Tendsto (fun n => g (φ n) x) atTop (𝓝 (h x)) := fun x => tendsto_pi_nhds.1 htend x
  refine ⟨φ, hφ, h, trivial, ?_, ?_, ?_⟩
  · have : (fun n => ∫ x, (g (φ n) x - h x) ^ 2 ∂μ) = fun n => ∑ x, μ.real {x} * (g (φ n) x - h x) ^ 2 := by
      funext n; rw [integral_finite]
    rw [this]
    have : (0 : ℝ) = ∑ x : X, μ.real {x} * (h x - h x) ^ 2 := by simp
    rw [this]
    exact tendsto_finsetSum _ fun x _ => (tendsto_const_nhds.mul (((hpt x).sub_const (h x)).pow 2))
  · have : (fun n => ∫ x, |Θ (g (φ n) x) - Θ (h x)| ∂μ) =
        fun n => ∑ x, μ.real {x} * |Θ (g (φ n) x) - Θ (h x)| := by
      funext n; rw [integral_finite]
    rw [this]
    have : (0 : ℝ) = ∑ x : X, μ.real {x} * |Θ (h x) - Θ (h x)| := by simp
    rw [this]
    exact tendsto_finsetSum _ fun x _ =>
      (tendsto_const_nhds.mul (((continuous_Θ.tendsto _).comp (hpt x)).sub_const (Θ (h x)) |>.abs))
  · intro b hb
    have h1 : Tendsto (fun n => E (g (φ n))) atTop (𝓝 (E h)) := (hEc.tendsto h).comp htend
    exact le_of_tendsto h1 hb

/-- **Discrete Rothaus alternative** (Saloff-Coste, Th. 2.2.3): on a finite irreducible Dirichlet form, if the optimal
log-Sobolev constant exceeds twice the optimal Poincaré constant, there is an extremal function. -/
theorem finite_rothaus (w : X → X → ℝ) (hw : ∀ x y, 0 ≤ w x y) (hπ : ∀ x, 0 < μ.real {x})
    (hconn : ∀ f : X → ℝ, ∑ x, ∑ y, w x y * (f x - f y) ^ 2 = 0 → ∀ x y, f x = f y)
    (hgt : 2 * (finiteForm μ w hw).optPI < (finiteForm μ w hw).optLSI) :
    ∃ f : X → ℝ, 0 < ∑ x, ∑ y, w x y * (f x - f y) ^ 2 ∧
      CutCur.entropyOf μ (fun x => f x ^ 2) =
        (finiteForm μ w hw).optLSI * ∑ x, ∑ y, w x y * (f x - f y) ^ 2 := by
  have hP := finite_PI μ w hw hπ hconn
  obtain ⟨f, -, h1, h2⟩ := rothaus_alternative (finiteForm μ w hw) (by
    obtain ⟨P, hP0, hP1⟩ := hP
    exact ⟨P, hP0, fun f _ => hP1 f⟩) (finite_compact μ w hw hπ hP) hgt
  exact ⟨f, h1, h2⟩

end Finite

end CutoffRigidity.Rothaus
