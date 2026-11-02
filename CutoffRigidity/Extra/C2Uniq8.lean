module

public import CutoffRigidity.Extra.C2Uniq7
public import CutoffRigidity.Extra.EuclideanDiffusion
public import CutoffRigidity.Paper.ExistsBrownian
public import CutoffRigidity.Paper.CarrierDefs

/-! # `C²` uniqueness, stage 7: `C²` transfer lemmas (Brownian carriers for `C²` convex potentials)

These replace `exists_isLangevin_of_isEuclideanLangevin`, `exists_isLangevin_of_rigid`,
`exists_isRigidSequence_of_K` and `exists_langevinSeq_of_K` when the smoothness clause of
`IsEuclideanLangevinInf` is weakened from `C^∞` to `C²`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutCur

open CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff Manifold

namespace C2U

/-- `IsEuclideanLangevinInf` with `C²` smoothness (same triple as `IsEuclideanLangevinC2` of
`C2Langevin.lean`, restated because that definition is not exposed). -/
def IsEucLangevin2 {d : ℕ} (V : Rd d → ℝ) (Pt : ℝ≥0 → Kernel (Rd d) (Rd d)) : Prop :=
  ContDiff ℝ 2 V ∧ IsProbabilityMeasure (gibbs V) ∧ IsEuclideanDiffusion V Pt

/-- `IsRigidSequenceKInf` with `C²` smoothness. -/
def IsRigidSeqK2 (V : ∀ n, Rd n → ℝ) (Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)) : Prop :=
  (∀ n, 0 < n → IsEucLangevin2 (V n) (Pt n) ∧ RigidCurvature (V n)) ∧
    0 < liminf (fun n => ENNReal.ofReal (spectralGap (V n))) atTop

theorem IsEucLangevin2.of_smooth {d : ℕ} {V : Rd d → ℝ} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (h : IsEuclideanLangevinInf V Pt) : IsEucLangevin2 V Pt :=
  ⟨h.1.of_le (by norm_cast), h.2.1, h.2.2⟩

/-- **`C²` transfer lemma.** -/
theorem exists_isLangevin_of_C2 {d : ℕ} {V : Rd d → ℝ} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (hL : IsEucLangevin2 V Pt) (hHess : ∀ x z : Rd d, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (B : ℝ≥0 → Ω → Rd d) (P : Measure Ω)
      (X : Rd d → ℝ≥0 → Ω → Rd d),
      IsProbabilityMeasure P ∧ IsLangevin V B P X ∧
        ∀ (t : ℝ≥0) (x₀ : Rd d), P.map (X x₀ t) = Pt t x₀ := by
  obtain ⟨Ω, hΩ, P, B, hP, hB⟩ := CutoffRigidity.Paper.exists_stdBrownian d
  have hB' : IsEuclideanBrownian B P := CutoffRigidity.Paper.isStdBrownian_iff.1 hB
  have hH : ∀ x z : Rd d, (0 : ℝ) * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z := by
    intro x z; simpa using hHess x z
  have hc : ConvexOn ℝ univ V := CutoffRigidity.NoBm.convexOn_univ_of_hessian_nonneg hL.1 hHess
  refine ⟨Ω, hΩ, B, P, fun x₀ => langevinProcess V B x₀, hP, ⟨hL.1, hL.2.1, hB, fun x₀ => ?_⟩,
    fun t x₀ => ?_⟩
  · exact CutoffRigidity.Paper.isLangevinSolution_langevinProcess hB' hL.1 0 le_rfl hH x₀
  · exact (langevinKernel_apply_eq_process_law hB' hL.1 0 le_rfl hH t x₀).symm.trans
      (euclideanDiffusion_unique_convex hL.1 hc hL.2.2
        (isEuclideanDiffusion_langevinKernel hB' hL.1 0 le_rfl hH) t x₀).symm

theorem exists_isLangevin_of_rigid_C2 {d : ℕ} {V : Rd d → ℝ} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (hL : IsEucLangevin2 V Pt) (hR : RigidCurvature V) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (B : ℝ≥0 → Ω → Rd d) (P : Measure Ω)
      (X : Rd d → ℝ≥0 → Ω → Rd d),
      IsProbabilityMeasure P ∧ IsLangevin V B P X ∧
        ∀ (t : ℝ≥0) (x₀ : Rd d), P.map (X x₀ t) = Pt t x₀ :=
  exists_isLangevin_of_C2 hL hR.hess_nonneg

/-- Sequence transfer (rigid sequences, `C²`). -/
theorem exists_isRigidSequence_of_K2 {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : IsRigidSeqK2 V Pt) :
    ∃ (Ω : ℕ → Type) (_ : ∀ n, MeasurableSpace (Ω n)) (B : ∀ n, ℝ≥0 → Ω n → Rd n)
      (P : ∀ n, Measure (Ω n)) (X : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n),
      (∀ n, 0 < n → IsProbabilityMeasure (P n)) ∧ IsRigidSequence V B P X ∧
        ∀ n, 0 < n → ∀ (t : ℝ≥0) (x₀ : Rd n), (P n).map (X n x₀ t) = Pt n t x₀ := by
  classical
  have hn : ∀ n : ℕ, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (B : ℝ≥0 → Ω → Rd n) (P : Measure Ω)
      (X : Rd n → ℝ≥0 → Ω → Rd n), 0 < n → (IsProbabilityMeasure P ∧
        IsLangevin (V n) B P X ∧ ∀ (t : ℝ≥0) (x₀ : Rd n), P.map (X x₀ t) = Pt n t x₀) := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨Ω, hΩ, B, P, X, h1⟩ := exists_isLangevin_of_rigid_C2 (h.1 n hn).1 (h.1 n hn).2
      exact ⟨Ω, hΩ, B, P, X, fun _ => h1⟩
    · exact ⟨Unit, inferInstance, fun _ _ => 0, 0, fun _ _ _ => 0, fun h' => absurd h' hn⟩
  choose Ω hΩ B P X hX using hn
  exact ⟨Ω, hΩ, B, P, X, fun n hn => (hX n hn).1,
    ⟨fun n hn => ⟨(hX n hn).2.1, (h.1 n hn).2⟩, h.2⟩, fun n hn => (hX n hn).2.2⟩

/-- Sequence transfer for sequences that are not necessarily rigid (`C²`). -/
theorem exists_langevinSeq_of_K2 {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : ∀ n, 0 < n → IsEucLangevin2 (V n) (Pt n) ∧
      ∀ x z : Rd n, 0 ≤ fderiv ℝ (fderiv ℝ (V n)) x z z) :
    ∃ (Ω : ℕ → Type) (_ : ∀ n, MeasurableSpace (Ω n)) (B : ∀ n, ℝ≥0 → Ω n → Rd n)
      (P : ∀ n, Measure (Ω n)) (X : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n),
      (∀ n, 0 < n → IsLangevin (V n) (B n) (P n) (X n)) ∧
        ∀ n, 0 < n → ∀ (t : ℝ≥0) (x₀ : Rd n), (P n).map (X n x₀ t) = Pt n t x₀ := by
  classical
  have hn : ∀ n : ℕ, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (B : ℝ≥0 → Ω → Rd n) (P : Measure Ω)
      (X : Rd n → ℝ≥0 → Ω → Rd n), 0 < n → (IsLangevin (V n) B P X ∧
        ∀ (t : ℝ≥0) (x₀ : Rd n), P.map (X x₀ t) = Pt n t x₀) := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨Ω, hΩ, B, P, X, -, h1, h2⟩ := exists_isLangevin_of_C2 (h n hn).1 (h n hn).2
      exact ⟨Ω, hΩ, B, P, X, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨Unit, inferInstance, fun _ _ => 0, 0, fun _ _ _ => 0, fun h' => absurd h' hn⟩
  choose Ω hΩ B P X hX using hn
  exact ⟨Ω, hΩ, B, P, X, fun n hn => (hX n hn).1, fun n hn => (hX n hn).2⟩

/-- **Existence for `C²` convex potentials** (the library `langevinKernel` of a Brownian carrier). -/
theorem exists_euclideanLangevin_C2 {d : ℕ} {V : Rd d → ℝ} (hV : ContDiff ℝ 2 V)
    (hHess : ∀ x z : Rd d, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (gibbs V)) :
    ∃ Pt : ℝ≥0 → Kernel (Rd d) (Rd d), IsEucLangevin2 V Pt := by
  obtain ⟨Ω, hΩ, P, B, hP, hB⟩ := CutoffRigidity.Paper.exists_stdBrownian d
  have hH : ∀ x z : Rd d, (0 : ℝ) * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z := by
    intro x z; simpa using hHess x z
  exact ⟨langevinKernel V B P, hV, hp,
    isEuclideanDiffusion_langevinKernel (CutoffRigidity.Paper.isStdBrownian_iff.1 hB) hV 0 le_rfl hH⟩

end C2U

end CutCur
