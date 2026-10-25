module

public import CutoffRigidity.Statements

/-!
# Brownian-carrier definitions (proof-side)

`worst` and `IsRigidSequence` (carrier versions of `worstK`, `IsRigidSequenceK`) and the mixing times.
None of them appears in `Challenge.lean` any more; the `_carrier` theorems use them.

The total variation, Wasserstein and entropy mixing times of a Brownian-carrier process `(Ω, P, X)`.
They are no longer part of `Challenge.lean` (whose statements use the kernel versions `mixingTimeK`,
`mixingTimeW2K`, `mixingTimeKLK`), but the `_carrier` theorems, kept as proof ingredients, are stated
with them.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

@[expose] public noncomputable section

namespace CutCur

/-- Worst case over initial conditions `x₀ ∈ S` of a discrepancy `δ` of `Law(X_t^{x₀})`. -/
def worst {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] (P : Measure Ω)
    (X : α → ℝ≥0 → Ω → α) (S : Set α) (δ : Measure α → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ⨆ x₀ ∈ S, δ (P.map (X x₀ t.toNNReal))

/-- The standing assumptions of Corollaries 1.3 and 1.4 for a sequence of dimensions `n`: the Euclidean setting and the curvature condition (1.4) in
every positive dimension, and `liminf λ₁⁽ⁿ⁾ > 0`. -/
def IsRigidSequence {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (V : ∀ n, Rd n → ℝ)
    (B : ∀ n, ℝ≥0 → Ω n → Rd n) (P : ∀ n, Measure (Ω n)) (X : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n) :
    Prop :=
  (∀ n, 0 < n → IsLangevin (V n) (B n) (P n) (X n) ∧ RigidCurvature (V n)) ∧
    0 < liminf (fun n => ENNReal.ofReal (spectralGap (V n))) atTop

/-- The total variation mixing time `t₀ = inf {t ≥ 0 : sup_{x₀ ∈ S} d_TV(Xₜ, μ) ≤ η}` (`+∞` if the set is empty). -/
def mixingTime {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (X : Rd d → ℝ≥0 → Ω → Rd d) (μ : Measure (Rd d)) (S : Set (Rd d)) (η : ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : worst P X S (fun ν => .ofReal (tvDist ν μ)) t ≤ .ofReal η), (t : ℝ≥0∞)

/-- The Wasserstein mixing time `inf {t ≥ 0 : sup_{x₀ ∈ S} W₂(Xₜ, μ) ≤ η}` (`+∞` if empty). -/
def mixingTimeW2 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (X : Rd d → ℝ≥0 → Ω → Rd d) (μ : Measure (Rd d)) (S : Set (Rd d)) (η : ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : worst P X S (fun ν => wasserstein2 ν μ) t ≤ .ofReal η), (t : ℝ≥0∞)

/-- The entropy mixing time `inf {t ≥ 0 : sup_{x₀ ∈ S} H(Xₜ | μ) ≤ η}` (`+∞` if empty). -/
def mixingTimeKL {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (X : Rd d → ℝ≥0 → Ω → Rd d) (μ : Measure (Rd d)) (S : Set (Rd d)) (η : ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : worst P X S (fun ν => InformationTheory.klDiv ν μ) t ≤ .ofReal η), (t : ℝ≥0∞)

end CutCur
