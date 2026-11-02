module

public import CutoffRigidity.Statements

/-!
# The `C^∞` Langevin predicates (proof-side)

Until the integration of the `C²` uniqueness (`C2Uniq*`), `IsEuclideanLangevin`, `IsRigidSequenceK` and
`IsSigmaLangevin` of `Challenge.lean` required `V ∈ C^∞`. The smoothness clause is now `C²` there. The older proof
modules (`EuclideanDiffusion`, `Dissip*`, `EuclideanKernelStatements`, ...) were written for the `C^∞` predicates;
they use the copies below (same text as the former Challenge definitions, with `C^∞`). These copies are not part of
the Challenge surface.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

namespace CutCur

/-- `IsEuclideanLangevin` with `V ∈ C^∞` (former definition). -/
def IsEuclideanLangevinInf {d : ℕ} (V : Rd d → ℝ) (Pt : ℝ≥0 → Kernel (Rd d) (Rd d)) : Prop :=
  ContDiff ℝ ∞ V ∧ IsProbabilityMeasure (gibbs V) ∧ IsEuclideanDiffusion V Pt

/-- `IsRigidSequenceK` with `V n ∈ C^∞` (former definition). -/
def IsRigidSequenceKInf (V : ∀ n, Rd n → ℝ) (Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)) : Prop :=
  (∀ n, 0 < n → IsEuclideanLangevinInf (V n) (Pt n) ∧ RigidCurvature (V n)) ∧
    0 < liminf (fun n => ENNReal.ofReal (spectralGap (V n))) atTop

/-- `IsSigmaLangevin` with `V ∈ C^∞` (former definition). -/
def IsSigmaLangevinInf {d : ℕ} (V : Rd d → ℝ) (σ : ℝ) (Pt : ℝ≥0 → Kernel (Rd d) (Rd d)) : Prop :=
  ContDiff ℝ ∞ V ∧ IsProbabilityMeasure (gibbs fun x => V x / σ ^ 2) ∧ IsSigmaDiffusion V σ Pt

end CutCur
