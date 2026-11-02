module

public import CutoffRigidity.Statements
public import CutoffRigidity.Extra.SmoothLangevin
public import CutoffRigidity.Extra.Rothaus

/-!
# Bridges between the Challenge definitions and the proof-side modules (round 2)

* `ouInf`: an Ornstein-Uhlenbeck `IsEuclideanLangevin` (smoothness `C²`) is an `IsEuclideanLangevinInf`
  (the OU potential is `C^∞`), so the `C^∞` OU theorems of `EuclideanKernelStatements` apply.
* `formToR`: the Challenge's abstract form `CutCur.Form` is the `Rothaus.Form` of the same data (the Orlicz weight
  `Θ` is inlined in the Challenge).
* `finite_rothaus`: the Challenge's discrete Rothaus alternative, for an arbitrary form with domain all functions and the
  Dirichlet energy, from `Rothaus.finite_rothaus` for `Rothaus.finiteForm`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

namespace CutoffRigidity.Paper

theorem ouInf {d : ℕ} {ρ c : ℝ} {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)}
    (hL : CutCur.IsEuclideanLangevin (fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c) Pt) :
    CutCur.IsEuclideanLangevinInf (fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c) Pt :=
  ⟨(contDiff_const.mul (contDiff_norm_sq ℝ)).add contDiff_const, hL.2.1, hL.2.2⟩

/-- A Challenge form as a `Rothaus.Form`. -/
def formToR {X : Type*} [MeasurableSpace X] {μ : Measure X} (F : CutCur.Form μ) : Rothaus.Form μ :=
  ⟨F.Q, F.E, F.smul_mem, F.add_const_mem, F.E_nonneg, F.E_smul, F.E_add_const, F.memLp, F.integrable_Θ⟩

theorem formToR_finite {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] (w : X → X → ℝ) (hw : ∀ x y, 0 ≤ w x y)
    (F : CutCur.Form μ) (hQ : F.Q = Set.univ) (hE : ∀ f, F.E f = ∑ x, ∑ y, w x y * (f x - f y) ^ 2) :
    formToR F = Rothaus.finiteForm μ w hw := by
  obtain ⟨Q, E, h1, h2, h3, h4, h5, h6, h7⟩ := F
  simp only at hQ hE
  subst hQ
  have : E = fun f => ∑ x, ∑ y, w x y * (f x - f y) ^ 2 := funext hE
  subst this
  rfl

theorem finite_rothaus {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] (μ : Measure X)
    [IsProbabilityMeasure μ] (w : X → X → ℝ) (hw : ∀ x y, 0 ≤ w x y) (hπ : ∀ x, 0 < μ.real {x})
    (hconn : ∀ f : X → ℝ, ∑ x, ∑ y, w x y * (f x - f y) ^ 2 = 0 → ∀ x y, f x = f y)
    (F : CutCur.Form μ) (hQ : F.Q = Set.univ) (hE : ∀ f, F.E f = ∑ x, ∑ y, w x y * (f x - f y) ^ 2)
    (hgt : 2 * F.optPI < F.optLSI) :
    ∃ f : X → ℝ, 0 < F.E f ∧ CutCur.entropyOf μ (fun x => f x ^ 2) = F.optLSI * F.E f := by
  have h := formToR_finite μ w hw F hQ hE
  have h1 : F.optPI = (Rothaus.finiteForm μ w hw).optPI := by rw [← h]; rfl
  have h2 : F.optLSI = (Rothaus.finiteForm μ w hw).optLSI := by rw [← h]; rfl
  obtain ⟨f, hf1, hf2⟩ := Rothaus.finite_rothaus μ w hw hπ hconn (by rw [← h1, ← h2]; exact hgt)
  exact ⟨f, by rw [hE]; exact hf1, by rw [hE, h2]; exact hf2⟩

end CutoffRigidity.Paper
