module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Weak derivatives and Sobolev classes on a finite dimensional Euclidean space

Basic definitions of the `ℝⁿ` elliptic regularity development (workstream REGn):
test functions, weak directional derivatives, the canonical weak derivative `wd`, global Sobolev
classes `Sob m` and squared norms `sobSq m` (relative to an orthonormal basis `b`).
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Directional derivative `∂_v f`. -/
noncomputable def pd (v : E) (f : E → ℝ) : E → ℝ := fun x => fderiv ℝ f x v

/-- Smooth compactly supported test function with support inside `Ω`. -/
def IsTest (Ω : Set E) (φ : E → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

/-- `w` is the weak derivative of `u` in direction `v` on `Ω`. -/
def HasWDeriv (Ω : Set E) (v : E) (u w : E → ℝ) : Prop :=
  LocallyIntegrableOn u Ω ∧ LocallyIntegrableOn w Ω ∧
    ∀ φ, IsTest Ω φ → ∫ x, u x * pd v φ x = -∫ x, w x * φ x

/-- Canonical (global, `L²`) weak derivative; junk value `0` when there is none. -/
noncomputable def wd (v : E) (u : E → ℝ) : E → ℝ :=
  open Classical in
  if h : ∃ w, HasWDeriv Set.univ v u w ∧ MemLp w 2 volume then h.choose else 0

variable {ι : Type*} [Fintype ι]

/-- Global Sobolev class `H^m(E)` with respect to the directions `b i`. -/
def Sob (b : OrthonormalBasis ι ℝ E) : ℕ → (E → ℝ) → Prop
  | 0, u => MemLp u 2 volume
  | m + 1, u => MemLp u 2 volume ∧ ∀ i, ∃ w, HasWDeriv Set.univ (b i) u w ∧ Sob b m w

/-- Squared `H^m` norm (junk if `u ∉ H^m`). -/
noncomputable def sobSq (b : OrthonormalBasis ι ℝ E) : ℕ → (E → ℝ) → ℝ
  | 0, u => ∫ x, u x ^ 2
  | m + 1, u => (∫ x, u x ^ 2) + ∑ i, sobSq b m (wd (b i) u)

/-- Squared `H^m` norm of a smooth function, with classical derivatives. -/
noncomputable def sobSmooth (b : OrthonormalBasis ι ℝ E) : ℕ → (E → ℝ) → ℝ
  | 0, u => ∫ x, u x ^ 2
  | m + 1, u => (∫ x, u x ^ 2) + ∑ i, sobSmooth b m (pd (b i) u)

end CutoffRigidity.Riemann.Diff
