# R6 Rothaus remark: worker report (round 2)

Manuscript (cutcur-lean.tex l.816-818): "in the compact setting, if the optimal LSI constant is not twice the optimal PI constant,
then there exists an extremal function for LSI" (Rothaus; Saloff-Coste Th. 2.2.3 for the discrete version).

Build target: `lake build CutoffRigidity.Extra.Rothaus` (umbrella, imports Rothaus17/18/21; files `CutoffRigidity/Extra/Rothaus1..21.lean`,
2150 lines). No sorry/axiom/native_decide; `#print axioms` of every theorem below: `[propext, Classical.choice, Quot.sound]`.
Progress/plan: `extra-status/rothaus-progress.md`.

## Verdict
* General compact Riemannian manifold: NOT formalised (obstruction below).
* Proved: the Rothaus theorem for an ABSTRACT Dirichlet form `(Q, E)` on a probability space, with the analytic input isolated in one
  explicit hypothesis `Form.Compact` (or, more classically, in `Form.Rellich` + `Form.Sobolev`), the full dichotomy "C_LSI >= 2 C_PI, and > implies
  an extremal", the finite-space case with NO analytic hypothesis left (= discrete Rothaus), and a verified non-vacuity example.

## Definitions (namespace `CutoffRigidity.Rothaus`, entropy = `CutCur.entropyOf` from `CutoffRigidity.Statements`)
```lean
structure Form {X} [MeasurableSpace X] (μ : Measure X) where
  Q : Set (X → ℝ);  E : (X → ℝ) → ℝ
  smul_mem : ∀ c f, f ∈ Q → c • f ∈ Q
  add_const_mem : ∀ c f, f ∈ Q → (fun x => f x + c) ∈ Q
  E_nonneg : ∀ f ∈ Q, 0 ≤ E f
  E_smul : ∀ c f, f ∈ Q → E (c • f) = c ^ 2 * E f
  E_add_const : ∀ c f, f ∈ Q → E (fun x => f x + c) = E f
  memLp : ∀ f ∈ Q, MemLp f 2 μ
  integrable_Θ : ∀ f ∈ Q, Integrable (fun x => Θ (f x)) μ       -- Θ t = t^2 log(1+t^2)  (f in L^2 log L)
def Form.optPI  F := sInf {C | 0 ≤ C ∧ ∀ f ∈ F.Q, variance f μ ≤ C * F.E f}
def Form.optLSI F := sInf {C | 0 ≤ C ∧ ∀ f ∈ F.Q, entropyOf μ (fun x => f x ^ 2) ≤ C * F.E f}
def Form.Compact F : Prop := ∀ B (g : ℕ → X → ℝ), (∀ n, g n ∈ F.Q) → (∀ n, ∫ g n = 0) → (∀ n, F.E (g n) ≤ B) →
  ∃ φ, StrictMono φ ∧ ∃ h ∈ F.Q, Tendsto (fun n => ∫ (g (φ n) x - h x)^2) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ |Θ (g (φ n) x) - Θ (h x)|) atTop (𝓝 0) ∧ ∀ b, (∀ᶠ n in atTop, F.E (g (φ n)) ≤ b) → F.E h ≤ b
def Form.Rellich F  -- same without the Θ-clause
def Form.Sobolev F : Prop := ∃ δ > 0, ∀ B, ∃ K, ∀ f ∈ F.Q, ∫ f = 0 → F.E f ≤ B →
      Integrable (fun x => |f x| ^ (2 + δ)) μ ∧ ∫ |f x| ^ (2 + δ) ≤ K
```
`optPI`/`optLSI` mirror `CutCur.optimalPI/optimalLSI` (sInf of admissible constants) but over `Q` (the H^1 class), not smooth bounded Lipschitz functions.

## Main theorems (exact Lean statements)
```lean
theorem rothaus_alternative [IsProbabilityMeasure μ] (F : Form μ)
    (hPI : ∃ P, 0 ≤ P ∧ ∀ f ∈ F.Q, variance f μ ≤ P * F.E f) (hcomp : F.Compact) (hgt : 2 * F.optPI < F.optLSI) :
    ∃ f ∈ F.Q, 0 < F.E f ∧ CutCur.entropyOf μ (fun x => f x ^ 2) = F.optLSI * F.E f

theorem two_optPI_le_optLSI [IsProbabilityMeasure μ] (F : Form μ)
    (hLSI : ∃ c, 0 ≤ c ∧ ∀ f ∈ F.Q, CutCur.entropyOf μ (fun x => f x ^ 2) ≤ c * F.E f) : 2 * F.optPI ≤ F.optLSI

theorem rothaus_alternative_ne [IsProbabilityMeasure μ] (F : Form μ) (hPI : ...) (hLSI : ...) (hcomp : F.Compact)
    (hne : F.optLSI ≠ 2 * F.optPI) : ∃ f ∈ F.Q, 0 < F.E f ∧ CutCur.entropyOf μ (fun x => f x ^ 2) = F.optLSI * F.E f

theorem Form.compact_of_rellich_sobolev [IsProbabilityMeasure μ] (F : Form μ) (hR : F.Rellich) (hS : F.Sobolev) : F.Compact
theorem rothaus_alternative_sobolev (F) (hPI) (hR : F.Rellich) (hS : F.Sobolev) (hgt : 2 * F.optPI < F.optLSI) : ∃ f ∈ F.Q, ...
theorem rothaus_alternative_sobolev_ne (F) (hPI) (hLSI) (hR) (hS) (hne : F.optLSI ≠ 2 * F.optPI) : ∃ f ∈ F.Q, ...

-- finite case (X Fintype, MeasurableSingletonClass, μ probability, w ≥ 0 weights, E f = ∑ x y, w x y * (f x - f y)^2)
theorem finite_rothaus (w) (hw : ∀ x y, 0 ≤ w x y) (hπ : ∀ x, 0 < μ.real {x})
    (hconn : ∀ f, ∑ x, ∑ y, w x y * (f x - f y)^2 = 0 → ∀ x y, f x = f y)
    (hgt : 2 * (finiteForm μ w hw).optPI < (finiteForm μ w hw).optLSI) :
    ∃ f : X → ℝ, 0 < ∑ x, ∑ y, w x y * (f x - f y)^2 ∧
      entropyOf μ (fun x => f x ^ 2) = (finiteForm μ w hw).optLSI * ∑ x, ∑ y, w x y * (f x - f y)^2

-- non-vacuity (Bool, μ{true} = e^{-3}, E f = p(1-p)(f true - f false)^2): no hypothesis left
theorem twoPoint_rothaus : 2 * TwoPoint.F.optPI < TwoPoint.F.optLSI ∧
    ∃ f : Bool → ℝ, 0 < TwoPoint.F.E f ∧ entropyOf TwoPoint.μ (fun x => f x ^ 2) = TwoPoint.F.optLSI * TwoPoint.F.E f
```
Notes: (i) finiteness of C_LSI is automatic from `2 optPI < optLSI` (sInf ∅ = 0, optPI >= 0), so `rothaus_alternative` has no LSI-finiteness hypothesis;
(ii) `hPI` is a genuine hypothesis (sInf over an empty set is the junk value 0); on finite irreducible forms `finite_PI` proves it;
(iii) `finite_compact` proves `Form.Compact` for finite forms (compactness of bounded sets in R^X; the bound comes from PI).

## What the proof actually does (Rothaus' argument, as formalised)
Normalised minimising sequence `Ent(u_n^2)=1`, `E(u_n) -> 1/C` (`exists_normalized`); write `u_n = m_n + g_n`, `g_n` mean zero (`m_n >= 0` after
a sign change). `Compact` gives `g_n -> h` (L^2 and Orlicz), `E h <= 1/C`. Case `m_n` bounded (`caseA`, `entropy_tendsto`, via generalised dominated
convergence `tendsto_integral_of_dominated_L1`): `h + m_0` is an extremal. Case `m_n -> ∞` (`caseB`): Gibbs bound `Ent((g+m)^2) <= ∫ m^2 ψ(g/m)`
(`entropy_le_scaled`) and `∫ m_n^2 ψ(g_n/m_n) -> 2∫h^2` (`tendsto_scaled`, Taylor bound `ψ_sub_small`: `|ψ t - 2t^2| <= 10|t|^3` for `|t|<=1/2`, `ψ <= 32 t^2 + 9Θ`
otherwise) give `1 <= 2 ∫h^2 <= 2 optPI/C`, contradicting `C > 2 optPI`. `two_optPI_le_optLSI` linearises LSI at large constants
(`entropy_ge_scaled`: `Ent((g+m)^2) >= ∫ m^2ψ(g/m) - (∫g^2)^2/m^2`).

## Obstruction for the general compact manifold (not proved)
1. Sobolev embedding `H^1 ⊂ L^{2+δ}` on a compact manifold (`Form.Sobolev`): absent from Mathlib and the project (only R^n chart pieces
   `DiffSobolevRn*`). Rellich in L^2 (`Form.Rellich`) IS in the project (`Qball_totallyBounded_of_tail`, tail trivial on compact M), but the project's
   `Q` is a submodule of L^2-classes (`M →₂[μ] ℝ`) with a bilinear `E`, so a wrapper to the function-level `Form` is needed (Θ-integrability of Q from Sobolev,
   PI on all of Q by density from `poincare_D`, lsc of E from closedness): est. 600-900 lines, conditional on `Form.Sobolev`.
2. Identification of `optPI/optLSI` over Q = H^1 (∩ L^2 log L) with the manuscript-style constants over smooth test functions (density/mollification on manifolds).
3. Concrete simple compact examples are vacuous: circle/torus/sphere have `C_LSI = 2 C_PI` (literature), so the alternative's second branch never occurs there.
   Non-vacuous examples need weights/finite spaces (done: two-point).

## Integration notes for the lead
* Files import `CutoffRigidity.Statements` for `CutCur.entropyOf` (Challenge.lean has its own copy in the Challenge library; a statement in Challenge
  would need `Form` inlined or `Form` restated; the theorems are ~25-line statements, `Form` + `Compact` + `optPI/optLSI` ~35 lines).
* Suggested Challenge-sized statements: `twoPoint_rothaus`-style is too specialised; recommended: `rothaus_alternative_sobolev_ne` (abstract) and `finite_rothaus`.
* No Challenge/Statements/Solution/lakefile edits were made; all new files are `CutoffRigidity/Extra/Rothaus*.lean`.
