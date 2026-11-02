# R6 Rothaus remark: progress (worker, round 2)

Manuscript (cutcur-lean.tex l.816): "in the compact setting, if the optimal LSI constant is not twice the optimal PI constant,
then there exists an extremal function for LSI" (Rothaus 1981; Saloff-Coste lecture notes Th. 2.2.3 for the discrete version).

## Honest feasibility
* Full manifold statement (C_LSI > 2 C_PI on a compact Riemannian manifold => extremal in H^1) needs, beyond the project's
  Riemannian L^2 Rellich (`Qball_totallyBounded_of_tail`): compactness of H^1 into the Orlicz class L^2 log L (Sobolev embedding on a
  compact manifold; only R^n chart pieces exist) and finiteness of C_LSI (itself Rothaus/BE input).
* Concrete special cases are VACUOUS for the circle/torus/sphere (C_LSI = 2 C_PI there). Non-vacuous examples: finite spaces
  (two-point space with small p), weighted models.
* Plan: abstract Rothaus theorem for a "form" (Q, E) on a probability space, with the analytic inputs isolated as ONE explicit
  hypothesis (`Compact`: L^2 + Orlicz compactness of energy balls + lower semicontinuity), then the finite-space corollary with
  every hypothesis discharged (= discrete Rothaus, Saloff-Coste), with a non-vacuity witness.

## Target statement (Rothaus1.lean)
```
structure Form (μ : Measure X)  -- Q : Set (X → ℝ), E : (X → ℝ) → ℝ, closed under smul/const shifts, E(c f)=c²E f, E(f+c)=E f, E ≥ 0,
                                --  f ∈ Q → MemLp f 2 μ ∧ Integrable (f² log(1+f²)) μ
def optPI  := sInf {C | 0 ≤ C ∧ ∀ f ∈ Q, variance f μ ≤ C * E f}
def optLSI := sInf {C | 0 ≤ C ∧ ∀ f ∈ Q, entropyOf μ (fun x => f x ^ 2) ≤ C * E f}
theorem rothaus_alternative (F) (hPI : ∃ P ≥ 0, PI P) (hLSI : ∃ c ≥ 0, LSI c) (hcomp : F.Compact) (h : 2 * F.optPI < F.optLSI) :
  ∃ f ∈ F.Q, 0 < F.E f ∧ entropyOf μ (fun x => f x ^ 2) = F.optLSI * F.E f
```
## Proof plan
1. Sup characterisation of C = optLSI; minimizing sequence with Ent(f_n^2)=1, E(f_n) -> 1/C.
2. f_n = m_n + g_n, g_n mean zero, E(g_n)=E(f_n) bounded; Compact gives g_n -> g (L^2 and Orlicz L^1), E g <= 1/C.
3. Case m_n bounded: Ent continuous (generalised DCT with L^1-convergent bound) => f=m+g extremal.
4. Case |m_n| -> ∞: Ent(h) <= ∫(h log(h/c) - h + c) with c=m^2 gives limsup Ent(f_n^2) <= 2‖g‖^2 (elementary bound
   psi(t)=(1+t)^2 log(1+t)^2-2t-t^2 <= 2t^2+c|t|^3 on |t|<=1/2, log growth elsewhere + Orlicz tails); then 1 <= 2‖g‖^2 <= 2 optPI/C: contradiction.
5. Finite space corollary (all hypotheses verified) + two-point witness of C_LSI > 2 C_PI.
6. Optional: 2 optPI <= optLSI under the same hypotheses (so "≠" is equivalent to ">").
7. Optional: instantiate for the project's Riemannian form, leaving only the Orlicz compactness as explicit hypothesis.

## State
(stage log below)

### Stage log
* Stage 1 DONE (Rothaus1-12.lean, all compile, no sorry): abstract `rothaus_alternative` (statement as in "Target statement" above, with
  `Form.Compact` as the single analytic hypothesis). Files: 1 elementary bounds (psi, Theta), 2 Form/optPI/optLSI + Gibbs bound,
  3 generalised DCT, 4 L2 => in measure / squares in L1, 5-6 entropy continuity (bounded means), 7-8 scaled asymptotics (means -> inf),
  9 cases A/B, 10 optimal-constant lemmas, 11 normalised minimising sequence, 12 main theorem.
* Stage 2 DONE (Rothaus13-17): `finiteForm`, `finite_PI` (irreducible => Poincare, by compactness), `finite_compact` (Compact holds on finite
  spaces), `finite_rothaus` (discrete Rothaus, all hypotheses discharged except irreducibility/full support/C_LSI > 2 C_PI),
  two-point witness `twoPoint_rothaus` (mu{true}=e^-3: C_PI <= 1, C_LSI >= 3, extremal exists) = non-vacuity.
* hLSI dropped from `rothaus_alternative` (automatic from 2 C_PI < C_LSI because sInf of the empty set is 0).
* Stage 3 DONE (Rothaus18): `two_optPI_le_optLSI` (C_LSI >= 2 C_PI, by linearising LSI at large constants) and
  `rothaus_alternative_ne` (manuscript form: C_LSI < infinity and C_LSI != 2 C_PI => extremal).
* Stage 4 DONE (Rothaus19-21): `Form.Compact` derived from `Form.Rellich` (L^2 compactness + lsc) and `Form.Sobolev` (uniform L^{2+delta}
  bound): `Form.compact_of_rellich_sobolev`, `rothaus_alternative_sobolev(_ne)`.
* Umbrella module `CutoffRigidity.Extra.Rothaus` (imports 17, 18, 21). `lake build CutoffRigidity.Extra.Rothaus` OK, 2150 lines, no sorry,
  axioms standard only.
* NOT done (exact obstruction, general compact manifold): (1) Sobolev H^1 ⊂ L^{2+delta} (absent from Mathlib and project; the
  project has only R^n chart pieces `DiffSobolevRn*`), (2) building `Form μ` out of the project's closed form `diffT` (Q is a submodule of
  L^2 classes; needs a representative-level wrapper, Theta-integrability of Q, PI on Q by density from `poincare_D`),
  (3) identifying optimal constants over Q=H^1 with those over smooth test functions (density/mollification on manifolds).
  Concrete flat torus / circle / sphere are vacuous (C_LSI = 2 C_PI there, literature).
