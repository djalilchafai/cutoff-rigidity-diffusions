module

public import CutoffRigidity.Extra.Rothaus21
public import CutoffRigidity.Extra.Rothaus18
public import CutoffRigidity.Extra.Rothaus17

/-! # The Rothaus remark (manuscript, subsection "Optimal constants")

"A famous alternative due to Oscar Rothaus states that in the compact setting, if the optimal LSI constant is not twice the
optimal PI constant, then there exists an extremal function for LSI."

Formalised here for an abstract Dirichlet-type form `(Q, E)` on a probability space (`CutoffRigidity.Rothaus.Form`; `Q` is the
energy domain `H¹`, `E` the energy `∫|∇f|²`), with the optimal constants `optPI`, `optLSI` defined as in
`CutCur.optimalPI`/`CutCur.optimalLSI` but over `Q`.

Main results (all in namespace `CutoffRigidity.Rothaus`):
* `rothaus_alternative`: PI + `Form.Compact` + `2 optPI < optLSI` ⟹ ∃ f ∈ Q, 0 < E f ∧ Ent(f²) = optLSI · E f.
* `two_optPI_le_optLSI`: `2 optPI ≤ optLSI` whenever the LSI holds with some constant (so "≠" means ">").
* `rothaus_alternative_ne`: the manuscript's form (finite `optLSI`, `optLSI ≠ 2 optPI`).
* `rothaus_alternative_sobolev(_ne)`: the analytic input `Form.Compact` replaced by Rellich `L²`-compactness (`Form.Rellich`)
  and a Sobolev `L^{2+δ}` bound (`Form.Sobolev`).
* `finite_rothaus`: finite irreducible spaces, no analytic hypothesis left (discrete Rothaus, Saloff-Coste Th. 2.2.3).
* `twoPoint_rothaus`: non-vacuity, `μ{true} = e^{-3}`: `2 C_PI < C_LSI` is proved and an extremal exists.

Not formalised: the instantiation of `Form` for a compact weighted Riemannian manifold (`Form.Sobolev` needs the Sobolev embedding
`H¹ ⊂ L^{2+δ}`, absent from Mathlib and the project; the identification of the optimal constants over `Q = H¹` with the ones over
smooth test functions needs a density argument).
-/
