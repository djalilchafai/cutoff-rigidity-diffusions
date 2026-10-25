# wassassemble: DONE

Files (new, compile, no sorry): `CutoffRigidity/Riemann/WassMehler.lean`, `CutoffRigidity/Riemann/WassAssemble.lean`.
The lead must add `public import CutoffRigidity.Riemann.WassAssemble` (and WassMehler) to CutoffRigidity.lean.

- `map_proj_eq_mehler`: if every functional x -> <z, p x> has the Gaussian Mehler law under nu then `nu.map p = SplitData.mehler` (charFun).
- `eigen_of_inner`: x -> <z, p x> is an eigenfunction (orthonormal basis from E.basis, a_i/sqrt(rho) basis of R^k, eigenSub closed under sums/smul).
- `exists_orthonormal_eigenbasis` (EigenFinite) already gave `basis`; `pos` from hpos.
- `CutoffRigidity.Paper.riemannian_wasserstein_estimate`: obtains the splitting, builds SplitData/EigenSplitting/TransportInputs
  (a = z by surjectivity of p; int f_z^2 = |z|^2/rho; contraction by squaring hcontr) and applies `riemannian_wasserstein_estimate_of_transport`.
- Axioms: propext, Classical.choice, Quot.sound. Scratch Solution.lean (importing WassAssemble) elaborates with the unchanged
  `apply CutoffRigidity.Paper.riemannian_wasserstein_estimate <;> assumption`.
- The amended hypotheses were sufficient; no fix needed.
