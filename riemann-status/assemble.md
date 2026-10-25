# assemble (S10/S11): DONE

File: `CutoffRigidity/Riemann/AssembleMain.lean` (module `CutoffRigidity.Riemann.AssembleMain`; lead must import it in CutoffRigidity.lean).
Builds with `lake build`, no sorry, `#print axioms CutoffRigidity.Paper.riemannian_gaussian_splitting` = propext, Classical.choice, Quot.sound.

Theorem `CutoffRigidity.Paper.riemannian_gaussian_splitting`: exactly the Challenge type (variables copied, `CutCur.` prefixes).
Checked: a scratch copy of the Challenge statement (taken verbatim from Solution.lean, in namespace CutCur with the Riemannian variables)
is closed by `apply CutoffRigidity.Paper.riemannian_gaussian_splitting <;> assumption` (axioms as above).

Proof: no separate k = 0 case is needed. `exists_frame_of_eigen` gives a Frame of size k = mFirstEigenDim (k = 0 included: Level = M, Rd 0 trivial).
F' = `CutoffRigidity.Riemann.LevelModel F (Rd k)`, N = `fr.Level`, Phi = `fr.splitEquiv`, V' = V∘val + (k/2) log(ρ/2π), μ' = μ.map fr.toLevel
(`weighted_factorization`, with `mvfderiv_V_X`), CD via `cd_level`, distance via `edist_sq`, instances all `inferInstance`.
Eigenfunction items: `affine_items` with g = √ρ s, p = sv; orthonormality from `μ.map sv = γ` (fst of the factorization) and
`covariance_eval_multivariateGaussian` + zero mean.
Note: attainment (0 < k) is not needed for this theorem (still open in gap.md, only relevant for other results).
