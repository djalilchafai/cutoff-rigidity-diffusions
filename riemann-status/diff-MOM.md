# diff-MOM (WS-MOM, Tier C): DONE, all checked

Files (new, build with `lake build`, no sorry/axiom; axioms = propext, Classical.choice, Quot.sound):
* `CutoffRigidity/Riemann/DiffLowerMoments.lean` (module `CutoffRigidity.Riemann.DiffLowerMoments`)
  - `lower_aux`: Cauchy-Schwarz lower bound on `E‖X-Z‖²` from mean/second moment of `X` and `Z` centered (discriminant argument).
  - `SplitData.proj_moments`: Gaussian moments of the coordinate under `μ`.
  - `SplitData.lower_of_moments` (C1): mean `e^{-ρt}⟪a,p x₀⟫` and second moment `e^{-2ρt}‖p x₀‖² + (k/ρ)(1-e^{-2ρt})` under a probability `ν`
    imply `ofReal(ρ e^{-2ρt}‖p x₀‖² + k(1-√(1-e^{-2ρt}))²) ≤ ofReal ρ * wasserstein2 ν μ ^ 2` (same right-hand side as `lower_of_mehler`).
  - `upper_iSup_dirac` (C2): pointwise bound `W₂²(P x, μ) ≤ q ∫ d²(x,·)dμ` gives the sup bound.
* `CutoffRigidity/Riemann/DiffMoments.lean`
  - `CutCur.mlaplacian_sq`, `mgenerator_sq` (`𝓛(f²)=2f𝓛f+2Γf`), `mlaplacian_const`, `mgenerator_const`.
  - `Diff.integral_bind_eq`, `Diff.sq_moment_of_eigen` (`K_t(T²)=e^{-2ρt}T²+(c/ρ)(1-e^{-2ρt})` when `ΓT=c`),
    `Diff.carre_eq_of_invariant` (`ΓT=ρ` recovered from invariance of `μ` and `∫T²=1`), `Diff.carre_const_of_eigen` (parallel gradient),
    `Diff.memLp_sq_inner` (Gaussian `L⁴`), and `Diff.eigen_moments` (C3: both moments of `p` under `Kk t x₀`, uses only `CanonicalDiffusion.eigen`, `.invariant`, `.markov`).
* `CutoffRigidity/Riemann/DiffAssembleCanonical.lean`
  - `CutoffRigidity.Paper.riemannian_wasserstein_estimate_of_canonical`: conclusion verbatim that of `riemannian_wasserstein_estimate`;
    hypotheses `hV hμ hρ hCD hgap hpos`, `Pt`, `Kk`, `hK : CanonicalDiffusion F V μ ρ Kk`, `hPK : ∀ t x, Pt t x = Kk t x`
    (no `hP`, `hinv`, `hcontr`, `hmehler`).  Only `hK.markov`, `.invariant`, `.eigen`, `.contraction` are used
    (`.dynkin` and `.smoothing` are not needed by Tier C).

Notes for the lead
* No change to DiffAPI is needed.  `hpos` stays a hypothesis (EigenSplitting.pos) until WS-HPOS delivers it.
* Imports to add to CutoffRigidity.lean: `DiffLowerMoments`, `DiffMoments`, `DiffAssembleCanonical`.
* The lemma `lower_of_moments` does not need Gaussianity of `Kk t x₀`, only the two moments.
