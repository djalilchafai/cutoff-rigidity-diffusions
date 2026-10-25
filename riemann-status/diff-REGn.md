# WS-REGn status: interior elliptic regularity in R^n (A5(i)) -- DONE, fully checked

All files in `CutoffRigidity/Riemann/`, namespace `CutoffRigidity.Riemann.Diff`, ~5000 lines, no `sorry`/`axiom`/
`native_decide`; `#print axioms` of all main theorems: propext, Classical.choice, Quot.sound. Build:
`lake build CutoffRigidity.Riemann.DiffEllipticRn17` (imports everything).

## Setting (statements adapted only to elaborate)
`E` finite-dim real inner product space with `[MeasurableSpace E] [BorelSpace E]` (volume = Haar), `b : OrthonormalBasis ι ℝ E`,
`[DecidableEq ι]`. Coefficients are SCALAR: `A : ι → ι → E → ℝ` (matrix entries in the basis `b`), derivatives
`pd v f x = fderiv ℝ f x v`. For `EuclideanSpace ℝ (Fin n)` use `EuclideanSpace.basisFun`; for a chart into a generic `F` use
`stdOrthonormalBasis`. Weak derivatives: `HasWDeriv Ω v u w` (tests `IsTest Ω φ` = C_c^∞ with tsupport ⊆ Ω).
Local Sobolev: `LocL2`, `LocH1 b Ω u u'` (u, weak gradient components u' j locally L²), `LocSob b Ω m u := ∀ cutoff χ, χ u ∈ H^m(E)`.

## Deliverables
* `weak_solution_smooth` (DiffEllipticRn12): Ω open; `A i j` ContDiffOn ∞ Ω, symmetric and pointwise elliptic on Ω; `ϱ` ContDiffOn, >0;
  `g` ContDiffOn; `lam : ℝ` (any sign); `hu : LocH1 b Ω u u'`; weak equation
  `∀ φ test, (Σ_i Σ_j ∫ A i j * u' j * ∂_i φ * ϱ) + lam ∫ u φ ϱ = ∫ g φ ϱ`. Conclusion `∃ ū, ContDiffOn ℝ ∞ ū Ω ∧ u =ᵐ[volume.restrict Ω] ū`.
  (Pointwise ellipticity is assumed, as in the plan; uniform ellipticity on compacts is derived: `exists_uniform_ellipticity`.)
* `weak_solution_regular_step` / `locSob_step` (Rn10, Rn17): `LocSob (m+1) u`, `LocSob m F`, `-div(A∇u)=F` ⇒ `LocSob (m+2) u`.
* `global_regularity` (Rn7): global compactly supported theory with CONSTANTS DEPENDING ONLY ON `(m, θ, K, #ι)`:
  `∃ C, ∀ A (Ell A θ K (m+1)), w ∈ H¹ (AESupp), F ∈ H^m, G_i ∈ H^{m+1}, weak eq. ⇒ w ∈ H^{m+2}`, `‖w‖²_{m+2} ≤ C(‖F‖²_m+Σ‖G_i‖²_{m+1}+‖w‖²_1)`.
  `regular_step0` (Rn3) is the H² step with explicit constant `stepConst`; `dq_energy` (Rn2) the difference quotient energy estimate.
* `caccioppoli` (Rn14), `interior_step` (Rn13), `interior_estimate` (Rn16): for every cutoff χ and order k there are a cutoff χ' and a constant C
  (independent of the solution) with `‖χ u‖²_{H^k} ≤ C(‖χ' g‖²_{H^{k-2}} + ‖χ' u‖²_{L²})` for all weak solutions (`WSol`).
  The constant depends on (Ω, A, ϱ, lam, χ, k) only through the construction (cutoffs, ellipticity constant on a compact, sup-norms of finitely many derivatives).
* `sobolev_embedding` (Rn10), `sobolev_embedding_loc`, `interior_sup_estimate` (Rn17): `finrank E + 2j < 2m` ⇒ `C^j` representative with
  `‖D^i ū‖_∞² ≤ C ‖χ u‖²_{H^m}`, and combined `‖D^i (χu)‖²_∞ ≤ C(‖χ'g‖²_{H^{m-2}}+‖χ'u‖²_{L²})` for i ≤ j.
  `sobolev_sup_sq_le` (Rn3): Sobolev inequality for C_c^∞ via Fourier/Plancherel (`sobSmooth b m f = ∫ geo ...`).
* Auxiliary reusable results: mollification in L² compatible with weak derivatives (Rn2), difference quotients and weak-derivative existence from bounded
  difference quotients through Banach-Alaoglu + Riesz (Rn6-Rn8), Leibniz rule/mixed symmetry of weak derivatives (Rn4), `exists_contDiff_limit` (Rn9),
  Sob algebra with explicit constants `mulConst` (Rn5).

## File map
DiffSobolevRn1 defs | Rn2 mollification | Rn3 Fourier Sobolev inequality | Rn4 weak-derivative calculus | Rn5 Sob API/algebra | Rn6 difference quotients |
Rn7 L² toolbox, ‖D_h f‖≤‖∂f‖ | Rn8 bounded dq ⇒ weak derivative | Rn9 C^j limits | Rn10 mollification in Sob, embedding |
DiffEllipticRn1 `Ell`, `WeakEq`, extension to H¹_c tests | Rn2 dq energy | Rn3 H² step | Rn4 cutoffs, supports | Rn5 differentiated equation | Rn6-7 induction (`global_regularity`) |
Rn8 localization tools | Rn9 localized coefficients/equation | Rn10 local step | Rn11 local smooth reps, gluing | Rn12 `weak_solution_smooth` | Rn13 one-step estimate |
Rn14 Caccioppoli | Rn15 weighted reduction | Rn16 interior estimate | Rn17 final statements.

## Notes / honesty
* `DiffEllipticRn14.caccioppoli` needs `set_option maxHeartbeats 1600000` (≈50 s). All else default.
* Not done (not requested here): the manifold-side transfer (chart ⇒ these hypotheses); consumer must supply `LocH1` (weak gradient in the chart, locally L²),
  scalar matrix entries `g^{ij}` and `ϱ = e^{-V}√det g` smooth positive in the chart.
* `Challenge/Statements/Solution/CutoffRigidity.lean` untouched; no existing file edited.
