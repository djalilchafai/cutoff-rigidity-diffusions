# Item 6 worker report (sphere, Gaussian isoperimetry, Theorem 1.7 on manifolds)

Files: `CutoffRigidity/Extra/Item6a.lean` (276 lines, builds with `lake build CutoffRigidity.Extra.Item6a`, no sorry,
axioms propext/Classical.choice/Quot.sound). No Item6b/Item6c files (see below). Nothing existing was edited.

## (a) Sphere, `rho = d-1`, `lambda_1 = d` (manuscript ~L711)
Proved (model form, no sphere instance): for any compact d-dimensional Riemannian manifold M (project's standing
instances, without `IsRiemannianManifold`) with `IsIsometricSphereMap F Phi` (`|Phi x| = 1`, `Phi` smooth into `R^(d+1)`,
pulled-back Euclidean inner product = Riemannian one, written with `mvfderiv`) and a probability measure `mu` whose image under
`Phi` is invariant under all linear isometries of `R^(d+1)`:
`theorem sphere_spectralGap_le (hF : finrank ℝ F = d) (hΦ : IsIsometricSphereMap F Φ) (hμ : ∀ T : 𝔼 ≃ₗᵢ[ℝ] 𝔼, μ.map (fun x => T (Φ x)) = μ.map Φ) : mSpectralGap F μ ≤ d`.
Proof: `f = <e_0, Phi>`; `|grad f|^2 = |a|^2 - <a,Phi>^2` (`norm_mgrad_sq`, via `range_deriv_eq`: range of dPhi = (Phi x)^perp by
dimension count); moments `∫Phi_0^2 = 1/(d+1)`, `∫Phi_0 = 0` from invariance (`coord_moments`); Rayleigh quotient exactly d.
Also `sphere_gap_bounds_of_CD`: IF `CD F (d-1) 0` (hypothesis) and `IsWeightedVolume`, `d ≥ 2`, then `d-1 ≤ mSpectralGap ≤ d`
(uses `Paper.mSpectralGap_ge_of_CD`).
NOT proved, with obstructions:
1. `CD(d-1, ∞)` on the sphere, i.e. `Ric = (d-1) g` via `CD_iff_ricci`: needs Levi-Civita of the induced metric = tangential
   projection (uniqueness via Koszul), Gauss equation, curvature computation with the project's `mCurv`/`mRic` extensions: est. 2-4k lines.
2. `lambda_1 >= d` (hence `= d`): not obtainable from `CD(d-1,∞)` (gives d-1); needs dimensional Bochner `|Hess f|^2 >= (Δf)^2/d` + integrated
   Bochner (1-2k lines) or spherical harmonics (absent from Mathlib).
3. Non-vacuity: Mathlib has no `RiemannianBundle` / `IsRiemannianManifold` / `ConnectedSpace` instance on `sphere`; the upper-bound theorem needs
   no `IsRiemannianManifold`, so a witness would need only the induced `RiemannianBundle` + smoothness (est. 300-600 lines), but the standing
   Challenge setting needs the geodesic metric (1.5-3k lines). Not built: as stated the theorem is conditional on the existence of such an M.
4. `rho = d-1` optimal (`¬CD rho` for `rho > d-1`) and cutoff on the sphere: not attempted (the manuscript gives no cutoff statement).
Total for a full faithful sphere statement: 5-10k lines (scoping estimate stands); only the upper bound was cheap (~280 lines).

## (b) Gaussian isoperimetric inequality (~L632)
The manuscript has no precise statement: only "Bakry-Emery ... implies ... a Gaussian isoperimetric inequality".
Cheapest precise forms: Sudakov-Tsirelson/Borell `γ(A_r) ≥ Φ(Φ^{-1}(γ(A)) + r)` or Bobkov's functional form
`I(∫f) ≤ ∫ sqrt(I(f)^2 + |∇f|^2)`, `I = φ∘Φ^{-1}`. Mathlib has neither the inverse Gaussian cdf as a regular function nor any isoperimetry.
Proof route (Bakry-Ledoux): OU/Mehler semigroup, gradient bound `|∇P_t f| ≤ e^{-t} P_t|∇f|`, Bobkov two-point/semigroup interpolation with
`I` (needs `I I'' = -1`, smoothness of Φ^{-1}), then approximation of indicators to get sets with enlargements: est. 4-8k lines; not attempted.
Available in the project: Gaussian/Gibbs LSI for exp of bounded Lipschitz tests (`LipschitzExponentialLogSobolev`), enough for Herbst
concentration `γ(f ≥ E f + r) ≤ e^{-r^2/2}` (est. 500-1000 lines), which is a weaker, DIFFERENT statement (not isoperimetry); not proved.

## (c) Theorem 1.7 on manifolds
Theorem 1.7 of this project = `th:prodcondcut` (product condition). Manuscript L437-439 has only the sentence "We state it in the restricted
Euclidean setting for simplicity, but it holds in the Riemannian setting, since it is the curvature bound and the diffusion property that matter."
No precise manifold statement, no proof. (The Riemannian Theorem 1.9 `main_thm_riem` is a different statement and is already in Challenge.)
Nothing to formalize; stopped. (geoB.md's draft statement TV/entropy-only is the only candidate; est. 10-20k lines.)
