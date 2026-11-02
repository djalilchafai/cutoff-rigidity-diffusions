# R7 sphere, round 2: progress file (worker)

Files: `CutoffRigidity/Extra/Sphere*.lean` only. Build: `lake build CutoffRigidity.Extra.SphereN`.

## Strategy (key design decision)
Work with the *model form* already used in `Item6a.lean`: any `M` (project's standing instances) with `IsIsometricSphereMap F Φ`
(`Φ : M → ℝ^(d+1)`, |Φ|=1, smooth, pulled-back product = Riemannian one). Prove everything for such `M`; the concrete sphere
then only needs `IsIsometricSphereMap` for the pullback metric (nearly definitional). This avoids Levi-Civita uniqueness /
covariant-derivative constructions: Mathlib's Koszul formula (`leviCivitaConnection_apply_inner`) + project's
`mvfderiv_mlieBracket` + `nabSmooth` + `curv_tensor` suffice.

Pen-and-paper (checked): with phi_a = <a,Phi>, Gauss: <nabla_X Y, Z> = sum_a Z(phi_a) X(Y phi_a);
(nabla_Y W)(phi_a) = Y(W phi_a) + g(W,Y) phi_a; hence <R(X,Y)W,Z> = g(Y,W) g(X,Z) - g(X,W) g(Y,Z) and Ric = (d-1) g.

## Stages and target statements
- S1 (Sphere1): `gauss_koszul`: for SmAt X Y Z at x, `inner (LC Y x (X x)) (Z x) = ∑ i, mvfderiv φ_i x (Z x) * mvfderiv (fun y => mvfderiv φ_i y (Y y)) x (X x)` (est. 250 lines).
- S2 (Sphere2): `nab_coord`, `curv_inner`: `inner (curv F X Y W x) (V x) = g(W,Y) g(V,X) - g(W,X) g(V,Y)`
  and `sphere_mRic : mRic F x v w = ((d:ℝ) - 1) * inner v w` given `finrank F = d`, `IsIsometricSphereMap F Φ` (est. 400 lines). Corollary `CD F (d-1) 0` via `CD_iff_ricci`.
- S3 (Sphere3): concrete sphere type: pullback `RiemannianBundle`, `IsContMDiffRiemannianBundle`, `IsIsometricSphereMap` (est. 300 lines).
- S4: geodesic metric (arccos distance) + `IsRiemannianManifold`, connected, complete (est. 1.5-3k lines; may be left).
- S5: `IsWeightedVolume` for the normalized sphere measure (est. 1-2k lines; may be left).
- S6: `lambda_1 >= d` (Lichnerowicz-Obata dimensional): needs dimensional Bochner `|Hess f|^2 >= (Lf)^2/d` plus an integrated
  argument; the project has no eigenfunction existence / spectral theory (see riemann-status/gap.md). Honest estimate 1-3k lines, possibly out of reach.

## State (update 1): stages S1-S4 and S5-S6 (concrete sphere, curvature part) DONE, all compile, no sorry, standard axioms
Build: `lake build CutoffRigidity.Extra.Sphere6` (chain Sphere1..Sphere6; Sphere1 imports Item6a, RicciBochner).
- Sphere1: `gauss_koszul`.  Sphere2: `sum_coord_tangent`, `deriv_tangent`, `nab_coord`.  Sphere3: `contMDiff_dfun`, `inner_nab_term`, `inner_lie_term`,
  `curv_inner : inner (curv F X Y W x) (V x) = inner (W x) (Y x) * inner (V x) (X x) - inner (W x) (X x) * inner (V x) (Y x)`.
- Sphere4 (model form, any M with `IsIsometricSphereMap F Φ`, `finrank F = d`): `sphere_mRic : mRic F x v w = ((d:ℝ) - 1) * inner v w`,
  `sphere_CD : CD F ((d:ℝ)-1) (fun _ => c)`, `sphere_not_CD` (optimality, d >= 1).
- Sphere5: `Sph d` (type synonym of `Metric.sphere 0 1 ⊂ ℝ^(d+1)`), instances: ChartedSpace (ℝ^d), IsManifold ∞, pullback RiemannianBundle,
  IsContMDiffRiemannianBundle ∞, IsContinuousRiemannianBundle.  Sphere6: `EMetricSpace` := `EMetricSpace.ofRiemannianMetric` (Mathlib; IsRiemannianManifold by `rfl`),
  CompleteSpace, `connectedSpace (hd : 1 ≤ d)`, `isIsometricSphereMap`, and the concrete theorems
  `Sph.mRic_eq`, `Sph.CD_sphere`, `Sph.not_CD_sphere`.
Remaining (next): S7 `IsWeightedVolume` for a probability measure on `Sph d` (plan: chart-density measure pushed through one stereographic chart,
generalize `local_chart_mass` to an arbitrary base chart, null pole); S8 invariance under isometries (isometric diffeo preserves IsWeightedVolume + uniqueness)
=> `mSpectralGap <= d` (Item6a `sphere_spectralGap_le`) and `d-1 <= mSpectralGap` (`mSpectralGap_ge_of_CD`); S9 lambda_1 >= d (needs eigenfunction attainment without hgap + dimensional Bochner).

## State (update 2): stages S7-S12 DONE (compile, no sorry)
- Sphere7 (generic, any manifold with the standing instances): `chart_mass_transfer` (generalization of `CutCur.local_chart_mass` to an arbitrary base chart),
  `isWeightedVolume_of_chart`, `chartMeasure`, `chartMeasure_isWeightedVolume`, finiteness/positivity, `exists_probability_isWeightedVolume`
  (compact manifold + one chart whose complement is chart-negligible => probability measure `μ` and `c` with `IsWeightedVolume F μ (fun _ => c)`).
- Sphere8: `Sph.exists_isWeightedVolume (hd : 1 ≤ d) : ∃ μ c, IsProbabilityMeasure μ ∧ IsWeightedVolume Fd μ (fun _ => c)` on the actual sphere.
- Sphere9: `mvfderiv_mgrad_phi`, `hess_phi` (Hess φ_a = -φ_a g), `mlaplacian_phi : Δ φ_a = -d φ_a`, `mgenerator_phi`.
- Sphere10: `integral_phi_identities` (∫φ_a = 0, ∫|∇φ_a|² = d ∫φ_a²), `sphere_gap_le : mSpectralGap F μ ≤ d` (NO rotation invariance used).
- Sphere11: `Sph.gap_bounds (hd : 2 ≤ d) : d-1 ≤ mSpectralGap Fd μ ∧ mSpectralGap Fd μ ≤ d` for every probability μ with IsWeightedVolume (constant potential).
- Sphere12: `exists_eigenfunction_of_compact_gap`: copy of the project's gap-attainment proof without the `CD` hypothesis (CD was used only in the last line).
Next: Sphere13 `lambda_1 >= d` via dimensional Bochner (`mlaplacian^2 <= d * mHessSq`) + integrated Bochner for the eigenfunction.

## State (update 3): ALL STAGES DONE (S1-S16). See extra-status/sphere-worker.md for the final statements. Build: `lake build CutoffRigidity.Extra.Sphere16`.
