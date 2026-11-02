# R7 sphere, round 2: worker report

Build target: `lake build CutoffRigidity.Extra.Sphere16` (chain `Sphere1` ... `Sphere16`, ~2.3k lines, all new files; nothing existing edited).
No sorry, no axiom, no native_decide; `#print axioms` of the main theorems: propext, Classical.choice, Quot.sound.
Progress/state file: `extra-status/sphere-progress.md`.

## Result: all three deliverables (a), (b), (c) are proved, for the actual round sphere in the project's own definitions

`Sph d` (Sphere5/6) is `Metric.sphere 0 1 ⊂ ℝ^(d+1)` as a type synonym with: Mathlib's smooth structure (model `ℝ^d`,
`EuclideanSpace ℝ (Fin d)`), the Riemannian metric induced by the inclusion (`immersionPullbackRiemannianBundle`, smooth of order ∞),
`EMetricSpace := EMetricSpace.ofRiemannianMetric` (Mathlib; so `IsRiemannianManifold` holds by `rfl`, the distance is the geodesic one),
`CompleteSpace` (compact), `ConnectedSpace` for `1 ≤ d`. All standing instances of `Challenge.lean` are available.
Notation: `Fd = EuclideanSpace ℝ (Fin d)`, `μ` any probability measure with `IsWeightedVolume Fd μ (fun _ => c)`.

(a) Ricci / CD (Sphere1-6):
- `Sph.mRic_eq (x) (v w) : mRic Fd x v w = ((d:ℝ) - 1) * inner ℝ v w`   (project's `mRic`, any d)
- `Sph.CD_sphere (c) : CD Fd ((d:ℝ) - 1) (fun _ : Sph d => c)`
- `Sph.not_CD_sphere (hd : 1 ≤ d) (c) {ρ} (hρ : (d:ℝ) - 1 < ρ) : ¬ CD Fd ρ (fun _ : Sph d => c)`   (d-1 optimal)
- model form (any `M` with Item6a's `IsIsometricSphereMap F Φ`, `finrank F = d`): `sphere_mRic`, `sphere_CD`, `sphere_not_CD`.
Method (no Levi-Civita uniqueness needed): Mathlib's Koszul formula + project's `mvfderiv_mlieBracket`, `nabSmooth`, `curv_tensor`:
Gauss `⟪∇_X Y, Z⟫ = ∑ₐ Z(φₐ) X(Yφₐ)` (`gauss_koszul`), `(∇_Y W)φₐ = Y(Wφₐ) + ⟪W,Y⟫φₐ` (`nab_coord`),
`⟪R(X,Y)W,V⟫ = ⟪Y,W⟫⟪X,V⟫ - ⟪X,W⟫⟪Y,V⟫` (`curv_inner`), then `Ric = (d-1) g` by summing over an orthonormal basis.

Weighted volume (Sphere7/8):
- `Sph.exists_isWeightedVolume (hd : 1 ≤ d) : ∃ (μ : Measure (Sph d)) (c : ℝ), IsProbabilityMeasure μ ∧ IsWeightedVolume Fd μ (fun _ => c)`
  (construction: chart-density measure of one stereographic chart, `chart_mass_transfer` generalizes the project's `local_chart_mass`
  to an arbitrary base chart; generic theorem `exists_probability_isWeightedVolume` for any compact manifold with one chart missing a chart-negligible set).

(b) `λ₁ ≤ d` (Sphere9-11): coordinate functions are eigenfunctions: `mlaplacian_phi : mlaplacian F (phi Φ a) x = -(d:ℝ) * phi Φ a x`,
`mgenerator_phi`; integrated identities `∫φ_a = 0`, `∫‖∇φ_a‖² = d∫φ_a²` by the project's `weightedIBP_of_isWeightedVolume`
(`integral_phi_identities`). NO rotation invariance of μ is needed (unlike Item6a `sphere_spectralGap_le`, which this supersedes).
- `sphere_gap_le : mSpectralGap F μ ≤ d` (model form);
- `Sph.gap_bounds (hd : 2 ≤ d) (hμ) : (d:ℝ) - 1 ≤ mSpectralGap Fd μ ∧ mSpectralGap Fd μ ≤ d` (lower bound = project's `mSpectralGap_ge_of_CD`).

(c) `λ₁ ≥ d` (Sphere12-14): Lichnerowicz-Obata.
- `exists_eigenfunction_of_compact_gap` (Sphere12): copy of the project's `gap_attained_of_compact` proof; the hypothesis `CD F ρ V` was
  used there only in the last line (`mFirstEigenDim_pos_iff`), so it is dropped; takes `ρ := mSpectralGap F μ`, `hgap := rfl`. Gives a nonzero smooth L² eigenfunction.
- `mlaplacian_sq_le : (Δf)² ≤ (finrank F) * mHessSq F f x` (Sphere13), `carre2_ge : Γ₂(f) ≥ (𝓛f)²/d + (d-1)Γ(f)` (Sphere14),
  integrated Bochner for the eigenfunction => `λ² ≥ λ²/d + (d-1)λ`:
- `sphere_gap_ge (hF) (hd : 2 ≤ d) (hΦ) (hμ) : (d:ℝ) ≤ mSpectralGap F μ` (model form).

Final concrete statements (Sphere15/16):
- `Sph.gap_eq (hd : 2 ≤ d) (hμ : IsWeightedVolume Fd μ (fun _ => c)) [IsProbabilityMeasure μ] : mSpectralGap Fd μ = d`
- `Sph.gap_ne_rho : mSpectralGap Fd μ ≠ (d:ℝ) - 1`   (hgap fails for ρ = d-1)
- `Sph.round_sphere (hd : 2 ≤ d) : ∃ μ c, IsProbabilityMeasure μ ∧ IsWeightedVolume Fd μ (fun _ => c) ∧ CD Fd (d-1) (fun _ => c) ∧ (∀ ρ > d-1, ¬ CD Fd ρ (fun _ => c)) ∧ mSpectralGap Fd μ = d ∧ mSpectralGap Fd μ ≠ d-1`
- `Sph.first_eigenspace_large (hd : 2 ≤ d) (hμ) : ∃ u : Fin (d+1) → (Sph d →₂[μ] ℝ), LinearIndependent ℝ u ∧ ∀ i, ∃ f, IsMEigenfunction Fd μ (fun _ => c) (mSpectralGap Fd μ) f ∧ f =ᵐ[μ] u i`
  (the first eigenspace has at least d+1 > d = dim independent elements: `CD(d-1)` holds, `hgap` fails, and the conclusion `k₁ ≤ dim M` of the Riemannian theorem is false; so `hgap` is genuinely needed.)

## What this shows / does not show
- The sphere satisfies the Challenge's CD and all standing hypotheses and is a curved Riemannian example where `λ₁ = d ≠ ρ = d-1`, exactly the manuscript's L711 remark ("the abstract theorem does not apply"). It is NOT a witness of the hypotheses of Thm 1.9 (hgap fails), and no curved witness with `hgap : λ₁ = ρ` is built (none exists on a compact manifold with ρ>0 by Obata/Lichnerowicz rigidity unless flat; not claimed).
- Not proved: finite-dimensionality of the first eigenspace of the sphere (so `mFirstEigenDim` itself is not computed; only d+1 independent eigenfunctions are exhibited); uniqueness of the weighted volume measure (not needed: statements are for every μ with `IsWeightedVolume`, and existence is proved); d = 0, 1 gap statements (`d ≥ 2` needed, CD statements hold for all d, `not_CD` for d ≥ 1); cutoff / manuscript's `λ₁/ρ → 1` stability remark (no precise statement in the manuscript).
- Item6a is unchanged; `sphere_gap_bounds_of_CD` there is now instantiated unconditionally by `Sph.gap_bounds`.
- Integration note: `Sphere12` copies a project proof (to drop one hypothesis); a lead may prefer to refactor `gap_attained_of_compact` in `DiffGapAttained.lean` instead (split off the eigenfunction part).

## Round 2 addendum: Sphere17 (`k1_fails`)
- New `CutoffRigidity/Extra/Sphere17.lean` (imports Sphere16; `lake build CutoffRigidity.Extra.Sphere17` builds the whole chain). Axioms: propext, Classical.choice, Quot.sound.
- `Sph.k1_fails (d) (hd : 2 ≤ d) {μ} [IsProbabilityMeasure μ] {c} (hμ : IsWeightedVolume Fd μ (fun _ => c)) : ¬ (1 ≤ mFirstEigenDim Fd μ (fun _ : Sph d => c) ∧ mFirstEigenDim Fd μ (fun _ : Sph d => c) ≤ d)`.
  So the conclusion of `riemannian_k1_bounds` is false on the round sphere without `hgap`.
- Docstring of `first_eigenspace_large` (Sphere16) corrected: it only gives d+1 linearly independent eigenfunction classes; no claim on mFirstEigenDim (that is k1_fails). Docstring-only edit.
