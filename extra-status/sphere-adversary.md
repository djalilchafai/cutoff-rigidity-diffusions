# Adversary report R7 (round sphere): verdict ACCEPT (with one recommended strengthening)

Recompiled `lake build CutoffRigidity.Extra.Sphere16`: OK (only linter warnings). `#print axioms` for mRic_eq, CD_sphere, not_CD_sphere,
exists_isWeightedVolume, gap_bounds, gap_eq, gap_ne_rho, round_sphere, first_eigenspace_large (namespace CutoffRigidity.Extra.Sphere.Sph):
all [propext, Classical.choice, Quot.sound]. No sorry/axiom/native_decide in Sphere*.lean (grep).

Faithfulness: `Sph d` = Metric.sphere 0 1 in R^{d+1} as a def (no inherited MetricSpace diamond), Mathlib stereographic charts with model R^d,
metric = project's immersionPullbackRiemannianBundle of the inclusion, so inner v w = <dval v, dval w> (checked by `rfl` in isIsometricSphereMap):
exactly the induced unit-sphere metric, no scaling. EMetricSpace = ofRiemannianMetric, IsRiemannianManifold by rfl. mRic, CD, IsWeightedVolume,
chartVolumeDensity, mSpectralGap, IsMEigenfunction, mFirstEigenDim: text identical to Challenge.lean (compared) and to Statements.lean.
mRic sign: docstring "positive on spheres"; mRic_eq gives (d-1) g. Junk: mSpectralGap=d is proved by two inequalities (gap_ge via an actual eigenfunction,
gap_le via coordinate test functions), d>=2>0 so sInf-empty/unbounded junk (0) cannot give it. Vacuity: exists_isWeightedVolume gives a
probability measure (chart complement of a stereographic chart is one point, null); hypotheses of round_sphere are satisfiable and d>=2 is the only restriction.
sphere_gap_ge (Sphere14) is a fresh proof; Sphere12 copies gap_attained_of_compact dropping only the CD use (semantics of definitions unchanged).
Sanity d=2: lambda_1=2, Ric=g, CD(1) optimal, gap != 1. Correct.

Scope gaps found:
1. first_eigenspace_large only gives d+1 independent classes; it does NOT state mFirstEigenDim >= d+1 (finrank of an infinite-dimensional span is 0).
   The docstring "this is what mFirstEigenDim counts" overstates. FIX (verified, compiles, standard axioms): the following closes the gap and in fact shows the
   conclusion of riemannian_k1_bounds fails on the sphere without hgap in every case (k1=0 violates 1<=k1; k1>=1 forces finite dim, then k1>=d+1):

```lean
theorem k1_fails (d : ℕ) (hd : 2 ≤ d) {μ : Measure (Sph d)} [IsProbabilityMeasure μ] {c : ℝ}
    (hμ : IsWeightedVolume (EuclideanSpace ℝ (Fin d)) μ (fun _ => c)) :
    ¬ (1 ≤ mFirstEigenDim (EuclideanSpace ℝ (Fin d)) μ (fun _ : Sph d => c) ∧
       mFirstEigenDim (EuclideanSpace ℝ (Fin d)) μ (fun _ : Sph d => c) ≤ d) := by
  rintro ⟨h1, h2⟩
  obtain ⟨u, hu, hmem⟩ := first_eigenspace_large d hd hμ
  have hpos : 0 < Module.finrank ℝ (Submodule.span ℝ
    {u : Sph d →₂[μ] ℝ | ∃ f, IsMEigenfunction (EuclideanSpace ℝ (Fin d)) μ (fun _ : Sph d => c)
      (mSpectralGap (EuclideanSpace ℝ (Fin d)) μ) f ∧ f =ᵐ[μ] u}) := h1
  haveI := Module.finite_of_finrank_pos hpos
  have hin : ∀ i, u i ∈ Submodule.span ℝ
    {u : Sph d →₂[μ] ℝ | ∃ f, IsMEigenfunction (EuclideanSpace ℝ (Fin d)) μ (fun _ : Sph d => c)
      (mSpectralGap (EuclideanSpace ℝ (Fin d)) μ) f ∧ f =ᵐ[μ] u} := fun i =>
    Submodule.subset_span (hmem i)
  set W := Submodule.span ℝ
    {u : Sph d →₂[μ] ℝ | ∃ f, IsMEigenfunction (EuclideanSpace ℝ (Fin d)) μ (fun _ : Sph d => c)
      (mSpectralGap (EuclideanSpace ℝ (Fin d)) μ) f ∧ f =ᵐ[μ] u} with hW
  have hli : LinearIndependent ℝ (fun i => (⟨u i, hin i⟩ : W)) :=
    LinearIndependent.of_comp W.subtype hu
  have := hli.fintype_card_le_finrank
  have h2' : Module.finrank ℝ W ≤ d := h2
  simp at this
  omega
end CutoffRigidity.Extra.Sphere.Sph
```
   (copy: `rintro` ... `omega`; add `have := Module.finite_of_finrank_pos hpos` from `h1`, membership by `Submodule.subset_span (hmem i)`,
   `LinearIndependent.of_comp W.subtype hu`, `.fintype_card_le_finrank`.) Not added to Extra (rule: scratch deleted); lead/worker should add it as Sphere17.
2. Thm 1.9 witness with hgap, finite-dimensionality of E1 on the sphere, k1 = d+1 exactly: not shown (only >=, and by k1_fails the exact value is not needed).
3. IsWeightedVolume for the actual round volume is only asserted for constant potential via the project definition; "e^{-c} vol_g" identification relies on chartVolumeDensity (project def, matches Challenge).

Challenge text suggestion (<=40 lines). Challenge.lean imports only Mathlib and cannot import Extra or project files, and `immersionPullbackRiemannianBundle`
(CutoffRigidity/RiemannianPullbackMetric.lean) is NOT in Mathlib. Cheapest faithful route: state GENERIC results for any M with the project's
IsIsometricSphereMap (inline that 5-line def; Item6a), which needs no Sph instances (the generic theorems sphere_mRic, sphere_CD, sphere_not_CD,
sphere_gap_ge/le in Sphere4/10/14 are generic). Then existence on Sph d is only in Extra. If concrete Sph is wanted, inline Sphere5/6 (~100 lines: the type,
instances, pullback bundle def + smoothness lemma) -- too large for the 5-line budget.
```lean
/-- Isometric immersion into the unit sphere of `E`. -/
def IsIsometricSphereMap {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (Φ : M → E) : Prop :=
  (∀ x, ‖Φ x‖ = 1) ∧ ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ Φ ∧
    ∀ x (v w : TangentSpace 𝓘(ℝ, F) x), inner ℝ v w = inner ℝ (mvfderiv 𝓘(ℝ, F) Φ x v) (mvfderiv 𝓘(ℝ, F) Φ x w)
/-- Model of the round `S^d` (any Riemannian `M^d` isometrically immersed in `S^d`): `Ric = (d-1) g`, `CD(d-1,∞)` optimal. -/
theorem sphere_ric_cd (hF : finrank ℝ F = d) {Φ : M → EuclideanSpace ℝ (Fin (d+1))} (hΦ : IsIsometricSphereMap Φ) :
    (∀ x v w, mRic F x v w = ((d:ℝ) - 1) * inner ℝ v w) ∧ ∀ c : ℝ, CD F ((d:ℝ) - 1) (fun _ => c) := sorry
/-- `λ₁ = d ≠ d-1` for such compact connected complete `M` (d ≥ 2) with probability weighted volume. -/
theorem sphere_gap_eq (hd : 2 ≤ d) ... (hμ : IsWeightedVolume F μ (fun _ => c)) : mSpectralGap F μ = d := sorry
/-- Why `hgap` is needed in `riemannian_k1_bounds`: on the round sphere, `CD(d-1)` holds but `¬(1 ≤ k₁ ≤ d)`. -/
theorem k1_needs_hgap ... -- needs concrete Sph (k1_fails); otherwise keep the docstring flag only.
```
Note sphere_gap_eq generic requires hypotheses used in Sphere14 (compact, connected, complete, IsRiemannianManifold); copy them from sphere_gap_ge.
Honest docstring points: (a) "d+1 independent eigenfunctions" is not "k1 = d+1"; (b) d>=2 needed; (c) existence of the measure is separate.
