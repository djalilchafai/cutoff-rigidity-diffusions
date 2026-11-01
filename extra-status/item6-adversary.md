# Item 6 adversary report (Item6a.lean)

Recompiled `lake build CutoffRigidity.Extra.Item6a`: OK. No sorry/axiom/native_decide/#print in the file.
`#print axioms` (scratch file outside repo) on sphere_spectralGap_le, sphere_gap_bounds_of_CD, norm_mgrad_sq,
coord_moments, range_deriv_eq: only propext, Classical.choice, Quot.sound.

## Verdicts
- `sphere_spectralGap_le`: ACCEPT (as a model-theoretic statement; see non-vacuity below).
- `sphere_gap_bounds_of_CD`: REPAIR (as written it is VACUOUS). Repair compiles, see below.

## Defect in `sphere_gap_bounds_of_CD`
It assumes `IsProbabilityMeasure μ` and `IsWeightedVolume F μ (0 : M → ℝ)`. The latter says mu = vol_g exactly
(density e^0 * sqrt(det g) in every chart), so mu(M) = vol_g(M). By (2) below, for d >= 2 and M connected, M is
isometric to the unit round S^d, so mu(M) = vol(S^d) = 2 pi^((d+1)/2)/Gamma((d+1)/2), which is a nonzero rational times
a power of pi (odd d: rational * pi^((d+1)/2); even d: rational * pi^(d/2)), hence transcendental, hence != 1.
Contradiction with probability. So no model satisfies the hypotheses: the conditional is vacuously true.
(The first theorem is NOT affected: it has no volume hypothesis.)
Repair: replace the potential 0 by an arbitrary constant c:
  (c : ℝ) (hvol : IsWeightedVolume F μ (fun _ : M => c)) (hCD : CD F ((d : ℝ) - 1) (fun _ : M => c))
and `contMDiff_const` for V. I compiled this change in a scratch copy
(/tmp/claude-1000/-chome-djay-S--Publis-2025-CRAS-CF-lean/25ce202f-e16f-4c7d-901c-94cac4f5c39d/scratchpad/adv6/B.lean):
compiles, no other edits needed (the type annotation `fun _ : M => c` is required, else instance stuck).
With c = log vol(S^d) the hypotheses are the true ones for the normalized round measure.

## Answers to the specific questions
(1) Satisfiability of theorem 1. d = 1: M = circle R/2piZ with unit speed Phi = (cos, sin), mu = normalized Haar:
Phi_* mu is O(2)-invariant, so hmu holds; Phi is isometric (unit speed). So non-vacuous mathematically. For d >= 2
the hypotheses hold exactly for M = S^d, Phi = inclusion, mu = normalized area (also for disjoint unions of copies
of S^d with equal weights, or the k-fold cover of the circle when d = 1). No Lean witness is cheap: Mathlib has no
RiemannianBundle on spheres (I could not find one); the induced bundle needs the pulled-back inner product on
TangentSpace of EuclideanSpace sphere, with IsContMDiffRiemannianBundle (smooth local trivializations via the
sphere charts, i.e. stereographic charts), plus EMetricSpace/instance coherence, plus the O(d+1) invariance of the
normalized measure (Mathlib has a Haar-on-sphere? probably only via `Measure.toSphere`; invariance under
orthogonal maps would need to be proved). I estimate 500-1000 lines; the worker's 300-600 is plausible only for
the bundle, the invariance of toSphere and the atlas smoothness on top push it higher. Not recommended.
(2) Forcing sphere. dim M = d, Phi smooth with the isometry identity gives d Phi injective with image (Phi x)^perp
of dimension d (the file proves this: `range_deriv_eq`), so Phi is a local diffeo/local isometry M -> S^d. With M
compact it is a covering map, so for d >= 2 and M connected it is an isometry onto S^d (simply connected); d = 1
gives a k-fold covering circle. Without connectedness M is a finite disjoint union of such. So the statement
genuinely concerns the round sphere (with the caveat that Item6a does not prove this; it does not need to).
Note hypotheses of theorem 1 do not include connectedness; the conclusion lambda_1 <= d is then true trivially
for the extra components (gap 0), fine.
(3) Junk values. mSpectralGap = sInf of the Rayleigh set over smooth compactly supported f with variance > 0. In the
proof the test function f = <e_0, Phi> is ContMDiff, compact support from CompactSpace, variance = 1/(d+1) > 0, so it is
in the test class; set is nonempty and bounded below (by 0), so `csInf_le` is used legitimately, no sInf-empty junk.
The Rayleigh value (1 - 1/(d+1))/(1/(d+1)) = d is checked by the proof. `mgrad` is the Riemannian gradient via the
project's bundle; norm_mgrad_sq proved from the isometry identity, not assumed.
(4) Challenge entry. Not recommended in the present form. Theorem 1 is true and non-vacuous but conditional on an
unconstructed model, its content is a one-line Rayleigh computation, and nobody can instantiate it in Lean
today; it would be a statement whose only instances live outside the formal library. The conditional bound is
vacuous as written, and even after repair gives only d-1 <= gap <= d, weaker than the manuscript's lambda_1 = d.
If the lead wants something, add theorem 1 as a Solution-side/Extra lemma (documented model-theoretic form,
like geoB `sphere_curvature_gap`), not a Challenge item; or include the repaired conditional with the explicit
caveat. A Challenge entry should wait until a real sphere instance (or an equality lambda_1 = d) exists.

## Remainder of item 6
(a) CD(d-1) and lambda_1 = d: genuinely blocked for the real sphere by the missing Riemannian structure on S^d in
Mathlib; the statements themselves are precise (CD(d-1,V=const) for the model; lambda_1 >= d via Bochner/Obata
is the sharp CD(d-1) improvement requiring dimension-dependent Bakry-Emery CD(rho,n), n = d, which the project's
CD(rho,infinity) does not state). So lambda_1 = d needs (i) the sphere instance, (ii) Ric = (d-1) g from the project's
mCurv on that instance, (iii) Obata-type/dimensional Bochner (or the spherical harmonics decomposition).
Cheaper route I see: circle d = 1 where M = ZMod/AddCircle has a flat structure: Mathlib has
AddCircle with ChartedSpace and a trivial tangent space; the Riemannian bundle there is the product metric
(still needs IsContMDiffRiemannianBundle but is far cheaper than S^d); d = 1 gives rho = 0 and lambda_1 = 1 for the unit
circle (Wirtinger), a genuine concrete instance of the model theorem 1 (Phi = (cos, sin)). Also the first-eigenvalue
upper bound could be established for any instance via the same coord argument. Lower bound lambda_1 >= 1 on the circle
is Fourier/Wirtinger and exists in Mathlib-ish forms (no, need to check). Feasibility moderate, value low
(d = 1 where d-1 = 0 is degenerate for rho > 0 hypotheses).
(b) Gaussian isoperimetry: no precise statement in the manuscript beyond citation; I agree it has no precise
statement to formalize. A cheap alternative would be the Gaussian Poincare/log-Sobolev already in the project via
OU CD(1), not isoperimetry.
(c) Theorem 1.7 on manifolds: agree blocked/not stated with exact hypotheses (requires manifold analogue of the
Langevin cutoff, i.e. the whole Riemann-section dynamics with Gamma_2 comparisons) unless the lead can reuse the
Riemannian infrastructure; no cheap route found.
