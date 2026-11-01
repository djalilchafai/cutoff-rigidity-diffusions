# sdeid-worker (item 5): kernel = SDE law, pathwise Lemma 3.3

Verdict: both parts DONE, mostly by assembling theorems already in the library (Paper/CoreBridge.lean, Paper/EigenmapOU.lean).
File: CutoffRigidity/Extra/SdeId1.lean (`lake build CutoffRigidity.Extra.SdeId1` OK; axioms: propext, Classical.choice, Quot.sound). No human review.

Facts checked: `IsLangevinSolution` = a.e. w: path continuous AND integral equation for ALL t simultaneously, X_0 = x0 follows (t=0).
So no amendment needed. Pathwise uniqueness is already `langevin_path_unique` (monotone drift, deterministic) used in
`IsLangevinSolution.ae_eq_langevinProcess` (CoreBridge).

## (a) Lean
theorem CutoffRigidity.Paper.isLangevinSolution_map_eq_kernel {Ω} [MeasurableSpace Ω] {d} {V : Rd d → ℝ} {Pt}
  (hL : IsEuclideanLangevin V Pt) (hHess : ∀ x z, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z)
  {B P} (hB : IsStdBrownian B P) {x₀ X} (hX : IsLangevinSolution V B P x₀ X) (t : ℝ≥0) : P.map (X t) = Pt t x₀
plus `isLangevinSolution_map_eq_kernel_of_rigid` (hR : RigidCurvature V instead of hHess).
(P need not be assumed probability: it follows from IsStdBrownian.) Proof: ae_eq_langevinProcess + langevinKernel_apply_eq_process_law
+ isEuclideanDiffusion_eq_langevinKernel (kernel uniqueness, V C^infty, probability Gibbs).

## (b) Lean (pathwise Lemma 3.3; already existed as `eigenmap_is_ou_carrier`, re-exported)
theorem CutoffRigidity.Paper.eigenmap_is_ou_pathwise (hV : RigidCurvature V) (hX : IsLangevin V B P X) (T) (hT : IsEigenbasis V T) :
  let ρ := spectralGap V; let Tv := fun x => (WithLp.toLp 2 fun i => T i x : Rd (firstEigenDim V))
  ∃ β, IsStdBrownian β P ∧ ∀ x₀, ∀ᵐ w ∂P, ∀ t : ℝ≥0,
    Tv (X x₀ t w) = Tv x₀ - ρ • ∫ s in 0..t, Tv (X x₀ s.toNNReal w) + Real.sqrt (2*ρ) • β t w
No Itô needed: eigenfunctions are affine (c2_L2_eigenfunction_is_affine), <a_i,∇V> = ρ T_i, rows a_i/√ρ orthonormal,
β = orthonormal projection of B (isStdBrownian_orthonormal_image). The statement is the integral form of dY = -ρY dt + √(2ρ) dβ,
for every solution family X (IsLangevin hypothesis, any carrier), not only the canonical one.

## Not proved / scope
- (b) is the integral (strong-solution) form, as the SDE has no other meaning here; the Challenge `eigenmap_is_ou` (law form)
  can be strengthened/accompanied by this statement. The IsLangevin hypothesis includes C^2 V and probability Gibbs; V C^infty is not needed for (b).
- (a) needs V C^infty only through IsEuclideanLangevin (kernel uniqueness).
