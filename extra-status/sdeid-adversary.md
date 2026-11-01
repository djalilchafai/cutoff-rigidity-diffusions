# SdeId1 adversary report (item 5)

Files inspected: CutoffRigidity/Extra/SdeId1.lean, Paper/CoreBridge.lean (`IsLangevinSolution.ae_eq_langevinProcess`, `map_eq_langevinKernel`),
Paper/EigenmapOU.lean (`eigenmap_is_ou_carrier`), Challenge.lean definitions, cutcur-lean.tex Lemma 3.3 (lem_proj_ou).
Rebuilt: `lake build CutoffRigidity.Extra.SdeId1` OK. grep sorry/axiom/native_decide/#print in SdeId1.lean: none.
`#print axioms` (scratch, outside repo) on isLangevinSolution_map_eq_kernel, ..._of_rigid, eigenmap_is_ou_pathwise,
IsLangevinSolution.ae_eq_langevinProcess, eigenmap_is_ou_carrier: only propext, Classical.choice, Quot.sound.

## Claim (a) isLangevinSolution_map_eq_kernel: ACCEPT
- `IsLangevinSolution`: a.e. w, paths continuous AND integral equation for all t simultaneously (inside the ∀ᵐ). Integral over `0..t` of
  `gradient V (X s.toNNReal w)`. Faithful to SDE (1.1) in strong form. Strong form is what `langevin_path_unique` needs; the theorem uses it correctly.
- Measurability: `P.map (X t)` is fine because `X t =ᵐ langevinProcess ...` (ae_eq_langevinProcess), `Measure.map_congr` needs no measurability of X t;
  no AEMeasurable hypothesis needed and none hidden.
- P is not assumed a probability measure, but `IsStdBrownian` forces it. I tried d = 0, P = 0 (the only worrying degenerate case): `iIndepFun` over the
  empty index family fails for the zero measure, so IsStdBrownian does not hold; the theorem compiling confirms there is no gap.
- Hypotheses: `IsEuclideanLangevin V Pt` (C^infty V, probability Gibbs, diffusion semigroup) + convexity (hHess). The proof uses only V C^2
  (hL.1.of_le) for the solution side and C^infty for kernel uniqueness; nothing false for nonsmooth V (V is smooth by hypothesis).
  Convexity is an extra hypothesis vs the manuscript, but needed (global existence/kernel identification via library) and automatic under RigidCurvature
  (the `_of_rigid` corollary is correct).
- Non-vacuity witness (scratch /tmp/.../scratchpad/sdeadv/T2.lean, compiles, no sorry): for any smooth convex V with probability Gibbs, `exists_euclideanLangevin`
  gives Pt, `exists_langevin` gives (Ω,B,P,X) with IsLangevin, and the theorem then yields `P.map (X x₀ t) = Pt t x₀` for all x₀, t. So all hypotheses
  are jointly satisfiable and the conclusion is nontrivial (identifies SDE law with the abstract kernel).
- Value: this closes the "Brownian-free replacement" gap: shows the Challenge's IsEuclideanDiffusion semigroup really is the law of the SDE solution
  for any solution (not only the library's langevinProcess).

## Claim (b) eigenmap_is_ou_pathwise: ACCEPT as statement, with the caveat that it is only a rename
- It is literally `eigenmap_is_ou_carrier hX hV T hT` (same statement, same variable order). It adds NO new mathematics; it only re-exports the
  existing theorem under a Challenge-friendly name (its hypotheses are all Challenge definitions: IsLangevin, RigidCurvature, IsEigenbasis).
- Statement check: β : ℝ≥0 → Ω → Rd (firstEigenDim V) with `IsStdBrownian β P` (independent standard real Brownian coordinates, same P); ∃ β chosen once,
  then ∀ x₀, ∀ᵐ w, ∀ t: `Tv(X x₀ t w) = Tv x₀ - ρ ∫_0^t Tv(X x₀ s.toNNReal w) ds + √(2ρ) β t w`. This is exactly dY = -ρY dt + √(2ρ) dβ, Y₀ = T x₀.
  Normalisation correct (rows of ∇T have norm √ρ, so √2·(∇T)B = √(2ρ)β). Quantifier structure strong: one β for all x₀ (nontrivial), a.e. w with all t
  simultaneously. Integral convention matches IsLangevinSolution.
- Junk values: firstEigenDim = 0 would make the statement trivial, but under RigidCurvature + smooth + probability Gibbs, `one_le_firstEigenDim` (Paper/SpectralBridge)
  gives 1 ≤ firstEigenDim; so no junk. (hX contains ContDiff 2 and the probability Gibbs.) ρ = spectralGap > 0 by RigidCurvature.
- Non-vacuity witness (scratch T2.lean, compiles): for smooth rigid V with probability Gibbs: `exists_isEigenbasis` gives T, `exists_langevin` gives IsLangevin data,
  `eigenmap_is_ou_pathwise` produces β with IsStdBrownian. All hypotheses satisfiable (e.g. OU potential via ou_gap_rigid).
- Versus manuscript: lem_proj_ou claims "T(X) is a Markov process with generator ρΔ - ρx·∇". The pathwise form gives that Y is a strong solution of the OU SDE
  (hence, by uniqueness of linear SDE, Y is a measurable functional of β, and Markov/OU in law). Neither the pathwise form nor the Challenge law form states
  the Markov property or the generator explicitly; the pathwise form is the stronger of the two (it implies the Gaussian marginals by a linear computation but
  not conversely), and is closer to the manuscript's Brownian-based Lemma 3.3. It does not state adaptedness of β to a filtration (IsStdBrownian has none), but
  β is a function of B, and Y is a functional of β by the displayed equation.
- Relation to Challenge `eigenmap_is_ou` (line 326, law form from IsEuclideanLangevin): different hypotheses (needs a Brownian carrier, not just a kernel) and
  different conclusion (process level vs time-t marginals). It strictly adds the process-level identity, but note that `eigenmap_is_ou_carrier` was already
  proved and available to the lead; SdeId1 contributes nothing beyond the name.

## Recommended Challenge entries (lead decides; Challenge.lean at 981/1000)
1. (a) `isLangevinSolution_map_eq_kernel` (convex form), about 10 lines with docstring: statement as in SdeId1.lean lines 25-32 (hL, hHess, hB, hX, t) with `Pt` and
   conclusion `P.map (X t) = Pt t x₀`; it fits in 19 lines. Put it after `IsEuclideanLangevin`/`exists_langevin` (Solution: apply isLangevinSolution_map_eq_kernel).
   If lines are scarce, use the rigid form (replace hHess by `hR : RigidCurvature V`), same length. Value: high (it makes the kernel-replacement honest).
2. (b) `eigenmap_is_ou_pathwise`, about 12 lines (statement lines 52-62 plus a 2-line docstring); fits in 19 lines together with (a) only if docstrings are
   kept to 1-2 lines (total about 22-24, so it does NOT fit both fully: 981 + 24 > 1000). Recommend: include (a) (about 11 lines) and (b) with a one-line docstring
   (about 12 lines) = about 23 lines, i.e. over budget by ~4; either shorten or choose (a) only. Since (b) is just a rename, if only one fits prefer (a);
   (b) can be surfaced via Solution/Statements alias without Challenge entry only if the lead decides to extend the Challenge.

## Verdict
(a) ACCEPT. (b) ACCEPT (faithful, nonvacuous, but a pure re-export of `eigenmap_is_ou_carrier`; novelty: none; count it as "already formalized, now surfaced").
No repair needed.
