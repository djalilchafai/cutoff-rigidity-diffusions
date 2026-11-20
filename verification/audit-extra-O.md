# Audit O (adversarial, statement only): `exists_euclideanLangevin_of_convex` (no. 68) and the definitions it uses

Method: I read the statement in `Challenge.lean` (C135-137) and `PalomarChallenge.lean` (C125-127, the same text), the definitions `Rd`, `gibbs`, `laplacian`, `generator`, `IsEuclideanDiffusion` and `IsEuclideanLangevin` (C28-82, identical in both files and in `CutoffRigidity/Statements.lean`), and compared them with `cutcur-lean.tex` (T86-108).
I did not read proofs to judge fidelity.
I wrote one scratch file outside the repo (`AuditO.lean`, which imports `Solution`). It compiled with `lake env lean`, and checks the following:
(a) the hypotheses are inhabited by `V(x) = |x|²/2 + (d/2) log(2π)`, for every `d`. `ContDiff` comes from `contDiff_norm_sq`, `hHess` from `CutoffRigidity.hessian_quadraticLangevinPotential` (it equals `‖z‖² ≥ 0`), and `hp` from the Challenge statement `gibbs_quadratic_isProb`. With these, `exists_euclideanLangevin_of_convex` gives `∃ Pt, IsEuclideanLangevin V Pt`;
(b) `#check C2U.euclideanDiffusion_unique_convex` shows it is stated for the same `CutCur.IsEuclideanDiffusion` (hypotheses: `ContDiff ℝ 2 V`, `ConvexOn ℝ univ V`; no Gibbs hypothesis);
(c) as a corollary, two `IsEuclideanLangevin V` kernels coincide when `V` is convex `C²`;
(d) `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound` for both theorems.
I edited no repo file except this report.

## Verdict: FAITHFUL WITH REMARKS (no defect)

### 1. Truth and match with the paper's setting
- T88-95: the paper assumes `V` is strictly convex, `C²`, with `V → +∞`, and adds a constant so that `e^{-V}` is a probability density.
  The Lean hypotheses are `C²`, `D²V(x)(z,z) ≥ 0` (which is equivalent to convexity for `C²` `V`), and that `gibbs V` is a probability measure.
  Every paper potential satisfies them: a convex coercive function grows at least linearly, so `e^{-V}` is integrable. The Lean class is LARGER, because strict convexity is dropped, and coercivity follows from convexity plus integrability.
  So the existence claim covers the paper's setting, and more. It is mathematically true: the drift `-∇V` is locally Lipschitz and satisfies the one-sided bound `⟨x, -∇V(x)⟩ ≤ |x||∇V(0)|` (from convexity), so the SDE has a non-exploding strong solution from every point.
  Its laws form a Markov semigroup, and Itô gives the Dynkin identity on `C_c^∞` with `s ↦ E[𝓛f(X_s)]` continuous.
- `hp` and `hV` are necessary, because they are conjuncts of `IsEuclideanLangevin`.
  `hHess` is probably not needed for existence alone: with a finite invariant measure the diffusion should be conservative. But it matches the paper's standing assumption, it is what makes uniqueness available, and it is harmless. Nothing is missing.
- `d = 0`: `Rd 0` is a point, and `gibbs V` is a probability measure iff `V(pt) = 0`. Then the only Markov kernel satisfies the identity (`Δ = 0`, `∇ = 0`). This case is true and trivial, and it is the correct degenerate Langevin process. No vacuity.

### 2. Is the predicate too weak (fake `Pt`)? No, under convexity
Junk checks on the Dynkin identity `∫ f d(Pₜx) = f(x) + ∫₀ᵗ ∫ 𝓛f d(Pₛx) ds`:
- Inner integral: `𝓛f = Δf - ⟨∇V, ∇f⟩` is continuous (since `V ∈ C¹`) and compactly supported, hence bounded. `Pₛx` is a probability measure (`IsMarkovKernel`), so the inner integral is never Bochner junk.
- Outer interval integral: the integrand is bounded, so junk 0 could only come from non-measurability of `s ↦ ∫ 𝓛f d(Pₛx)`.
  I tried to build a fake `Pₜ = Q_t ∘ R_{h(t)}` for the OU potential, where `R` is a rotation (it commutes with OU) and `h` is a non-measurable additive angle function. The semigroup law and the Markov property hold.
  But wherever the time integrand fails to be measurable, the identity forces `∫ f d(Pₜx) = f(x)`, which is false for such `Pₜ`. And `x = 0` gives a genuine identity anyway.
  More decisively, `euclideanDiffusion_unique_convex` (proved, standard axioms, in `Solution`'s import closure, check (b)) shows that ANY two `IsEuclideanDiffusion V` families coincide for convex `C²` `V`. So no fake `Pt` exists in the convex setting, whatever the junk conventions.
  The genuine Langevin transition kernel satisfies the predicate (Itô, as above). So the unique witness IS the Langevin semigroup (a mathematical, not Lean, step).
- `s.toNNReal`: the interval is `[0, t]` with `t ≥ 0`, so no negative times are used and the orientation is correct.
- REMARK (trust boundary): `euclideanDiffusion_unique_convex` is NOT a Challenge/Comparator statement; it lives in `Extra/C2Uniq7`.
  A reviewer who relies only on the Comparator surface gets existence (no. 68), not uniqueness. Without uniqueness, the kernel theorems (Thm 1.1, Cor 1.3/1.4, (1.25), 1.6, Thm 1.7, Lemma 3.3) hold for every `Pt` satisfying the predicate. Because uniqueness holds, they are about the Langevin semigroup and nothing else.
  The uniqueness statement is short and uses only Challenge definitions (it can be read via `#check`). Recommendation: promote it to the Challenge (e.g. `euclideanDiffusion_unique_convex` with `ConvexOn` or the same `hHess` form), so that both existence and uniqueness are Comparator-checked. Severity: low (documentation/trust), not a fidelity defect.
- Existence alone does not show that the witness is the SDE law. That identification is a Challenge statement only under `RigidCurvature` (no. 49). This was already noted in audit N.

### 3. Inhabitation
Confirmed in Lean, check (a), for `V = |x|²/2 + (d/2) log(2π)` and every `d`, using only Challenge statements (`gibbs_quadratic_isProb`) plus standard calculus.

### 4. Docstrings
- Theorem: "for a `C²` potential with nonnegative Hessian (that is, convex) and probability Gibbs measure, the Euclidean Langevin semigroup exists". This is accurate.
  Suggested additions: "a kernel family satisfying `IsEuclideanLangevin` exists; it is unique (`euclideanDiffusion_unique_convex`, not a Challenge statement); the hypotheses are weaker than the paper's (strict convexity not required; `V → ∞` follows from convexity and integrability)".
- `IsEuclideanLangevin`: "Satisfiable for convex `C²` `V`" could read "for every convex `C²` `V` whose Gibbs measure is a probability measure". That condition is implied by the predicate itself, so this is cosmetic.
- `IsEuclideanDiffusion`: "so it is the law of the SDE (1.1) solution" overstates what is formalized. Inside the Challenge this holds only under `RigidCurvature` (no. 49); otherwise it rests on Itô/Dynkin for the SDE law, which is not formalized for general convex `V`.
  Suggest: "(mathematically, the SDE law satisfies this predicate, hence equals `Pt`; in Lean, kernel = SDE law is proved under `RigidCurvature`, `isLangevinSolution_map_eq_kernel_of_rigid`)". This repeats audit N's remark.
- The uniqueness lemma's name is cited in two docstrings but is not on the Comparator surface. Say so explicitly ("proved in `Extra/C2Uniq7`, not a Challenge statement").
