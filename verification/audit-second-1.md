# Independent second audit of Challenge theorems 1-7 (AI, 25 October 2026)

Nature: an AI audit by a second, independent agent. It is not a human review. I read
`Challenge.lean` lines 1-262 and `cutcur-lean.tex` lines 83-430 (and `AUDIT_BRIEF.md`) and
formed verdicts BEFORE reading `verification/semantic-audit.md`. I did not read proofs. I did not
run Lean scratch files: the checks below are by reading Challenge.lean, the Mathlib sources for
`IsBrownianReal` and `klDiv`, and hand computations (OU closed forms). No project file was edited.

## 0. Summary

No defect found in theorems 1-7. All seven are faithful; four carry remarks (none affects truth or
non-vacuity).

| # | Theorem | Paper | Verdict |
|---|---|---|---|
| 1 | `main_wasserstein_estimate` | Thm 1.1 (T:126-151) | faithful |
| 2 | `eigenspace_dim_and_lambda` | Rem 1.2 (T:153-164) | faithful (adds `1 <= k1`, a harmless strengthening) |
| 3 | `wasserstein_cutoff` | Cor 1.3 (T:166-193) | faithful |
| 4 | `information_cutoff` | Cor 1.4 (T:229-261) | faithful |
| 5 | `lp_cutoff` | (1.25) (T:387-409) | faithful with remark (`p = infinity` excluded, correctly) |
| 6 | `convex_interaction` | Thm 1.5 (T:307-318) | faithful with remark (`0 < d`, necessary) |
| 7 | `convex_interaction_cutoff` | Cor 1.6 (T:336-347) | faithful |

Note on the brief: Theorem 1.1 in the manuscript has NO covariance correction. The formula is
`q/lam * sup Lambda + k1 (1 - sqrt(1-q))^2 / lam <= sup W2^2 <= q sup int |x-x0|^2 dmu`, `q = e^{-2 lam t}`.
The Lean statement matches it term by term (see 1.1 below).

## 1. Definitions (Challenge.lean 1-150), adversarially

* `gibbs`: `withDensity (ofReal (exp (-V)))`. Probability only under hypothesis. OK.
* `laplacian`/`generator`: `sum_i D^2 f(e_i,e_i)`, `Delta f - <grad V, grad f>`. Right normalisation for
  `dX = -grad V dt + sqrt2 dB`. Used only on `C^2` functions, so no `fderiv` junk.
* `spectralGap`: `sInf` of Rayleigh quotients over `C_c^infty`, `Var > 0`. Quotients are `>= 0` so
  `sInf` is a true infimum; the set is empty iff `d = 0`, giving junk `0`. Every consumer has
  `0 < spectralGap` (RigidCurvature, which therefore excludes `d = 0`) or explicit `0 < d`/`rho > 0`.
  `variance` is applied to bounded functions: no `evariance.toReal` junk. Equals the bottom of the nonzero
  spectrum of the Friedrichs extension (`C_c^infty` is a form core for locally bounded smooth-enough
  weights); under strong convexity this is the paper's `lam1`.
* `IsEigenfunction`: `C^2`, `MemLp 2`, pointwise equation. The constants are excluded when `lam > 0`.
  `lam` closed under linear combination, so `firstEigenspace` (span of classes) consists of classes of
  eigenfunctions. With `V in C^2` elliptic regularity gives `C^2` (W^{2,p}_loc then C^{2,alpha}), so the
  paper's `E1` has C^2 representatives; by essential self-adjointness every classical `L^2` solution is in the
  domain. The Lean `E1` therefore equals (and is at worst contained in) the paper's `E1`.
* `firstEigenDim`: `finrank`; junk `0` if infinite-dimensional, but `1 <= k1` in theorem 2 (and discreteness)
  rule that out. Not used elsewhere without that.
* `IsEigenbasis`/`eigenLambda`: `k1` orthonormal elements of a `k1`-dimensional space are a basis; the
  `iSup` is over a nonempty set (a basis exists), `ofReal` of a nonnegative sum, no truncation.
* `RigidCurvature`: `0 < gap` and `Hess V(x)(z,z) >= gap |z|^2` for all `x, z`, with `fderiv (fderiv V)`
  (V `C^2` supplied by IsLangevin / explicit hypothesis). Matches (1.4). Implies strong convexity, so the
  paper's "strictly convex, V -> infinity" is implied, not lost.
* `IsStdBrownian`/`IsLangevinSolution`/`IsLangevin`: I checked Mathlib's `IsBrownianReal`: it contains
  `HasLaw` of every finite-dimensional restriction against `projectiveFamily` (so `P` is forced to be a
  probability measure once `d >= 1`, `B 0 = 0` a.s., coordinates AEMeasurable) plus a.s. continuity. Coordinates are
  independent. The SDE is the integral equation, a.s. for all `t` simultaneously, with `s.toNNReal` only on
  `s >= 0`. Because `Hess V >= gap > 0` the drift is monotone, so a strong solution exists, unique and
  non-exploding, and `P.map (X x0 t)` is a genuine probability law (AEMeasurable via the equation; if it were
  not, `map = 0` would make `wasserstein2 = top` and break the upper bound, but the hypotheses exclude this).
  Hypotheses are jointly satisfiable in principle (e.g. OU on a Wiener space) but, as in the earlier audit, a
  concrete instance requires the existence of Brownian motion (not available in Mathlib at the pinned revision).
* `wasserstein2`: `inf` over couplings (marginals by `Measure.map fst/snd`, prob. measures) of
  `int edist^2`, then `^(1/2:R)` in `R>=0inf`. `edist` on `EuclideanSpace` is the `l^2` distance. `top^(1/2) = top`,
  `0^(1/2) = 0`. `(a^(1/2))^2 = a`, so `W2^2` in theorem 1 is the coupling cost exactly. Infimum over an empty
  set is `top` (only for non-probability inputs, never here). Borel sigma-algebra on the product equals the
  product sigma-algebra (second countable). OK.
* `tvDist`: real `iSup` over measurable sets of `|mu A - nu A|`; bounded by 1 for probability measures, index
  type nonempty. `ofReal` at use is lossless. OK.
* `fisherInfo`: the identity `int sqrt(h) grad phi = - int phi G` has no measure written, so it is against
  LEBESGUE measure (the weak gradient of `sqrt h` in the usual sense), while `G in L^2(mu)`. This is the
  correct notion (a `mu`-weighted integration by parts would have produced `grad u - u grad V`). I checked the
  Bochner-junk risk: `e^{-V}` is locally bounded below, so `G in L^2(mu)` implies `G in L^2_loc(dx)`, and
  `sqrt h in L^2(mu)` (since `nu` finite) gives local integrability of `sqrt h grad phi`, so the integrals are
  never junk-zero for the laws that occur. Uniqueness of the weak gradient makes `inf_G` a single value;
  empty set gives `top` (the paper's `+infinity` convention). `4 int |grad sqrt h|^2 dmu = int |grad h|^2/h dmu`.
  Matches T:219-226 for smooth positive `h`.
* `klDiv`: Mathlib: `ofReal(int llr + nu.real - mu.real)` if `mu << nu` and `llr` integrable, else `top`.
  For probability measures this is `H(nu | mu)` with the paper's convention.
* `relLp`: `if nu << mu then eLpNorm (rnDeriv.toReal - 1) p mu else top`. The `toReal` of a `top` density is
  junk only on a `mu`-null set for `nu` finite and `nu << mu`. OK.
* `worst`: `iSup` over `x0 in S` of `delta (P.map (X x0 t.toNNReal))`. `t.toNNReal` clamps negative times to `0`;
  all times used are `(1 +- eps) t*` with `t* >= 0` (gap > 0, `log n >= 0`), so no clamping occurs.
* `HasCutoff`: `forall eps in (0,1)`, then `Tendsto` at `(1-eps) t_n` to `before` and `(1+eps) t_n` to `after`.
  The quantifier order (`eps` first, limit in `n`) is that of the paper. The range `eps in (0,1)` is the paper's.
  `n = 0` (`log 0 = 0`) is irrelevant for a limit.
* `meanBall`: closed ball of radius `c sqrt d` about `int x dmu` (Bochner of an integrable function: the measure
  has Gaussian tails under strong convexity). Matches `{|x - m| <= c sqrt d}`. `meanCube`: `|x_i - m_i| <= c`
  for all `i`; matches `m + [-c,c]^d`.
* `criticalTime d gap = log d / (2 gap)`; `gap = 0` junk never occurs (gap > 0 in every use).
* `IsRigidSequence`: `forall n > 0`, IsLangevin and RigidCurvature, and `0 < liminf ofReal(gap_n)` in `R>=0inf`
  (a `liminf` of `top` is allowed, as the paper's `liminf > 0` allows `+infinity`). OK.

## 2. Per-theorem verdicts

### 1. `main_wasserstein_estimate` (C:153-166) vs Thm 1.1 (T:126-151). Faithful.
* Lower bound: `ofReal(q/gap) * (sup_S Lambda) + ofReal(k1 (1 - sqrt(1-q))^2 / gap)` with `q = exp(-2 gap t)`: identical to T:135-137.
  `q/gap > 0`, so `0 * top` does not occur; `Lambda = top` forces `top <= sup W` (the right meaning).
  Sanity check with OU (`V = rho|x|^2/2`, `Lambda = rho|x0|^2`, `k1 = d`): both sides equal
  `q|x0|^2 + d(1 - sqrt(1-q))^2/rho`, the exact W2^2. At `t = 0` the lower bound is `(Lambda + k1)/lam <= int|x-x0|^2 dmu`, plausible.
* Upper bound: `sup W <= ofReal q * sup_{x0} int edist(x,x0)^2 dmu` (T:139). Parsing: `A <= B /\ C <= D` inside the
  `forall S, S.Nonempty ->` is as intended (the iSup is a single term at the right precedence).
* Ranges: all `t >= 0` (`t : R>=0`), all nonempty `S`. Matches.
* Ball refinement: `mean = 0 -> forall R >= 0, lower(ofReal(gap R^2)) <= sup_{|x0|<=R} W`. The paper says `sup Lambda` over the
  ball "can be replaced by `lam1 R^2`". It is true and sharp: for centred `mu`, `E1` consists of the linear functions
  `sqrt(lam) <e, x>` (Gaussian factor), so `Lambda(x0) = lam |P x0|^2` and `sup = lam R^2` (needs `k1 >= 1`). The Lean form is
  the resulting inequality, k1-term kept, same as the paper. No covariance correction exists in the manuscript or is needed.
* Hypotheses: `IsLangevin` (V C^2, prob. measure, Brownian, solutions) plus `RigidCurvature`. Strictly convexity and `V -> infinity` of the paper are implied. `d = 0` is excluded by `0 < gap`. No dropped hypothesis, none added beyond the amended carrier.
* Remark only: `IsLangevin` demands solutions for ALL `x0` with the same `B`; harmless (strong solutions).

### 2. `eigenspace_dim_and_lambda` (C:170-173) vs Rem 1.2. Faithful.
`1 <= k1 <= d` (paper: `k1 <= d`; `1 <= k1` is the eigenvalue claim and also rules out the `finrank` junk `0`) and
`Lambda(x0) = sum f_i(x0)^2` for EVERY orthonormal basis (Parseval). The `forall f` is not an existence claim, but a basis exists
(finite-dimensional, `k1 >= 1`), so the set is nonempty and the statement is not vacuous. "Elements of `E1` are `C^2`" is built into the
definition rather than being a theorem (see section 1). No hypothesis beyond `C^2`, probability, RigidCurvature.

### 3. `wasserstein_cutoff` (C:189-193) vs Cor 1.3. Faithful.
`HasCutoff` of `sup_{x0 in ball(m, c sqrt d)} W2` at `log n/(2 gap_n)`, before `top`, after `0`, `c > 0` arbitrary, `eps in (0,1)`.
Sanity: before: `q = n^{-(1-eps)}`, ball refinement gives `W2^2 >= c^2 n^{eps} -> infinity`, independent of `gap`;
after: `W2^2 <= n^{-(1+eps)}(Tr Cov + c^2 n) <= n^{-eps}(1/liminf gap + c^2) -> 0`. Hypotheses = IsRigidSequence. Faithful, nothing added or missing. (`W2` is `R>=0inf`-valued, so `top` before is meaningful.)

### 4. `information_cutoff` (C:198-207) vs Cor 1.4. Faithful.
Adds exactly the paper's `lam = o(log d)` (`=o[atTop] log`). Three profiles: Fisher `top -> 0`, KL `top -> 0`, TV `1 -> 0` (`1` in `R>=0inf`). Uses the definitions checked in section 1. The TV limit `1` is `ofReal` of a real sup, no truncation. Faithful.

### 5. `lp_cutoff` (C:213-219) vs (1.25). Faithful with remark.
`p : R>=0inf`, `1 <= p`, `p != top`; before-limit `if p = 1 then 2 else top`, after `0`. This is the paper's `max` (T:406). The paper's range is `1 <= p < infinity`, so the Lean one is identical. The manuscript says "all `p`" in the abstract (T:70) while the body (T:407) says `p = infinity` is excluded; the Lean docstring is right. Hand check of the Lp norm for OU, `x0 = 0`, `rho = 1`: `int h^p dmu = (1-q^2)^{-d(p-1)/2}(1+(p-1)q^2)^{-d/2} ~ exp(d p(p-1) q^4/4)`, so the `L^p` norm tends to 1 (i.e. `|h-1|_p -> 0`) only for `t > (1/4) log d`; for the worst initial point in the ball of radius `c sqrt d`, the shift term `exp(c^2 p(p-1) q^2 d/2)` gives the transition exactly at `q^2 d ~ 1`, i.e. `t* = (1/2) log d`. So the cutoff time is `t*`, as claimed. Assumes hypotheses of Cor 1.4 (IsRigidSequence + `o(log)`), as the paper does (T:387-389). Remark: `p = 1` limit `2` equals twice the TV limit `1`; consistent.

### 6. `convex_interaction` (C:229-240) vs Thm 1.5. Faithful with remark.
* `0 < d`: necessary (for `d = 0`, `spectralGap = sInf empty = 0 != rho`). Harmless.
* `hp : IsProbabilityMeasure (gibbs V)` is the paper's normalisation ("add a constant to V"). Satisfiable (e.g. `W` = constant). Shifts preserve `C^2`, convexity and invariance, so no loss.
* (i) `spectralGap V = rho` and `IsEigenfunction V rho (sum x_i)`: `E1` membership follows because `gap = rho` is in the same conjunct. `Delta(sum x_i) = 0`, `grad(sum x_i) = (1,...,1)`, `<grad V, 1> = rho sum x_i + <grad W, 1> = rho sum x_i` by invariance. OK.
* (ii) `rho |z|^2 <= Hess V` equals "`rho`-convex" for `C^2`. The Gaussian factor is stated as the product identity `law(<u,x>, pi x) = N(0, 1/rho) tensor law(pi)` under `mu`, with `u = (1,..,1)/sqrt d`, `pi x = x - <u,x>u`. Stronger than the paper's wording and correct from the factorisation `e^{-V} = e^{-rho s^2/2} e^{-(W(pi x) + rho|pi x|^2/2)}` and normalisation. `gaussianReal 0 rho^{-1}.toNNReal` has variance `1/rho` (`rho > 0`). (iii) `RigidCurvature V` (uses `gap = rho`).
* The paper says "Langevin process with V as in (1.6)" but (i)-(iii) do not involve the process; the Lean statement correctly carries no Brownian hypothesis.
* Flagged `0 < d` is the only amendment; no unflagged deviation.

### 7. `convex_interaction_cutoff` (C:246-262) vs Cor 1.6. Faithful.
Fixed `rho > 0` (so `rho = o(log n)` and `liminf rho > 0` hold automatically, no extra hypotheses needed), critical time `log n/(2 rho)`; `forall cube : Bool` covers ball and cube, both about the mean; the four profiles W2, Fisher, KL, TV with limits `top/0`, `top/0`, `top/0`, `1/0`; `c > 0`. Hypotheses per `n > 0`: `W` is `C^2`, convex, `(1,..,1)`-invariant, and IsLangevin for `rho|x|^2/2 + W`. Cube lower bound check: the cube contains `m + c(1,...,1)`, a point with `|x0 - m| = c sqrt d` along `u in E1`-direction, so the Lambda lower bound is as for the ball; cube `subset` ball for the upper bound. Faithful.

## 3. Pitfall checklist (theorems 1-7)

Division by zero: `q/gap`, `criticalTime`: `gap > 0` always. `sInf empty`: only `d = 0`, excluded. `top` truncation: `ofReal` applied to nonnegative reals, products with positive constants. `toReal` of `top`: only on null sets. Non-integrable Bochner: Gibbs mean, `G` integrals, `E1` inner products: all integrable under strong convexity. Non-measurable `Measure.map`: excluded by IsBrownian/IsLangevin. Quantifier order (`eps` before `n`, all `t`, all `S`): correct. Ranges `eps in (0,1)`, `c > 0`, `p in [1,infinity)`: correct. Limits `2` vs `top` in Lp: correct (`2` iff `p = 1`). Vacuity: hypotheses are satisfiable in principle (OU / `W`-constant), only the Brownian-existence caveat below.

## 4. Remarks / residual risks (none a defect)

* R-a: concrete instantiation of `IsLangevin` needs Brownian-motion existence (not proved in the project or in Mathlib at this revision); thus non-vacuity is by mathematical argument, not a Lean witness.
* R-b: `E1`, `lam1` are defined classically; agreement with the spectral definitions uses elliptic regularity and essential self-adjointness. The inclusion goes in the safe direction for the lower bounds.
* R-c: Theorem 2 quantifies over bases rather than asserting existence; non-vacuous because `1 <= k1` and finite-dimensionality.
* R-d (cosmetic): theorem 6 states `E1` membership as `IsEigenfunction V rho` instead of `in firstEigenspace V`; equivalent given the first conjunct.

## 5. Comparison with `semantic-audit.md` (read AFTER forming the above)

Agreements: all seven verdicts (no defect). Same readings of `RigidCurvature` excluding `d = 0`, `1 <= k1`, `lp_cutoff` excluding `p = infinity`, Gaussian-factor strength, `0 < d` necessary, ball refinement as an inequality, and the Brownian-existence and classical-`E1` caveats (their R1).
Differences (all minor, mine additional or finer): (a) I explicitly verified the Lebesgue-vs-`mu` integration by parts in `fisherInfo` and the local integrability that rules out Bochner junk; (b) I verified from Mathlib that `IsBrownianReal` forces `P` to be a probability measure (`HasLaw` against `projectiveFamily`, `d >= 1`) and `B 0 = 0`; (c) the Lp worst-case time check by the explicit OU formula; (d) I rated #1 faithful rather than "faithful with remark" (their remark is the shared caveat, which I list as R-a/R-b); I rated #5 and #6 "with remark" where they gave "faithful" for #6 (the remark is the necessary `0 < d`). I found no disagreement of substance. The brief's "covariance correction" does not occur in the manuscript or the Lean statement.
