# Dyson-OU static statement: adversary report (item 3)

Verdict: **ACCEPT** (with docstring caveats, no mathematical repair needed).

## Recompilation / hygiene
- `lake build CutoffRigidity.Extra.Dyson7`: success (only unused-variable linter warnings).
- grep for sorry / axiom / native_decide / #print in Dyson*.lean: nothing.
- Scratch `#print axioms` (scratchpad/ax.lean, outside repo) on dyson_ou_static, dysonMeasure_eq, optimalPIDyson_eq,
  dyson_neumann, dyson_poincare, dyson_generator_sum: only propext, Classical.choice, Quot.sound.
- Non-vacuity: `dyson_ou_static` instantiated at (d=1, rho=1, beta=0) and (d=2, rho=1, beta=2) typechecks. The
  hypotheses 0<d, 0<rho, 0<=beta are satisfiable; conclusion is a conjunction of nontrivial facts (not reducible to True).

## Attack results
1. Faithfulness of V. Manuscript (eq:VW) and the displayed W: V = rho/2 |x|^2 + W, W = sum_{i<j} h(x_i-x_j), no 1/d
   scaling, sum over i<j (not i!=j), h = -beta log on (0,inf), +inf else, domain x_1>...>x_d. Lean `dysonV` is
   rho/2 ‖x‖^2 + sum_i sum_{j with i<j} (-beta log(x_i-x_j)): exact match. The +inf is encoded by restricting Lebesgue
   to `chamber` (open convex, x_j<x_i for i<j; matches the manuscript's chamber and orientation). Note the manuscript
   asks h convex EVEN in the general (VW) example; the DOU h is not even, but the manuscript itself uses it, fine.
2. Junk values. `Real.log` of nonpositive numbers occurs only off the chamber, where `dysonMeasure` is 0 by the
   restriction; `dysonMeasure_eq` shows density Dlim = indicator * exp(-rho|x|^2/2) prod (x_i-x_j)^beta with
   (rpow, fine since positive base). generator conjunct is quantified only over x in the open chamber, where dysonV is
   differentiable (gradient/laplacian genuine, not junk). Neumann conjunct: integrals are Bochner integrals (junk 0 if
   non-integrable) but integrability of h*phi, <grad h, grad phi> is proved (Dyson6 integrable lemmas), and the Poincare
   conjunct integrates bounded functions. optimalPIDyson: the set is nonempty (rho^-1 in it), bounded below by 0, and
   `IsLeast.csInf_eq` is used with a genuine lower bound (`inv_le_of_poincare`, via bounded truncations S_n∘hsum), so
   `= rho^-1` is NOT trivial (sInf of empty set = 0 would give 0, not rho^-1; sInf of unbounded-below would be 0 too).
   Math check of the boundary term (d=2, beta=0): walls x1=x2, outward normal n=(1,-1)/sqrt2, grad h=(1,1), so
   grad h . n = 0; IBP of the Neumann form gives int <grad h,grad phi> e^{-V} = -int phi L h e^{-V} + boundary(phi d_n h e^{-V}) = rho int h phi e^{-V}
   for arbitrary smooth phi (no wall condition on phi). In general walls x_i=x_{i+1}, n=e_i-e_{i+1}, grad h.n=0. For beta>0 the density
   also vanishes at the walls. So the claim is TRUE and no hidden boundary term. The proof is by an eps-regularisation
   (softplus smoothing + dominated convergence, Dyson1D..Dyson3, Dyson2 eps_ibp), consistent.
3. Test function class `IsTestFunction`: smooth, bounded, Lipschitz on all R^d (restricted to chamber; fine, the
   chamber is convex so the Neumann form is the natural one). Same class as the project's `optimalPI`.
4. Conjunct by conjunct (read as Lean): (1) finite, 0<mu(univ), prob of normalised; (2) chamber open, convex, dysonV-rho/2|x|^2
   ConvexOn chamber (this IS rho-convexity of V on the convex domain, in the convexity-of-V-minus-quadratic sense,
   not a pointwise Hessian statement); (3) generator identity on chamber with `CutCur.generator`; (4) Neumann weak form,
   all test phi; (5) Poincare 1/rho; (6) optimalPIDyson = rho^-1, h in L^2, Var h >0, Var h = optimalPIDyson * int|grad h|^2
   (Var h = d/rho, int|grad h|^2 = d). All implied by Lean text.
5. NOT claimed / possible over-claims:
   - The project's `CutCur.spectralGap` / `lambda_1` of the Dyson operator is NOT mentioned or proved; the Dyson-OU
     process, its reflection/Friedrichs-Neumann generator, semigroup, and Hess V >= rho pointwise are NOT proved
     (only ConvexOn of V - rho|x|^2/2). Dyson7 module docstring says so honestly.
   - Docstring of `dyson_ou_static` item 6 says "(so lambda_1 = rho with h extremal)": this is an over-claim unless read as
     "optimal Poincare constant on bounded Lipschitz smooth functions"; recommend rewording to "the optimal Poincare constant
     over bounded smooth Lipschitz test functions is 1/rho, attained in the L^2 sense by h" and dropping lambda_1.
   - Item 2 docstring "V is rho-convex on C": say "V - rho|x|^2/2 is convex on C".
   - Test functions are not C_c^infty; equality of the optimal constant with the Rayleigh/ spectral gap over C_c^infty on
     the chamber (cutoff argument at the walls) is not shown. The manuscript says only that h is an eigenfunction for the gap.
   - Manuscript sentence "x_1+...+x_d is an eigenfunction associated to the spectral gap" is formalised as: L h = -rho h on
     the open chamber + weak Neumann + optimal PI = 1/rho. Good faithful surrogate, but not literally spectral-theoretic.

## Challenge.lean size
Currently 981 lines / 69194 bytes (limit 1000 lines / 100 KiB). Bytes are fine (~30 KB of room); lines are the bottleneck:
only 19 spare. Required Lean-level definitions in Challenge (they must be there): `chamber`, `dysonV` (or inline into
measure), `dysonMeasure`, `dysonProb`, optionally `optimalPIDyson`, plus the theorem. Estimated cost: chamber 2 lines,
dysonV 3, dysonProb 3 (define normalised measure directly as `(c)⁻¹ • ...` or via withDensity on the restricted volume
with a normalisation constant), optimalPIDyson 4, theorem ~22 (multi-line conjunction) => ~35-40 lines with one-line docstrings.
To fit: (a) drop `optimalPIDyson` and conjunct (6): state Poincare 1/rho for all test functions plus h in L^2, Var h =
rho^-1 ∫|grad h|^2, 0<Var h (this proves optimality without any sInf def) saving ~6 lines; (b) merge dysonMeasure/dysonProb
into one def `dysonProb d rho beta := (m univ)⁻¹ • m` with `m` as a local `let` (or `withDensity` inline) saving ~3 lines;
(c) free ~20 lines by compressing docstrings in the Challenge (e.g. shorten the 11-line module docstring; remove blank
lines between short defs; join multi-line docstrings), so net ~+25 lines, room to ~1006 before compression of ~10-25 lines.
Recommended: do (a)+(b) and compress ~15 lines of existing docstrings.

## Recommended minimal Challenge statement
```lean
def chamber (d : ℕ) : Set (Rd d) := {x | ∀ i j : Fin d, i < j → x j < x i}
/-- Dyson-OU Gibbs probability on the Weyl chamber: e^{-V} 1_chamber dx / Z, V = ρ|x|²/2 - β ∑_{i<j} log(x_i-x_j). -/
def dysonProb (d : ℕ) (ρ β : ℝ) : Measure (Rd d) :=
  let m := (volume.restrict (chamber d)).withDensity fun x => ENNReal.ofReal
    (Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + ∑ i, ∑ j with i < j, -β * Real.log (x i - x j))))
  (m univ)⁻¹ • m
theorem dyson_ou_static {d : ℕ} (hd : 0 < d) {ρ β : ℝ} (hρ : 0 < ρ) (hβ : 0 ≤ β) :
    IsProbabilityMeasure (dysonProb d ρ β) ∧ IsOpen (chamber d) ∧ Convex ℝ (chamber d) ∧
    ConvexOn ℝ (chamber d) (fun x => ∑ i, ∑ j with i < j, -β * Real.log (x i - x j)) ∧
    (∀ x ∈ chamber d, generator (fun x => ρ / 2 * ‖x‖ ^ 2 + ∑ i, ∑ j with i < j, -β * Real.log (x i - x j))
        (fun x => ∑ i, x i) x = -ρ * ∑ i, x i) ∧
    (∀ φ, IsTestFunction φ → ∫ x, inner ℝ (gradient (fun x : Rd d => ∑ i, x i) x) (gradient φ x) ∂dysonProb d ρ β
        = ρ * ∫ x, (∑ i, x i) * φ x ∂dysonProb d ρ β) ∧
    (∀ f, IsTestFunction f → variance f (dysonProb d ρ β) ≤ ρ⁻¹ * ∫ x, ‖gradient f x‖ ^ 2 ∂dysonProb d ρ β) ∧
    (MemLp (fun x : Rd d => ∑ i, x i) 2 (dysonProb d ρ β) ∧ 0 < variance (fun x : Rd d => ∑ i, x i) (dysonProb d ρ β) ∧
     variance (fun x : Rd d => ∑ i, x i) (dysonProb d ρ β) =
       ρ⁻¹ * ∫ x, ‖gradient (fun x : Rd d => ∑ i, x i) x‖ ^ 2 ∂dysonProb d ρ β)
```
(Needs a bridging lemma in Extra that this inlined form equals the worker's `dysonProb`/`dysonV`; trivial by `rfl`/unfolding
since `dysonMeasure`, `dysonV` unfold definitionally, but check `rfl` once before integrating. If `optimalPIDyson = ρ⁻¹`
is wanted in Challenge, add the 4-line def mirroring `optimalPI`; it is proved by `optimalPIDyson_eq`.)
Docstring wording: say "optimal Poincare constant over bounded smooth Lipschitz test functions", not "spectral gap lambda_1".
