# Adversary report, item R1 round 2: Dyson-OU spectral gap (DysonGap.lean .. DysonGap4.lean)

VERDICT: ACCEPT (no repair needed; integration notes at the end).

## Recompilation and axioms
- `lake build CutoffRigidity.Extra.DysonGap4` succeeds (only unused-variable linter warnings).
- grep for sorry/axiom/native_decide/#print in DysonGap*.lean and Dyson*.lean: nothing.
- Scratch file (outside the repo, scratchpad/ax.lean) `#print axioms` on `dysonSpectralGap`, `dysonSpectralGap_eq`,
  `dyson_spectralGap_eigenfunction`, `rayleigh_ge`, `tendsto_rayleigh_fR`, `tendsto_H1_fR`, `rayleigh_hsum`:
  all only [propext, Classical.choice, Quot.sound].

## (1) Same notion as `spectralGap`?
Line by line: `CutCur.spectralGap V = sInf {r | ∃ f, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ 0 < variance f μ ∧ r = (∫‖gradient f x‖² ∂μ)/variance f μ}`
with μ = `gibbs V` (UNNORMALISED in general: `volume.withDensity e^{-V}`). `dysonSpectralGap d ρ β` is the same text with
μ = `dysonProb d ρ β`: same test class (ContDiff ∞, compact support, positive variance), same `sInf` junk value (0 on empty set,
irrelevant since the set is nonempty and bounded below). Mathlib `variance` uses the unnormalised mean `∫ f ∂μ`, so for a
non-probability μ the Rayleigh quotient is NOT scale invariant; this quirk of `spectralGap` is harmless here because
`dysonProb` is a genuine probability measure (`isProbabilityMeasure_dysonProb`, needs d>0, ρ>0, β≥0, all assumed), so the
quotient is the usual one. `spectralGap V` itself cannot express the chamber (V=+∞ off it, `gibbs` needs real V), hence a separate
definition is required; no mismatch found.
Checked in scratch (scratchpad/eq.lean): `CutoffRigidity.Dyson.dysonProb d ρ β = CutCur.dysonProb d ρ β := rfl`,
`CutoffRigidity.Dyson.chamber d = CutCur.chamber d := rfl`, and `dysonSpectralGap d ρ β` is `rfl`-equal to the same sInf set written with
the Challenge/Statements `CutCur.dysonProb`. So the theorem transfers to the Challenge's `dysonProb` verbatim.

## (2) Is `dysonSpectralGap = ρ` mathematically right?
Yes. Test functions are C_c^∞(ℝ^d) restricted to the chamber (no vanishing at the walls): the Neumann/Friedrichs Rayleigh quotient,
which is what the manuscript's spectral gap of the Dyson-OU generator (reflecting at walls for β small, same form domain) means.
- Lower bound: `rayleigh_ge` uses `dyson_poincare` (already in the project, constant 1/ρ) after `isTestFunction_of_compact` (C_c^∞ implies
  bounded and Lipschitz). Not circular: Poincaré is proved independently in Dyson5.
- Upper bound: f_R = χ_R · h with a fixed bump, h = Σ x_i. Var(f_R) → Var h = d/ρ (dominated convergence, E h = 0, E h² = d/ρ) and
  ∫|∇f_R|² ≤ (1+1/R) d + (1+R)(M/R)² d/ρ → d, so Rayleigh → d/(d/ρ) = ρ. The elementary inequality (a+b)² ≤ (1+1/R)a²+(1+R)b² is
  correct. The cutoff argument uses only moments of h under dysonProb, not the gap itself.
- Non-emptiness/positivity of the class: variance of f_R is eventually > d/(2ρ)... (`hVpos`), so the class is nonempty with positive
  variance; bounded below by ρ. Final step is `le_antisymm` of `csInf_le`/`ge_of_tendsto` and `le_csInf`: correct.

## (3) Conjuncts of `dyson_spectralGap_eigenfunction`
1. `dysonSpectralGap d ρ β = ρ`. Exactly as claimed.
2. `MemLp h 2 μ`, `0 < variance h μ`, `(∫‖∇h‖² dμ)/variance h = ρ`. Genuine (∇h = diagonal, ‖∇h‖² = d, Var h = d/ρ).
3. For all φ ∈ C_c^∞: `∫⟨∇h,∇φ⟩dμ = ρ ∫ h φ dμ`. No weakening: ranges over every smooth compactly supported φ (not only vanishing at walls),
   via `dyson_neumann` applied to `isTestFunction_of_compact`.
4. ∃ f : ℕ → ℝ^d → ℝ, each ContDiff ∞, HasCompactSupport, 0 < variance, with ∫(f_n - h)² dμ → 0 and ∫‖∇f_n - ∇h‖² dμ → 0. Meaningful H¹(μ)-closure
   statement; f_n = f_{R_n} with R_n → ∞, eventually-positive variance shifted by N. Note: h itself is not in C_c^∞, so the infimum is not attained
   inside the test class; the docstring phrase "where the infimum is attained" is a prose gloss (attainment = conjuncts 1+2+4 together), not a conjunct.
No hidden hypotheses beyond 0<d, 0<ρ, 0≤β (the manuscript's). `gradient` is Mathlib's, same as in Challenge.

## (4) Non-vacuity
Hypotheses are plain arithmetic. Scratch instances compile: `dysonSpectralGap 1 1 0 = 1` (d=1: the chamber is all of ℝ,
μ = N(0,1/ρ), the classical OU gap), `dysonSpectralGap 2 1 0 = 1`, `dysonSpectralGap 2 1 3 = 1` (d=2, β=3>0). The test class is nonempty with
positive variance for every such triple (proved inside `dysonSpectralGap_eq`).

## (5) Junk values
- `gradient f x` for f on ℝ^d: used on the chamber only through the integral against dysonProb (mass zero off the chamber); no mismatch.
- `Real.log (x i - x j)` off the chamber: irrelevant, density restricted to the open chamber (defeq to the Challenge definition).
- `variance` w.r.t. a probability measure, standard. `sInf` junk 0 on empty set: not reached.
- `variance f (dysonProb ..)` is a `toReal` of an extended variance; positivity hypothesis `0 < variance` rules out infinite-variance junk (0)
  for bounded f anyway.

## Statement size and proposed compact Challenge entry
Worker's version: ~9 lines definition+docstring and ~25 lines theorem+docstring = ~34 lines; too long for a 995/1000 file.
Conjuncts 2 and 3 are already covered by `dyson_ou_static` (MemLp, variance>0, Var h = ρ⁻¹∫|∇h|², Neumann weak form for IsTestFunction,
which contains C_c^∞), so only conjuncts 1 and 4 are new. Proposed (about 14 lines, or 11 without the def):

```lean
/-- Spectral gap of the Dyson–OU law: Rayleigh infimum over `C_c^∞(ℝ^d)` (not required to vanish on the walls), as `spectralGap`. -/
def dysonGap (d : ℕ) (ρ β : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ f : Rd d → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ 0 < variance f (dysonProb d ρ β) ∧
    r = (∫ x, ‖gradient f x‖ ^ 2 ∂dysonProb d ρ β) / variance f (dysonProb d ρ β)}

/-- **Spectral gap of Dyson–OU** (manuscript L315-335): `λ₁ = ρ`, and `∑ xᵢ` is the `H¹(μ)`-limit of `C_c^∞` test functions. -/
theorem dyson_spectralGap {d : ℕ} (hd : 0 < d) {ρ β : ℝ} (hρ : 0 < ρ) (hβ : 0 ≤ β) :
    dysonGap d ρ β = ρ ∧ ∃ f : ℕ → Rd d → ℝ, (∀ n, ContDiff ℝ ∞ (f n) ∧ HasCompactSupport (f n) ∧ 0 < variance (f n) (dysonProb d ρ β)) ∧
      Tendsto (fun n => ∫ x, (f n x - ∑ i, x i) ^ 2 ∂dysonProb d ρ β) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x, ‖gradient (f n) x - gradient (fun y : Rd d => ∑ i, y i) x‖ ^ 2 ∂dysonProb d ρ β) atTop (𝓝 0) := by
  sorry
```
(Even more compact: merge the two docstrings and drop the hd/hρ/hβ name `dysonGap` by inlining the sInf: saves 4 lines. If the lead wants all four
original conjuncts, append conjuncts 2-3 verbatim from `dyson_spectralGap_eigenfunction`, +6 lines.) Needs ~14 lines of compression elsewhere
in Challenge.lean (at 995/1000). The proof file is `CutoffRigidity/Extra/DysonGap4.lean`; for Solution/Statements transport, the
`rfl` equalities above show `CutoffRigidity.Dyson.dysonProb`/`chamber` coincide with `CutCur.dysonProb`/`chamber`, so the proof is a direct `exact`
after restating (or `dysonGap = dysonSpectralGap` by `rfl`).

## Minor remarks (no repair required)
- Docstring "where the infimum is attained" in `dyson_spectralGap_eigenfunction` is informal; keep it out of the Challenge docstring.
- Stray unused-variable linter warnings (`hd`, `hR`) in DysonGap4; cosmetic.
