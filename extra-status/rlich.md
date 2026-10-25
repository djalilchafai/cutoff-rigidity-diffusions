# rlich: Riemannian Lichnerowicz (CD(rho,inf), rho>0 => mSpectralGap >= rho), manuscript lines ~619-627

File: CutoffRigidity/Extra/RiemannLichnerowicz.lean (module CutoffRigidity.Extra.RiemannLichnerowicz, ~470 lines).
`lake build CutoffRigidity.Extra.RiemannLichnerowicz` succeeds; no sorry/axiom; `#print axioms
CutoffRigidity.Paper.mSpectralGap_ge_of_CD` = propext, Classical.choice, Quot.sound. No existing file edited.
Not reviewed by a human.

## PROVED: CutoffRigidity.Paper.mSpectralGap_ge_of_CD (no hgap)
Amendment (flagged): `0 < Module.finrank ℝ F`. Without it the claim is false: for finrank F = 0, M is a point,
mu = Dirac, the Rayleigh set in `mSpectralGap` (smooth compactly supported f with 0 < variance) is empty,
`sInf ∅ = 0 < rho`, while CD, IsWeightedVolume etc. hold vacuously. Nothing else added (the set is nonempty
once M has two points: proved via bump functions + open-positivity of mu).

Proposed Challenge text (put in the `Riemannian` section after `riemannian_wasserstein_estimate`, where
`F`, `M` and the instances are already variables; Paper version identical, names under `CutCur.`):
```lean
/-- **Lichnerowicz / Bakry–Émery spectral gap bound** (lines 619–627, `λ₁ ≥ ρ`): on a connected complete weighted
Riemannian manifold with probability measure `μ = e^{-V} vol`, `CD(ρ,∞)` with `ρ > 0` implies `λ₁ ≥ ρ`.
(`0 < finrank ℝ F` is needed: on a point the Rayleigh set is empty and `sInf ∅ = 0`.) -/
theorem mSpectralGap_ge_of_CD (hF : 0 < Module.finrank ℝ F) {V : M → ℝ}
    (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
    {μ : Measure M} [IsProbabilityMeasure μ] (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ)
    (hCD : CD F ρ V) : ρ ≤ mSpectralGap F μ := by
  sorry
```

## Proof (what was actually needed; hgap was only used for ergodicity, now replaced)
All in namespace CutoffRigidity.Riemann.Diff unless said.
1. `abs_sub_le_of_mgrad_le`: smooth U with ‖∇U‖ ≤ ℓ satisfies |U a − U b| ≤ ℓ·dd a b (near-minimizing C¹ curve
   `exists_curve` + monotone auxiliary function).
2. `variance_le_of_lip`, `tendsto_double_minsq`, `tendsto_variance_zero`: bounded continuous h_n with
   |h_n x − h_n y| ≤ c_n dd x y, c_n → 0 have Var(h_n) → 0 (Jensen + nested dominated convergence, no moment of mu
   needed, no product-measure measurability).
3. `sqFun_hasDerivAt`: d/ds ∫ (K_s g)² dmu = −2 ∫ Γ(K_s g) (s>0), `sqFun_continuous`; `sqFun_zero_le`:
   ∫g² ≤ ∫(K_T g)² + (1/ρ)∫Γg from `grad_decay_int` (Bakry–Émery) by a monotone auxiliary function.
4. `poincare_of_strong_BE`: ρ Var f ≤ ∫Γf for test f, from the strong BE bound ‖∇K_t f‖ ≤ e^{-ρt} K_t‖∇f‖ only:
   Var f ≤ Var(K_n f) + (1/ρ)∫Γf, and Var(K_n f) → 0 because |K_n f| ≤ sup|f| and K_n f is e^{-ρ n}Lip(f)-Lipschitz.
5. `poincare_of_CD` (concrete Kk, `beStrong_of_CD`, `kerCanonical_Kk`), `nontrivial_of_finrank_pos`,
   `exists_pos_variance`, `mSpectralGap_ge_of_CD'`, then the Paper wrapper.
Findings: `contraction_of_CD`, `beStrong_of_CD`, `gradBound_of_CD`, `kerCanonical_Kk` never needed hgap; only
`lsi_of_CD`/`poincare_of_gap` used it. With `poincare_of_CD` available, the hgap hypothesis of `lsi_of_CD`
could be removed (replace `poincare_of_gap F hgap` by `poincare_of_CD F hV hμ hρ hCD`); not done (no existing
file edited).
