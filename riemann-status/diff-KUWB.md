# diff-KUWB (A10, Kuwada contraction) -- DONE, modulo BE

All files in CutoffRigidity/Riemann/, namespace CutoffRigidity.Riemann.Diff; all build, no sorry in any DiffKuw*/DiffHopfLax* file;
`#print axioms contraction_of_BE` = propext, Classical.choice, Quot.sound. (`contraction_of_CD`, `exists_canonical` show sorryAx only
because they import workstream BE's `bePointwise_of_CD`, whose file DiffBESemi.lean still has sorries.)

## Variant of the plan (simpler than the sketch)
No Rademacher, no a.e. statements. The gradient of a Lipschitz function is replaced by the *pointwise local Lipschitz constant*
`lipAt ψ y = lim_{ε→0} locLip ψ y ε` (DiffKuwPre). Everything holds at every point. The kernel a.c. (`Kk_ac`) is not needed.
Interpolation is run along a C^1 curve (Mathlib `exists_lt_locally_constant_of_riemannianEDist_lt`), with a time-change
r'(τ) = (|γ'|+κ)/(2(ℓ+κ)), and a Dini comparison (`image_le_of_liminf_slope_right_lt_deriv_boundary'`), so only continuity of G is needed.
The plan's "slope" version was false as stated for Hopf-Lax (lower slope at kinks); lipAt fixes it: lipAt(Q_r h)(y) ≤ max_opt d(y,z)/r.

## Files / statements
* DiffKuwPre: `BETestFun F V μ ρ Kk` (= the plan's BEPointwise, renamed to avoid a clash with BE's `BEPointwise` on `testSub`;
  `betestFun_of_bePointwise` bridges), `dd, locLip, lipAt` (+ measurable, `lipAt_le`, `lipAt_le_of`...), `SharpApprox F M`.
* DiffHopfLax1/2: `hlQ h r y = ⨅ z, h z + dd y z^2/(2r)`; `exists_opt`, `abs_hlQ_sub_le`, `lipschitzWith_hlQ`, and
  `hlQ_hj : ∃ E ≥ 0, lipAt (hlQ h r) y ≤ E/r ∧ ∀ s>r, hlQ h s y - hlQ h r y ≤ -(E^2 (s-r))/(2 r s)`.
* DiffKuwApprox1/2: `sharpApprox : SharpApprox F M` (smooth g, |g-ψ|≤ε, ‖∇g(x)‖ ≤ (1+η) locLip ψ x ε + η).
* DiffKuwBE1-3: `semi_smooth_of_lip`, `grad_semi_sub_le`, and `beLip (hBE : BETestFun F V μ ρ (Kk F hV hμ)) (hA) (hψ : LipschitzWith L ψ)
  (hB : ∀ x, |ψ x| ≤ B) (ht : t ≠ 0) x : ‖mgrad F (semi (Kk F hV hμ) t ψ) x‖^2 ≤ exp(-2ρt) * ∫ lipAt ψ y ^2 ∂Kk t x`.
* DiffKuwada1-3: `curve_interpolation` (abstract interpolation along a C^1 curve; see diff-KUWB-D.md).
* DiffKuwFinal: `contraction_of_dualPair` (dual-pair inequality + invariance + Markov ⇒ W2 contraction; uses
  `wasserstein2_sq_le_of_dual_budget_manifold`, handles ∫⁻ d² = ⊤).
* DiffKuwGlue: `exists_curve`, `dualPair`, and
  `theorem contraction_of_BE (hBE : BETestFun F V μ ρ (Kk F hV hμ)) (t : ℝ≥0) (x) : wasserstein2 (Kk F hV hμ t x) μ ^ 2 ≤ ofReal (exp (-2ρt)) * ∫⁻ y, edist x y ^ 2 ∂μ`
  (hyps: hV, [IsProbabilityMeasure μ], hμ; no hρ needed).
* DiffKuw (umbrella), DiffKuwMain: `contraction_of_CD (hV hμ hρ hCD) t x` (same conclusion) and
  `exists_canonical : ∃ Kk, CanonicalDiffusion F V μ ρ Kk` (via BE's `bePointwise_of_CD`, `gradBound_of_CD`, `kerCanonical_Kk`).
Imports to add to CutoffRigidity.lean: DiffKuwMain (pulls everything).
