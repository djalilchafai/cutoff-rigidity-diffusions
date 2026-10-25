# Workstream A (weighted): status

## Decomposition of `manifold_eigenfunction_parallel_gradient`
Proof of lem_rig reduced to four geometric inputs (Props in `Riemann/WeightedInterface.lean`):
* G0 `WeightedRegular V`: Gamma(f,g), L f smooth, ‖Hess f‖² continuous for smooth f. (sub-agent G0, `WeightedRegular*.lean`)
* G1 `WeightedIBP μ V`: ∫Γ(u,v)dμ = -∫u 𝓛v dμ, u compactly supported smooth. (sub-agent G1, `WeightedIBP*.lean`)
* G2 `WeightedBochnerIneq V ρ`: ‖Hess f‖²+ρΓ(f) ≤ Γ₂(f) from Challenge `CD`. (sub-agent G2, `WeightedBochner*.lean`)
* G3 `WeightedCutoffs M`: smooth compactly supported cutoffs, ‖∇χ_n‖ ≤ 1/(n+1), χ_n → 1 (Hopf-Rinow + smoothing). (sub-agent G3)
* G4 μ charges nonempty open sets: from `IsWeightedVolume` + continuity/positivity of `chartVolumeDensity` on chart targets (the two density facts are requested from G1).

## Proved and checked (no sorry; axioms propext, Classical.choice, Quot.sound)
`Riemann/WeightedInterface.lean`: definitions mHessNormSq, MSmooth, WeightedIBP, WeightedBochnerIneq, WeightedRegular, WeightedCutoffs.
`Riemann/WeightedPointwise.lean`: clm_norm_sq_le (‖Av‖² ≤ ‖v‖² ∑‖A b_i‖²), mgrad_mdiffAt, mvfderiv_carre_self (dΓ(f,f)(v)=2Hess f(v,∇f)), carre_eq_mvfderiv, mgrad_mul, carre_mul_left, abs_carre_le, abs_carre_carre_le (|Γ(χ,Γ f)| ≤ 2‖∇χ‖‖Hess f‖‖∇f‖), mgrad_eq_zero_of_notMem_tsupport, hasCompactSupport_carre.
`Riemann/WeightedRigidity.lean`: mgrad_const_mul, carre2_eigen (Γ₂ = ½𝓛Γ+λΓ), hess_le_half_generator, caccioppoli, hess_cutoff_bound, lintegral_ofReal_le_of_approx (Fatou), `hess_eq_zero_of_eigenfunction`, `parallel_gradient_of_geometry`.
`Riemann/WeightedSupport.lean`: `measure_pos_of_isWeightedVolume` (assuming continuity+positivity of chartVolumeDensity on targets).
`Riemann/WeightedMain.lean`: `manifold_eigenfunction_parallel_gradient_of_geometry` (conditional on G0-G3 and the density facts).

## Observations
* The spectral-gap hypothesis `hgap` is NOT needed for parallel gradients: only eigenvalue ρ>0 (≥0), CD(ρ), completeness, μ probability. 
* Challenge definitions are consistent with the proof; no falsity found. Mathlib has no curvature tensor and no smoothness theorem for leviCivitaConnection, no Hopf-Rinow; the project's gradient smoothness is only C¹ (hence G0).
* Not done: positivity/attainment facts on mSpectralGap for identifying mFirstEigenDim.

## UPDATE: unconditional theorem (all four inputs proved by sub-agents)
`CutCur.manifold_eigenfunction_parallel_gradient` (`Riemann/WeightedFinal.lean`): for the hypotheses of `riemannian_gaussian_splitting` (hV, hμ, hρ, hCD, hgap; hgap unused) every `IsMEigenfunction F μ V ρ f` has `leviCivitaConnection (mgrad F f) x = 0` for all x.
Inputs: `weightedRegular` (G0, WeightedRegular*.lean), `weightedIBP_of_isWeightedVolume` (G1, WeightedIBP*.lean), `weightedBochnerIneq_of_CD` (G2, WeightedBochner*.lean), `weightedCutoffs_of_complete` (G3, WeightedProper*/Mollify/Smoothing/Cutoffs). Details in weighted-G0..G3.md.
Axioms: propext, Classical.choice, Quot.sound. Lead must add the new modules (import CutoffRigidity.Riemann.WeightedFinal) to CutoffRigidity.lean.
Open: mSpectralGap positivity/attainment facts for mFirstEigenDim.
