# Workstream `measure` (splitting item S8): status

All files compile, no `sorry`, axioms only propext/Classical.choice/Quot.sound.
The lead must import `CutoffRigidity.Riemann.MeasureFinal` (it imports all the others).
No existing file was edited.

## Final statement (CutoffRigidity/Riemann/MeasureFinal.lean)
`CutCur.Frame.weighted_factorization` (namespace `CutCur.Frame`, `fr : Frame F M k`), hypotheses:
`[MeasurableSpace F] [BorelSpace F] [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M]`
(plus the usual `[IsRiemannianManifold] [CompleteSpace M]` of `Frame`), `hV : ContMDiff .. ∞ V`,
`[IsProbabilityMeasure μ]`, `hμ : IsWeightedVolume F μ V`, `hρ : 0 < ρ`,
`hVX : ∀ i x, mvfderiv 𝓘(ℝ,F) V x (fr.X i x) = ρ * fr.s i x` (from `Frame.mvfderiv_V_X` for an eigenframe).
Conclusion (with `V' y := V y.val + (k/2) * Real.log (ρ/(2π))`, `μ' := μ.map fr.toLevel`):
`ContMDiff .. ∞ V' ∧ IsProbabilityMeasure μ' ∧ IsWeightedVolume (LevelModel F (Rd k)) μ' V' ∧
 μ.map fr.splitEquiv = (multivariateGaussian 0 (ρ⁻¹ • 1)).prod μ'`.
The constant is exactly `(k/2) log(ρ/2π)`: `e^{-V(t·y)} = (ρ/2π)^{k/2} e^{-ρ|t|²/2} · e^{-V'(y)}`.
`ConnectedSpace M` is only used to get `SigmaCompactSpace`, hence second countability, of `M`
(`sigmaCompactSpace_of_complete_riemannian`); `N` inherits it as a subtype.

## Proof architecture (all new, in `CutoffRigidity/Riemann/`)
* `MeasureDensity.lean`: `gramDens` (= `LinearMap.normDet`, `gramDens_eq_normDet`, `gramDens_comp`),
  `chartDensity Ξ w` (Riemannian density `√det g` of an ARBITRARY chart `Ξ : OpenPartialHomeomorph M F`;
  `chartVolumeDensity_eq_chartDensity : chartVolumeDensity F x₀ z = chartDensity (chartAt F x₀) z`),
  `chartDensity_transition` (`ρ_φ(z) = ρ_Ξ(Ξ φ⁻¹ z)·|det D(Ξ∘φ⁻¹)(z)|`, via `normDet_comp_of_finrank_eq`).
* `MeasureChart.lean`: `local_chart_mass`, **`map_chart_density`**: for any `Ξ` with `Ξ`, `Ξ.symm` `C¹`
  (`ContMDiffOn`), and `IsWeightedVolume F μ V`, on a second countable `M`:
  `(μ.restrict Ξ.source).map Ξ = (volume.restrict Ξ.target).withDensity (ofReal(e^{-V∘Ξ.symm} * chartDensity Ξ))`
  (chart independence of `IsWeightedVolume`: Lindelöf cover by `chartAt` domains, Mathlib change of variables
  `lintegral_image_eq_lintegral_abs_det_fderiv_mul`, gluing `Measure.restrict_iUnion_congr`).
  Also `measurableSet_inter_preimage_of_continuousOn`.
* `MeasureGram.lean`: `sumMap`, `gramDens_sumMap` (Gram density of `(a,c) ↦ ∑ aᵢXᵢ + u c` ∘ isometry equals that of `u`,
  block determinant on `OrthonormalBasis.prod`).
* `MeasureLevel.lean`: `inner_mfderiv_level_val`, `inner_X_mfderiv_level_val` (`dval` lands in `X^⊥`),
  `mfderiv_val_chart_symm`, `chartVolumeDensity_level` (density of `N` computed through `val : N → M`).
* `MeasureProduct.lean`: `Jc J`, `prodChart`, `Θ`, `Ξ J y₀ = Jc∘(id × chartAt y₀)∘Φ` (a `C^∞` chart of `M` with values in `F`),
  `contMDiffOn_Ξ`, `contMDiffOn_Ξ_symm`, `mfderiv_Ξ_symm_apply`, **`chartDensity_Ξ`**:
  `chartDensity (Ξ J y₀) w = chartVolumeDensity F' y₀ (zc J w)` (uses `inner_mfderiv_comp`, `mfderiv_comp_X`, `mfderiv_comp_joint`,
  block Gram). Here `J : WithLp 2 (Rd k × F') ≃ₗᵢ F` is any isometry (exists: `exists_J`, needs `k ≤ finrank F`).
* `MeasureFactor.lean`: `eJ`, `measurePreserving_eJ`, `map_Θ_eq`, **`map_Θ_prod`**:
  `(μ.restrict Θ.source).map Θ = γ.prod (levelMeasure)` in the product chart (`V_action`, `multivariateGaussian_eq_withDensity`,
  `prod_withDensity₀`).
* `MeasureFinal.lean`: `k_le_finrank`, `exists_J`, `measurable_toLevel`, `levelMeasure`, `map_level_chart` (the level marginal has
  the chart density, i.e. `IsWeightedVolume`), `restrict_splitEquiv` (local rectangle formula via `Measure.prod_eq`),
  `weighted_factorization` (countable cover of `N`, `Measure.restrict_iUnion_congr`).

## Notes for assembly
* `weighted_factorization` is stated with the instances `levelCharted`, `levelRiemannianBundle`, ... of `SplitProduct/SplitRiemannLevel`;
  `MeasurableSpace`/`BorelSpace` on `N = fr.Level` are the subtype ones; on `F'` the `EuclideanSpace` ones; `μ.map fr.splitEquiv`
  uses the product σ-algebra.
* Nothing blocked. Not done here (other items): `CD ρ V'` on `N` (S9) and eigenfunction items (S10/S11).
