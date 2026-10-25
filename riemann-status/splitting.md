# Workstream B (splitting): status

Files: `CutoffRigidity/Riemann/Split*.lean` (all compile, no `sorry`, axioms only
propext/Classical.choice/Quot.sound; the lead must import them). Premise to be discharged by workstream A
(now available as `CutCur.manifold_eigenfunction_parallel_gradient`):
`∀ f, IsMEigenfunction F μ V ρ f → ∀ x, leviCivitaConnection 𝓘(ℝ,F) M (mgrad F f) x = 0`.
Workstream `gap` supplies `exists_orthonormal_eigenbasis`, `mFirstEigenDim_eq_finrank`, linearity of 𝓛
(`EigenLinear.lean`, `EigenFinite.lean`); workstream A supplies `weightedIBP_of_isWeightedVolume`,
`contMDiff_mgrad`, positivity facts for `chartVolumeDensity`.

## 0. Findings

1. **Regularity gap, now closed for the geometric part.** The existing project machinery for the flow
   splitting is only `C¹`/`C²` (flow, diffeo, induced metric, level atlas), while the Challenge needs
   `Φ : M ≃ₘ^∞ ...`. Mathlib (this version) has no `C^k` dependence of ODE flows on initial data. I proved it
   (`SplitFlow*`), re-did the level-set atlas for a vector valued submersion at order `∞`
   (`SplitLevel*`) and the induced metric at order `∞` (`SplitMetric`).
2. **No obstruction from typeclass fields / universes** in the Challenge statement:
   `F' := EuclideanSpace ℝ (Fin (finrank F - k))`, `N := {x : M // s x = 0}` are in `Type`; `MeasurableSpace N`,
   `BorelSpace N` are the subtype instances; `Φ` is continuous so `μ.map Φ` is meaningful for the product σ-algebra
   (no second countability needed). `k ≤ finrank F` since the `k` gradients are pointwise orthonormal.
3. `hgap` is used only to define `k`. If `k = 0` (no nonzero eigenfunction; attainment is NOT proved, see
   `gap.md`) the conclusion is trivial (`N = M`, `Φ = (const, id)`, every eigenfunction is `0` by full support).
4. `‖a‖² = ρ‖f‖²` and orthogonality of the `a`'s do not need integration by parts once the Gaussian factor is known
   (`SplitEigen.lean`); the constant Gram matrix `⟨∇gᵢ,∇gⱼ⟩` is forced to be `ρ·Id` by `∫ gᵢgⱼ = δᵢⱼ` and the Gaussian
   factor `X_i V = ρ s_i`.
5. Design: the `k`-fold splitting is done in ONE step through the frame `s = (s_1..s_k)` (functions with parallel
   gradients and `Γ(sᵢ,sⱼ) = δᵢⱼ`), fibre `N = s⁻¹(0)`, action `A(t,y) = φ¹_{t₁}∘…∘φᵏ_{t_k}(y)`; bijectivity does not
   need commutation of flows, the commutation needed for the isometry is derived from
   `s_j ∘ φ_i^t = s_j + δ_ij t` + tangent isometry (`mfderiv_flow_X`).

## 1. Proved and checked

### `SplitEigen.lean` (items 4-5 of the Challenge conclusion, abstractly)
`integral_sum_mul_orthonormal`, `integral_sum_mul_sum_orthonormal`, `exists_vector_of_combination`,
`vector_unique`, `affine_items` (for any `E : (Ω→ℝ) → Prop` whose members are combinations of an `L²`-orthonormal
`gᵢ`, with `p = ρ^{-1/2} g`: `∃ a, f = ⟨a,p⟩ ∧ ‖a‖² = ρ∫f²`, and orthogonality of the vectors).

### `SplitFlowSmooth.lean`, `SplitFlowManifold.lean`, `SplitFlowGlobal.lean` (smooth flows)
`exists_contDiff_localFlow m E F hF x₀` (local flow of a `C^{m+1}` field on a finite-dim space is `C^{m+1}` jointly;
induction through the variational field `(y,J) ↦ (F y, DF(y)∘J)`), `exists_contMDiff_localIntegralFlow_nat`,
`contMDiff_completeBoundedFlow_joint_nat`, **`contMDiff_completeBoundedFlow_joint_infty`**.

### `SplitLevelEuclid/Data/Manifold/Atlas.lean` (level set of a submersion `Ψ : M → G`, `C^∞`)
`exists_contDiff_regular_coordinates` (IFT chart, `C^∞` both ways on the whole domain), `vecLevelChart`, `LevelData`,
`nonempty_levelData`, `levelChartedSpace`, `isManifold_level`, `contMDiff_level_val`, `injective_mfderiv_level_val`,
`contMDiff_into_level`.

### `SplitMetric.lean`
`isContMDiffRiemannianBundle_of_chartFrame_inner_top`, `isContMDiffRiemannianBundle_immersionPullback_top`.

### `SplitFrame.lean` (namespace `CutCur`)
`Frame F M k` (structure: smooth `s i`, `∀ i x, leviCivitaConnection (mgrad (s i)) x = 0`,
`carre (s i) (s j) = δ`), `Frame.X`, `norm_X`, `flow`, `s_flow` (`s_j(φ_i^t x) = s_j x + δ_ij t`),
`contMDiff_flow_joint`, `norm_mfderiv_flow`, **`mfderiv_flow_X`** (`dφ_i^t(X_j) = X_j ∘ φ_i^t`).

### `SplitAction.lean`, `SplitProduct.lean`
`comp`, `compRev`, `comp_compRev`, `compRev_comp`, `s_comp`, `s_compRev`, `contMDiff_comp(Rev)`, `sv`, `mfderiv_sv_apply`,
`surjective_mfderiv_sv`, `retr`, `sv_retr`, `comp_retr`, `retr_comp`, `sv_comp`; instances `levelCharted`,
`levelIsManifold`; **`Frame.splitEquiv : M ≃ₘ^∞⟮𝓘(ℝ,F), 𝓘(ℝ,Rd k).prod 𝓘(ℝ,LevelModel F (Rd k))⟯ Rd k × fr.Level`**
with `toFun x = (sv x, ⟨retr x,_⟩)`, `invFun (t,y) = comp (finRange k) t y`.

### `SplitTangent.lean`, `SplitIsometry.lean`, `SplitDistance.lean`, `SplitRiemannLevel.lean`
`inner_mfderiv_comp`, `mfderiv_comp_X`, `mfderiv_comp_t`, `mfderiv_comp_joint`, `decomp`,
`norm_sq_action` (Pythagoras for `dA`), `norm_sq_split` (`‖v‖² = ‖ds v‖² + ‖dretr v‖²`),
`edist_ge`, `edist_le_aux`, **`Frame.edist_sq : edist x y ^ 2 = edist (sv x) (sv y) ^ 2 + edist (retr x) (retr y) ^ 2`**
(the Challenge's distance identity, with `edist` on `N` = restriction of `M`),
instances `levelRiemannianBundle`, `levelIsContMDiffRiemannianBundle`, **`levelIsRiemannianManifold`**
(i.e. `IsRiemannianManifold 𝓘(ℝ,F') fr.Level`), `norm_mfderiv_level_val`, `toLevel`, `norm_mfderiv_toLevel_le`.

So for ANY frame the following Challenge components are done: `F'`, `N` with `EMetricSpace`, `ChartedSpace`,
`IsManifold ∞`, `RiemannianBundle`, `IsContMDiffRiemannianBundle ∞`, `IsRiemannianManifold`, `Φ : M ≃ₘ^∞ Rd k × N` and
the distance identity.

### Added later (all built, no sorry)
* `SplitEigenFrame.lean`: `exists_orthonormalizer` (G pos. def. => A G Aᵀ = 1), `mgrad_lincomb`,
  `isOpenPosMeasure_of_weighted`, **`CutCur.exists_frame_of_eigen`**: under the hypotheses of the Challenge there is a
  `Frame F M (mFirstEigenDim F μ V)` whose members are eigenfunctions and such that every eigenfunction is a linear
  combination of them (uses `gap`'s eigenbasis and A's parallel-gradient theorem).
* `SplitWeight.lean`: `Frame.mvfderiv_V_X` (⟨∇V,X_i⟩ = ρ s_i for an eigenframe), `V_flow`, `V_comp`,
  **`V_action : V (comp t y) = V y + ρ‖t‖²/2`** for `y` in the level.
* `SplitGaussian.lean` (written by a delegated sub-agent, checked): `multivariateGaussian_eq_withDensity`,
  `lintegral_exp_neg_sq`.

## 2. Remaining (honest)

Everything for the geometry (Φ, N, metric, IsRiemannianManifold, distance identity, frame from eigenfunctions,
potential decomposition) is done. NOT done:
* **S8 measure**: `V' := V∘val + (k/2) log(ρ/2π)`, `μ' := μ.map toLevel`, `μ.map Φ = γ ⊗ μ'`, `IsWeightedVolume F' μ' V'`.
  Plan: Mathlib now has `LinearMap.normDet` (`Analysis/InnerProductSpace/NormDet.lean`: `normDet_sq_eq_det_gram`,
  `normDet_comp`, `LinearIsometry.normDet_eq_one`) which turns `chartVolumeDensity` into `normDet (mfderiv chart.symm z)`
  and gives the chart-transition Jacobian `normDet(dφ⁻¹) = normDet(dΞ⁻¹)·|det DT|`; with `Ξ = J∘(s, ψ∘π)`,
  `J : WithLp 2 (Rd k × F') ≃ₗᵢ F` (volume preserving, `WithLp.volume_preserving_ofLp`), block structure by
  `norm_sq_action` (needs a bilinear version by polarization), change of variables
  (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`), Lindelöf patching (M, N are σ-compact:
  `sigmaCompactSpace_of_complete_riemannian`), Tonelli + `multivariateGaussian_eq_withDensity`.
* **S9 CD on N**: (I1) `Γ_M(u'∘π,w'∘π)=Γ_N(u',w')∘π`; (I2) `𝓛_M(v'∘π)=(𝓛_N v')∘π` via integration by parts on both
  sides (`weightedIBP_of_isWeightedVolume`) with test functions `χ(s)u'(π)` once S8 is available; then CD(ρ) of M applied to `f'∘π`.
* **S10/S11**: apply `SplitEigen.affine_items` with `g = √ρ s` (orthonormality from the Gaussian covariance) and assemble
  `riemannian_gaussian_splitting_of_parallel`; k = 0 case trivial.
