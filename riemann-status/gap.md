# Workstream `gap`: first eigenspace (finite dimension, orthonormal basis, attainment)

Files (compile, no sorry, axioms propext/Classical.choice/Quot.sound; lead must import them):
`CutoffRigidity/Riemann/EigenLinear.lean`, `CutoffRigidity/Riemann/EigenFinite.lean` (namespace `CutCur`).

## Proved
EigenLinear: `mgrad_add'`, `mgrad_zero'`, `mlaplacian_add`, `mlaplacian_const_mul`, `mlaplacian_zero`,
`mgenerator_add`, `mgenerator_const_mul`, `mgenerator_zero` (linearity on smooth functions; uses
`IsCovariantDerivativeOn.add/smul_const` for the Levi-Civita connection and `mgrad_mdiffAt`).

EigenFinite (hypotheses = those of `riemannian_gaussian_splitting`: hV, hμ, hρ, hCD, hgap, complete
connected Riemannian M, μ probability):
* `eigenSub F μ V lam : Submodule ℝ (M → ℝ)` (smooth L² eigenfunctions form a vector space), `eigenClasses` (their L² classes, a submodule of `M →₂[μ] ℝ`).
* `eigenfunction_eq_zero_of_grad_zero`: eigenfunction (ρ ≠ 0) with parallel gradient and ∇h(x₀)=0 is 0
  (Γ(h,h) has zero differential, hence is constant on connected M; then 𝓛h = 0 = -ρh).
* `finiteDimensional_eigenSub` (dim ≤ dim F, via f ↦ ∇f(x₀) injective, using
  `manifold_eigenfunction_parallel_gradient`), `finiteDimensional_eigenClasses`.
* `mFirstEigenDim_eq_finrank : mFirstEigenDim F μ V = finrank ℝ (eigenClasses F μ V ρ)`; so Module.finrank
  is the true dimension, no junk-value from infinite dimension.
* `exists_orthonormal_eigenbasis`: ∃ T : Fin (mFirstEigenDim F μ V) → M → ℝ, all `IsMEigenfunction F μ V ρ (T i)`
  and `∫ T i * T j ∂μ = if i = j then 1 else 0` (exactly `EigenSplitting.basis`).
* `mFirstEigenDim_pos_iff : 0 < mFirstEigenDim F μ V ↔ ∃ f, IsMEigenfunction F μ V ρ f ∧ ∃ x, f x ≠ 0`
  (uses full support of μ, `measure_pos_of_isWeightedVolume` + density facts).

## NOT proved: attainment (`0 < mFirstEigenDim`)
So `EigenSplitting.pos` reduces exactly to: *there is a nonzero smooth L² eigenfunction for ρ*.

Analysis. The Challenge definitions are consistent (hgap = ρ > 0 forces the sInf set to be nonempty, so no
junk value 0; the span in `mFirstEigenDim` is finite dimensional by the above, so k₁ = 0 can only mean "no
eigenfunction"). The statement is TRUE mathematically, the paper (cutcur-lean.tex l.111, 634) cites
GMS15 Prop. 6.7: under CD(ρ,∞), ρ>0, the spectrum of -𝓛 is discrete (Rellich-type compactness of
H¹(μ) ↪ L²(μ)), so λ₁ = ρ is an eigenvalue. Honest proof route: (1) Bakry-Emery LSI(ρ) / Talagrand, so a bounded
H¹ ball has uniformly bounded ∫d²f²dμ (tightness); (2) local Rellich on charts with smooth positive density;
(3) a Rayleigh minimising sequence (compactly supported smooth, variance 1, ∫Γ → ρ) has an L² limit f that is a
weak (H¹) eigenfunction; (4) elliptic regularity for 𝓛 to get f smooth (needed since `IsMEigenfunction` demands
`ContMDiff ∞` and a pointwise equation). Obstructions in this project: no LSI/Talagrand/semigroup
(the Bakry-Emery route needs the diffusion semigroup), no Rellich on manifolds, no weak-solution / elliptic
regularity theory in Mathlib (steps 3-4). Without discreteness the claim can fail in general (ρ could be only in
the essential spectrum for a measure without Gaussian tails, but CD(ρ,∞) excludes this), so no extra
hypothesis can be avoided without proving (1)-(4). No counterexample to the Challenge was found; the Challenge needs
no extra hypothesis mathematically, but the formal proof requires the discrete-spectrum theorem.
Minimal sufficient extra hypothesis (precisely the open piece): `∃ f, IsMEigenfunction F μ V ρ f ∧ ∃ x, f x ≠ 0`,
equivalent to `0 < mFirstEigenDim F μ V` by `mFirstEigenDim_pos_iff`. Alternatives that imply it:
compactness of H¹(μ) ↪ L²(μ) plus elliptic regularity.
