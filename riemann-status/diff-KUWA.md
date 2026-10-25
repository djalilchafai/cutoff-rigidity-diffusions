# WS-KUW-A: Kantorovich budget duality on a proper metric space -- DONE

Files (all build, no sorry, axioms = propext, Classical.choice, Quot.sound), namespace `CutoffRigidity.Riemann`:
* `CutoffRigidity/Riemann/DiffKantorovichProper1.lean` (83 l.): `exists_weak_limit_coupling` (Prokhorov for couplings on a complete
  separable metric space `X`, general version of `exists_coupling_limit_of_marginals_tendsto`), `lintegral_le_liminf_of_tendsto`.
* `CutoffRigidity/Riemann/DiffKantorovichProper2.lean` (303 l.): truncated cost `cR R x y = (min (dist x y) R)^2`, `exists_extension_pair`
  (two `cR`-transforms extend a compact dual pair to bounded Lipschitz `F,G` on `X`), `truncTo`, `exists_trunc_coupling`
  (compact strong duality via `exists_compact_transport_coupling_of_dual_budget`, error `R^2 * tails`).
* `CutoffRigidity/Riemann/DiffKantorovichProper.lean` (201 l.): main results.

Main statements:
```lean
theorem cost2_le_of_lipschitz_dual_budget {X} [MetricSpace X] [ProperSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (K : ℝ)
  (hDual : ∀ (f g : X →ᵇ ℝ) (L J : ℝ≥0), LipschitzWith L f → LipschitzWith J g →
     (∀ x y, f x + g y ≤ dist x y ^ 2) → ∫ x, f x ∂μ + ∫ y, g y ∂ν ≤ K) :
  cost2 μ ν ≤ ENNReal.ofReal K
-- (cost2 lives in CutoffRigidity.Riemann, file Riemann/TransportW2.lean)

theorem wasserstein2_sq_le_of_dual_budget_manifold (F) {M} [EMetricSpace M] [ChartedSpace F M] ... [IsRiemannianManifold 𝓘(ℝ,F) M]
  [ConnectedSpace M] [CompleteSpace M] [MeasurableSpace M] [BorelSpace M] (μ ν) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (K : ℝ)
  (hDual : ∀ (f g : M →ᵇ ℝ) (L J : ℝ≥0), LipschitzWith L f → LipschitzWith J g →
     (∀ x y, f x + g y ≤ (edist x y).toReal ^ 2) → ∫ f ∂μ + ∫ g ∂ν ≤ K) :
  CutCur.wasserstein2 μ ν ^ 2 ≤ ENNReal.ofReal K
```
Notes for users (KUW-B / FINAL): `F` is an explicit argument of the manifold corollary; Lipschitz is w.r.t. `edist` (`LipschitzWith`);
the constraint uses `(edist x y).toReal ^ 2` (= `dist^2` of the Riemannian metric space). No moment assumption, no
duality assumed; the proof truncates the cost, restricts to balls (outside mass to the base point), uses compact duality, then
Prokhorov/Portmanteau and monotone convergence. Nothing outside these three files was edited.
