# diff-BRIDGE (WS-BRIDGE): DONE, fully checked

Files (CutoffRigidity/Riemann/): `DiffPerronAPI.lean` (defs), `DiffBridge.lean` (372 lines), `DiffBridge1.lean` (215 lines).
All build with `lake build`; no sorry/axiom; `#print axioms bridge_of_minimal` = propext, Classical.choice, Quot.sound.
Namespace `CutoffRigidity.Riemann.Diff`.

## DiffPerronAPI (import this)
* `resolventU Pt lam g x := ∫ s in Ioi 0, exp (-lam*s) * semi Pt s.toNNReal g x`
* `MinimalResolvent F V Kk` exactly as in CO_PLAN section 4 (f smooth, compact support, `lam f - 𝓛 f ≤ g`, `resolventU Kk lam g x - η ≤ f x`).

## DiffBridge.lean
* `laplace_unique` (continuous bounded φ, `∫_{Ioi 0} e^{-(m+2)s} φ = 0 ∀ m` ⇒ φ = 0 on [0,∞); Weierstrass applied to `y ↦ y φ(-log y)`).
* `resolventU_integrableOn`, `resolventU_sub`, `resolventU_mono`, `resolventU_nonneg`,
  `resolventU_dynkin` (`U_λ(λ f - 𝓛 f) = f` at every x; integration by parts on Ioi, `hasDerivAt_dynkin`),
  `resolventU_le_of_minimal` (`U^K g ≤ U^P g` for g ≥ 0 in C_c^∞).
## DiffBridge1.lean
* `tendsto_resolventU_const` (dominated convergence), `resolventU_eq_of_minimal` (mass trick with `WeightedCutoffs`;
  uses pointwise-eventually-1 cutoffs only, via the split g = gχ_n + g(1-χ_n)),
* **`bridge_of_minimal`**: `(hP : IsDiffusionSemigroup F V Pt) (hK : IsDiffusionSemigroup F V Kk) (hV : MSmooth F V)
  (hmin : MinimalResolvent F V Kk) : ∀ t x, Pt t x = Kk t x`, under `[IsRiemannianManifold] [ConnectedSpace M] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M]`. Only adaptation vs CO_PLAN: extra hypothesis `hV : MSmooth F V` (needed for `msmooth_mgenerator`).
  Final step reuses `measure_eq_of_integral_smooth` of DiffIdentify (imported); signed g handled via g = (g + Cψ) - Cψ, ψ a smooth bump.

No mathematical obstruction. Nothing outside the three new files was edited.
