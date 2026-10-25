# diff-PERRON (WS-PERRON, P4): Perron property of the resolvent and the final bridge

Status: DONE and checked, with ONE blocker for the last module (a name clash, fix = one `sed`, see below).
No sorry/axiom/native_decide; `#print axioms` of every theorem below = propext, Classical.choice, Quot.sound.
Namespace `CutoffRigidity.Riemann.Diff`. Standing hypotheses as `DiffPenalMain` (F, M complete connected Riemannian,
`hV : MSmooth F V`, `[IsFiniteMeasure μ]`, `hμ : IsWeightedVolume F μ V`).

## Deviation from CO_PLAN 2.2 step 7 (the plan's two monotone limits are NOT needed)
The double limit (K -> infinity, then a -> infinity) is replaced by a direct variational estimate with no limit at all.
With `B(s,t) = E(s,t) + lam <s,t>`, `u = R_lam g`, `v = v_{a,K}` (killing `kappa = K theta0(zeta - a)`), and ANY `phi in D`
with `kappa phi = 0` (i.e. supp phi in {zeta < a}): `B(u-v, phi - v) = -∫ kappa v² <= 0`, hence
`B(u-phi,u-phi) >= B(u-v,u-v) >= lam ||u-v||²`, uniformly in `K >= 0`. Density of `D` in `Q` for the energy norm
(`approx_energy`) then gives: for every delta there is a0 with `||u - v_{a,K}||_{L2} <= delta` for all `a >= a0`, all `K >= 0`.
The pointwise bound at `x` uses `interior_sup_estimate_manifold` on the FIXED open set `{zeta < zeta x + 1}` (constant independent
of a, K), then `penalized_perron` (epsilon = eta/4) gives the compactly supported subsolution. The goal statement is unchanged.

## Files
| file | lines | content |
|---|---|---|
| DiffPerron3 | 86 | generic over `DirFriedrichs`: `approx_energy`, `variational_dist` |
| DiffPerron4 | 212 | `penalized_l2_close`, `ResolventRepr`, `minimalResolvent_of_repr` |
| DiffPerron5 | 46 | `resolventRepr_Kk`, `minimalResolvent_Kk` (= `minimalResolvent_of_canonical`) |
| DiffPerron6 | 53 | `bridge_final`, `bridge_final_canonical` (see blocker) |

## Statements
* `approx_energy (T : DirFriedrichs S) (hu : u ∈ T.Q) (hε : 0 < ε) : ∃ φ : S.D, T.E (u - φ) (u - φ) ≤ ε ∧ ‖u - φ‖ ≤ ε`
* `variational_dist (hlam : 0 < lam) (hu hv hφ : ∈ T.Q) (P : H → ℝ) (hwu : ∀ ψ ∈ Q, E u ψ + lam ⟪u,ψ⟫ = ⟪g,ψ⟫)
   (hwv : ∀ ψ ∈ Q, E v ψ + lam ⟪v,ψ⟫ + P ψ = ⟪g,ψ⟫) (hPφ : P φ = 0) (hPv : 0 ≤ P v) :
   lam * ‖u - v‖ ^ 2 ≤ T.E (u - φ) (u - φ) + lam * ‖u - φ‖ ^ 2`
* `penalized_l2_close F hV hμ (hζ : MSmooth F ζ) (hlam) (gL : M →₂[μ] ℝ) (hδ : 0 < δ) :
   ∃ a0, ∀ a ≥ a0, ∀ K ≥ 0, ∀ v, IsPenal hV hμ lam (fun x => K * smoothTransition (ζ x - a)) gL v → ‖R_lam gL - v‖ ≤ δ`
* `def ResolventRepr F hV hμ Kk` = the field `resolvent_repr` (smooth `ū` a.e. equal to `R_lam (testToL2 g)` with `ū x = resolventU Kk lam g x`).
* `minimalResolvent_of_repr (hrepr : ResolventRepr F hV hμ Kk) : MinimalResolvent F V Kk`  (works for ANY kernel family with the representation)
* `resolventRepr_Kk : ResolventRepr F hV hμ (Kk F hV hμ)` (from `resolvent_repr`);
  `minimalResolvent_Kk : MinimalResolvent F V (Kk F hV hμ)`  (the requested `minimalResolvent_of_canonical`; `Kk F hV hμ` is literally the
  witness of `exists_kernel`).
* `bridge_final F hV hμ (hP : IsDiffusionSemigroup F V Pt) : ∀ t x, Pt t x = Kk F hV hμ t x`
* `bridge_final_canonical (hP) (hK : KerCanonical F V μ Kk') : ∀ t x, Pt t x = Kk' t x`  (any canonical kernel; uniqueness of diffusions).

## BLOCKER (needs a one-line change in files not owned by PERRON; refused by the permission system for me)
`DiffBridge.lean` and `DiffKer9.lean` both declare `Diff.continuous_semi_time` (different statements), so no module can import both
`DiffBridge*` and `DiffKer*`; `DiffPerron6` imports both and therefore does not build yet. DiffPerron3-5 build (they do not import DiffBridge).
Fix (verified: with this rename in temporary copies of DiffBridge/DiffBridge1, `DiffPerron6` built and all axioms are standard):
```
cd CutoffRigidity/Riemann && sed -i 's/continuous_semi_time/continuous_semi_time_of_diffusion/g' DiffBridge.lean DiffBridge1.lean
```
(only DiffBridge.lean and DiffBridge1.lean use that name on the Bridge side; DiffKer9/DiffKer11 are untouched). Then
`lake build CutoffRigidity.Riemann.DiffPerron6`.
