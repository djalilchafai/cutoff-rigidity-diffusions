# diff-KER: Tier A kernel (A5ii, A6, A7) -- DONE, all checked

Final module `CutoffRigidity.Riemann.DiffKer` (imports everything below). No sorry/axiom/native_decide; `#print axioms` of
every theorem listed = propext, Classical.choice, Quot.sound. Namespace `CutoffRigidity.Riemann.Diff`. No existing file edited.
Standing hypotheses as in DiffInstance2 (`F`, `M` complete connected Riemannian, `hV : MSmooth F V`, `[IsFiniteMeasure μ]`,
`hμ : IsWeightedVolume F μ V`; full support of `μ` derived from `hμ`). Sub-agent status files: diff-KER-REG.md, diff-KER-EIG.md,
diff-KER-LAP.md, diff-KER-GRAD.md.

## Files
DiffReg1,2,RegSmooth (chart bootstrap, REG), DiffReg3..8, DiffRegPot (potential + interior estimate), DiffEig1,2,Eigen (EIG),
DiffLap1, DiffLaplace (LAP), DiffKer1..12, DiffKer (mine). All < 500 lines.

## Main statements
* `smooth_rep_of_pow (v) (h : ∀ k, ∃ w, v = ((diffFR..).resolvent 1 ^ k) w) : ∃ ū, MSmooth F ū ∧ v =ᵐ[μ] ū`;
  `smooth_rep_semigroup (ht : t ≠ 0) u : ∃ ū, MSmooth F ū ∧ ⇑((diffFR..).semigroup t u) =ᵐ[μ] ū` (A5ii smoothness, any `u ∈ L²`).
* `Q_smooth_of_weak_eq_pot` (potential κ smooth, weak equation `E u φ + lam⟪u,φ⟫ + ∫ κ u φ dμ = ⟪g,φ⟫`) and
  `interior_sup_estimate_manifold (hW : IsOpen W) (hB : IsCompact B) (hBW : B ⊆ W) lam : ∃ C ≥ 0, ∀ w smooth, (∀ y ∈ W, 𝓛 w y = lam w y) →
  MemLp w 2 (μ.restrict W) → ∀ x ∈ B, |w x| ≤ C (∫_W w²)^(1/2)` (extra hypothesis `MemLp`: otherwise Bochner junk 0 makes it false).
* `Tc t u` (smooth representative of `T_t u`, `t ≠ 0`), `Tc_smooth`, `Tc_ae`, `Tc_add/smul/sub`, `Tc_nonneg`, `Tc_one`, `Tc_comp`
  (`Tc (s+t) u = Tc s (T_t u)`), `Tc_bound` / `local_bound_of_smooth_rep` (closed graph theorem into `C(Kc,ℝ)`),
  **`Tc_local_bound (ht) (hK : IsCompact K) : ∃ C, ∀ u, ∀ x ∈ K, |Tc t u x| ≤ C‖u‖ ∧ |𝓛 (Tc t u) x| ≤ C‖u‖`**,
  **`Tc_generator`: `𝓛 (Tc t (testToL2 f)) x = Tc t (testToL2 (testGen f)) x`** for test functions `f`.
  **`Tc_grad_bound (ht) (hK) : ∃ C, ∀ u, ∀ x ∈ K, ‖mgrad F (Tc t u) x‖ ≤ C‖u‖`** (DiffKerGrad, closed graph in charts; also generic `local_grad_bound_of_smooth_rep`).
* Kernel: `evalCLM`, `pk t x : L²` (Riesz density, `inner_pk : ⟪pk t x, u⟫ = Tc t u x`, `pk_nonneg`), `kmeas t x = μ.withDensity (ofReal ∘ pk)`,
  `Kk t : Kernel M M` (`Kk 0 = Kernel.id`, `Kk_zero`; `Kk_apply_of_ne : Kk t x = kmeas t x`, `Kk_ac : Kk t x ≪ μ`),
  `Kk_markov`, **`Kk_comp : Kk (s+t) = Kk t ∘ₖ Kk s`** (every x), **`Kk_bind : μ.bind (Kk t) = μ`**, `kmeas_integral`
  (`Integrable h (kmeas t x) ∧ ∫ h = Tc t h x` for `h ∈ L²`), `semi_Kk_eq_Tc : semi Kk t f x = Tc t (testToL2 f) x` (f test function),
  `semi_Kk_zero`, `abs_Tc_sub_le : |Tc s f y - f y| ≤ B s` (B bounds |𝓛f|), `continuous_semi_time`, `hasDerivAt_semi_time`,
  **`dynkin_Kk`** (pointwise Dynkin for every x, t), **`isDiffusionSemigroup_Kk : IsDiffusionSemigroup F V (Kk F hV hμ)`**.
* A7: `Kk_eigen (hu : MSmooth u) (hL2 : MemLp u 2 μ) (hc : ∀ x, 𝓛 u x = -c u x) t x : Integrable u (Kk t x) ∧ ∫ u dKk t x = exp(-c t) u x`
  (via `eigen_semigroup`, DiffEig2, and `Q`-membership by Gaffney).
* `resolvent_repr (hlam : 0 < lam) (g) (hg : MSmooth g) (hc : HasCompactSupport g) : ∃ ū, MSmooth ū ∧ ⇑(resolvent lam (testToL2 ⟨g,hg,hc⟩)) =ᵐ ū ∧
  ∀ x, ū x = ∫ s in Ioi 0, exp(-lam s) * semi (Kk F hV hμ) s.toNNReal g x`  (via `FormData.inner_resolvent_eq_laplace`, DiffLap1).

## The deliverable
```lean
structure KerCanonical (V) (μ) (Kk) : Prop  -- = CanonicalDiffusion without `contraction` and without the gradient bound
  markov, dynkin, invariant, eigen,
  smoothing : ∀ g smooth cpt, ∀ t, MSmooth (semi Kk t g) ∧ 𝓛 (semi Kk t g) = semi Kk t (𝓛 g) ∧
      ∃ C, ∀ s x, |semi Kk s g x| ≤ C ∧ |𝓛 (semi Kk s g) x| ≤ C
theorem exists_kernel (hV) (hμ) : ∃ Kk, KerCanonical F V μ Kk          -- Kk := Kk F hV hμ
theorem KerCanonical.toCanonical (h) (hgrad : ∀ g smooth cpt, ∃ C, ∀ s x, ‖mgrad F (semi Kk s g) x‖ ≤ C) (hcontr : contraction) :
   CanonicalDiffusion F V μ ρ Kk
```
Only the uniform-in-s gradient bound and `contraction` are missing (BE / KUW-B).

## Notes
* Closed graph theorem is used instead of quantitative Sobolev chains for `C(K,t)`; constants exist but are not explicit.
* `IsFiniteMeasure μ` suffices (probability not needed here).
