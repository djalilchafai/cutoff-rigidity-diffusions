# diff-KUWB-BE: BEPointwise extended to bounded Lipschitz functions -- DONE

Files: CutoffRigidity/Riemann/DiffKuwBE1.lean, DiffKuwBE2.lean, DiffKuwBE3.lean, umbrella DiffKuwBE.lean.
Namespace CutoffRigidity.Riemann.Diff. Standing hypotheses of DiffKer12 (F, M complete connected Riemannian,
hV : MSmooth F V, [IsFiniteMeasure μ], hμ : IsWeightedVolume F μ V); `Kk F hV hμ`. `SharpApprox` is a hypothesis (hA). No sorry/axiom;
axioms of all theorems: propext, Classical.choice, Quot.sound.

* (B0) `semi_eq_Tc_of_lip (hc : Continuous ψ) (hB : ∀ x, |ψ x| ≤ B) (ht : t ≠ 0) : ∃ u : M →₂[μ] ℝ, (u : M → ℝ) =ᵐ[μ] ψ ∧ ∀ x, semi (Kk F hV hμ) t ψ x = Tc F hV hμ t u x`
* `semi_smooth_of_lip (hc) (hB) (ht) : MSmooth F (semi (Kk F hV hμ) t ψ)`; `integrable_Kk_of_bdd`; `memLp_of_bdd_cont`.
* (B1, 0th order) `semi_sub_le (hc₁ hc₂ hB₁ hB₂) t (h : ∀ y, |ψ₁ y - ψ₂ y| ≤ δ) x : |semi t ψ₁ x - semi t ψ₂ x| ≤ δ`.
* (B1) `grad_semi_sub_le (ht : t ≠ 0) (hK : IsCompact K) : ∃ C, 0 ≤ C ∧ ∀ ψ₁ ψ₂ B₁ B₂, Continuous ψ₁ → Continuous ψ₂ → (∀ x, |ψ₁ x| ≤ B₁) → (∀ x, |ψ₂ x| ≤ B₂) → ∀ δ ≥ 0, (∀ y, |ψ₁ y - ψ₂ y| ≤ δ) → ∀ x ∈ K, ‖mgrad F (semi t ψ₁) x - mgrad F (semi t ψ₂) x‖ ≤ C * δ`.
  (BE2) `grad_semi_sub_le_L2` (same with C * sqrt (∫ (ψ₁-ψ₂)² dμ)), `tendsto_grad_semi`, `norm_sq_L2`.
* (B2) `integrable_lipAt_sq (hψ : LipschitzWith L ψ) t x : Integrable (fun y => lipAt ψ y ^ 2) (Kk F hV hμ t x)`
* (B2) **`beLip (hBE : BEPointwise F V μ ρ (Kk F hV hμ)) (hA : SharpApprox F M) (hψ : LipschitzWith L ψ) (hB : ∀ x, |ψ x| ≤ B) (ht : t ≠ 0) (x : M) : ‖mgrad F (semi (Kk F hV hμ) t ψ) x‖ ^ 2 ≤ Real.exp (-2 * ρ * t) * ∫ y, lipAt ψ y ^ 2 ∂(Kk F hV hμ t x)`**
  (only IsFiniteMeasure μ needed; t : ℝ≥0).
