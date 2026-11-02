module

public import CutoffRigidity.Extra.GaussIso4

/-! # Monotonicity of `Ψ` and the 1D Bobkov inequality for good data (stage 3c) -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology

set_option linter.unusedSectionVars false

namespace CutoffRigidity.GaussIso

/-- `Ψ(s) = ∫ √(I(P_s f)² + (P_s f)'²) dγ`. -/
noncomputable def Psi (f f1 : ℝ → ℝ) (s : ℝ) : ℝ := ∫ x, pF (G0 f s) (G1 f1 s) x ∂γ1

lemma Prof.continuous_SF {ε : ℝ} {g0 g1 g2 g3 : ℝ → ℝ} (P : Prof ε g0 g1 g2 g3) :
    Continuous (pSF g0 g1 g2 g3) := by
  have hF := P.continuous_F
  have hFne : ∀ x, pF g0 g1 x ≠ 0 := fun x => (P.pF_pos x).ne'
  have hA := P.continuous_A; have hQ := P.continuous_Q
  have h1 := P.b1.cont; have h2 := P.b2.cont; have h3 := P.b3.cont
  unfold pSF
  exact Continuous.div (by fun_prop) hF hFne

lemma integrable_linear_bound (D : ℝ) : Integrable (fun x : ℝ => D * (1 + |x|)) γ1 := by
  have h1 : Integrable (fun y : ℝ => |y|) γ1 := (memLp_id_gaussianReal 1).integrable le_rfl |>.norm
  have := ((integrable_const (1:ℝ)).add h1).const_mul D
  exact this

lemma tendsto_rr_atTop : Tendsto rr atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero

lemma tendsto_sg_atTop : Tendsto sg atTop (𝓝 1) := by
  have h : Tendsto (fun s : ℝ => Real.exp (-2 * s)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (show (0:ℝ) < 2 by norm_num))
    refine this.congr fun s => ?_
    simp [Function.comp]
  have := (Real.continuous_sqrt.tendsto (1 - 0)).comp (tendsto_const_nhds.sub h)
  rw [show Real.sqrt (1 - 0) = 1 by simp] at this
  refine this.congr fun s => ?_
  simp only [Function.comp, sg]

section good
variable {ε : ℝ} {f f1 f2 f3 : ℝ → ℝ} (H : Good ε f f1 f2 f3)
include H

lemma Good.integrable_pF (s : ℝ) : Integrable (pF (G0 f s) (G1 f1 s)) γ1 := by
  obtain ⟨C, hC⟩ := (H.prof s).bd_F
  exact Integrable.mono' (integrable_const C) (H.prof s).continuous_F.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa using hC x)

lemma Good.hasDerivAt_Psi {s : ℝ} (hs : 0 < s) :
    HasDerivAt (Psi f f1) (∫ x, pSF (G0 f s) (G1 f1 s) (G2 f2 s) (G3 f3 s) x ∂γ1) s := by
  obtain ⟨D, hD⟩ := H.exists_bound_SF
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ1) (𝕜 := ℝ)
    (F := fun t x => pF (G0 f t) (G1 f1 t) x)
    (F' := fun t x => pSF (G0 f t) (G1 f1 t) (G2 f2 t) (G3 f3 t) x)
    (x₀ := s) (s := Metric.ball s (s / 2)) (bound := fun x => D * (1 + |x|))
    (Metric.ball_mem_nhds _ (by linarith))
    (Eventually.of_forall fun t => (H.prof t).continuous_F.aestronglyMeasurable)
    (H.integrable_pF s)
    (H.prof s).continuous_SF.aestronglyMeasurable
    (Eventually.of_forall fun x t ht => by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
      have := hD t (by linarith) x
      simpa using this)
    (integrable_linear_bound D)
    (Eventually.of_forall fun x t ht => by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
      exact H.hasDerivAt_pF x (by linarith))
  exact key.2

lemma Good.deriv_Psi_nonpos {s : ℝ} (hs : 0 < s) : deriv (Psi f f1) s ≤ 0 := by
  rw [(H.hasDerivAt_Psi hs).deriv, (H.prof s).integral_SF, neg_nonpos]
  exact integral_nonneg fun x => (H.prof s).pM_nonneg x

lemma Good.continuousOn_Psi : ContinuousOn (Psi f f1) (Ici 0) := by
  obtain ⟨C1, hC1⟩ := H.b1.bdd
  have hC1' : 0 ≤ C1 := (abs_nonneg _).trans (hC1 0)
  unfold Psi
  refine continuousOn_of_dominated (bound := fun _ => gφ 0 + C1) (fun s _ => ?_) (fun s hs => ?_) ?_ ?_
  · exact (H.prof s).continuous_F.aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_pos ((H.prof s).pF_pos x)]
    have hs' : 0 ≤ s := hs
    have hg : |G1 f1 s x| ≤ C1 := abs_G1_le hC1 hs' x
    unfold pF
    calc Real.sqrt (gI (G0 f s x) ^ 2 + G1 f1 s x ^ 2) ≤ Real.sqrt ((gφ 0 + C1) ^ 2) := by
          apply Real.sqrt_le_sqrt
          have h1 : gI (G0 f s x) ≤ gφ 0 := gI_le _
          have h2 : G1 f1 s x ^ 2 ≤ C1 ^ 2 := by nlinarith [abs_nonneg (G1 f1 s x), sq_abs (G1 f1 s x)]
          nlinarith [gI_nonneg (G0 f s x), gφ_pos 0]
      _ = gφ 0 + C1 := Real.sqrt_sq (by have := gφ_pos 0; linarith)
  · exact integrable_const _
  · refine Eventually.of_forall fun x => ?_
    have hg0 : Continuous fun s => G0 f s x := continuous_mT_s H.b0 x
    have hg1 : Continuous fun s => G1 f1 s x := continuous_rr.mul (continuous_mT_s H.b1 x)
    have hI : ∀ s, ContinuousAt gI (G0 f s x) := fun s =>
      (hasDerivAt_gI ((H.prof s).mem x)).continuousAt
    have hc : Continuous fun s => gI (G0 f s x) :=
      continuous_iff_continuousAt.2 fun s => ContinuousAt.comp (f := fun s => G0 f s x) (x := s) (hI s) hg0.continuousAt
    show ContinuousOn (fun s => Real.sqrt (gI (G0 f s x) ^ 2 + G1 f1 s x ^ 2)) _
    exact (Real.continuous_sqrt.comp ((hc.pow 2).add (hg1.pow 2))).continuousOn

lemma Good.antitoneOn_Psi : AntitoneOn (Psi f f1) (Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) H.continuousOn_Psi ?_ ?_
  · intro s hs
    rw [interior_Ici] at hs
    exact (H.hasDerivAt_Psi hs).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    exact H.deriv_Psi_nonpos hs

lemma Good.G0_zero (x : ℝ) : G0 f 0 x = f x := by
  unfold G0 mT
  have : sg 0 = 0 := by simp [sg]
  simp [this, rr]

lemma Good.G1_zero (x : ℝ) : G1 f1 0 x = f1 x := by
  unfold G1 mT
  have : sg 0 = 0 := by simp [sg]
  simp [this, rr]

lemma Good.Psi_zero : Psi f f1 0 = ∫ x, Real.sqrt (gI (f x) ^ 2 + f1 x ^ 2) ∂γ1 := by
  unfold Psi pF
  simp_rw [H.G0_zero, H.G1_zero]


lemma Good.tendsto_G0 (x : ℝ) : Tendsto (fun s => G0 f s x) atTop (𝓝 (∫ y, f y ∂γ1)) := by
  have hc := (continuous_mT_ab H.b0 x).tendsto (0, 1)
  have h2 : Tendsto (fun s => (rr s, sg s)) atTop (𝓝 ((0:ℝ), (1:ℝ))) :=
    Filter.Tendsto.prodMk_nhds tendsto_rr_atTop tendsto_sg_atTop
  have := hc.comp h2
  have e : mT f 0 1 x = ∫ y, f y ∂γ1 := by simp [mT]
  simp only [e] at this
  exact this

lemma Good.tendsto_G1 (x : ℝ) : Tendsto (fun s => G1 f1 s x) atTop (𝓝 0) := by
  obtain ⟨C1, hC1⟩ := H.b1.bdd
  refine squeeze_zero_norm' ?_ (Filter.Tendsto.mul_const C1 tendsto_rr_atTop |>.congr (fun s => rfl) |> fun h => by simpa using h)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
  rw [Real.norm_eq_abs]
  unfold G1
  rw [abs_mul, abs_of_pos (rr_pos s)]
  exact mul_le_mul_of_nonneg_left ((mT_abs_le hC1 _ _ x)) (rr_pos s).le


lemma Good.mean_mem : ε ≤ ∫ y, f y ∂γ1 ∧ ∫ y, f y ∂γ1 ≤ 1 - ε := by
  have h := H.tendsto_G0 0
  exact ⟨ge_of_tendsto h (Eventually.of_forall fun s => ((H.prof s).rng 0).1),
    le_of_tendsto h (Eventually.of_forall fun s => ((H.prof s).rng 0).2)⟩

lemma Good.tendsto_Psi : Tendsto (Psi f f1) atTop (𝓝 (gI (∫ y, f y ∂γ1))) := by
  obtain ⟨C1, hC1⟩ := H.b1.bdd
  have hC1' : 0 ≤ C1 := (abs_nonneg _).trans (hC1 0)
  have hm : (∫ y, f y ∂γ1) ∈ Ioo (0:ℝ) 1 :=
    ⟨H.hε.trans_le H.mean_mem.1, by linarith [H.mean_mem.2, H.hε]⟩
  have hlim : ∀ x, Tendsto (fun s => pF (G0 f s) (G1 f1 s) x) atTop (𝓝 (gI (∫ y, f y ∂γ1))) := by
    intro x
    have h1 : Tendsto (fun s => gI (G0 f s x)) atTop (𝓝 (gI (∫ y, f y ∂γ1))) :=
      (hasDerivAt_gI hm).continuousAt.tendsto.comp (H.tendsto_G0 x)
    have h2 := (Real.continuous_sqrt.tendsto _).comp ((h1.pow 2).add ((H.tendsto_G1 x).pow 2))
    have e : Real.sqrt (gI (∫ y, f y ∂γ1) ^ 2 + 0 ^ 2) = gI (∫ y, f y ∂γ1) := by
      simp [Real.sqrt_sq (gI_nonneg _)]
    rw [e] at h2
    exact h2
  have := tendsto_integral_filter_of_dominated_convergence (μ := γ1) (l := atTop)
    (F := fun s x => pF (G0 f s) (G1 f1 s) x) (f := fun _ => gI (∫ y, f y ∂γ1))
    (bound := fun _ => gφ 0 + C1)
    (Eventually.of_forall fun s => (H.prof s).continuous_F.aestronglyMeasurable)
    (by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
      refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_of_pos ((H.prof s).pF_pos x)]
      have hg : |G1 f1 s x| ≤ C1 := abs_G1_le hC1 hs x
      unfold pF
      calc Real.sqrt (gI (G0 f s x) ^ 2 + G1 f1 s x ^ 2) ≤ Real.sqrt ((gφ 0 + C1) ^ 2) := by
            apply Real.sqrt_le_sqrt
            have h1 : gI (G0 f s x) ≤ gφ 0 := gI_le _
            have h2 : G1 f1 s x ^ 2 ≤ C1 ^ 2 := by nlinarith [abs_nonneg (G1 f1 s x), sq_abs (G1 f1 s x)]
            nlinarith [gI_nonneg (G0 f s x), gφ_pos 0]
        _ = gφ 0 + C1 := Real.sqrt_sq (by have := gφ_pos 0; linarith))
    (integrable_const _)
    (Eventually.of_forall hlim)
  simp only [integral_const, probReal_univ, one_smul] at this
  exact this

/-- **One-dimensional Bobkov inequality** for good data. -/
theorem Good.bobkov :
    gI (∫ y, f y ∂γ1) ≤ ∫ x, Real.sqrt (gI (f x) ^ 2 + f1 x ^ 2) ∂γ1 := by
  rw [← H.Psi_zero]
  refine le_of_tendsto H.tendsto_Psi ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
  exact H.antitoneOn_Psi (mem_Ici.2 le_rfl) (mem_Ici.2 hs) hs

end good
end CutoffRigidity.GaussIso
