module

public import CutoffRigidity.Paper.ConvexCutoff
public import CutoffRigidity.ProductConditionTheorem

/-! # Theorem 1.7 (curvature product condition) on the statement surface -/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped ENNReal NNReal Topology Asymptotics

universe u

section Profiles

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}

theorem worst_tv_curved (D : CurvedLangevinData Ω' d) {S : Set (CutCur.Rd d)}
    (hS : S.Nonempty) {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hk : ∀ (t : ℝ≥0) (x : CutCur.Rd d), langevinKernel D.potential D.driver D.noiseLaw t x =
      P.map (X x t)) (t : ℝ) :
    CutCur.worst P X S
      (fun ν => ENNReal.ofReal (CutCur.tvDist ν (CutCur.gibbs D.potential))) t =
        ENNReal.ofReal (curvedTVProfile D S t) := by
  have := D.probability
  have hmk := langevinKernel_isMarkovKernel D.brownian D.smooth D.curvature D.curvature_pos.le
    D.hessian t.toNNReal
  let tv := fun x => totalVariationDistance
    (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume D.potential)
  have hf : Monotone ENNReal.ofReal := fun a b hab => ENNReal.ofReal_le_ofReal hab
  have hbdd : BddAbove (tv '' S) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact totalVariationDistance_le_one _ _
  have hcs := hf.map_csSup_of_continuousAt ENNReal.continuous_ofReal.continuousAt (hS.image tv) hbdd
  unfold CutCur.worst curvedTVProfile kernelTVProfile
  rw [iSup_subtype']
  change _ = ENNReal.ofReal (sSup (tv '' S))
  rw [hcs, Set.image_image, sSup_image']
  refine iSup_congr fun x => ?_
  rw [← hk t.toNNReal x.1]
  beta_reduce
  rw [tvDist_eq_totalVariationDistance]
  rfl

theorem worst_kl_curved (D : CurvedLangevinData Ω' d) (S : Set (CutCur.Rd d))
    {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hk : ∀ (t : ℝ≥0) (x : CutCur.Rd d), langevinKernel D.potential D.driver D.noiseLaw t x =
      P.map (X x t)) (t : ℝ) :
    CutCur.worst P X S (InformationTheory.klDiv · (CutCur.gibbs D.potential)) t =
      curvedEntropyProfile D S t := by
  unfold CutCur.worst curvedEntropyProfile
  rw [iSup_subtype']
  refine iSup_congr fun x => ?_
  rw [← hk t.toNNReal x.1]
  rfl

theorem worst_fisher_curved (D : CurvedLangevinData Ω' d) (S : Set (CutCur.Rd d))
    {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hk : ∀ (t : ℝ≥0) (x : CutCur.Rd d), langevinKernel D.potential D.driver D.noiseLaw t x =
      P.map (X x t)) (t : ℝ) :
    CutCur.worst P X S (CutCur.fisherInfo D.potential) t = curvedFisherProfile D S t := by
  have := D.probability
  have := langevinKernel_isMarkovKernel D.brownian D.smooth D.curvature D.curvature_pos.le
    D.hessian t.toNNReal
  unfold CutCur.worst curvedFisherProfile
  rw [iSup_subtype']
  refine iSup_congr fun x => ?_
  rw [← hk t.toNNReal x.1]
  exact fisherInfo_eq_relativeFisherInformation D.smooth D.probability D.curvature
    D.curvature_pos D.hessian _

theorem worst_wasserstein_curved (D : CurvedLangevinData Ω' d) (S : Set (CutCur.Rd d))
    {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hk : ∀ (t : ℝ≥0) (x : CutCur.Rd d), langevinKernel D.potential D.driver D.noiseLaw t x =
      P.map (X x t)) (t : ℝ) :
    CutCur.worst P X S (CutCur.wasserstein2 · (CutCur.gibbs D.potential)) t =
      curvedWassersteinSqProfile D S t ^ (1 / 2 : ℝ) := by
  have hmap := (ENNReal.orderIsoRpow (1 / 2) (by norm_num)).map_iSup
    (fun x : S => squaredWasserstein
      (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume D.potential))
  unfold CutCur.worst curvedWassersteinSqProfile
  rw [iSup_subtype']
  refine Eq.trans (iSup_congr fun x => ?_) hmap.symm
  rw [← hk t.toNNReal x.1]
  beta_reduce
  rw [wasserstein2_eq_rpow]
  rfl

theorem mixingTime_eq_curved (D : CurvedLangevinData Ω' d) {S : Set (CutCur.Rd d)}
    (hS : S.Nonempty) {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hk : ∀ (t : ℝ≥0) (x : CutCur.Rd d), langevinKernel D.potential D.driver D.noiseLaw t x =
      P.map (X x t)) {η : ℝ} (hη : 0 ≤ η) :
    CutCur.mixingTime P X (CutCur.gibbs D.potential) S η = curvedMixingTime D S η := by
  unfold CutCur.mixingTime curvedMixingTime langevinTVMixingTime kernelTVMixingTime
  refine iInf_congr fun t => iInf_congr_Prop ?_ fun _ => rfl
  rw [worst_tv_curved D hS hk, ENNReal.ofReal_le_ofReal_iff hη]
  have : curvedTVProfile D S (t : ℝ) =
      kernelTVProfile (langevinKernel D.potential D.driver D.noiseLaw) (gibbsMeasure volume D.potential)
        S t := by
    unfold curvedTVProfile
    rw [Real.toNNReal_coe]
  rw [this]

end Profiles

/-- The trivial dimension-zero data. -/
noncomputable def padCurved {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] :
    CurvedLangevinData Ω' 0 where
  potential := fun _ => 0
  smooth := contDiff_const
  probability := by
    have := volume_rd_zero
    simpa [gibbsMeasure] using this
  driver := fun _ _ => 0
  noiseLaw := P'
  brownian := ⟨fun i => i.elim0, iIndepFun.of_subsingleton⟩
  curvature := 1
  curvature_pos := one_pos
  hessian := fun x z => by
    have : z = 0 := Subsingleton.elim _ _
    subst this
    simp

/-- **Theorem 1.7** (curvature product condition), in the amended form. -/
theorem product_condition_cutoff {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    {V : ∀ n, CutCur.Rd n → ℝ} {B : ∀ n, ℝ≥0 → Ω n → CutCur.Rd n} {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, CutCur.Rd n → ℝ≥0 → Ω n → CutCur.Rd n} {κ : ℕ → ℝ} {S : ∀ n, Set (CutCur.Rd n)}
    {η : ℝ}
    (hL : ∀ n, 0 < n → CutCur.IsLangevin (V n) (B n) (P n) (X n) ∧ 0 < κ n ∧
      ∀ x z : CutCur.Rd n, κ n * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (V n)) x z z)
    (hS : ∀ n, (S n).Nonempty) (hη : 0 < η) (hη1 : η < 1) :
    let t₀ := fun n => CutCur.mixingTime (P n) (X n) (CutCur.gibbs (V n)) (S n) η
    let prof := fun (δ : ∀ n, Measure (CutCur.Rd n) → ℝ≥0∞) n =>
      CutCur.worst (P n) (X n) (S n) (δ n)
    (∀ᶠ n in atTop, t₀ n < ⊤) → Tendsto (fun n => κ n * (t₀ n).toReal) atTop atTop →
      (CutCur.HasCutoff (prof fun n ν => .ofReal (CutCur.tvDist ν (CutCur.gibbs (V n))))
          (fun n => (t₀ n).toReal) 1 0 ∧
        CutCur.HasCutoff (prof fun n ν => InformationTheory.klDiv ν (CutCur.gibbs (V n)))
          (fun n => (t₀ n).toReal) ⊤ 0) ∧
      (0 < liminf (fun n => ENNReal.ofReal (κ n)) atTop →
        Tendsto (fun n => (t₀ n).toReal) atTop atTop →
        CutCur.HasCutoff (prof fun n => CutCur.fisherInfo (V n)) (fun n => (t₀ n).toReal) ⊤ 0 ∧
        CutCur.HasCutoff (prof fun n ν => CutCur.wasserstein2 ν (CutCur.gibbs (V n)))
          (fun n => (t₀ n).toReal) ⊤ 0) := by
  intro t₀ prof hfin hprod
  obtain ⟨Ω', _, drv, P', hdrv, hnoise⟩ :=
    exists_seqBrownian (fun n hn => isStdBrownian_iff.mp (hL n hn).1.2.2.1)
  have hP' : IsProbabilityMeasure P' := (hdrv 1).isProbabilityMeasure
  let D : ∀ n, CurvedLangevinData Ω' n := fun n =>
    match n with
    | 0 => padCurved P'
    | m + 1 =>
      { potential := V (m + 1)
        smooth := (hL (m + 1) (Nat.succ_pos m)).1.1
        probability := gibbs_probability (hL (m + 1) (Nat.succ_pos m)).1.2.1
        driver := drv (m + 1)
        noiseLaw := P'
        brownian := hdrv (m + 1)
        curvature := κ (m + 1)
        curvature_pos := (hL (m + 1) (Nat.succ_pos m)).2.1
        hessian := (hL (m + 1) (Nat.succ_pos m)).2.2 }
  have hev : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hpot : ∀ n, 0 < n → (D n).potential = V n := fun n hn => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rfl
  have hcurv : ∀ n, 0 < n → (D n).curvature = κ n := fun n hn => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rfl
  have hk : ∀ n, 0 < n → ∀ (s : ℝ≥0) (x : CutCur.Rd n),
      langevinKernel (D n).potential (D n).driver (D n).noiseLaw s x = (P n).map (X n x s) := by
    intro n hn s x
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    change langevinKernel (V (m + 1)) (drv (m + 1)) P' s x = _
    rw [IsLangevin.map_eq_langevinKernel (hL (m + 1) hn).1 (κ (m + 1)) (hL (m + 1) hn).2.1.le
      (hL (m + 1) hn).2.2 x s, langevinKernel_congr_noise (V (m + 1)) (hnoise (m + 1) hn)]
  have hmix : ∀ n, 0 < n → t₀ n = curvedMixingTime (D n) (S n) η := fun n hn => by
    have := mixingTime_eq_curved (D n) (hS n) (hk n hn) hη.le
    rw [hpot n hn] at this
    exact this
  have hcrit : ∀ n, 0 < n → curvedCriticalTime (D n) (S n) η = (t₀ n).toReal := fun n hn => by
    rw [hmix n hn]; rfl
  have hfinite : ∀ᶠ n in atTop, curvedMixingTime (D n) (S n) η < ⊤ := by
    filter_upwards [hfin, hev] with n h1 hn
    rwa [hmix n hn] at h1
  have hprod' : Tendsto (fun n => (D n).curvature * curvedCriticalTime (D n) (S n) η) atTop atTop := by
    refine hprod.congr' ?_
    filter_upwards [hev] with n hn
    rw [hcrit n hn, hcurv n hn]
  -- profile transfer
  have prof_transfer : ∀ {δ : ∀ n, Measure (CutCur.Rd n) → ℝ≥0∞} {Q : ℕ → ℝ → ℝ≥0∞},
      (∀ n, 0 < n → ∀ s : ℝ, CutCur.worst (P n) (X n) (S n) (δ n) s = Q n s) →
      ∀ (a : ℝ≥0∞) (σ : ℝ),
        Tendsto (fun n => Q n (σ * curvedCriticalTime (D n) (S n) η)) atTop (𝓝 a) →
        Tendsto (fun n => prof δ n (σ * (t₀ n).toReal)) atTop (𝓝 a) := by
    intro δ Q hQ a σ hlim
    refine hlim.congr' ?_
    filter_upwards [hev] with n hn
    rw [hcrit n hn]
    exact (hQ n hn _).symm
  have hTv : ∀ {a : ℝ} {u : ℕ → ℝ}, Tendsto u atTop (𝓝 a) →
      Tendsto (fun n => ENNReal.ofReal (u n)) atTop (𝓝 (ENNReal.ofReal a)) :=
    fun hu => (ENNReal.continuous_ofReal.tendsto _).comp hu
  have hTVq : ∀ n, 0 < n → ∀ s : ℝ, CutCur.worst (P n) (X n) (S n)
      (fun ν => .ofReal (CutCur.tvDist ν (CutCur.gibbs (V n)))) s =
        ENNReal.ofReal (curvedTVProfile (D n) (S n) s) := fun n hn s => by
    have := worst_tv_curved (D n) (hS n) (hk n hn) s
    rw [hpot n hn] at this
    exact this
  have hKq : ∀ n, 0 < n → ∀ s : ℝ, CutCur.worst (P n) (X n) (S n)
      (fun ν => InformationTheory.klDiv ν (CutCur.gibbs (V n))) s =
        curvedEntropyProfile (D n) (S n) s := fun n hn s => by
    have := worst_kl_curved (D n) (S n) (hk n hn) s
    rw [hpot n hn] at this
    exact this
  have hFq : ∀ n, 0 < n → ∀ s : ℝ, CutCur.worst (P n) (X n) (S n) (CutCur.fisherInfo (V n)) s =
      curvedFisherProfile (D n) (S n) s := fun n hn s => by
    have := worst_fisher_curved (D n) (S n) (hk n hn) s
    rw [hpot n hn] at this
    exact this
  have hWq : ∀ n, 0 < n → ∀ s : ℝ, CutCur.worst (P n) (X n) (S n)
      (fun ν => CutCur.wasserstein2 ν (CutCur.gibbs (V n))) s =
        curvedWassersteinSqProfile (D n) (S n) s ^ (1 / 2 : ℝ) := fun n hn s => by
    have := worst_wasserstein_curved (D n) (S n) (hk n hn) s
    rw [hpot n hn] at this
    exact this
  refine ⟨⟨fun ε h0 h1 => ?_, fun ε h0 h1 => ?_⟩, fun hliminf ht0 => ⟨fun ε h0 h1 => ?_, fun ε h0 h1 => ?_⟩⟩
  · obtain ⟨hTVb, hTVa, -, -⟩ := curvature_product_condition_tv_entropy D S hS η hη hη1 hfinite
      hprod' ε h0 h1
    refine ⟨prof_transfer (Q := fun n s => ENNReal.ofReal (curvedTVProfile (D n) (S n) s)) hTVq _ _ ?_,
      prof_transfer (Q := fun n s => ENNReal.ofReal (curvedTVProfile (D n) (S n) s)) hTVq _ _ ?_⟩
    · have := hTv hTVb
      rwa [ENNReal.ofReal_one] at this
    · have := hTv hTVa
      rwa [ENNReal.ofReal_zero] at this
  · obtain ⟨-, -, hHb, hHa⟩ := curvature_product_condition_tv_entropy D S hS η hη hη1 hfinite
      hprod' ε h0 h1
    exact ⟨prof_transfer (Q := fun n s => curvedEntropyProfile (D n) (S n) s) hKq _ _ hHb,
      prof_transfer (Q := fun n s => curvedEntropyProfile (D n) (S n) s) hKq _ _ hHa⟩
  · have hliminf' : 0 < liminf (fun n => ENNReal.ofReal (D n).curvature) atTop := by
      have := Filter.liminf_congr (f := atTop) (u := fun n => ENNReal.ofReal (D n).curvature)
        (v := fun n => ENNReal.ofReal (κ n))
        (by filter_upwards [hev] with n hn using by rw [hcurv n hn])
      rwa [this]
    have ht0' : Tendsto (fun n => curvedCriticalTime (D n) (S n) η) atTop atTop := by
      refine ht0.congr' ?_
      filter_upwards [hev] with n hn
      rw [hcrit n hn]
    obtain ⟨hIb, hIa⟩ := curvature_product_condition_fisher D S hS η hη hη1 hfinite hprod' hliminf'
      ht0' ε h0 h1
    exact ⟨prof_transfer (Q := fun n s => curvedFisherProfile (D n) (S n) s) hFq _ _ hIb,
      prof_transfer (Q := fun n s => curvedFisherProfile (D n) (S n) s) hFq _ _ hIa⟩
  · have hliminf' : 0 < liminf (fun n => ENNReal.ofReal (D n).curvature) atTop := by
      have := Filter.liminf_congr (f := atTop) (u := fun n => ENNReal.ofReal (D n).curvature)
        (v := fun n => ENNReal.ofReal (κ n))
        (by filter_upwards [hev] with n hn using by rw [hcurv n hn])
      rwa [this]
    have ht0' : Tendsto (fun n => curvedCriticalTime (D n) (S n) η) atTop atTop := by
      refine ht0.congr' ?_
      filter_upwards [hev] with n hn
      rw [hcrit n hn]
    obtain ⟨hWb, hWa⟩ := curvature_product_condition_wasserstein D S hS η hη hη1 hfinite hprod'
      hliminf' ht0' ε h0 h1
    have hsq := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto
    refine ⟨prof_transfer (Q := fun n s => curvedWassersteinSqProfile (D n) (S n) s ^ (1 / 2 : ℝ))
        hWq _ _ ?_,
      prof_transfer (Q := fun n s => curvedWassersteinSqProfile (D n) (S n) s ^ (1 / 2 : ℝ))
        hWq _ _ ?_⟩
    · have := (hsq ⊤).comp hWb
      rwa [ENNReal.top_rpow_of_pos (by norm_num)] at this
    · have := (hsq 0).comp hWa
      rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this

end CutoffRigidity.Paper
