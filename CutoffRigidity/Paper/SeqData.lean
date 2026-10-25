module

public import CutoffRigidity.Paper.GapBridge
public import CutoffRigidity.SpectralInformationLowerCutoffs
public import Mathlib.Probability.ProductMeasure

/-! # Common probability space for a sequence of statement-surface dimensions

The library proves the `Lᵖ` cutoff for sequences of data living on one common
probability space. The statement surface lets the probability space vary with the
dimension. Both are reconciled by the infinite product of the spaces: each
dimension's Brownian motion and Langevin solutions are pulled back along the
measure-preserving coordinate projection, which leaves every law unchanged.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology Asymptotics

/-! ### Transfer along measure-preserving maps -/

section Transfer

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}

theorem isBrownianReal_comp_measurePreserving {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} {P' : Measure Ω'}
    {f : Ω' → Ω} (hf : MeasurePreserving f P' P) (hX : IsBrownianReal X P) :
    IsBrownianReal (fun t ω => X t (f ω)) P' where
  hasLaw I := (hX.hasLaw I).comp hf.hasLaw
  cont := hf.quasiMeasurePreserving.ae hX.cont

theorem isEuclideanBrownian_comp_measurePreserving {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    {P : Measure Ω} {P' : Measure Ω'} {f : Ω' → Ω} (hf : MeasurePreserving f P' P)
    (hB : IsEuclideanBrownian B P) : IsEuclideanBrownian (fun t ω => B t (f ω)) P' := by
  have hP' : IsProbabilityMeasure P' := hf.hasLaw.isProbabilityMeasure_iff.mpr hB.isProbabilityMeasure
  have hP := hB.isProbabilityMeasure
  refine ⟨fun i => isBrownianReal_comp_measurePreserving hf (hB.coordinate i), ?_⟩
  have hm : ∀ i, AEMeasurable (fun ω => fun t : ℝ≥0 => B t ω i) P := fun i =>
    realBrownian_aemeasurable_path (hB.coordinate i)
  have hind := (iIndepFun_iff_map_fun_eq_pi_map hm).mp hB.independent
  rw [iIndepFun_iff_map_fun_eq_pi_map
    (f := fun i ω => fun t : ℝ≥0 => B t (f ω) i)
    (μ := P') (fun i => (hm i).comp_quasiMeasurePreserving hf.quasiMeasurePreserving :
      ∀ i, AEMeasurable (fun ω => fun t : ℝ≥0 => B t (f ω) i) P')]
  have h1 : P'.map (fun ω i => fun t : ℝ≥0 => B t (f ω) i) =
      P.map (fun ω i => fun t : ℝ≥0 => B t ω i) := by
    rw [← hf.map_eq, AEMeasurable.map_map_of_aemeasurable]
    · rfl
    · rw [hf.map_eq]
      exact AEMeasurable.of_eval hm
    · exact hf.aemeasurable
  rw [h1, hind]
  congr 1
  ext i : 1
  rw [← hf.map_eq, AEMeasurable.map_map_of_aemeasurable (by rw [hf.map_eq]; exact hm i)
    hf.aemeasurable]
  rfl

theorem brownianNoiseLaw_comp {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} {P : Measure Ω}
    {P' : Measure Ω'} {f : Ω' → Ω} (hf : MeasurePreserving f P' P)
    (hB : IsEuclideanBrownian B P) :
    brownianNoiseLaw (fun t ω => B t (f ω)) P' = brownianNoiseLaw B P := by
  unfold brownianNoiseLaw
  rw [← hf.map_eq, AEMeasurable.map_map_of_aemeasurable
    (by rw [hf.map_eq]; exact brownianContinuousDrivingPath_aemeasurable hB) hf.aemeasurable]
  rfl

theorem volume_rd_zero : IsProbabilityMeasure (volume : Measure (EuclideanSpace ℝ (Fin 0))) := by
  constructor
  have h := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (ι := Fin 0))
  have h2 := h.measure_preimage_equiv (s := Set.univ)
  rw [Set.preimage_univ] at h2
  have h3 : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
    rw [volume_pi, Measure.pi_univ]; simp
  exact h2.trans h3

end Transfer

/-! ### Library data attached to the statement-surface hypotheses -/

section Data

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}

theorem gibbs_probability {V : CutCur.Rd d → ℝ} (h : IsProbabilityMeasure (CutCur.gibbs V)) :
    IsProbabilityMeasure (gibbsMeasure volume V) := h

/-- The library data of a rigid Langevin dimension, with the Brownian motion pulled back
along a measure-preserving map. -/
noncomputable def lpData {V : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω}
    {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d} (hL : CutCur.IsLangevin V B P X)
    (hrig : CutCur.RigidCurvature V) {P' : Measure Ω'} {f : Ω' → Ω}
    (hf : MeasurePreserving f P' P) : SpectralInformationLowerData Ω' d where
  potential := V
  smooth := hL.1
  rate := CutCur.spectralGap V
  rate_pos := hrig.1
  hessian := hrig.2
  probability := gibbs_probability hL.2.1
  spectral := fun _ => (spectralGap_eq_gibbsSpectralGap hL.1 (gibbs_probability hL.2.1) hrig).symm
  driver := fun t ω => B t (f ω)
  noiseLaw := P'
  brownian := isEuclideanBrownian_comp_measurePreserving hf (isStdBrownian_iff.mp hL.2.2.1)

/-- The trivial data in dimension zero (a padding of the natural index). -/
noncomputable def padData (P' : Measure Ω') [IsProbabilityMeasure P'] : SpectralInformationLowerData Ω' 0 where
  potential := fun _ => 0
  smooth := contDiff_const
  rate := 1
  rate_pos := one_pos
  hessian := fun x z => by
    have : z = 0 := Subsingleton.elim _ _
    subst this
    simp
  probability := by
    have := volume_rd_zero
    simpa [gibbsMeasure] using this
  spectral := fun h => absurd h (lt_irrefl 0)
  driver := fun _ _ => 0
  noiseLaw := P'
  brownian := ⟨fun i => i.elim0, iIndepFun.of_subsingleton⟩

/-- The library kernel of the pulled-back data is the law of the original solution. -/
theorem lpData_kernel {V : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω}
    {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d} (hL : CutCur.IsLangevin V B P X)
    (hrig : CutCur.RigidCurvature V) {P' : Measure Ω'} {f : Ω' → Ω}
    (hf : MeasurePreserving f P' P) (t : ℝ≥0) (x : CutCur.Rd d) :
    langevinKernel (lpData hL hrig hf).potential (lpData hL hrig hf).driver
      (lpData hL hrig hf).noiseLaw t x = P.map (X x t) := by
  have hB : IsEuclideanBrownian B P := isStdBrownian_iff.mp hL.2.2.1
  have hB' : IsEuclideanBrownian (fun t ω => B t (f ω)) P' :=
    isEuclideanBrownian_comp_measurePreserving hf hB
  have hrate := hrig.1.le
  change langevinKernel V (fun t ω => B t (f ω)) P' t x = _
  rw [IsLangevin.map_eq_langevinKernel hL _ hrate hrig.2 x t,
    langevinKernel_apply_noiseLaw hB' hL.1 _ hrate hrig.2,
    langevinKernel_apply_noiseLaw hB hL.1 _ hrate hrig.2]
  rw [brownianNoiseLaw_comp hf hB]

end Data

/-! ### One common space for a rigid sequence -/

universe u

theorem exists_seqData {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] {V : ∀ n, CutCur.Rd n → ℝ}
    {B : ∀ n, ℝ≥0 → Ω n → CutCur.Rd n} {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, CutCur.Rd n → ℝ≥0 → Ω n → CutCur.Rd n}
    (hL : ∀ n, 0 < n → CutCur.IsLangevin (V n) (B n) (P n) (X n) ∧ CutCur.RigidCurvature (V n)) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (D : ∀ n : ℕ, SpectralInformationLowerData Ω' n),
      ∀ n, 0 < n → (D n).rate = CutCur.spectralGap (V n) ∧ (D n).potential = V n ∧
        ∀ (t : ℝ≥0) (x : CutCur.Rd n), langevinKernel (D n).potential (D n).driver
          (D n).noiseLaw t x = (P n).map (X n x t) := by
  classical
  have hprob : ∀ m : ℕ, IsProbabilityMeasure (P (m + 1)) := fun m =>
    (isStdBrownian_iff.mp (hL (m + 1) (Nat.succ_pos m)).1.2.2.1).isProbabilityMeasure
  let P' : Measure (∀ m : ℕ, Ω (m + 1)) := Measure.infinitePi fun m => P (m + 1)
  have : IsProbabilityMeasure P' := inferInstance
  refine ⟨∀ m : ℕ, Ω (m + 1), inferInstance, fun n =>
    match n with
    | 0 => padData P'
    | m + 1 => lpData (hL (m + 1) (Nat.succ_pos m)).1 (hL (m + 1) (Nat.succ_pos m)).2
        (measurePreserving_eval_infinitePi (fun m => P (m + 1)) m), ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact ⟨rfl, rfl, fun t x => lpData_kernel _ _ _ t x⟩

/-- The common-space data of a rigid sequence, with the transfer of the standing spectral
assumptions: the rates agree eventually with the gaps, `liminf > 0`, and the critical times
agree. -/
theorem exists_seqData_rigid {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    {V : ∀ n, CutCur.Rd n → ℝ} {B : ∀ n, ℝ≥0 → Ω n → CutCur.Rd n} {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, CutCur.Rd n → ℝ≥0 → Ω n → CutCur.Rd n}
    (h : CutCur.IsRigidSequence V B P X) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (D : ∀ n : ℕ, SpectralInformationLowerData Ω' n),
      (∀ n, 0 < n → (D n).rate = CutCur.spectralGap (V n) ∧ (D n).potential = V n ∧
        ∀ (t : ℝ≥0) (x : CutCur.Rd n), langevinKernel (D n).potential (D n).driver
          (D n).noiseLaw t x = (P n).map (X n x t)) ∧
      0 < Filter.liminf (fun n => ENNReal.ofReal (D n).rate) Filter.atTop ∧
      (∀ n, 0 < n → CutCur.criticalTime n (CutCur.spectralGap (V n)) =
        criticalTime n (D n).rate) ∧
      ((fun n => CutCur.spectralGap (V n)) =o[Filter.atTop] (fun n : ℕ => Real.log n) →
        (fun n => (D n).rate) =o[Filter.atTop] (fun n : ℕ => Real.log n)) := by
  obtain ⟨hL, hlim⟩ := h
  obtain ⟨Ω', _, D, hD⟩ := exists_seqData hL
  have hev : ∀ᶠ n : ℕ in Filter.atTop, 0 < n := Filter.eventually_gt_atTop 0
  have hrateEv : (fun n => (D n).rate) =ᶠ[Filter.atTop] fun n => CutCur.spectralGap (V n) := by
    filter_upwards [hev] with n hn using (hD n hn).1
  refine ⟨Ω', inferInstance, D, hD, ?_, ?_, fun hs => hs.congr' hrateEv.symm Filter.EventuallyEq.rfl⟩
  · have := Filter.liminf_congr (f := Filter.atTop) (u := fun n => ENNReal.ofReal (D n).rate)
      (v := fun n => ENNReal.ofReal (CutCur.spectralGap (V n)))
      (by filter_upwards [hrateEv] with n hn using by rw [hn])
    rwa [this]
  · intro n hn
    rw [(hD n hn).1]
    rfl

end CutoffRigidity.Paper
