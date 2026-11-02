module

public import CutoffRigidity.Extra.GaussIso8

/-! # Tensorisation (stage 5a): Minkowski, Fubini for `Fin (n+1) → ℝ`, coordinate-wise `C¹` class -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology

set_option linter.unusedSectionVars false

namespace CutoffRigidity.GaussIso

/-- The standard Gaussian on `ℝⁿ` as a product measure. -/
noncomputable abbrev γn (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi fun _ => γ1

/-- **Minkowski's inequality** for a finite family: `√(∑ (∫ vᵢ)²) ≤ ∫ √(∑ vᵢ²)`. -/
lemma minkowski {ι : Type*} [Fintype ι] {ν : Measure ℝ} [IsProbabilityMeasure ν] (v : ι → ℝ → ℝ)
    (hv : ∀ i, Integrable (v i) ν) (hS : Integrable (fun t => Real.sqrt (∑ i, v i t ^ 2)) ν) :
    Real.sqrt (∑ i, (∫ t, v i t ∂ν) ^ 2) ≤ ∫ t, Real.sqrt (∑ i, v i t ^ 2) ∂ν := by
  set a : ι → ℝ := fun i => ∫ t, v i t ∂ν with ha
  set A := Real.sqrt (∑ i, a i ^ 2) with hA
  have hR : 0 ≤ ∫ t, Real.sqrt (∑ i, v i t ^ 2) ∂ν := integral_nonneg fun t => Real.sqrt_nonneg _
  rcases (Real.sqrt_nonneg (∑ i, a i ^ 2)).eq_or_lt with h0 | hpos
  · have : A = 0 := h0.symm
    rw [this]; exact hR
  have hA2 : A ^ 2 = ∑ i, a i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have h1 : ∑ i, a i ^ 2 = ∫ t, ∑ i, a i * v i t ∂ν := by
    rw [integral_finsetSum _ (fun i _ => (hv i).const_mul (a i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]; simp [ha, sq]
  have h2 : ∫ t, ∑ i, a i * v i t ∂ν ≤ ∫ t, A * Real.sqrt (∑ i, v i t ^ 2) ∂ν := by
    refine integral_mono (integrable_finsetSum _ fun i _ => (hv i).const_mul (a i)) (hS.const_mul A)
      fun t => ?_
    exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  rw [integral_const_mul] at h2
  have : A * A ≤ A * ∫ t, Real.sqrt (∑ i, v i t ^ 2) ∂ν := by
    nlinarith [h1, h2, hA2]
  exact le_of_mul_le_mul_left this hpos

/-- Fubini decomposition of the product Gaussian on `Fin (n+1) → ℝ`. -/
lemma integral_γn_succ {n : ℕ} {G : (Fin (n + 1) → ℝ) → ℝ}
    (hG : Integrable G (γn (n + 1))) :
    ∫ x, G x ∂(γn (n + 1)) = ∫ x', ∫ t, G (Fin.cons t x') ∂γ1 ∂(γn n) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hmp : MeasurePreserving e (γn (n + 1)) (γ1.prod (γn n)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => γ1) 0
  have hint : Integrable (fun p => G (e.symm p)) (γ1.prod (γn n)) := by
    have := (hmp.symm e).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) |>.2 hG
    exact this
  have h1 := hmp.integral_comp' (fun p => G (e.symm p))
  simp only [MeasurableEquiv.symm_apply_apply] at h1
  rw [h1, integral_prod_symm _ hint]
  congr 1; funext x'; congr 1; funext t
  show G (e.symm (t, x')) = _
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  simp [Fin.insertNthEquiv]


/-- Coordinate-wise `C¹` data on `ℝⁿ`: `f` continuous with values in `[0,1]`, continuous bounded partial
derivatives `d i` (derivative of `s ↦ f (update x i s)`). -/
structure PC (n : ℕ) (f : (Fin n → ℝ) → ℝ) (d : Fin n → (Fin n → ℝ) → ℝ) : Prop where
  cont : Continuous f
  dcont : ∀ i, Continuous (d i)
  dbdd : ∀ i, ∃ C, ∀ x, |d i x| ≤ C
  hasDeriv : ∀ i x, HasDerivAt (fun s => f (Function.update x i s)) (d i x) (x i)
  rng : ∀ x, 0 ≤ f x ∧ f x ≤ 1

section marginal
variable {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ} {d : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ}
  (P : PC (n + 1) f d)
include P

lemma PC.cons_cont (x' : Fin n → ℝ) : Continuous (fun t : ℝ => (Fin.cons t x' : Fin (n + 1) → ℝ)) := by
  refine continuous_pi fun i => ?_
  induction i using Fin.cases with
  | zero => simp only [Fin.cons_zero]; exact continuous_id
  | succ j => simpa using continuous_const

lemma PC.cons_cont' (t : ℝ) : Continuous (fun x' : Fin n → ℝ => (Fin.cons t x' : Fin (n + 1) → ℝ)) := by
  refine continuous_pi fun i => ?_
  induction i using Fin.cases with
  | zero => simpa using continuous_const
  | succ j => simpa using continuous_apply j

lemma PC.cons_cont2 : Continuous (fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ)) := by
  refine continuous_pi fun i => ?_
  induction i using Fin.cases with
  | zero => simpa using continuous_fst
  | succ j => simp only [Fin.cons_succ]; exact (continuous_apply j).comp continuous_snd

lemma PC.slice_bc (x' : Fin n → ℝ) : BC (fun t => f (Fin.cons t x')) :=
  ⟨P.cont.comp (PC.cons_cont P x'), 1, fun t => by
    have := P.rng (Fin.cons t x'); rw [abs_of_nonneg this.1]; exact this.2⟩

lemma PC.slice_bc0 (x' : Fin n → ℝ) : BC (fun t => d 0 (Fin.cons t x')) := by
  obtain ⟨C, hC⟩ := P.dbdd 0
  exact ⟨(P.dcont 0).comp (PC.cons_cont P x'), C, fun t => hC _⟩

lemma PC.slice_deriv0 (x' : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun t => f (Fin.cons t x' : Fin (n + 1) → ℝ)) (d 0 (Fin.cons t x')) t := by
  have := P.hasDeriv 0 (Fin.cons t x')
  simp only [Fin.cons_zero] at this
  have e : (fun s => f (Function.update (Fin.cons t x' : Fin (n + 1) → ℝ) 0 s)) =
      fun s => f (Fin.cons s x') := funext fun s => by rw [Fin.update_cons_zero]
  rw [e] at this
  exact this


/-- Marginal: integrate out the first coordinate. -/
noncomputable def marg (f : (Fin (n + 1) → ℝ) → ℝ) (x' : Fin n → ℝ) : ℝ :=
  ∫ t, f (Fin.cons t x') ∂γ1

/-- Partial derivatives of the marginal. -/
noncomputable def margd (d : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ) (j : Fin n) (x' : Fin n → ℝ) : ℝ :=
  ∫ t, d j.succ (Fin.cons t x') ∂γ1

theorem PC.marginal : PC n (marg f) (margd d) := by
  have hint : ∀ x', Integrable (fun t => f (Fin.cons t x' : Fin (n + 1) → ℝ)) γ1 := fun x' =>
    (PC.slice_bc P x').integrable_g
  refine ⟨?_, fun j => ?_, fun j => ?_, fun j x' => ?_, fun x' => ?_⟩
  · unfold marg
    refine continuous_of_dominated (bound := fun _ => 1) (fun x' => ?_) (fun x' => ?_)
      (integrable_const 1) ?_
    · exact (P.cont.comp (PC.cons_cont P x')).aestronglyMeasurable
    · exact Eventually.of_forall fun t => by
        have := P.rng (Fin.cons t x'); rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2
    · exact Eventually.of_forall fun t => P.cont.comp (PC.cons_cont' P t)
  · obtain ⟨C, hC⟩ := P.dbdd j.succ
    unfold margd
    refine continuous_of_dominated (bound := fun _ => C) (fun x' => ?_) (fun x' => ?_)
      (integrable_const C) ?_
    · exact ((P.dcont j.succ).comp (PC.cons_cont P x')).aestronglyMeasurable
    · exact Eventually.of_forall fun t => by simpa using hC _
    · exact Eventually.of_forall fun t => (P.dcont j.succ).comp (PC.cons_cont' P t)
  · obtain ⟨C, hC⟩ := P.dbdd j.succ
    refine ⟨C, fun x' => ?_⟩
    unfold margd
    have := norm_integral_le_of_norm_le_const (μ := γ1) (f := fun t => d j.succ (Fin.cons t x')) (C := C)
      (Eventually.of_forall fun t => by simpa using hC _)
    simpa using this
  · obtain ⟨C, hC⟩ := P.dbdd j.succ
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ1) (𝕜 := ℝ)
      (F := fun s t => f (Fin.cons t (Function.update x' j s) : Fin (n + 1) → ℝ))
      (F' := fun s t => d j.succ (Fin.cons t (Function.update x' j s))) (x₀ := x' j)
      (s := univ) (bound := fun _ => C) Filter.univ_mem
      (Eventually.of_forall fun s => (P.cont.comp (PC.cons_cont P _)).aestronglyMeasurable)
      (hint _)
      (((P.dcont j.succ).comp (PC.cons_cont P _)).aestronglyMeasurable)
      (Eventually.of_forall fun t s _ => by simpa using hC _)
      (integrable_const C)
      (Eventually.of_forall fun t s _ => by
        have := P.hasDeriv j.succ (Fin.cons t (Function.update x' j s))
        simp only [Fin.cons_succ, Function.update_self] at this
        have e : (fun s' => f (Function.update (Fin.cons t (Function.update x' j s) : Fin (n + 1) → ℝ) j.succ s')) =
            fun s' => f (Fin.cons t (Function.update x' j s')) := by
          funext s'
          rw [← Fin.cons_update, Function.update_idem]
        rw [e] at this
        exact this)
    have h := key.2
    simp only [Function.update_eq_self] at h
    exact h
  · constructor
    · exact integral_nonneg fun t => (P.rng _).1
    · calc marg f x' ≤ ∫ t, (1:ℝ) ∂γ1 := integral_mono (hint x') (integrable_const 1) fun t => (P.rng _).2
        _ = 1 := by simp

end marginal
end CutoffRigidity.GaussIso
