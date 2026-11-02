module

public import Mathlib
public import CutoffRigidity.Extra.Rothaus11

/-! # Rothaus remark (stage 12): the Rothaus alternative for abstract forms

If the optimal log-Sobolev constant of a form with the compactness property `Form.Compact` exceeds twice the optimal Poincaré
constant, then the log-Sobolev inequality has an extremal function: a nonconstant `f ∈ Q` with
`Ent(f²) = C_LSI · E(f)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace CutoffRigidity.Rothaus

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem integral_eq_zero_of_sq_tendsto [IsProbabilityMeasure μ] {g : ℕ → X → ℝ} {h : X → ℝ}
    (hg : ∀ n, MemLp (g n) 2 μ) (hh : MemLp h 2 μ) (h0 : ∀ n, ∫ x, g n x ∂μ = 0)
    (hc : Tendsto (fun n => ∫ x, (g n x - h x) ^ 2 ∂μ) atTop (𝓝 0)) : ∫ x, h x ∂μ = 0 := by
  have hsq : ∀ n, (∫ x, (g n x - h x) ∂μ) ^ 2 ≤ ∫ x, (g n x - h x) ^ 2 ∂μ := by
    intro n
    have hm : MemLp (fun x => g n x - h x) 2 μ := (hg n).sub hh
    have h1 := variance_nonneg (fun x => g n x - h x) μ
    rw [variance_eq_sub hm] at h1
    simp only [Pi.pow_apply] at h1
    linarith
  have h2 : ∀ n, ∫ x, (g n x - h x) ∂μ = -∫ x, h x ∂μ := by
    intro n
    rw [integral_sub ((hg n).integrable one_le_two) (hh.integrable one_le_two), h0 n]; ring
  simp_rw [h2] at hsq
  have h3 : (∫ x, h x ∂μ) ^ 2 ≤ 0 := by
    refine le_of_tendsto_of_tendsto' tendsto_const_nhds hc fun n => ?_
    simpa using hsq n
  nlinarith [sq_nonneg (∫ x, h x ∂μ)]

theorem variance_eq_of_mean_zero [IsProbabilityMeasure μ] {h : X → ℝ} (hh : MemLp h 2 μ) (h0 : ∫ x, h x ∂μ = 0) :
    variance h μ = ∫ x, h x ^ 2 ∂μ := by
  rw [variance_eq_sub hh, h0]; simp

/-- Auxiliary form of the Rothaus alternative, with the finiteness of the LSI constant as an explicit hypothesis. -/
theorem rothaus_alternative_aux [IsProbabilityMeasure μ] (F : Form μ)
    (hPI : ∃ P, 0 ≤ P ∧ ∀ f ∈ F.Q, variance f μ ≤ P * F.E f)
    (hLSI : ∃ c, 0 ≤ c ∧ ∀ f ∈ F.Q, CutCur.entropyOf μ (fun x => f x ^ 2) ≤ c * F.E f)
    (hcomp : F.Compact) (hgt : 2 * F.optPI < F.optLSI) :
    ∃ f ∈ F.Q, 0 < F.E f ∧ CutCur.entropyOf μ (fun x => f x ^ 2) = F.optLSI * F.E f := by
  set C := F.optLSI with hCdef
  set P := F.optPI with hPdef
  have hP0 : 0 ≤ P := F.optPI_nonneg
  have hC : 0 < C := by linarith
  obtain ⟨u, huQ, hent, hmean, hlow, hup⟩ := exists_normalized F hLSI hC
  set m : ℕ → ℝ := fun n => ∫ x, u n x ∂μ with hm
  set g : ℕ → X → ℝ := fun n x => u n x + -(m n) with hg
  have hgQ : ∀ n, g n ∈ F.Q := fun n => F.add_const_mem _ _ (huQ n)
  have hgm : ∀ n, ∫ x, g n x ∂μ = 0 := by
    intro n
    simp only [hg]
    rw [integral_add ((F.integrable_self (huQ n))) (integrable_const _)]
    simp [hm]
  have hgE : ∀ n, F.E (g n) = F.E (u n) := fun n => F.E_add_const _ _ (huQ n)
  have hgu : ∀ n x, g n x + m n = u n x := fun n x => by simp [hg]
  have hentg : ∀ n, CutCur.entropyOf μ (fun x => (g n x + m n) ^ 2) = 1 := by
    intro n
    have : (fun x => (g n x + m n) ^ 2) = fun x => u n x ^ 2 := funext fun x => by rw [hgu]
    rw [this, hent]
  have hB : ∀ n, F.E (g n) ≤ 2 / C := by
    intro n
    rw [hgE]
    refine (hup n).trans ?_
    have : 1 / (C * (n + 1)) ≤ 1 / C := by
      apply one_div_le_one_div_of_le hC
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have e : 2 / C = 1 / C + 1 / C := by ring
    linarith
  obtain ⟨φ, hφ, h, hhQ, hL2, hΘ, hlsc⟩ := hcomp (2 / C) g hgQ hgm hB
  have hh0 : ∫ x, h x ∂μ = 0 :=
    integral_eq_zero_of_sq_tendsto (g := fun n => g (φ n)) (fun n => F.memLp _ (hgQ _)) (F.memLp _ hhQ)
      (fun n => hgm _) hL2
  have hEh : F.E h ≤ 1 / C := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    refine hlsc _ ?_
    have h1 : Tendsto (fun n : ℕ => 1 / (C * ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 / C)
      simp only [mul_zero] at this
      refine this.congr fun n => ?_
      field_simp
    have h2 := (h1.comp hφ.tendsto_atTop).eventually (gt_mem_nhds hε)
    filter_upwards [h2] with n hn
    rw [hgE]
    have := hup (φ n)
    simp only [Function.comp_apply] at hn
    linarith
  by_cases hT : Tendsto (fun n => m (φ n)) atTop atTop
  · exfalso
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hT.eventually_ge_atTop 1)
    have hshift : Tendsto (fun n : ℕ => n + N) atTop atTop := tendsto_add_atTop_nat N
    have key := caseB F (g := fun n => g (φ (n + N))) (h := h) (m := fun n => m (φ (n + N)))
      (fun n => hgQ _) hhQ (fun n => hN _ (by omega)) (hT.comp hshift) (hL2.comp hshift) (hΘ.comp hshift)
      (fun n => hentg _)
    have hv := F.pi_spec hPI hhQ
    rw [variance_eq_of_mean_zero (F.memLp _ hhQ) hh0] at hv
    have h3 : P * F.E h ≤ P * (1 / C) := mul_le_mul_of_nonneg_left hEh hP0
    have h4 : 1 ≤ 2 * (P * (1 / C)) := by nlinarith
    rw [mul_one_div, ← mul_div_assoc, le_div_iff₀ hC] at h4
    linarith
  · rw [tendsto_atTop] at hT
    push Not at hT
    obtain ⟨K, hK⟩ := hT
    obtain ⟨ψ, hψ, hψK⟩ := Filter.extraction_of_frequently_atTop hK
    have hmem : ∀ n, m (φ (ψ n)) ∈ Set.Icc (0 : ℝ) K := fun n => ⟨hmean _, (hψK n).le⟩
    obtain ⟨m₀, -, ρ, hρ, hρt⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc 0 K) hmem
    have hθ : StrictMono (fun n => φ (ψ (ρ n))) := hφ.comp (hψ.comp hρ)
    have hθt : Tendsto (fun n => φ (ψ (ρ n))) atTop atTop := hθ.tendsto_atTop
    have key := caseA F (g := fun n => g (φ (ψ (ρ n)))) (h := h) (m := fun n => m (φ (ψ (ρ n)))) (m₀ := m₀)
      (fun n => hgQ _) hhQ hρt (hL2.comp (hψ.comp hρ).tendsto_atTop) (hΘ.comp (hψ.comp hρ).tendsto_atTop)
      (fun n => hentg _)
    have hfQ : (fun x => h x + m₀) ∈ F.Q := F.add_const_mem _ _ hhQ
    have hfE : F.E (fun x => h x + m₀) = F.E h := F.E_add_const _ _ hhQ
    have hls := F.lsi_spec hLSI hfQ
    rw [key, hfE] at hls
    have hup' : C * F.E h ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hEh hC.le
      have e : C * (1 / C) = 1 := by field_simp
      rwa [e] at this
    refine ⟨fun x => h x + m₀, hfQ, ?_, ?_⟩
    · rw [hfE]
      by_contra hneg
      have h0 : F.E h = 0 := le_antisymm (not_lt.1 hneg) (F.E_nonneg h hhQ)
      rw [h0] at hls
      norm_num at hls
    · rw [key, hfE]
      linarith

/-- **Rothaus alternative (abstract form).** If the form `(Q, E)` satisfies a Poincaré inequality and the compactness
property `Form.Compact`, and the optimal log-Sobolev constant is strictly larger than twice the optimal Poincaré constant,
then there is an extremal function for the log-Sobolev inequality: a nonconstant `f ∈ Q` (`0 < E f`) with
`Ent(f²) = C_LSI · E(f)`. (Finiteness of `C_LSI` is automatic from `2 C_PI < C_LSI`, since `sInf ∅ = 0`.) -/
theorem rothaus_alternative [IsProbabilityMeasure μ] (F : Form μ)
    (hPI : ∃ P, 0 ≤ P ∧ ∀ f ∈ F.Q, variance f μ ≤ P * F.E f)
    (hcomp : F.Compact) (hgt : 2 * F.optPI < F.optLSI) :
    ∃ f ∈ F.Q, 0 < F.E f ∧ CutCur.entropyOf μ (fun x => f x ^ 2) = F.optLSI * F.E f := by
  refine rothaus_alternative_aux F hPI ?_ hcomp hgt
  by_contra hne
  have hempty : {C : ℝ | 0 ≤ C ∧ ∀ f ∈ F.Q, CutCur.entropyOf μ (fun x => f x ^ 2) ≤ C * F.E f} = ∅ := by
    exact Set.eq_empty_of_forall_notMem fun c hc => hne ⟨c, hc⟩
  have : F.optLSI = 0 := by
    unfold Form.optLSI; rw [hempty, Real.sInf_empty]
  linarith [F.optPI_nonneg]

end CutoffRigidity.Rothaus
