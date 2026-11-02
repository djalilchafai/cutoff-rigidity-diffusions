module

public import CutoffRigidity.Extra.C2Uniq8
public import CutoffRigidity.Extra.Dissip4

/-! # `C²` versions of the integrated de Bruijn statements (kernel form) -/

public section

set_option backward.isDefEq.respectTransparency false

namespace CutoffRigidity.Dissip

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal Topology

private theorem hess_nonneg' {d : ℕ} {V : CutCur.Rd d → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x z : CutCur.Rd d) : 0 ≤ fderiv ℝ (fderiv ℝ V) x z z :=
  le_trans (by positivity) (hHess x z)

/-- **Integrated de Bruijn inequality, kernel form, arbitrary initial law of finite entropy.** -/
theorem langevin_dissipation_ge_C2 {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)} (hL : CutCur.C2U.IsEucLangevin2 V Pt)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν]
    (hfin : klDiv ν (CutCur.gibbs V) ≠ ⊤) {s t : ℝ≥0} (hs : 0 < s) (hst : s < t) :
    (∫⁻ r in Ioc (s : ℝ) t, CutCur.fisherInfo V (ν.bind (Pt r.toNNReal))) +
        klDiv (ν.bind (Pt t)) (CutCur.gibbs V) ≤
      klDiv (ν.bind (Pt s)) (CutCur.gibbs V) := by
  obtain ⟨Ω, _, B, P, X, -, hLang, key⟩ :=
    CutCur.C2U.exists_isLangevin_of_C2 hL (hess_nonneg' hρ hHess)
  have hb : ∀ u : ℝ≥0, (fun x => P.map (X x u)) = ⇑(Pt u) := fun u => funext fun x => key u x
  have hB := Paper.isStdBrownian_iff.mp hLang.2.2.1
  have hbind : ∀ u : ℝ≥0, ν.bind (Pt u) = langevinKernel V B P u ∘ₘ ν := fun u => by
    rw [← Paper.law_bind_eq_comp hLang hρ.le hHess ν u, hb]
  have hbind' : ∀ r : ℝ, ν.bind (Pt r.toNNReal) = lawAt (B := B) (P := P) V ν r :=
    fun r => hbind _
  simp only [hbind', hbind]
  have h := langevin_dissipation_ge hB hLang.1 hLang.2.1 ρ hρ hHess ν hfin
    (NNReal.coe_pos.mpr hs) (NNReal.coe_lt_coe.mpr hst)
  simpa only [lawAt, Real.toNNReal_coe] using h

/-- **Full integrated de Bruijn identity, kernel form, compact-perturbation initial densities.** -/
theorem langevin_dissipation_core_C2 {d : ℕ} {V g : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)} (hL : CutCur.C2U.IsEucLangevin2 V Pt)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (hNorm : ∫ x, c + g x ∂CutCur.gibbs V = 1) {s t : ℝ≥0} (hst : s < t) :
    klDiv (((CutCur.gibbs V).withDensity (fun x => ENNReal.ofReal (c + g x))).bind (Pt s))
        (CutCur.gibbs V) =
      klDiv (((CutCur.gibbs V).withDensity (fun x => ENNReal.ofReal (c + g x))).bind (Pt t))
        (CutCur.gibbs V) +
      ∫⁻ r in Ioc (s : ℝ) t, CutCur.fisherInfo V
        (((CutCur.gibbs V).withDensity (fun x => ENNReal.ofReal (c + g x))).bind (Pt r.toNNReal)) := by
  obtain ⟨Ω, _, B, P, X, -, hLang, key⟩ :=
    CutCur.C2U.exists_isLangevin_of_C2 hL (hess_nonneg' hρ hHess)
  have hb : ∀ u : ℝ≥0, (fun x => P.map (X x u)) = ⇑(Pt u) := fun u => funext fun x => key u x
  have hB := Paper.isStdBrownian_iff.mp hLang.2.2.1
  set ν := (CutCur.gibbs V).withDensity (fun x => ENNReal.ofReal (c + g x)) with hν
  have hbind : ∀ u : ℝ≥0, ν.bind (Pt u) = langevinKernel V B P u ∘ₘ ν := fun u => by
    rw [← Paper.law_bind_eq_comp hLang hρ.le hHess ν u, hb]
  have hbind' : ∀ r : ℝ, ν.bind (Pt r.toNNReal) = lawAt (B := B) (P := P) V ν r :=
    fun r => hbind _
  simp only [hbind', hbind]
  have h := langevin_dissipation_core hB hLang.1 hLang.2.1 ρ hρ hHess hg hgc c m hm hpos hNorm
    (NNReal.coe_nonneg s) (NNReal.coe_lt_coe.mpr hst)
  simp only [lawAt, Real.toNNReal_coe] at h
  exact h

/-- **Integrated de Bruijn inequality, kernel form, finite entropy at an earlier time `a < s`.** -/
theorem langevin_dissipation_ge_C2' {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)} (hL : CutCur.C2U.IsEucLangevin2 V Pt)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν] {a s t : ℝ≥0}
    (hfin : klDiv (ν.bind (Pt a)) (CutCur.gibbs V) ≠ ⊤) (has : a < s) (hst : s < t) :
    (∫⁻ r in Ioc (s : ℝ) t, CutCur.fisherInfo V (ν.bind (Pt r.toNNReal))) +
        klDiv (ν.bind (Pt t)) (CutCur.gibbs V) ≤
      klDiv (ν.bind (Pt s)) (CutCur.gibbs V) := by
  have _hM : ∀ t, IsMarkovKernel (Pt t) := hL.2.2.1
  have hsg : ∀ s t, Pt (s + t) = Pt t ∘ₖ Pt s := hL.2.2.2.1
  have hcomp : ∀ (u v : ℝ≥0), ν.bind (Pt (u + v)) = (ν.bind (Pt u)).bind (Pt v) := fun u v => by
    show (Pt (u + v)) ∘ₘ ν = (Pt v) ∘ₘ ((Pt u) ∘ₘ ν)
    rw [Measure.comp_assoc, hsg]
  have : IsProbabilityMeasure (ν.bind (Pt a)) := by
    show IsProbabilityMeasure ((Pt a) ∘ₘ ν)
    infer_instance
  have hpos : 0 < s - a := tsub_pos_of_lt has
  have h := langevin_dissipation_ge_C2 hL hρ hHess (ν.bind (Pt a)) hfin hpos
    (tsub_lt_tsub_right_of_le has.le hst)
  have hat : ∀ u : ℝ≥0, a ≤ u → ν.bind (Pt u) = (ν.bind (Pt a)).bind (Pt (u - a)) := fun u hu => by
    rw [← hcomp, add_tsub_cancel_of_le hu]
  rw [← hat t (has.le.trans hst.le), ← hat s has.le] at h
  have hI : ∫⁻ r in Ioc (s : ℝ) t, CutCur.fisherInfo V (ν.bind (Pt r.toNNReal)) =
      ∫⁻ r in Ioc ((s - a : ℝ≥0) : ℝ) ((t - a : ℝ≥0) : ℝ),
        CutCur.fisherInfo V ((ν.bind (Pt a)).bind (Pt r.toNNReal)) := by
    have hpre : (fun x : ℝ => x - (a : ℝ)) ⁻¹' Ioc ((s - a : ℝ≥0) : ℝ) ((t - a : ℝ≥0) : ℝ) =
        Ioc (s : ℝ) t := by
      ext x
      have h1 : (a : ℝ) ≤ s := NNReal.coe_le_coe.mpr has.le
      have h2 : (a : ℝ) ≤ t := NNReal.coe_le_coe.mpr (has.le.trans hst.le)
      simp only [mem_preimage, mem_Ioc, NNReal.coe_sub has.le, NNReal.coe_sub (has.le.trans hst.le)]
      constructor <;> rintro ⟨u, v⟩ <;> constructor <;> linarith
    rw [← (measurePreserving_sub_right (volume : Measure ℝ) (a : ℝ)).setLIntegral_comp_preimage_emb
      (measurableEmbedding_subRight (a : ℝ))
      (fun r => CutCur.fisherInfo V ((ν.bind (Pt a)).bind (Pt r.toNNReal))), hpre]
    refine setLIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    have hra : (a : ℝ) ≤ r := le_trans (NNReal.coe_le_coe.mpr has.le) hr.1.le
    have : r.toNNReal = a + (r - a).toNNReal := by
      apply NNReal.eq
      simp [Real.coe_toNNReal _ (sub_nonneg.mpr hra), Real.coe_toNNReal _ (hra.trans' a.2)]
    rw [this, hcomp]
  rw [hI]
  exact h

/-- **Integrated de Bruijn inequality for a Dirac initial law**: for every `x₀` and `0 < s < t`,
`∫_s^t I(P_r(x₀,·)|μ) dr + H(P_t(x₀,·)|μ) ≤ H(P_s(x₀,·)|μ)`. -/
theorem langevin_dissipation_dirac_C2 {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)} (hL : CutCur.C2U.IsEucLangevin2 V Pt)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : CutCur.Rd d) {s t : ℝ≥0} (hs : 0 < s) (hst : s < t) :
    (∫⁻ r in Ioc (s : ℝ) t, CutCur.fisherInfo V (Pt r.toNNReal x₀)) +
        klDiv (Pt t x₀) (CutCur.gibbs V) ≤ klDiv (Pt s x₀) (CutCur.gibbs V) := by
  obtain ⟨Ω, _, B, P, X, -, hLang, key⟩ :=
    CutCur.C2U.exists_isLangevin_of_C2 hL (fun x z => le_trans (by positivity) (hHess x z))
  have hb : ∀ u : ℝ≥0, (fun x => P.map (X x u)) = ⇑(Pt u) := fun u => funext fun x => key u x
  have hB := Paper.isStdBrownian_iff.mp hLang.2.2.1
  have hK : ∀ u : ℝ≥0, Pt u = langevinKernel V B P u := fun u => by
    ext x : 1
    have h1 := Paper.law_bind_eq_comp hLang hρ.le hHess (Measure.dirac x) u
    rw [hb u] at h1
    rw [Measure.dirac_bind (langevinKernel V B P u).measurable] at h1
    rwa [show (⇑(Pt u) ∘ₘ Measure.dirac x) = Pt u x from
      Measure.dirac_bind (Pt u).measurable x] at h1
  have hd : ∀ (u : ℝ≥0), (Measure.dirac x₀).bind (Pt u) = Pt u x₀ := fun u =>
    Measure.dirac_bind (Pt u).measurable x₀
  have hfin : klDiv ((Measure.dirac x₀).bind (Pt (s / 2))) (CutCur.gibbs V) ≠ ⊤ := by
    rw [hd]
    have hT : (0 : ℝ) < ((s / 2 : ℝ≥0) : ℝ) := by
      exact_mod_cast (half_pos hs)
    have := klDiv_langevinKernel_ne_top hB hLang.1 hLang.2.1 ρ hρ hHess x₀ _ hT
    rwa [Real.toNNReal_coe, ← hK] at this
  have h := langevin_dissipation_ge_C2' hL hρ hHess (Measure.dirac x₀) hfin (half_lt_self hs) hst
  simpa only [hd] using h

end CutoffRigidity.Dissip
