module

public import CutoffRigidity.Extra.Dissip4
public import CutoffRigidity.Extra.DissipEq1
public import CutoffRigidity.Extra.DissipEq4

/-! # Integrated de Bruijn identity with equality, for arbitrary initial laws

For the Euclidean Langevin semigroup `Pt` of a smooth potential `V` with `Hess V ≥ ρ > 0`, an
initial probability law `ν` with `H(ν P_a | μ) < ∞` for some `a < s`, and `0 < s < t`:
`∫_s^t I(ν P_r | μ) dr + H(ν P_t | μ) = H(ν P_s | μ)`; and the Dirac corollary.
-/

public section

set_option backward.isDefEq.respectTransparency false

namespace CutoffRigidity.DissipEq

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal Topology
open CutoffRigidity CutoffRigidity.Dissip

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Carrier level: the reverse inequality `H(μ_s) ≤ ∫_s^t I + H(μ_t)`. -/
theorem langevin_dissipation_le {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] (hfin : klDiv ν (CutCur.gibbs V) ≠ ⊤)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    klDiv (lawAt (B := B) (P := P) V ν s) (CutCur.gibbs V) ≤
      (∫⁻ r in Ioc s t, CutCur.fisherInfo V (lawAt (B := B) (P := P) V ν r)) +
        klDiv (lawAt (B := B) (P := P) V ν t) (CutCur.gibbs V) := by
  have hmk : ∀ r : ℝ≥0, IsMarkovKernel (langevinKernel V B P r) := fun r =>
    langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess r
  set μ := gibbsMeasure volume V with hμ
  have h0 := lawAt_zero (B := B) (P := P) hB hV ρ hρ.le hHess ν
  have hHfin : ∀ r : ℝ, 0 ≤ r → klDiv (lawAt (B := B) (P := P) V ν r) μ ≠ ⊤ := by
    intro r hr
    rcases hr.eq_or_lt with h | h
    · rw [← h, h0]; exact hfin
    · have := drop_ennreal hB hV hp ρ hρ hHess ν (le_refl (0:ℝ)) h
      rw [h0] at this
      exact ne_top_of_le_ne_top hfin (le_trans le_self_add this)
  have hIfin : ∀ r : ℝ, 0 < r → CutCur.fisherInfo V (lawAt (B := B) (P := P) V ν r) ≠ ⊤ := by
    intro r hr h
    have := drop_ennreal hB hV hp ρ hρ hHess ν (le_refl (0:ℝ)) hr
    rw [h0, h, sub_zero, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hr).ne', add_top] at this
    exact hfin (top_le_iff.mp this)
  set H : ℝ → ℝ := fun r => (klDiv (lawAt (B := B) (P := P) V ν r) μ).toReal with hH
  set I : ℝ → ℝ := fun r => (CutCur.fisherInfo V (lawAt (B := B) (P := P) V ν r)).toReal with hI
  have hanti : AntitoneOn I (Ici s) := by
    intro a ha b hb hab
    have ha' : (0:ℝ) < a := lt_of_lt_of_le hs ha
    have hb' : (0:ℝ) < b := lt_of_lt_of_le hs hb
    let := hmk a.toNNReal
    let := hmk b.toNNReal
    have e1 := fisherInfo_eq_relativeFisherInformation hV hp ρ hρ hHess
      (lawAt (B := B) (P := P) V ν a)
    have e2 := fisherInfo_eq_relativeFisherInformation hV hp ρ hρ hHess
      (lawAt (B := B) (P := P) V ν b)
    have := relativeFisherInformation_langevinKernel_antitone hB hV hp ρ hρ hHess ν
      a.toNNReal b.toNNReal (Real.toNNReal_mono hab)
    show (CutCur.fisherInfo V (lawAt (B := B) (P := P) V ν b)).toReal ≤
      (CutCur.fisherInfo V (lawAt (B := B) (P := P) V ν a)).toReal
    refine ENNReal.toReal_mono (hIfin a ha') ?_
    rw [e1, e2]
    exact this
  have hrd : ∀ r u : ℝ, s ≤ r → 0 < u → H r ≤ H (r + u) + u * I r := by
    intro r u hr hu
    have hr0 : 0 < r := lt_of_lt_of_le hs hr
    let := hmk r.toNNReal
    have : IsProbabilityMeasure (lawAt (B := B) (P := P) V ν r) := inferInstance
    have h := reverse_drop hB hV hp ρ hρ hHess (lawAt (B := B) (P := P) V ν r)
      (hHfin r hr0.le) (hIfin r hr0) hu
    have hc : lawAt (B := B) (P := P) V (lawAt (B := B) (P := P) V ν r) u =
        lawAt (B := B) (P := P) V ν (r + u) := by
      show langevinKernel V B P u.toNNReal ∘ₘ (langevinKernel V B P r.toNNReal ∘ₘ ν) =
        langevinKernel V B P (r + u).toNNReal ∘ₘ ν
      rw [Measure.comp_assoc, langevinKernel_comp hB hV ρ hρ.le hHess, ← Real.toNNReal_add
        hr0.le hu.le]
    rw [hc] at h
    have hfin' := hHfin (r + u) (by linarith)
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin',
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hIfin r hr0)⟩) h
    rw [ENNReal.toReal_add hfin' (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hIfin r hr0)),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hu.le] at h2
    exact h2
  have hnn : ∀ r, s ≤ r → 0 ≤ I r := fun r _ => ENNReal.toReal_nonneg
  have hreal := sub_le_integral_of_rdrop hrd hanti hnn hst
  have hint : IntervalIntegrable I volume s t :=
    (hanti.mono (by
      intro r hr
      rw [uIcc_of_le hst.le] at hr
      exact hr.1)).intervalIntegrable
  have hint' : IntegrableOn I (Ioc s t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hst.le).mp hint
  have hnn' : ∀ r ∈ Ioc s t, 0 ≤ I r := fun r _ => ENNReal.toReal_nonneg
  have hlint : ∫⁻ r in Ioc s t, CutCur.fisherInfo V (lawAt (B := B) (P := P) V ν r) =
      ENNReal.ofReal (∫ r in s..t, I r) := by
    rw [intervalIntegral.integral_of_le hst.le,
      ofReal_integral_eq_lintegral_ofReal hint'
        ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hnn'))]
    refine setLIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
    exact (ENNReal.ofReal_toReal (hIfin r (hs.trans hr.1))).symm
  rw [hlint]
  show klDiv (lawAt (B := B) (P := P) V ν s) μ ≤ ENNReal.ofReal (∫ r in s..t, I r) +
    klDiv (lawAt (B := B) (P := P) V ν t) μ
  have hfs := hHfin s hs.le
  have hft := hHfin t (hs.trans hst).le
  have hIn : 0 ≤ ∫ r in s..t, I r :=
    intervalIntegral.integral_nonneg hst.le fun r _ => ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_toReal hft, ← ENNReal.ofReal_toReal hfs,
    ← ENNReal.ofReal_add hIn ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal (by simp only [hH] at hreal ⊢; linarith)

/-- **Integrated de Bruijn identity (equality), carrier level.** -/
theorem langevin_dissipation_eq {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] (hfin : klDiv ν (CutCur.gibbs V) ≠ ⊤)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    (∫⁻ r in Ioc s t, CutCur.fisherInfo V (lawAt (B := B) (P := P) V ν r)) +
        klDiv (lawAt (B := B) (P := P) V ν t) (CutCur.gibbs V) =
      klDiv (lawAt (B := B) (P := P) V ν s) (CutCur.gibbs V) :=
  le_antisymm (langevin_dissipation_ge hB hV hp ρ hρ hHess ν hfin hs hst)
    (langevin_dissipation_le hB hV hp ρ hρ hHess ν hfin hs hst)


private theorem hess_nonneg'' {d : ℕ} {V : CutCur.Rd d → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x z : CutCur.Rd d) : 0 ≤ fderiv ℝ (fderiv ℝ V) x z z :=
  le_trans (by positivity) (hHess x z)

/-- **Integrated de Bruijn identity, kernel form, finite entropy of `ν`.** -/
theorem langevin_dissipation_eq_K {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)} (hL : CutCur.IsEuclideanLangevinInf V Pt)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν]
    (hfin : klDiv ν (CutCur.gibbs V) ≠ ⊤) {s t : ℝ≥0} (hs : 0 < s) (hst : s < t) :
    (∫⁻ r in Ioc (s : ℝ) t, CutCur.fisherInfo V (ν.bind (Pt r.toNNReal))) +
        klDiv (ν.bind (Pt t)) (CutCur.gibbs V) =
      klDiv (ν.bind (Pt s)) (CutCur.gibbs V) := by
  obtain ⟨Ω, _, B, P, X, -, hLang, key⟩ :=
    CutCur.exists_isLangevin_of_isEuclideanLangevin hL (hess_nonneg'' hρ hHess)
  have hb : ∀ u : ℝ≥0, (fun x => P.map (X x u)) = ⇑(Pt u) := fun u => funext fun x => key u x
  have hB := Paper.isStdBrownian_iff.mp hLang.2.2.1
  have hbind : ∀ u : ℝ≥0, ν.bind (Pt u) = langevinKernel V B P u ∘ₘ ν := fun u => by
    rw [← Paper.law_bind_eq_comp hLang hρ.le hHess ν u, hb]
  have hbind' : ∀ r : ℝ, ν.bind (Pt r.toNNReal) = lawAt (B := B) (P := P) V ν r :=
    fun r => hbind _
  simp only [hbind', hbind]
  have h := langevin_dissipation_eq hB hLang.1 hLang.2.1 ρ hρ hHess ν hfin
    (NNReal.coe_pos.mpr hs) (NNReal.coe_lt_coe.mpr hst)
  simpa only [lawAt, Real.toNNReal_coe] using h

/-- **Integrated de Bruijn identity (equality), kernel form, finite entropy at an earlier time
`a < s`.** For `0 < s < t`:
`∫_s^t I(ν P_r | μ) dr + H(ν P_t | μ) = H(ν P_s | μ)`. -/
theorem langevin_dissipation_eq_K' {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)} (hL : CutCur.IsEuclideanLangevinInf V Pt)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν] {a s t : ℝ≥0}
    (hfin : klDiv (ν.bind (Pt a)) (CutCur.gibbs V) ≠ ⊤) (has : a < s) (hst : s < t) :
    (∫⁻ r in Ioc (s : ℝ) t, CutCur.fisherInfo V (ν.bind (Pt r.toNNReal))) +
        klDiv (ν.bind (Pt t)) (CutCur.gibbs V) =
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
  have h := langevin_dissipation_eq_K hL hρ hHess (ν.bind (Pt a)) hfin hpos
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

/-- **Integrated de Bruijn identity (equality) for a Dirac initial law**: for every `x₀` and
`0 < s < t`, `∫_s^t I(P_r(x₀,·)|μ) dr + H(P_t(x₀,·)|μ) = H(P_s(x₀,·)|μ)`. -/
theorem langevin_dissipation_eq_dirac_K {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)} (hL : CutCur.IsEuclideanLangevinInf V Pt)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : CutCur.Rd d) {s t : ℝ≥0} (hs : 0 < s) (hst : s < t) :
    (∫⁻ r in Ioc (s : ℝ) t, CutCur.fisherInfo V (Pt r.toNNReal x₀)) +
        klDiv (Pt t x₀) (CutCur.gibbs V) = klDiv (Pt s x₀) (CutCur.gibbs V) := by
  obtain ⟨Ω, _, B, P, X, -, hLang, key⟩ :=
    CutCur.exists_isLangevin_of_isEuclideanLangevin hL (hess_nonneg'' hρ hHess)
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
  have h := langevin_dissipation_eq_K' hL hρ hHess (Measure.dirac x₀) hfin (half_lt_self hs) hst
  simpa only [hd] using h

end CutoffRigidity.DissipEq
