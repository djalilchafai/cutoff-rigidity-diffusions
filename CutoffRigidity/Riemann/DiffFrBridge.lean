module

public import CutoffRigidity.Riemann.DiffMarkov
public import CutoffRigidity.Riemann.DiffFrResolvent

/-! # Bridge to the DIR interface (`DirFormData`, `DirFriedrichs`, `DirResolvent`)

FR's closed form is the one of the DIR mirror structures: `Q` is the set of `H`-limits of
energy-Cauchy sequences of `D`, and `E` is the limit of the energies.
-/

@[expose] public section

open Filter Topology Set
open scoped NNReal InnerProductSpace

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

namespace FormData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (S : FormData H)

/-- The same data as a `DirFormData`. -/
abbrev toDir : DirFormData H where
  D := S.D
  dense := S.dense
  A := S.A
  symm := S.symm
  nonneg := S.nonneg

/-- `Dom → D`. -/
abbrev toD (g : S.Dom) : S.D := g

/-- Embedding `D → K`. -/
noncomputable def toK (f : S.D) : S.K := ((show S.Dom from f : S.Dom) : S.K)

lemma ι_toK (f : S.D) : S.ι (S.toK f) = (f : H) := S.ι_coe (show S.Dom from f)

lemma inner_toK (f g : S.D) :
    inner ℝ (S.toK f) (S.toK g) = inner ℝ (f : H) (g : H) + inner ℝ (S.A f) (g : H) := by
  unfold toK
  rw [UniformSpace.Completion.inner_coe, S.inner_dom]
  rfl

lemma en_eq (f g : S.D) :
    S.toDir.en f g = inner ℝ (S.toK f) (S.toK g) - inner ℝ (f : H) (g : H) := by
  rw [S.inner_toK]
  show inner ℝ (S.A f) (g : H) = _
  ring

lemma norm_toK_sq (f : S.D) :
    ‖S.toK f‖ ^ 2 = ‖(f : H)‖ ^ 2 + S.toDir.en f f := by
  rw [← real_inner_self_eq_norm_sq, S.inner_toK, real_inner_self_eq_norm_sq]; rfl

lemma toK_sub (f g : S.D) : S.toK (f - g) = S.toK f - S.toK g := by
  unfold toK
  exact UniformSpace.Completion.coe_sub (show S.Dom from f) (show S.Dom from g)

lemma en_le_norm_toK_sq (f : S.D) : S.toDir.en f f ≤ ‖S.toK f‖ ^ 2 := by
  rw [S.norm_toK_sq]; nlinarith [sq_nonneg ‖(f : H)‖]

lemma mem_Q_seq (u : H) : u ∈ S.Q ↔ ∃ f : ℕ → S.toDir.D,
    Tendsto (fun n => (f n : H)) atTop (𝓝 u) ∧ S.toDir.EnCauchy f := by
  constructor
  · rintro ⟨x, rfl⟩
    have hx : x ∈ closure (Set.range ((↑) : S.Dom → S.K)) := by
      rw [(UniformSpace.Completion.denseRange_coe (α := S.Dom)).closure_range]; trivial
    obtain ⟨a, ha, hlim⟩ := mem_closure_iff_seq_limit.mp hx
    choose d hd using ha
    refine ⟨fun n => S.toD (d n), ?_, ?_⟩
    · have h1 : ∀ n, ((S.toD (d n) : S.D) : H) = S.ι (a n) := fun n => by
        rw [← hd n]; exact (S.ι_coe (d n)).symm
      simp only [h1]
      exact (S.ι.continuous.tendsto x).comp hlim
    · intro ε hε
      have hc := hlim.cauchySeq
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
      refine ⟨N, fun m hm n hn => ?_⟩
      have h1 := hN m hm n hn
      rw [dist_eq_norm] at h1
      have e : S.toK (S.toD (d m) - S.toD (d n)) = a m - a n := by
        rw [S.toK_sub, ← hd m, ← hd n]; rfl
      have h2 := S.en_le_norm_toK_sq (S.toD (d m) - S.toD (d n))
      rw [e] at h2
      have h3 : ‖a m - a n‖ ^ 2 < ε := by
        have := pow_lt_pow_left₀ h1 (norm_nonneg _) (two_ne_zero)
        rwa [Real.sq_sqrt hε.le] at this
      exact lt_of_le_of_lt h2 h3
  · rintro ⟨f, hf, hc⟩
    have hK : CauchySeq fun n => S.toK (f n) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      have hH := hf.cauchySeq
      obtain ⟨N1, h1⟩ := Metric.cauchySeq_iff.mp hH (ε / 2) (by positivity)
      obtain ⟨N2, h2⟩ := hc ((ε / 2) ^ 2) (by positivity)
      refine ⟨max N1 N2, fun m hm n hn => ?_⟩
      have a1 := h1 m (le_trans (le_max_left _ _) hm) n (le_trans (le_max_left _ _) hn)
      have a2 := h2 m (le_trans (le_max_right _ _) hm) n (le_trans (le_max_right _ _) hn)
      rw [dist_eq_norm] at a1 ⊢
      rw [← S.toK_sub]
      have e := S.norm_toK_sq (f m - f n)
      have hsub : ((f m - f n : S.D) : H) = (f m : H) - f n := rfl
      rw [hsub] at e
      have : ‖S.toK (f m - f n)‖ ^ 2 < ε ^ 2 := by
        rw [e]
        have := pow_lt_pow_left₀ a1 (norm_nonneg _) (two_ne_zero)
        nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 hε.le this
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hK
    refine ⟨x, ?_⟩
    have h1 : Tendsto (fun n => S.ι (S.toK (f n))) atTop (𝓝 (S.ι x)) :=
      (S.ι.continuous.tendsto x).comp hx
    simp only [S.ι_toK] at h1
    exact tendsto_nhds_unique h1 hf

lemma exists_limit_K {f : ℕ → S.toDir.D} {u : H} (hf : Tendsto (fun n => (f n : H)) atTop (𝓝 u))
    (hc : S.toDir.EnCauchy f) :
    ∃ x : S.K, Tendsto (fun n => S.toK (f n)) atTop (𝓝 x) ∧ S.ι x = u := by
  have hK : CauchySeq fun n => S.toK (f n) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hH := hf.cauchySeq
    obtain ⟨N1, h1⟩ := Metric.cauchySeq_iff.mp hH (ε / 2) (by positivity)
    obtain ⟨N2, h2⟩ := hc ((ε / 2) ^ 2) (by positivity)
    refine ⟨max N1 N2, fun m hm n hn => ?_⟩
    have a1 := h1 m (le_trans (le_max_left _ _) hm) n (le_trans (le_max_left _ _) hn)
    have a2 := h2 m (le_trans (le_max_right _ _) hm) n (le_trans (le_max_right _ _) hn)
    rw [dist_eq_norm] at a1 ⊢
    rw [← S.toK_sub]
    have e := S.norm_toK_sq (f m - f n)
    have hsub : ((f m - f n : S.D) : H) = (f m : H) - f n := rfl
    rw [hsub] at e
    have : ‖S.toK (f m - f n)‖ ^ 2 < ε ^ 2 := by
      rw [e]
      have := pow_lt_pow_left₀ a1 (norm_nonneg _) (two_ne_zero)
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le this
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hK
  refine ⟨x, hx, ?_⟩
  have h1 : Tendsto (fun n => S.ι (S.toK (f n))) atTop (𝓝 (S.ι x)) :=
    (S.ι.continuous.tendsto x).comp hx
  simp only [S.ι_toK] at h1
  exact tendsto_nhds_unique h1 hf

/-- The energy extended by `0` outside `Q × Q`. -/
noncomputable def Eext (u v : H) : ℝ :=
  open scoped Classical in
  if h : u ∈ S.Q ∧ v ∈ S.Q then S.E ⟨u, h.1⟩ ⟨v, h.2⟩ else 0

lemma Eext_of_mem {u v : H} (hu : u ∈ S.Q) (hv : v ∈ S.Q) : S.Eext u v = S.E ⟨u, hu⟩ ⟨v, hv⟩ := by
  unfold Eext; rw [dif_pos ⟨hu, hv⟩]

lemma tendsto_en {f g : ℕ → S.toDir.D} {u v : H}
    (hf : Tendsto (fun n => (f n : H)) atTop (𝓝 u)) (hfc : S.toDir.EnCauchy f)
    (hg : Tendsto (fun n => (g n : H)) atTop (𝓝 v)) (hgc : S.toDir.EnCauchy g) :
    Tendsto (fun n => S.toDir.en (f n) (g n)) atTop (𝓝 (S.Eext u v)) := by
  obtain ⟨x, hx, rfl⟩ := S.exists_limit_K hf hfc
  obtain ⟨y, hy, rfl⟩ := S.exists_limit_K hg hgc
  have h1 : Tendsto (fun n => inner ℝ (S.toK (f n)) (S.toK (g n)) - inner ℝ (f n : H) (g n : H))
      atTop (𝓝 (inner ℝ x y - inner ℝ (S.ι x) (S.ι y))) := by
    apply Tendsto.sub (hx.inner hy) (hf.inner hg)
  have h2 : S.Eext (S.ι x) (S.ι y) = inner ℝ x y - inner ℝ (S.ι x) (S.ι y) := by
    have hu : S.ι x ∈ S.Q := ⟨x, rfl⟩
    have hv : S.ι y ∈ S.Q := ⟨y, rfl⟩
    rw [S.Eext_of_mem hu hv]
    have := S.E_eq x y
    rw [← this]
    rfl
  rw [h2]
  refine h1.congr (fun n => ?_)
  rw [S.en_eq]

/-- FR's closed form is a `DirFriedrichs`. -/
noncomputable def toDirFriedrichs : DirFriedrichs S.toDir where
  Q := (S.Q : Set H)
  E := S.Eext
  mem_Q := fun u => S.mem_Q_seq u
  E_lim := fun f g u v hf hfc hg hgc => S.tendsto_en hf hfc hg hgc

lemma toDirResolvent {lam : ℝ} (hlam : 0 < lam) :
    DirResolvent S.toDirFriedrichs lam (S.resolvent lam) where
  mem := fun g => S.resolvent_mem_Q hlam g
  weak := fun g φ hφ => by
    have h := S.E_resolvent hlam g ⟨φ, hφ⟩
    have e := S.Eext_of_mem (S.resolvent_mem_Q hlam g) hφ
    show S.Eext _ _ + _ = _
    rw [e]
    exact h

end FormData

end CutoffRigidity.Riemann.Diff
