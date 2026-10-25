module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

/-! # Actual quadratic infimum convolution

This is the Hopf–Lax operator in the cited Hamilton–Jacobi proof of the
transportation inequality. Its infimum and regularity are proved directly.
-/
public section
namespace CutoffRigidity
open Set
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E]

@[expose] noncomputable def hopfLax (t : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  if 0 < t then sInf (range (fun y => f y + ‖x-y‖^2/(2*t))) else f x

theorem hopfLax_nonpos {t : ℝ} (ht : t ≤ 0) (f : E → ℝ) : hopfLax t f = f := by
  funext x
  simp only [hopfLax, not_lt.mpr ht, ↓reduceIte]

private theorem hopfLax_cost_bddBelow {t M : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : ∀ y, -M ≤ f y) (x : E) :
    BddBelow (range (fun y => f y + ‖x-y‖^2/(2*t))) := by
  refine ⟨-M, ?_⟩
  rintro _ ⟨y,rfl⟩
  exact (hf y).trans (le_add_of_nonneg_right (by positivity))

/-- Every actual competitor bounds the actual infimum convolution. -/
theorem hopfLax_le_cost {t M : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : ∀ y, -M ≤ f y) (x y : E) :
    hopfLax t f x ≤ f y + ‖x-y‖^2/(2*t) := by
  rw [hopfLax, ite_eq_left ht]
  exact csInf_le (hopfLax_cost_bddBelow ht hf x) ⟨y,rfl⟩

/-- Actual boundedness is preserved, including at time zero. -/
theorem hopfLax_bounds {t M : ℝ} (ht : 0 ≤ t)
    {f : E → ℝ} (hf : ∀ y, |f y| ≤ M) (x : E) :
    -M ≤ hopfLax t f x ∧ hopfLax t f x ≤ f x := by
  by_cases htpos : 0 < t
  · have hlo (y : E) : -M ≤ f y := (abs_le.mp (hf y)).1
    constructor
    · rw [hopfLax, ite_eq_left htpos]
      apply le_csInf (range_nonempty _)
      rintro _ ⟨y,rfl⟩
      exact (hlo y).trans (le_add_of_nonneg_right (by positivity))
    · simpa only [sub_self,norm_zero,zero_pow (by decide : 2≠0),zero_div,add_zero]
        using hopfLax_le_cost htpos hlo x x
  · have he : t = 0 := le_antisymm (le_of_not_gt htpos) ht
    simp only [he,hopfLax,lt_self_iff_false,↓reduceIte,le_refl,and_true]
    exact (abs_le.mp (hf x)).1

/-- Quadratic infimum convolution preserves the actual global Lipschitz
constant, by translating every competitor by the displacement. -/
theorem lipschitzWith_hopfLax {t M : ℝ} (_ht : 0 ≤ t)
    {f : E → ℝ} (hf : ∀ y, |f y| ≤ M) {L : NNReal} (hL : LipschitzWith L f) :
    LipschitzWith L (hopfLax t f) := by
  by_cases htpos : 0 < t
  · have hlo (y : E) : -M ≤ f y := (abs_le.mp (hf y)).1
    have hbound (x y : E) : hopfLax t f x ≤ hopfLax t f y + L*‖x-y‖ := by
      apply sub_le_iff_le_add.mp
      conv_rhs => rw [hopfLax,ite_eq_left htpos]
      apply le_csInf (range_nonempty _)
      rintro _ ⟨z,rfl⟩
      have hcost := hopfLax_le_cost htpos hlo x (z+(x-y))
      have hn : x-(z+(x-y)) = y-z := by abel
      rw [hn] at hcost
      have hfLip : f (z+(x-y)) ≤ f z + L*‖x-y‖ := by
        have hh := hL.norm_sub_le (z+(x-y)) z
        have hh' : f (z+(x-y))-f z ≤ L*‖x-y‖ := by
          apply (le_abs_self _).trans
          simpa only [Real.norm_eq_abs,add_sub_cancel_left] using hh
        linarith
      linarith
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq,abs_le,dist_eq_norm]
    constructor
    · have hh := hbound y x
      rw [norm_sub_rev] at hh
      linarith
    · have hh := hbound x y
      linarith
  · rw [hopfLax_nonpos (le_of_not_gt htpos)]
    exact hL

/-- On a proper normed space every bounded continuous test has a genuine
minimizing point in the quadratic infimum convolution. -/
theorem exists_hopfLax_minimizer [ProperSpace E] {t M : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : ∀ y, |f y| ≤ M) (hfc : Continuous f) (x : E) :
    ∃ y, hopfLax t f x = f y + ‖x-y‖^2/(2*t) := by
  have hM : 0 ≤ M := (abs_nonneg (f x)).trans (hf x)
  let R := Real.sqrt (4*M*t)
  let cost := fun y : E => f y + ‖x-y‖^2/(2*t)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hRsq : R^2 = 4*M*t := Real.sq_sqrt (by positivity)
  have hC : Continuous cost := by dsimp only [cost]; fun_prop
  obtain ⟨y,hy,hmin⟩ := (isCompact_closedBall x R).exists_isMinOn
    ⟨x,Metric.mem_closedBall_self hR⟩ hC.continuousOn
  have hAll (z : E) : cost y ≤ cost z := by
    by_cases hz : z ∈ Metric.closedBall x R
    · exact hmin hz
    · have hzNorm : R ≤ ‖x-z‖ := by
        have hh : R < dist z x := lt_of_not_ge hz
        rw [dist_eq_norm,norm_sub_rev] at hh
        exact hh.le
      have hzSq := (sq_le_sq₀ hR (norm_nonneg (x-z))).mpr hzNorm
      have hLarge : M ≤ cost z := by
        dsimp only [cost]
        have hfLower := (abs_le.mp (hf z)).1
        have hQuot : 2*M ≤ ‖x-z‖^2/(2*t) := by
          apply (le_div_iff₀ (by positivity : 0 < 2*t)).mpr
          nlinarith only [hzSq,hRsq]
        linarith
      have hx : cost x ≤ M := by simpa [cost] using (abs_le.mp (hf x)).2
      exact (hmin (Metric.mem_closedBall_self hR)).trans (hx.trans hLarge)
  refine ⟨y,le_antisymm (hopfLax_le_cost ht (fun z => (abs_le.mp (hf z)).1) x y) ?_⟩
  rw [hopfLax,ite_eq_left ht]
  apply le_csInf (range_nonempty _)
  rintro _ ⟨z,rfl⟩
  exact hAll z

/-- Completing the square gives the actual uniform initial-time control
for Lipschitz tests in the Hamilton–Jacobi argument. -/
theorem hopfLax_lower_of_lipschitz {t : ℝ} (ht : 0 < t)
    {f : E → ℝ} {L : NNReal} (hL : LipschitzWith L f) (x : E) :
    f x - t*(L:ℝ)^2/2 ≤ hopfLax t f x := by
  rw [hopfLax,ite_eq_left ht]
  apply le_csInf (range_nonempty _)
  rintro _ ⟨y,rfl⟩
  have hLip : f x-f y ≤ (L:ℝ)*‖x-y‖ := by
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hL.norm_sub_le x y)
  have hYoung : (L:ℝ)*‖x-y‖ - t*(L:ℝ)^2/2 ≤ ‖x-y‖^2/(2*t) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*t)).mpr
    nlinarith only [sq_nonneg (‖x-y‖-t*(L:ℝ))]
  linarith

/-- The actual Hopf–Lax values converge uniformly to a bounded Lipschitz
test at time zero, with the exact quadratic-error bound. -/
theorem norm_hopfLax_sub_le {t M : ℝ} (ht : 0 ≤ t)
    {f : E → ℝ} (hf : ∀ y, |f y| ≤ M) {L : NNReal} (hL : LipschitzWith L f) (x : E) :
    ‖hopfLax t f x-f x‖ ≤ t*(L:ℝ)^2/2 := by
  by_cases hpos : 0 < t
  · have hu := (hopfLax_bounds ht hf x).2
    have hl := hopfLax_lower_of_lipschitz hpos hL x
    rw [Real.norm_eq_abs,abs_le]
    constructor <;> linarith [sq_nonneg (L:ℝ)]
  · have he : t = 0 := le_antisymm (le_of_not_gt hpos) ht
    simp [he,hopfLax]

/-- The actual infimum convolution decreases with its positive time. -/
theorem hopfLax_antitone_time {s t M : ℝ} (hs : 0 < s) (hst : s ≤ t)
    {f : E → ℝ} (hf : ∀ y, |f y| ≤ M) (x : E) : hopfLax t f x ≤ hopfLax s f x := by
  have ht : 0 < t := hs.trans_le hst
  conv_rhs => rw [hopfLax,ite_eq_left hs]
  apply le_csInf (range_nonempty _)
  rintro _ ⟨y,rfl⟩
  apply (hopfLax_le_cost ht (fun z => (abs_le.mp (hf z)).1) x y).trans
  apply add_le_add le_rfl
  apply (div_le_div_iff₀ (by positivity : 0 < 2*t) (by positivity : 0 < 2*s)).mpr
  nlinarith [sq_nonneg ‖x-y‖]

/-- Genuine positive-time variation control, derived from actual minimizing
points, is the time regularity required by the a.e. Hamilton–Jacobi proof. -/
theorem hopfLax_time_sub_le [ProperSpace E] {s t M : ℝ} (hs : 0 < s) (hst : s ≤ t)
    {f : E → ℝ} (hf : ∀ y, |f y| ≤ M) (hfc : Continuous f) (x : E) :
    hopfLax s f x-hopfLax t f x ≤ 2*M*(t-s)/s := by
  have ht : 0 < t := hs.trans_le hst
  have hM : 0 ≤ M := (abs_nonneg (f x)).trans (hf x)
  obtain ⟨y,hy⟩ := exists_hopfLax_minimizer ht hf hfc x
  have hQ := (hopfLax_bounds ht.le hf x).2.trans (abs_le.mp (hf x)).2
  have hfLow := (abs_le.mp (hf y)).1
  have hR : ‖x-y‖^2/(2*t) ≤ 2*M := by rw [hy] at hQ; linarith
  have hComp := hopfLax_le_cost hs (fun z => (abs_le.mp (hf z)).1) x y
  have hId : (‖x-y‖^2/(2*t))*((t-s)/s) = ‖x-y‖^2/(2*s)-‖x-y‖^2/(2*t) := by
    field_simp
  calc
    _ ≤ (‖x-y‖^2/(2*t))*((t-s)/s) := by rw [hy,hId]; linarith
    _ ≤ (2*M)*((t-s)/s) := mul_le_mul_of_nonneg_right hR (div_nonneg (sub_nonneg.mpr hst) hs.le)
    _ = _ := by ring

/-- The actual time curve is Lipschitz on each interval separated from
zero, with a finite bound derived from the bounded test itself. -/
theorem lipschitzOnWith_hopfLax_time [ProperSpace E] {a M : ℝ} (ha : 0 < a)
    {f : E → ℝ} (hf : ∀ y, |f y| ≤ M) (hfc : Continuous f) (x : E) :
    LipschitzOnWith ⟨2*M/a, div_nonneg (by have := (abs_nonneg (f x)).trans (hf x); positivity) ha.le⟩
      (fun t => hopfLax t f x) (Ioi a) := by
  have hM : 0 ≤ M := (abs_nonneg (f x)).trans (hf x)
  have hbound {s t : ℝ} (hs : a < s) (hst : s ≤ t) :
      hopfLax s f x-hopfLax t f x ≤ (2*M/a)*(t-s) := by
    have hspos := ha.trans hs
    apply (hopfLax_time_sub_le hspos hst hf hfc x).trans
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff₀ hspos ha).mpr
    nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2*M) (sub_nonneg.mpr hst)) (sub_nonneg.mpr hs.le)]
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  change dist (hopfLax s f x) (hopfLax t f x) ≤ (2*M/a)*dist s t
  rw [Real.dist_eq,Real.dist_eq]
  rcases le_total s t with hst|hts
  · have hh := hbound hs hst
    have hm := hopfLax_antitone_time (ha.trans hs) hst hf x
    rw [abs_of_nonneg (sub_nonneg.mpr hm),abs_of_nonpos (sub_nonpos.mpr hst)]
    linarith
  · have hh := hbound ht hts
    have hm := hopfLax_antitone_time (ha.trans ht) hts hf x
    rw [abs_of_nonpos (sub_nonpos.mpr hm),abs_of_nonneg (sub_nonneg.mpr hts)]
    linarith

end CutoffRigidity
