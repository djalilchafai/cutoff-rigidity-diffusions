module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Complexification of a real Hilbert space

Mathlib's continuous functional calculus needs a complex C*-algebra.  To apply it to a
self-adjoint operator on a *real* Hilbert space `H` we complexify: `Cx H = H × H` with
`(a + i b) • (x, y) = (a x - b y, a y + b x)`.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate Pointwise

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Complexification of a real Hilbert space. -/
def Cx : Type _ := WithLp 2 (H × H)

namespace Cx

noncomputable instance : NormedAddCommGroup (Cx H) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (H × H)))
instance [CompleteSpace H] : CompleteSpace (Cx H) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (H × H)))

variable {H}

/-- Constructor. -/
def mk (a b : H) : Cx H := WithLp.toLp 2 (a, b)
/-- Real part. -/
def re (v : Cx H) : H := WithLp.fst v
/-- Imaginary part. -/
def im (v : Cx H) : H := WithLp.snd v

@[ext] lemma ext {v w : Cx H} (h1 : v.re = w.re) (h2 : v.im = w.im) : v = w := by
  apply WithLp.ofLp_injective
  exact Prod.ext h1 h2

@[simp] lemma re_mk (a b : H) : (mk a b).re = a := rfl
@[simp] lemma im_mk (a b : H) : (mk a b).im = b := rfl
@[simp] lemma mk_re_im (v : Cx H) : mk v.re v.im = v := rfl
@[simp] lemma re_add (v w : Cx H) : (v + w).re = v.re + w.re := rfl
@[simp] lemma im_add (v w : Cx H) : (v + w).im = v.im + w.im := rfl
@[simp] lemma re_sub (v w : Cx H) : (v - w).re = v.re - w.re := rfl
@[simp] lemma im_sub (v w : Cx H) : (v - w).im = v.im - w.im := rfl
@[simp] lemma re_neg (v : Cx H) : (-v).re = -v.re := rfl
@[simp] lemma im_neg (v : Cx H) : (-v).im = -v.im := rfl
@[simp] lemma re_zero : (0 : Cx H).re = 0 := rfl
@[simp] lemma im_zero : (0 : Cx H).im = 0 := rfl

lemma norm_sq (v : Cx H) : ‖v‖ ^ 2 = ‖v.re‖ ^ 2 + ‖v.im‖ ^ 2 := by
  exact WithLp.prod_norm_sq_eq_of_L2 (show WithLp 2 (H × H) from v)

/-- Scalar multiplication by a complex number. -/
instance : SMul ℂ (Cx H) where
  smul z v := mk (z.re • v.re - z.im • v.im) (z.re • v.im + z.im • v.re)

@[simp] lemma re_smul (z : ℂ) (v : Cx H) : (z • v).re = z.re • v.re - z.im • v.im := rfl
@[simp] lemma im_smul (z : ℂ) (v : Cx H) : (z • v).im = z.re • v.im + z.im • v.re := rfl

instance : Module ℂ (Cx H) where
  one_smul v := by ext <;> simp
  mul_smul a b v := by
    ext <;> simp [Complex.mul_re, Complex.mul_im, sub_smul, add_smul, smul_sub, smul_add,
      mul_smul] <;> abel
  smul_zero a := by ext <;> simp
  smul_add a v w := by ext <;> simp [smul_add] <;> abel
  add_smul a b v := by ext <;> simp [add_smul] <;> abel
  zero_smul v := by ext <;> simp

instance : NormedSpace ℂ (Cx H) where
  norm_smul_le z v := by
    have h : ‖z • v‖ ^ 2 = (‖z‖ * ‖v‖) ^ 2 := by
      rw [norm_sq, mul_pow, norm_sq]
      simp only [re_smul, im_smul]
      have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      rw [hz]
      have e1 : ‖z.re • v.re - z.im • v.im‖ ^ 2 = z.re ^ 2 * ‖v.re‖ ^ 2 + z.im ^ 2 * ‖v.im‖ ^ 2
          - 2 * z.re * z.im * inner ℝ v.re v.im := by
        rw [@norm_sub_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right]
        simp [mul_pow, Real.norm_eq_abs, sq_abs]; ring
      have e2 : ‖z.re • v.im + z.im • v.re‖ ^ 2 = z.re ^ 2 * ‖v.im‖ ^ 2 + z.im ^ 2 * ‖v.re‖ ^ 2
          + 2 * z.re * z.im * inner ℝ v.re v.im := by
        rw [@norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right,
          real_inner_comm]
        simp [mul_pow, Real.norm_eq_abs, sq_abs]; ring
      rw [e1, e2]; ring
    exact le_of_eq (by
      have := sq_eq_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ‖z‖ * ‖v‖) |>.mp h
      exact this)

/-- The complex inner product (conjugate-linear in the first variable). -/
noncomputable instance : Inner ℂ (Cx H) where
  inner v w := ((inner ℝ v.re w.re + inner ℝ v.im w.im : ℝ) : ℂ) +
    ((inner ℝ v.re w.im - inner ℝ v.im w.re : ℝ) : ℂ) * Complex.I

lemma inner_def (v w : Cx H) : ⟪v, w⟫_ℂ = ((inner ℝ v.re w.re + inner ℝ v.im w.im : ℝ) : ℂ) +
    ((inner ℝ v.re w.im - inner ℝ v.im w.re : ℝ) : ℂ) * Complex.I := rfl

lemma inner_re (v w : Cx H) : (⟪v, w⟫_ℂ).re = inner ℝ v.re w.re + inner ℝ v.im w.im := by
  simp [inner_def]

lemma inner_im (v w : Cx H) : (⟪v, w⟫_ℂ).im = inner ℝ v.re w.im - inner ℝ v.im w.re := by
  simp [inner_def]

noncomputable instance : InnerProductSpace ℂ (Cx H) where
  norm_sq_eq_re_inner v := by
    rw [norm_sq, RCLike.re_to_complex, inner_re]; simp [real_inner_self_eq_norm_sq]
  conj_inner_symm v w := by
    apply Complex.ext
    · simp [inner_re, real_inner_comm]
    · simp [inner_im, real_inner_comm]
  add_left u v w := by
    apply Complex.ext
    · simp [inner_re, inner_add_left]; ring
    · simp [inner_im, inner_add_left]; ring
  smul_left u v z := by
    apply Complex.ext
    · simp [inner_re, inner_im, inner_add_left, inner_sub_left, inner_smul_left,
        Complex.mul_re]; ring
    · simp [inner_re, inner_im, inner_add_left, inner_sub_left, inner_smul_left,
        Complex.mul_im]; ring

section Operators

variable [CompleteSpace H]

lemma re_smul_real (c : ℝ) (v : Cx H) : (c • v).re = c • v.re := by
  show ((c : ℂ) • v).re = _
  simp only [re_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]

lemma im_smul_real (c : ℝ) (v : Cx H) : (c • v).im = c • v.im := by
  show ((c : ℂ) • v).im = _
  simp only [im_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, add_zero]

/-- Complexification of a real bounded operator. -/
noncomputable def cx (T : H →L[ℝ] H) : Cx H →L[ℂ] Cx H :=
  LinearMap.mkContinuous
    { toFun := fun v => mk (T v.re) (T v.im)
      map_add' := fun v w => by ext <;> simp
      map_smul' := fun z v => by
        ext <;> simp [map_sub, map_add] }
    ‖T‖ (fun v => by
      show ‖mk (T v.re) (T v.im)‖ ≤ ‖T‖ * ‖v‖
      have h1 : ‖T v.re‖ ≤ ‖T‖ * ‖v.re‖ := T.le_opNorm _
      have h2 : ‖T v.im‖ ≤ ‖T‖ * ‖v.im‖ := T.le_opNorm _
      have hT := norm_nonneg T
      apply le_of_sq_le_sq _ (by positivity)
      rw [mul_pow, norm_sq, norm_sq]
      simp only [re_mk, im_mk]
      nlinarith [mul_self_le_mul_self (norm_nonneg _) h1, mul_self_le_mul_self (norm_nonneg _) h2])

@[simp] lemma re_cx (T : H →L[ℝ] H) (v : Cx H) : (cx T v).re = T v.re := rfl
@[simp] lemma im_cx (T : H →L[ℝ] H) (v : Cx H) : (cx T v).im = T v.im := rfl

lemma cx_mul (S T : H →L[ℝ] H) : cx (S * T) = cx S * cx T := by
  ext v <;> simp
lemma cx_one : cx (1 : H →L[ℝ] H) = 1 := by ext v <;> simp
lemma cx_add (S T : H →L[ℝ] H) : cx (S + T) = cx S + cx T := by ext v <;> simp
lemma cx_sub (S T : H →L[ℝ] H) : cx (S - T) = cx S - cx T := by ext v <;> simp
lemma cx_smul (c : ℝ) (T : H →L[ℝ] H) : cx (c • T) = c • cx T := by
  ext v
  · simp [re_smul_real]
  · simp [im_smul_real]
lemma cx_pow (T : H →L[ℝ] H) (n : ℕ) : cx (T ^ n) = cx T ^ n := by
  induction n with
  | zero => simpa using cx_one
  | succ n ih => rw [pow_succ, cx_mul, ih, pow_succ]

lemma cx_injective : Function.Injective (cx : (H →L[ℝ] H) → _) := by
  intro S T h
  ext x
  have := congrArg (fun X => (X (mk x 0)).re) h
  simpa using this

lemma norm_cx (T : H →L[ℝ] H) : ‖cx T‖ = ‖T‖ := by
  apply le_antisymm
  · exact (cx T).opNorm_le_bound (norm_nonneg T) (fun v => by
      have h1 : ‖T v.re‖ ≤ ‖T‖ * ‖v.re‖ := T.le_opNorm _
      have h2 : ‖T v.im‖ ≤ ‖T‖ * ‖v.im‖ := T.le_opNorm _
      have hT := norm_nonneg T
      apply le_of_sq_le_sq _ (by positivity)
      rw [mul_pow, norm_sq, norm_sq]
      simp only [re_cx, im_cx]
      nlinarith [mul_self_le_mul_self (norm_nonneg _) h1, mul_self_le_mul_self (norm_nonneg _) h2])
  · refine T.opNorm_le_bound (norm_nonneg _) (fun x => ?_)
    have := (cx T).le_opNorm (mk x 0)
    have e1 : ‖mk x 0‖ = ‖x‖ := by
      have := norm_sq (mk x 0)
      simp at this
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by simpa using this)
    have e2 : ‖cx T (mk x 0)‖ = ‖T x‖ := by
      have := norm_sq (cx T (mk x 0))
      simp at this
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by simpa using this)
    rw [e1, e2] at this
    exact this

/-- Complex conjugation on the complexification. -/
def sig (v : Cx H) : Cx H := mk v.re (-v.im)

@[simp] lemma re_sig (v : Cx H) : (sig v).re = v.re := rfl
@[simp] lemma im_sig (v : Cx H) : (sig v).im = -v.im := rfl
@[simp] lemma sig_sig (v : Cx H) : sig (sig v) = v := by ext <;> simp
@[simp] lemma sig_add (v w : Cx H) : sig (v + w) = sig v + sig w := by
  ext
  · simp
  · simp; abel

lemma norm_sig (v : Cx H) : ‖sig v‖ = ‖v‖ := by
  have := norm_sq (sig v)
  simp only [re_sig, im_sig, norm_neg] at this
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by rw [this, norm_sq])

lemma continuous_sig : Continuous (sig : Cx H → Cx H) := by
  apply Isometry.continuous
  apply Isometry.of_dist_eq
  intro v w
  rw [dist_eq_norm, dist_eq_norm, ← norm_sig (v - w)]
  congr 1
  ext
  · simp
  · simp; abel

lemma inner_sig (v w : Cx H) : ⟪sig v, sig w⟫_ℂ = conj ⟪v, w⟫_ℂ := by
  apply Complex.ext
  · rw [Complex.conj_re, inner_re, inner_re]; simp
  · rw [Complex.conj_im, inner_im, inner_im]; simp; ring

lemma sig_smul_real (c : ℝ) (v : Cx H) : sig (c • v) = c • sig v := by
  ext
  · simp [re_smul_real]
  · simp [im_smul_real]

lemma adjoint_cx (T : H →L[ℝ] H) : ContinuousLinearMap.adjoint (cx T) = cx (ContinuousLinearMap.adjoint T) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  apply Complex.ext
  · simp [inner_re, ContinuousLinearMap.adjoint_inner_left]
  · simp [inner_im, ContinuousLinearMap.adjoint_inner_left]

lemma star_cx (T : H →L[ℝ] H) : star (cx T) = cx (star T) := adjoint_cx T

lemma isSelfAdjoint_cx {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) : IsSelfAdjoint (cx T) := by
  rw [IsSelfAdjoint, star_cx, hT.star_eq]

/-- Operators commuting with complex conjugation. -/
def Fixed (X : Cx H →L[ℂ] Cx H) : Prop := ∀ v, X (sig v) = sig (X v)

lemma Fixed.mul {X Y : Cx H →L[ℂ] Cx H} (hX : Fixed X) (hY : Fixed Y) : Fixed (X * Y) := by
  intro v
  show X (Y (sig v)) = sig (X (Y v))
  rw [hY, hX]

lemma Fixed.add {X Y : Cx H →L[ℂ] Cx H} (hX : Fixed X) (hY : Fixed Y) : Fixed (X + Y) := by
  intro v
  rw [add_apply, add_apply, hX, hY, sig_add]

lemma Fixed.algebraMap (c : ℝ) : Fixed (algebraMap ℝ (Cx H →L[ℂ] Cx H) c) := by
  intro v
  rw [Algebra.algebraMap_eq_smul_one]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  exact (sig_smul_real c v).symm

lemma Fixed.star {X : Cx H →L[ℂ] Cx H} (hX : Fixed X) : Fixed (Star.star X) := by
  intro v
  apply ext_inner_right ℂ
  intro w
  have h1 : ⟪sig (Star.star X v), w⟫_ℂ = conj ⟪Star.star X v, sig w⟫_ℂ := by
    rw [← inner_sig, sig_sig]
  have h2 : ⟪Star.star X (sig v), w⟫_ℂ = ⟪sig v, X w⟫_ℂ :=
    ContinuousLinearMap.adjoint_inner_left X w (sig v)
  have h3 : ⟪Star.star X v, sig w⟫_ℂ = ⟪v, X (sig w)⟫_ℂ :=
    ContinuousLinearMap.adjoint_inner_left X (sig w) v
  rw [h2, h1, h3, hX w]
  have h4 : ⟪sig v, X w⟫_ℂ = conj ⟪v, sig (X w)⟫_ℂ := by
    rw [← inner_sig, sig_sig]
  exact h4

/-- The star subalgebra of operators commuting with complex conjugation. -/
noncomputable def fixedSub : StarSubalgebra ℝ (Cx H →L[ℂ] Cx H) where
  carrier := {X | Fixed X}
  mul_mem' := fun hX hY => Fixed.mul hX hY
  add_mem' := fun hX hY => Fixed.add hX hY
  algebraMap_mem' := fun c => Fixed.algebraMap c
  star_mem' := fun hX => Fixed.star hX

lemma mem_fixedSub {X : Cx H →L[ℂ] Cx H} : X ∈ (fixedSub (H := H)) ↔ Fixed X := Iff.rfl

lemma isClosed_fixedSub :
    IsClosed ((fixedSub (H := H) : StarSubalgebra ℝ (Cx H →L[ℂ] Cx H)) : Set (Cx H →L[ℂ] Cx H)) := by
  have : ((fixedSub (H := H) : StarSubalgebra ℝ (Cx H →L[ℂ] Cx H)) : Set (Cx H →L[ℂ] Cx H)) =
      ⋂ v : Cx H, {X | X (sig v) = sig (X v)} := by
    ext X; simp [mem_fixedSub, Fixed]
  rw [this]
  apply isClosed_iInter
  intro v
  exact isClosed_eq (ContinuousLinearMap.apply ℂ (Cx H) (sig v)).continuous
    (continuous_sig.comp (ContinuousLinearMap.apply ℂ (Cx H) v).continuous)

lemma cx_fixed (T : H →L[ℝ] H) : Fixed (cx T) := by
  intro v; ext <;> simp

lemma mk_eq (x y : H) : mk x y = mk x 0 + Complex.I • mk y 0 := by
  ext <;> simp

lemma exists_of_fixed {X : Cx H →L[ℂ] Cx H} (hX : Fixed X) : ∃ T : H →L[ℝ] H, cx T = X := by
  have him : ∀ x : H, (X (mk x 0)).im = 0 := by
    intro x
    have h := hX (mk x 0)
    have h2 : sig (mk x 0) = mk x 0 := by ext <;> simp
    rw [h2] at h
    have := congrArg Cx.im h
    simp only [im_sig] at this
    have h3 : (X (mk x 0)).im = - (X (mk x 0)).im := this
    have : (2 : ℝ) • (X (mk x 0)).im = 0 := by
      rw [two_smul]; nth_rewrite 1 [h3]; simp
    simpa using this
  let f : H →ₗ[ℝ] H :=
    { toFun := fun x => (X (mk x 0)).re
      map_add' := fun x y => by
        have : mk (x + y) 0 = mk x 0 + mk y 0 := by ext <;> simp
        rw [this, map_add]; rfl
      map_smul' := fun c x => by
        have : mk (c • x) 0 = (c : ℂ) • mk x 0 := by
          ext
          · simp only [re_mk, re_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]
          · simp only [im_mk, im_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, add_zero, smul_zero]
        rw [this, map_smul]
        show ((c : ℂ) • X (mk x 0)).re = _
        simp [re_smul_real] }
  let T : H →L[ℝ] H := LinearMap.mkContinuous f ‖X‖ (fun x => by
    show ‖(X (mk x 0)).re‖ ≤ ‖X‖ * ‖x‖
    have h1 : ‖X (mk x 0)‖ ≤ ‖X‖ * ‖mk x 0‖ := X.le_opNorm _
    have e1 : ‖mk x 0‖ = ‖x‖ := by
      have := norm_sq (mk x 0)
      simp at this
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by simpa using this)
    have h2 : ‖(X (mk x 0)).re‖ ≤ ‖X (mk x 0)‖ := by
      apply le_of_sq_le_sq _ (norm_nonneg _)
      rw [norm_sq (X (mk x 0)), him]; simp
    rw [e1] at h1
    linarith)
  have hT : ∀ x, T x = (X (mk x 0)).re := fun x => rfl
  refine ⟨T, ?_⟩
  have key : ∀ x, X (mk x 0) = mk (T x) 0 := by
    intro x; ext
    · rw [hT]; rfl
    · simpa using him x
  have hv : ∀ v : Cx H, X v = mk (T v.re) 0 + Complex.I • mk (T v.im) 0 := by
    intro v
    have : v = mk v.re 0 + Complex.I • mk v.im 0 := mk_eq v.re v.im
    conv_lhs => rw [this]
    rw [map_add, map_smul, key, key]
  ext v
  · rw [hv]; simp
  · rw [hv]; simp

end Operators

section Calculus

variable [CompleteSpace H]

open scoped ContinuousFunctionalCalculus

/-- Real continuous functional calculus of a (bounded, self-adjoint) operator on a real Hilbert
space, obtained from the complex one on the complexification.  Junk value `0` if no operator
`T` with `cx T = cfc f (cx R)` exists (which never happens for self-adjoint `R`). -/
noncomputable def rcfc (f : ℝ → ℝ) (R : H →L[ℝ] H) : H →L[ℝ] H :=
  open scoped Classical in
  if h : ∃ T : H →L[ℝ] H, cx T = cfc f (cx R) then h.choose else 0

lemma cx_rcfc (R : H →L[ℝ] H) (f : ℝ → ℝ) :
    cx (rcfc f R) = cfc f (cx R) := by
  have hmem : cfc f (cx R) ∈ (fixedSub (H := H)) := by
    have : IsClosed ((fixedSub (H := H) : StarSubalgebra ℝ (Cx H →L[ℂ] Cx H)) :
      Set (Cx H →L[ℂ] Cx H)) := isClosed_fixedSub
    exact cfc_mem (𝕜' := ℝ) (s := (fixedSub (H := H))) f (cx_fixed R)
  have hex : ∃ T : H →L[ℝ] H, cx T = cfc f (cx R) := exists_of_fixed hmem
  unfold rcfc
  rw [dif_pos hex]
  exact hex.choose_spec

/-- `R` is self-adjoint with `0 ≤ R ≤ 1`. -/
structure UnitOp (R : H →L[ℝ] H) : Prop where
  selfAdjoint : IsSelfAdjoint R
  nonneg : ∀ x, 0 ≤ inner ℝ (R x) x
  le_one : ∀ x, inner ℝ (R x) x ≤ inner ℝ x x

lemma isPositive_cx {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) (h : ∀ x, 0 ≤ inner ℝ (T x) x) :
    (cx T).IsPositive := by
  refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (isSelfAdjoint_cx hT),
    fun v => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_complex, inner_re]
  have := h v.re
  have := h v.im
  simp only [re_cx, im_cx]
  linarith

lemma UnitOp.spectrum_subset {R : H →L[ℝ] H} (hR : UnitOp R) :
    spectrum ℝ (cx R) ⊆ Set.Icc 0 1 := by
  have h0 := (isPositive_cx hR.selfAdjoint hR.nonneg).spectrumRestricts
  have hsa1 : IsSelfAdjoint (1 - R) := (IsSelfAdjoint.one _).sub hR.selfAdjoint
  have h1 := (isPositive_cx hsa1 (fun x => by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_left,
      sub_nonneg]
    exact hR.le_one x)).spectrumRestricts
  rw [SpectrumRestricts.nnreal_iff] at h0 h1
  intro x hx
  refine ⟨h0 x hx, ?_⟩
  have : 1 - x ∈ spectrum ℝ (cx (1 - R)) := by
    rw [cx_sub, cx_one]
    have hmem : 1 - x ∈ ({1} : Set ℝ) - spectrum ℝ (cx R) := ⟨1, rfl, x, hx, rfl⟩
    rw [spectrum.singleton_sub_eq, map_one] at hmem
    exact hmem
  have := h1 _ this
  linarith

section API

variable {R : H →L[ℝ] H} (hR : UnitOp R)
include hR

lemma UnitOp.cx_sa : IsSelfAdjoint (cx R) := isSelfAdjoint_cx hR.selfAdjoint

lemma UnitOp.rcfc_id : rcfc id R = R := by
  apply cx_injective
  rw [cx_rcfc]
  exact cfc_id ℝ (cx R) hR.cx_sa

lemma UnitOp.rcfc_const (c : ℝ) : rcfc (fun _ => c) R = c • (1 : H →L[ℝ] H) := by
  apply cx_injective
  rw [cx_rcfc, cx_smul, cx_one, cfc_const c (cx R) hR.cx_sa]
  rw [Algebra.algebraMap_eq_smul_one]

lemma UnitOp.rcfc_one : rcfc (fun _ => (1 : ℝ)) R = 1 := by
  rw [hR.rcfc_const, one_smul]

lemma UnitOp.rcfc_add {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hg : ContinuousOn g (Set.Icc 0 1)) :
    rcfc (fun x => f x + g x) R = rcfc f R + rcfc g R := by
  apply cx_injective
  rw [cx_add, cx_rcfc, cx_rcfc, cx_rcfc]
  have ha := hR.cx_sa
  exact cfc_add (cx R) f g (hf.mono hR.spectrum_subset) (hg.mono hR.spectrum_subset)

lemma UnitOp.rcfc_mul {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hg : ContinuousOn g (Set.Icc 0 1)) :
    rcfc (fun x => f x * g x) R = rcfc f R * rcfc g R := by
  apply cx_injective
  rw [cx_mul, cx_rcfc, cx_rcfc, cx_rcfc]
  have ha := hR.cx_sa
  exact cfc_mul f g (cx R) (hf.mono hR.spectrum_subset) (hg.mono hR.spectrum_subset)

lemma UnitOp.rcfc_smul (c : ℝ) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1)) :
    rcfc (fun x => c * f x) R = c • rcfc f R := by
  apply cx_injective
  rw [cx_smul, cx_rcfc, cx_rcfc]
  have ha := hR.cx_sa
  exact cfc_smul c f (cx R) (hf.mono hR.spectrum_subset)

lemma UnitOp.rcfc_congr {f g : ℝ → ℝ} (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = g x) :
    rcfc f R = rcfc g R := by
  apply cx_injective
  rw [cx_rcfc, cx_rcfc]
  exact cfc_congr' (fun x hx => h x (hR.spectrum_subset hx))

lemma UnitOp.norm_rcfc_le {f : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ c) : ‖rcfc f R‖ ≤ c := by
  rw [← norm_cx, cx_rcfc]
  have ha := hR.cx_sa
  exact norm_cfc_le hc (fun x hx => by
    rw [Real.norm_eq_abs]; exact h x (hR.spectrum_subset hx))

lemma UnitOp.isSelfAdjoint_rcfc (f : ℝ → ℝ) : IsSelfAdjoint (rcfc f R) := by
  have h : cx (star (rcfc f R)) = cx (rcfc f R) := by
    rw [← star_cx, cx_rcfc]
    have ha := hR.cx_sa
    exact (cfc_predicate f (cx R)).star_eq
  exact cx_injective h

lemma UnitOp.commute_rcfc (f g : ℝ → ℝ) : Commute (rcfc f R) (rcfc g R) := by
  apply cx_injective
  rw [cx_mul, cx_mul, cx_rcfc, cx_rcfc]
  exact cfc_commute_cfc f g (cx R)

lemma UnitOp.rcfc_inner_nonneg {f : ℝ → ℝ} (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x) (x : H) :
    0 ≤ inner ℝ (rcfc f R x) x := by
  have ha := hR.cx_sa
  have h : 0 ≤ cfc f (cx R) := cfc_nonneg (fun y hy => hf y (hR.spectrum_subset hy))
  have hp : (cx (rcfc f R)).IsPositive := by
    rw [cx_rcfc]
    have := (ContinuousLinearMap.le_def (f := 0) (g := cfc f (cx R))).mp h
    simpa using this
  have := hp.re_inner_nonneg_left (Cx.mk x 0)
  rw [RCLike.re_to_complex, inner_re] at this
  simpa using this

lemma UnitOp.rcfc_sub {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hg : ContinuousOn g (Set.Icc 0 1)) :
    rcfc (fun x => f x - g x) R = rcfc f R - rcfc g R := by
  apply cx_injective
  rw [cx_sub, cx_rcfc, cx_rcfc, cx_rcfc]
  have ha := hR.cx_sa
  exact cfc_sub (a := cx R) (f := f) (g := g) (hf.mono hR.spectrum_subset) (hg.mono hR.spectrum_subset)

lemma UnitOp.rcfc_pow {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1)) (n : ℕ) :
    rcfc (fun x => f x ^ n) R = rcfc f R ^ n := by
  induction n with
  | zero => simpa using hR.rcfc_one
  | succ n ih =>
    have h1 : ContinuousOn (fun x => f x ^ n) (Set.Icc 0 1) := hf.pow n
    have := hR.rcfc_mul h1 hf
    simp only [pow_succ]
    rw [this, ih]

end API

end Calculus

end Cx

end CutoffRigidity.Riemann.Diff
