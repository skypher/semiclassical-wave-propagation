import Qschubert.Statements
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Every boundary point is `g • ∞` with `g` fixing the base point (BND-1, part (a))

Obligation BND-1 of `lean/BLUEPRINT.md` (S5, R39). `∂ℍ = ℝ ∪ {∞}` is `OnePoint ℝ` with Mathlib's
`GL(2, ℝ)` action. For every `x₀ ∈ ℍ` and `b ∈ ∂ℍ` there is `g ∈ SL(2, ℝ)` with `g • x₀ = x₀` and
`g • ∞ = b` (`exists_stab_smul_infty`): conjugate a rotation about `i` by `z ↦ q z + p`
(`x₀ = p + iq`). So the statements of `Qschubert/Statements.lean`, which quantify over such `g`,
cover every boundary point.
-/

namespace Qschubert

open Matrix UpperHalfPlane
open scoped MatrixGroups OnePoint

/-- The rotation about `i` with `k • ∞ = r`: entries `c = r/√(1+r²)`, `s = -1/√(1+r²)`. -/
noncomputable def rotI (r : ℝ) : SL(2, ℝ) :=
  ⟨!![r / √(1 + r ^ 2), -1 / √(1 + r ^ 2); 1 / √(1 + r ^ 2), r / √(1 + r ^ 2)], by
    have h : 0 < 1 + r ^ 2 := by positivity
    rw [Matrix.det_fin_two_of]
    field_simp
    rw [Real.sq_sqrt h.le]
    ring⟩

/-- The map `z ↦ q z + p` for `x₀ = p + iq`. -/
noncomputable def transH (x₀ : ℍ) : SL(2, ℝ) :=
  ⟨!![√x₀.im, x₀.re / √x₀.im; 0, 1 / √x₀.im], by
    have h : 0 < √x₀.im := Real.sqrt_pos.2 x₀.im_pos
    rw [Matrix.det_fin_two_of]
    field_simp
    ring⟩

lemma rotI_smul_I (r : ℝ) : rotI r • I = I := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply]
  have h : 0 < √(1 + r ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hd : ((1 / √(1 + r ^ 2) : ℝ) : ℂ) * Complex.I + ((r / √(1 + r ^ 2) : ℝ) : ℂ) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    exact h.ne' this
  simp only [rotI, Algebra.algebraMap_self, RingHom.id_apply, coe_I]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [div_eq_iff (by simpa using hd)]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

lemma transH_smul_I (x₀ : ℍ) : transH x₀ • I = x₀ := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply]
  have h : 0 < √x₀.im := Real.sqrt_pos.2 x₀.im_pos
  have hq : (√x₀.im : ℂ) ≠ 0 := by exact_mod_cast h.ne'
  simp only [transH, Algebra.algebraMap_self, RingHom.id_apply, coe_I]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  field_simp
  have hsq : (√x₀.im : ℂ) ^ 2 = (x₀.im : ℂ) := by exact_mod_cast Real.sq_sqrt x₀.im_pos.le
  rw [hsq]
  simp only [mul_zero, zero_add, one_mul]
  apply Complex.ext <;> simp

lemma rotI_smul_infty (r : ℝ) :
    SpecialLinearGroup.toGL (rotI r) • (∞ : OnePoint ℝ) = (r : OnePoint ℝ) := by
  rw [OnePoint.smul_infty_eq_ite]
  have h : 0 < √(1 + r ^ 2) := Real.sqrt_pos.2 (by positivity)
  have h10 : (SpecialLinearGroup.toGL (rotI r) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 1 / √(1 + r ^ 2) := rfl
  have h00 : (SpecialLinearGroup.toGL (rotI r) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = r / √(1 + r ^ 2) := rfl
  rw [h10, h00, ite_eq_right (by positivity)]
  congr 1
  field_simp

lemma transH_smul_infty (x₀ : ℍ) :
    SpecialLinearGroup.toGL (transH x₀) • (∞ : OnePoint ℝ) = ∞ := by
  rw [OnePoint.smul_infty_eq_self_iff]
  rfl

/-- **BND-1 (a)**: every boundary point is `g • ∞` with `g ∈ SL(2, ℝ)` fixing `x₀`. -/
theorem exists_stab_smul_infty (x₀ : ℍ) (b : OnePoint ℝ) :
    ∃ g : SL(2, ℝ), g • x₀ = x₀ ∧ SpecialLinearGroup.toGL g • (∞ : OnePoint ℝ) = b := by
  set h := transH x₀ with hh
  set b' := (SpecialLinearGroup.toGL h)⁻¹ • b with hb'
  have hb : b = SpecialLinearGroup.toGL h • b' := by rw [hb', smul_inv_smul]
  have hhinf : (SpecialLinearGroup.toGL h)⁻¹ • (∞ : OnePoint ℝ) = ∞ := by
    rw [inv_smul_eq_iff, transH_smul_infty]
  have hx : h⁻¹ • x₀ = I := by rw [inv_smul_eq_iff, transH_smul_I]
  by_cases hinf : b' = ∞
  · refine ⟨1, one_smul _ _, ?_⟩
    rw [map_one, one_smul, hb, hinf, transH_smul_infty]
  · obtain ⟨r, hr⟩ := OnePoint.ne_infty_iff_exists.1 hinf
    refine ⟨h * rotI r * h⁻¹, ?_, ?_⟩
    · rw [mul_smul, mul_smul, hx, rotI_smul_I, transH_smul_I]
    · rw [map_mul, map_mul, mul_smul, mul_smul, map_inv, hhinf, rotI_smul_infty, hr, ← hb]

/-- An element of `SL(2, ℝ)` fixing `x₀ ∈ ℍ` and `∞` acts trivially on `ℍ` (it is `±1`). -/
lemma smul_eq_self_of_fix (k : SL(2, ℝ)) {x₀ : ℍ} (hx : k • x₀ = x₀)
    (hinf : SpecialLinearGroup.toGL k • (∞ : OnePoint ℝ) = ∞) (z : ℍ) : k • z = z := by
  have h10 : (k : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := OnePoint.smul_infty_eq_self_iff.1 hinf
  have hdet : (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * k 1 1 = 1 := by
    have := k.2; rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at this; exact this
  have h11 : (k : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  have hx' := congrArg UpperHalfPlane.coe hx
  rw [coe_specialLinearGroup_apply] at hx'
  simp only [Algebra.algebraMap_self, RingHom.id_apply, h10, Complex.ofReal_zero, zero_mul,
    zero_add] at hx'
  rw [div_eq_iff (by exact_mod_cast h11)] at hx'
  have him := congrArg Complex.im hx'
  have hre := congrArg Complex.re hx'
  simp at him hre
  have hq := x₀.im_pos
  have hdiag : (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = k 1 1 := by
    have : ((k : Matrix (Fin 2) (Fin 2) ℝ) 0 0 - k 1 1) * x₀.im = 0 := by
      simp only [UpperHalfPlane.im] at him ⊢; linarith
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hq.ne')
  have h01 : (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by
    simp only [UpperHalfPlane.re] at hre ⊢
    rw [hdiag] at hre; linarith
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, h10, h01, hdiag, Complex.ofReal_zero,
    zero_mul, zero_add, add_zero]
  have h11' : ((k : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) ≠ 0 := by exact_mod_cast h11
  field_simp

/-- **BND-1 (b)**: two elements of `SL(2, ℝ)` fixing `x₀` with the same `g • ∞` act identically on
`ℍ`; so `initState` and `approxSolB` depend only on the boundary point `b = g • ∞`. -/
theorem smul_eq_of_stab_of_smul_infty {g g' : SL(2, ℝ)} {x₀ : ℍ} (hg : g • x₀ = x₀)
    (hg' : g' • x₀ = x₀)
    (hb : SpecialLinearGroup.toGL g • (∞ : OnePoint ℝ) = SpecialLinearGroup.toGL g' • ∞)
    (z : ℍ) : g • z = g' • z := by
  have hk : (g⁻¹ * g') • x₀ = x₀ := by rw [mul_smul, hg', inv_smul_eq_iff, hg]
  have hkinf : SpecialLinearGroup.toGL (g⁻¹ * g') • (∞ : OnePoint ℝ) = ∞ := by
    rw [map_mul, mul_smul, ← hb, map_inv, inv_smul_smul]
  have := smul_eq_self_of_fix (g⁻¹ * g') hk hkinf z
  rw [mul_smul, inv_smul_eq_iff] at this
  exact this.symm

theorem initState_eq_of_stab {g g' : SL(2, ℝ)} {x₀ : ℍ} (hg : g • x₀ = x₀) (hg' : g' • x₀ = x₀)
    (hb : SpecialLinearGroup.toGL g • (∞ : OnePoint ℝ) = SpecialLinearGroup.toGL g' • ∞)
    (ħ' : ℝ) (a : ℍ → ℂ) : initState g ħ' a = initState g' ħ' a := by
  have hinv : ∀ z : ℍ, g⁻¹ • z = g'⁻¹ • z := fun z => by
    rw [inv_smul_eq_iff, smul_eq_of_stab_of_smul_infty hg hg' hb, smul_inv_smul]
  funext z
  simp only [initState, phaseB, hinv]

theorem approxSolB_eq_of_stab {g g' : SL(2, ℝ)} {x₀ : ℍ} (hg : g • x₀ = x₀) (hg' : g' • x₀ = x₀)
    (hb : SpecialLinearGroup.toGL g • (∞ : OnePoint ℝ) = SpecialLinearGroup.toGL g' • ∞)
    (K : ℕ) (ħ' t : ℝ) (a : ℍ → ℂ) : approxSolB g K ħ' t a = approxSolB g' K ħ' t a := by
  have hinv : ∀ z : ℍ, g⁻¹ • z = g'⁻¹ • z := fun z => by
    rw [inv_smul_eq_iff, smul_eq_of_stab_of_smul_infty hg hg' hb, smul_inv_smul]
  have hfun : (fun w => a (g • w)) = fun w => a (g' • w) := by
    funext w; rw [smul_eq_of_stab_of_smul_infty hg hg' hb]
  funext z
  simp only [approxSolB, hinv, hfun]

end Qschubert
