import Qschubert.CuspLower
import Mathlib.NumberTheory.Modular

/-!
# The modular group and coprime bottom rows

Stage E of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), part E1. `modGroup` is the image of `SL(2, ℤ)` in
`PGL(2, ℝ)`.

* `modQ : SL(2, ℤ) →* modGroup` is surjective, `modQ A • z = A • z`, and `modQ A = modQ B` iff `A = ±B`
  (`modQ_eq`, `modQ_neg`).
* `NPair`: coprime pairs `(c, d)` with `c > 0`, or `(0, 1)`; these are the bottom rows up to sign.
* `npMap : NPair × ℤ → modGroup`, `(p, n) ↦ modQ (T^n σ(p))` with `σ(p)` a matrix with bottom row `p`, is a bijection
  (`npMap_bijective`): the cosets of the translations `z ↦ z + n` in `PSL(2, ℤ)` are parametrized by `NPair`.
-/

namespace Qschubert

open Matrix UpperHalfPlane ModularGroup
open scoped MatrixGroups

/-- `SL(2, ℤ) → PSL(2, ℤ) ⊆ PGL(2, ℝ)`. -/
noncomputable def modQ : SL(2, ℤ) →* modGroup :=
  (SpecialLinearGroup.toPGL.comp (SpecialLinearGroup.map (Int.castRingHom ℝ))).codRestrict modGroup
    fun A => Subgroup.mem_map_of_mem _ ⟨A, rfl⟩

lemma modQ_coe (A : SL(2, ℤ)) :
    ((modQ A : modGroup) : PGL(2, ℝ)) = SpecialLinearGroup.toPGL (SpecialLinearGroup.map (Int.castRingHom ℝ) A) := rfl

lemma modQ_smul (A : SL(2, ℤ)) (z : ℍ) : modQ A • z = A • z := by
  show SpecialLinearGroup.toPGL (SpecialLinearGroup.map (Int.castRingHom ℝ) A) • z = A • z
  rw [toPGL_smul]
  rfl

lemma modQ_surjective : Function.Surjective modQ := by
  rintro ⟨γ, hγ⟩
  obtain ⟨g, ⟨A, rfl⟩, rfl⟩ := hγ
  exact ⟨A, rfl⟩

lemma neg_one_mem_center : (-1 : SL(2, ℝ)) ∈ Subgroup.center SL(2, ℝ) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by simp, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

lemma modQ_neg (A : SL(2, ℤ)) : modQ (-A) = modQ A := by
  apply Subtype.ext
  rw [modQ_coe, modQ_coe]
  have e : SpecialLinearGroup.map (Int.castRingHom ℝ) (-A) = -1 * SpecialLinearGroup.map (Int.castRingHom ℝ) A := by
    ext i j
    simp
  have hk : SpecialLinearGroup.toPGL (-1 : SL(2, ℝ)) = 1 := by
    rw [← MonoidHom.mem_ker, SpecialLinearGroup.toPGL_ker]
    exact neg_one_mem_center
  rw [e, map_mul, hk, one_mul]

/-- `modQ A = modQ B` only if `A = ±B`. -/
theorem modQ_eq {A B : SL(2, ℤ)} (h : modQ A = modQ B) : A = B ∨ A = -B := by
  set C : SL(2, ℤ) := A * B⁻¹ with hC
  have h1 : modQ C = 1 := by rw [hC, map_mul, map_inv, h, mul_inv_cancel]
  have h2 : SpecialLinearGroup.map (Int.castRingHom ℝ) C ∈ Subgroup.center SL(2, ℝ) := by
    rw [← SpecialLinearGroup.toPGL_ker, MonoidHom.mem_ker]
    exact congrArg Subtype.val h1
  obtain ⟨r, hr, hs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h2
  have hr2 : r = 1 ∨ r = -1 := by
    have h3 : r ^ 2 = 1 := by simpa using hr
    exact sq_eq_one_iff.1 h3
  have h00 : ((C 0 0 : ℤ) : ℝ) = r := by
    have := congrFun (congrFun hs 0) 0
    simpa [Matrix.scalar_apply] using this.symm
  have h01 : ((C 0 1 : ℤ) : ℝ) = 0 := by
    have := congrFun (congrFun hs 0) 1
    simpa [Matrix.scalar_apply] using this.symm
  have h10 : ((C 1 0 : ℤ) : ℝ) = 0 := by
    have := congrFun (congrFun hs 1) 0
    simpa [Matrix.scalar_apply] using this.symm
  have h11 : ((C 1 1 : ℤ) : ℝ) = r := by
    have := congrFun (congrFun hs 1) 1
    simpa [Matrix.scalar_apply] using this.symm
  have e01 : C 0 1 = 0 := by exact_mod_cast h01
  have e10 : C 1 0 = 0 := by exact_mod_cast h10
  have hA : A = C * B := by rw [hC, inv_mul_cancel_right]
  rcases hr2 with h | h
  · left
    have e00 : C 0 0 = 1 := by rw [h] at h00; exact_mod_cast h00
    have e11 : C 1 1 = 1 := by rw [h] at h11; exact_mod_cast h11
    have hC1 : C = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11]
    rw [hA, hC1, one_mul]
  · right
    have e00 : C 0 0 = -1 := by rw [h] at h00; exact_mod_cast h00
    have e11 : C 1 1 = -1 := by rw [h] at h11; exact_mod_cast h11
    have hC1 : C = -1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11]
    rw [hA, hC1, neg_one_mul]

/-- Coprime pairs `(c, d)` with `c > 0`, or `(0, 1)`: the bottom rows of `SL(2, ℤ)` up to sign. -/
def NPair : Type := {p : Fin 2 → ℤ // IsCoprime (p 0) (p 1) ∧ (0 < p 0 ∨ (p 0 = 0 ∧ p 1 = 1))}

lemma exists_sl_row (p : NPair) : ∃ A : SL(2, ℤ), (A : Matrix (Fin 2) (Fin 2) ℤ) 1 = p.1 := by
  obtain ⟨A, -, hA⟩ := ModularGroup.bottom_row_surj (R := ℤ)
    (show p.1 ∈ {cd : Fin 2 → ℤ | IsCoprime (cd 0) (cd 1)} from p.2.1)
  exact ⟨A, hA⟩

/-- A matrix with bottom row `p`. -/
noncomputable def npSec (p : NPair) : SL(2, ℤ) := (exists_sl_row p).choose

lemma npSec_row (p : NPair) : (npSec p : Matrix (Fin 2) (Fin 2) ℤ) 1 = p.1 := (exists_sl_row p).choose_spec

lemma row_T_zpow_mul (n : ℤ) (A : SL(2, ℤ)) :
    ((T ^ n * A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 = (A : Matrix (Fin 2) (Fin 2) ℤ) 1 := by
  funext j
  simp

lemma row_neg_T_zpow_mul (n : ℤ) (A : SL(2, ℤ)) :
    ((-(T ^ n * A) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 = -(A : Matrix (Fin 2) (Fin 2) ℤ) 1 := by
  funext j
  have e := congrFun (row_T_zpow_mul n A) j
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Pi.neg_apply, e]

/-- `(p, n) ↦` the class of `T^n σ(p)`. -/
noncomputable def npMap (pn : NPair × ℤ) : modGroup := modQ (T ^ pn.2 * npSec pn.1)

lemma npMap_injective : Function.Injective npMap := by
  rintro ⟨p, n⟩ ⟨p', m⟩ h
  have h1 : T ^ n * npSec p = T ^ m * npSec p' ∨ T ^ n * npSec p = -(T ^ m * npSec p') := modQ_eq h
  have hrow : p.1 = p'.1 ∨ p.1 = -p'.1 := by
    rcases h1 with h1 | h1
    · left
      have h2 := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 1) h1
      simp only [row_T_zpow_mul, npSec_row] at h2
      exact h2
    · right
      have h2 := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 1) h1
      simp only [row_T_zpow_mul, row_neg_T_zpow_mul, npSec_row] at h2
      exact h2
  have hneg : ∀ q q' : NPair, q.1 = -q'.1 → False := by
    intro q q' h2
    have e0 : q.1 0 = -(q'.1 0) := by rw [h2]; rfl
    have e1 : q.1 1 = -(q'.1 1) := by rw [h2]; rfl
    rcases q.2.2 with hc | ⟨hc, hd⟩ <;> rcases q'.2.2 with hc' | ⟨hc', hd'⟩ <;> omega
  have hp : p = p' := by
    rcases hrow with h2 | h2
    · exact Subtype.ext h2
    · exact (hneg p p' h2).elim
  subst hp
  have h3 : T ^ n * npSec p = T ^ m * npSec p := by
    rcases h1 with h1 | h1
    · exact h1
    · exfalso
      have h2 := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 1) h1
      simp only [row_T_zpow_mul, row_neg_T_zpow_mul, npSec_row] at h2
      exact hneg p p h2
  have h4 : T ^ n = T ^ m := mul_right_cancel h3
  have h5 := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1) h4
  simp only [coe_T_zpow] at h5
  have h6 : n = m := by simpa using h5
  rw [h6]

lemma npMap_surjective : Function.Surjective npMap := by
  intro γ
  obtain ⟨A₀, rfl⟩ := modQ_surjective γ
  obtain ⟨A, hA, hnorm⟩ : ∃ A : SL(2, ℤ), modQ A = modQ A₀ ∧ (0 < A 1 0 ∨ (A 1 0 = 0 ∧ A 1 1 = 1)) := by
    have hcop := ModularGroup.bottom_row_coprime A₀
    rcases lt_trichotomy (A₀ 1 0) 0 with h | h | h
    · refine ⟨-A₀, modQ_neg A₀, Or.inl ?_⟩
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
      omega
    · have hd : A₀ 1 1 = 1 ∨ A₀ 1 1 = -1 := by
        rw [h] at hcop
        exact Int.isUnit_iff.1 (isCoprime_zero_left.1 hcop)
      rcases hd with hd | hd
      · exact ⟨A₀, rfl, Or.inr ⟨h, hd⟩⟩
      · refine ⟨-A₀, modQ_neg A₀, Or.inr ⟨?_, ?_⟩⟩
        · simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
          omega
        · simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
          omega
    · exact ⟨A₀, rfl, Or.inl h⟩
  set p : NPair := ⟨(A : Matrix (Fin 2) (Fin 2) ℤ) 1, ModularGroup.bottom_row_coprime A, hnorm⟩ with hp
  set B : SL(2, ℤ) := A * (npSec p)⁻¹ with hB
  have hS : ∀ k, (npSec p : Matrix (Fin 2) (Fin 2) ℤ) 1 k = A 1 k := fun k => congrFun (npSec_row p) k
  have hBj : ∀ j, B 1 j = (1 : Matrix (Fin 2) (Fin 2) ℤ) 1 j := by
    intro j
    have h1 : ((npSec p * (npSec p)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 j
        = (1 : Matrix (Fin 2) (Fin 2) ℤ) 1 j := by
      rw [mul_inv_cancel]
      rfl
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h1
    show ((A * (npSec p)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 j = _
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ← hS 0, ← hS 1]
    exact h1
  have hB10 : B 1 0 = 0 := by simpa using hBj 0
  have hB11 : B 1 1 = 1 := by simpa using hBj 1
  have hdet : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    have := B.det_coe
    rwa [Matrix.det_fin_two] at this
  have hB00 : B 0 0 = 1 := by
    rw [hB10, hB11] at hdet
    simpa using hdet
  have hBT : B = T ^ (B 0 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_T_zpow, hB00, hB10, hB11]
  refine ⟨(p, B 0 1), ?_⟩
  show modQ (T ^ (B 0 1) * npSec p) = modQ A₀
  rw [← hBT, hB, inv_mul_cancel_right, hA]

theorem npMap_bijective : Function.Bijective npMap := ⟨npMap_injective, npMap_surjective⟩

/-- **The sum over `PSL(2, ℤ)` as a sum over bottom rows and translations.** -/
theorem tsum_modGroup_smul (U : ℍ → ℂ) (z : ℍ) :
    ∑' γ : modGroup, U (γ • z) = ∑' pn : NPair × ℤ, U ((T ^ pn.2 * npSec pn.1) • z) := by
  rw [← (Equiv.ofBijective npMap npMap_bijective).tsum_eq]
  refine tsum_congr fun pn => ?_
  show U (npMap pn • z) = _
  rw [npMap, modQ_smul]

end Qschubert
