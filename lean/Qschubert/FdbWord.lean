import Qschubert.FdbFun
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Words of `X`, `Y` applied to `X₀^{-β}`: the polynomial form

For a word `S = [Z₁, …, Z_j]` (`true = X = y∂ₓ`, `false = Y = y∂_y`), `wordR S F = Z₁(⋯(Z_j F))`.
With `ξ = xiF`, `υ = upF`, `h = hF = X₀^{-1}` and the derivations

  `D_X P = (υ - ξ²)∂_ξP - ξυ ∂_υP - βξ P`,  `D_Y P = (ξ - ξυ)∂_ξP + (2υ - υ²)∂_υP - β(υ - 1)P`

on `ℝ[ξ, υ]`, and `P_S` defined by `P_[] = 1`, `P_{Z::S} = D_Z P_S` (`PS`):

  `wordR S (h^β) = h^β · P_S(ξ, υ)` on `ℍ`  (`wordR_hpow`),

i.e. `X₀^β Z_S X₀^{-β} = P_S(ξ, υ)`. The proof uses the chain rule for polynomial evaluation along
`(ξ, υ)` (`hasFDerivAt_ev`) and the identities of `FdbFun`.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology MvPolynomial
open scoped ContDiff

/-- Polynomials in `ξ` (variable `0`) and `υ` (variable `1`). -/
abbrev P2 := MvPolynomial (Fin 2) ℝ

/-- `P(a, b)`. -/
noncomputable def ev (P : P2) (a b : ℝ) : ℝ := eval ![a, b] P

/-- The direction of a letter: `true ↦ 1` (`X`), `false ↦ i` (`Y`). -/
noncomputable def letter (z : Bool) : ℂ := if z then 1 else Complex.I

/-- `wordR [Z₁, …, Z_j] F = Z₁(⋯(Z_j F))`. -/
noncomputable def wordR : List Bool → (ℂ → ℝ) → (ℂ → ℝ)
  | [], F => F
  | z :: S, F => vfR (letter z) (wordR S F)

/-- `D_X`. -/
noncomputable def DX (β : ℝ) (P : P2) : P2 :=
  (X 1 - X 0 ^ 2) * pderiv 0 P - X 0 * X 1 * pderiv 1 P - C β * X 0 * P

/-- `D_Y`. -/
noncomputable def DY (β : ℝ) (P : P2) : P2 :=
  (X 0 - X 0 * X 1) * pderiv 0 P + (C 2 * X 1 - X 1 ^ 2) * pderiv 1 P - C β * (X 1 - 1) * P

/-- `D_Z`. -/
noncomputable def DZ (β : ℝ) (z : Bool) : P2 → P2 := if z then DX β else DY β

/-- `P_S`. -/
noncomputable def PS (β : ℝ) : List Bool → P2
  | [] => 1
  | z :: S => DZ β z (PS β S)

/-! ### Calculus for `vfR` -/

lemma vfR_congr {F G : ℂ → ℝ} {w : ℂ} (h : F =ᶠ[𝓝 w] G) (v : ℂ) : vfR v F w = vfR v G w := by
  simp only [vfR, h.fderiv_eq]

lemma vfR_of_hasFDerivAt {F : ℂ → ℝ} {F' : ℂ →L[ℝ] ℝ} {w : ℂ} (h : HasFDerivAt F F' w) (v : ℂ) :
    vfR v F w = w.im * F' v := by
  simp only [vfR, h.fderiv]

lemma ev_X0 (P : P2) (a b : ℝ) : ev (P * X 0) a b = ev P a b * a := by
  simp [ev]

lemma ev_X1 (P : P2) (a b : ℝ) : ev (P * X 1) a b = ev P a b * b := by
  simp [ev]

/-- **The chain rule for polynomial evaluation along `(ξ, υ)`.** -/
theorem hasFDerivAt_ev (P : P2) (w : ℂ) :
    HasFDerivAt (fun u => ev P (xiF u) (upF u))
      (ev (pderiv 0 P) (xiF w) (upF w) • fderiv ℝ xiF w
        + ev (pderiv 1 P) (xiF w) (upF w) • fderiv ℝ upF w) w := by
  have hx : HasFDerivAt xiF (fderiv ℝ xiF w) w :=
    ((contDiff_xiF.differentiable (by simp)) w).hasFDerivAt
  have hu : HasFDerivAt upF (fderiv ℝ upF w) w :=
    ((contDiff_upF.differentiable (by simp)) w).hasFDerivAt
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [ev, eval_C, pderiv_C, map_zero, zero_smul, add_zero]
    exact hasFDerivAt_const a w
  | add p q hp hq =>
    have h := hp.add hq
    simp only [ev, map_add] at h ⊢
    convert h using 1
    rw [add_smul, add_smul]; abel
  | mul_X p n hp =>
    have hn : n = 0 ∨ n = 1 := by fin_cases n <;> simp
    rcases hn with rfl | rfl
    · have h := hp.fun_mul hx
      have e : (fun u => ev (p * X 0) (xiF u) (upF u)) = fun u => ev p (xiF u) (upF u) * xiF u := by
        funext u; exact ev_X0 p _ _
      rw [e]
      refine h.congr_fderiv ?_
      simp only [pderiv_mul, pderiv_X, ev, map_add, map_mul, eval_X]
      simp [Pi.single_apply, add_smul, mul_smul, smul_add]
      module
    · have h := hp.fun_mul hu
      have e : (fun u => ev (p * X 1) (xiF u) (upF u)) = fun u => ev p (xiF u) (upF u) * upF u := by
        funext u; exact ev_X1 p _ _
      rw [e]
      refine h.congr_fderiv ?_
      simp only [pderiv_mul, pderiv_X, ev, map_add, map_mul, eval_X]
      simp [Pi.single_apply, add_smul, mul_smul, smul_add]
      module

/-- `Z P(ξ, υ) = ∂_ξP · Zξ + ∂_υP · Zυ`. -/
lemma vfR_ev (P : P2) (v w : ℂ) :
    vfR v (fun u => ev P (xiF u) (upF u)) w
      = ev (pderiv 0 P) (xiF w) (upF w) * vfR v xiF w + ev (pderiv 1 P) (xiF w) (upF w) * vfR v upF w := by
  rw [vfR_of_hasFDerivAt (hasFDerivAt_ev P w)]
  simp only [vfR, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- `Z (h^β) = β h^{β-1} Z h` where `h > 0`. -/
lemma hasFDerivAt_hpow (β : ℝ) {w : ℂ} (hw : 0 < w.im) :
    HasFDerivAt (fun u => hF u ^ β) ((β * hF w ^ (β - 1)) • fderiv ℝ hF w) w := by
  have hh : HasFDerivAt hF (fderiv ℝ hF w) w := ((contDiff_hF.differentiable (by simp)) w).hasFDerivAt
  exact (Real.hasDerivAt_rpow_const (Or.inl (hF_pos hw).ne')).comp_hasFDerivAt w hh

lemma ev_DX (β : ℝ) (P : P2) (a b : ℝ) :
    ev (DX β P) a b = (b - a ^ 2) * ev (pderiv 0 P) a b - a * b * ev (pderiv 1 P) a b - β * a * ev P a b := by
  simp [DX, ev]

lemma ev_DY (β : ℝ) (P : P2) (a b : ℝ) :
    ev (DY β P) a b = (a - a * b) * ev (pderiv 0 P) a b + (2 * b - b ^ 2) * ev (pderiv 1 P) a b
      - β * (b - 1) * ev P a b := by
  simp [DY, ev]

/-- **`Z_S(h^β) = h^β P_S(ξ, υ)` on `ℍ`.** -/
theorem wordR_hpow (β : ℝ) (S : List Bool) {w : ℂ} (hw : 0 < w.im) :
    wordR S (fun u => hF u ^ β) w = hF w ^ β * ev (PS β S) (xiF w) (upF w) := by
  induction S generalizing w with
  | nil => simp [wordR, PS, ev]
  | cons z S ih =>
    have hev : wordR S (fun u => hF u ^ β) =ᶠ[𝓝 w]
        fun u => hF u ^ β * ev (PS β S) (xiF u) (upF u) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hw] with u hu
      exact ih hu
    have hG := (hasFDerivAt_hpow β hw).fun_mul (hasFDerivAt_ev (PS β S) w)
    show vfR (letter z) (wordR S (fun u => hF u ^ β)) w = _
    rw [vfR_congr hev, vfR_of_hasFDerivAt hG]
    have hh := hF_pos hw
    have hpow : hF w ^ (β - 1) * hF w = hF w ^ β := by
      rw [Real.rpow_sub_one hh.ne', div_mul_cancel₀ _ hh.ne']
    have e0 : ∀ v, w.im * fderiv ℝ xiF w v = vfR v xiF w := fun v => rfl
    have e1 : ∀ v, w.im * fderiv ℝ upF w v = vfR v upF w := fun v => rfl
    have e2 : ∀ v, w.im * fderiv ℝ hF w v = vfR v hF w := fun v => rfl
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    cases z
    · simp only [PS, DZ, letter, Bool.false_eq_true, ite_false]
      have a0 := e0 Complex.I; have a1 := e1 Complex.I; have a2 := e2 Complex.I
      rw [vfR_xiF_I] at a0; rw [vfR_upF_I] at a1; rw [vfR_hF_I] at a2
      rw [ev_DY]
      linear_combination (hF w ^ β * ev (pderiv 0 (PS β S)) (xiF w) (upF w)) * a0
        + (hF w ^ β * ev (pderiv 1 (PS β S)) (xiF w) (upF w)) * a1
        + (β * hF w ^ (β - 1) * ev (PS β S) (xiF w) (upF w)) * a2
        + (β * ev (PS β S) (xiF w) (upF w) * (1 - upF w)) * hpow
    · simp only [PS, DZ, letter, ite_true]
      have a0 := e0 1; have a1 := e1 1; have a2 := e2 1
      rw [vfR_xiF_one] at a0; rw [vfR_upF_one] at a1; rw [vfR_hF_one] at a2
      rw [ev_DX]
      linear_combination (hF w ^ β * ev (pderiv 0 (PS β S)) (xiF w) (upF w)) * a0
        + (hF w ^ β * ev (pderiv 1 (PS β S)) (xiF w) (upF w)) * a1
        + (β * hF w ^ (β - 1) * ev (PS β S) (xiF w) (upF w)) * a2
        + (-(β * ev (PS β S) (xiF w) (upF w) * xiF w)) * hpow

end Qschubert
