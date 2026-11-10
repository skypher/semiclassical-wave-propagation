import Qschubert.EllipticId
import Qschubert.MollGen

/-!
# Weak identities for `u ∈ Dom(-Δ)` and the localized Laplacian

For `u` in the domain of `-Δ` (`negLapH`), `v = -Δu`, and its form-space lift `ℓ = ι*(u + v)`
(`liftDom`, `ι ℓ = u`), put `Xu = X ℓ`, `Yu = Y ℓ` (`FormOps.lean`). Against test functions `P`:
* `⟪ΔP, u⟫ = -⟪P, v⟫` (`inner_lapTest_dom`),
* `⟪XP, u⟫ = -⟪P, Xu⟫`, `⟪YP, u⟫ = -⟪P, Yu⟫ + ⟪P, u⟫` (`inner_vf_dom`),
and with the product rules for `X`, `Y`, `Δ` on test functions, for every test function `χ`
(`inner_local_lap`):
`⟪χ ΔP, u⟫ = -⟪χ P, v⟫ + 2⟪(Xχ) P, Xu⟫ + 2⟪(Yχ) P, Yu⟫ + ⟪(Δχ) P, u⟫`,
for REAL `χ` (with `P = conj φ`) the weak form of `Δ(χu) = χΔu + 2(XχXu + YχYu) + (Δχ)u`
(R67's localization); for complex `χ` the inner product conjugates `χ`, `Xχ`, `Yχ`, `Δχ` (R70).
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology Physicslib4.Spectral.Unbounded
open scoped ContDiff ComplexConjugate InnerProductSpace

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)

/-- The form-space lift of `u ∈ Dom(-Δ)`: `ι*(u + (-Δ)u)`. -/
noncomputable def liftDom (u : negLapH.domain) : FormSpace negLap := formLift ((u : L2H) + negLapH u)

theorem formIncl_liftDom (u : negLapH.domain) : formIncl negLap (liftDom u) = u := by
  obtain ⟨g, hg⟩ := u.2
  have heq : u = resEquiv negLap negLap_hasDenseDomain g := Subtype.ext hg.symm
  have hS : negLapH u = g - formRes negLap g := by
    rw [heq]; exact friedrichsExt_apply negLap negLap_hasDenseDomain g
  have hg' : formRes negLap g = (u : L2H) := hg
  show formRes negLap ((u : L2H) + negLapH u) = u
  rw [hS, ← hg', add_sub_cancel]

/-- `Xu`, `Yu` for `u ∈ Dom(-Δ)`. -/
noncomputable def domX (u : negLapH.domain) : L2H := formVec 1 (Or.inl rfl) (liftDom u)
noncomputable def domY (u : negLapH.domain) : L2H := formVec Complex.I (Or.inr rfl) (liftDom u)

/-- `⟪P, y∂_v w⟫ = -⟪y∂_v P, ιw⟫ + v.im ⟪P, ιw⟫` on the form space. -/
lemma inner_toL2_formVec (v : ℂ) (hv : v = 1 ∨ v = Complex.I) (P : testFn) (w : FormSpace negLap) :
    inner ℂ (toL2 P) (formVec v hv w)
      = -inner ℂ (toL2 (vfTest v P)) (formIncl negLap w)
        + ((v.im : ℝ) : ℂ) * inner ℂ (toL2 P) (formIncl negLap w) := by
  refine UniformSpace.Completion.induction_on w ?_ ?_
  · exact isClosed_eq (continuous_const.inner (formVec v hv).continuous)
      (((continuous_const.inner (formIncl negLap).continuous).neg).add
        (continuous_const.mul (continuous_const.inner (formIncl negLap).continuous)))
  · intro x
    rw [formVec_coe, formIncl_coe, formDom_val_eq]
    set Q := toL2Equiv.symm (FormDom.toDom negLap x)
    show inner ℂ (toL2 P) (toL2 (vfTest v Q)) = -inner ℂ (toL2 (vfTest v P)) (toL2 Q)
      + ((v.im : ℝ) : ℂ) * inner ℂ (toL2 P) (toL2 Q)
    rw [inner_vf_left]
    ring

/-- `⟪XP, u⟫ = -⟪P, Xu⟫` and `⟪YP, u⟫ = -⟪P, Yu⟫ + ⟪P, u⟫`. -/
theorem inner_X_dom (P : testFn) (u : negLapH.domain) :
    inner ℂ (toL2 (vfTest 1 P)) u = -inner ℂ (toL2 P) (domX u) := by
  rw [domX, inner_toL2_formVec, formIncl_liftDom]; simp

theorem inner_Y_dom (P : testFn) (u : negLapH.domain) :
    inner ℂ (toL2 (vfTest Complex.I P)) u = -inner ℂ (toL2 P) (domY u) + inner ℂ (toL2 P) u := by
  rw [domY, inner_toL2_formVec, formIncl_liftDom]; simp

/-- The weak equation: `⟪ΔP, u⟫ = -⟪P, (-Δ)u⟫`. -/
theorem inner_lapTest_dom (P : testFn) (u : negLapH.domain) :
    inner ℂ (toL2 (lapTest P)) u = -inner ℂ (toL2 P) (negLapH u) := by
  have hP := toL2_mem_negLapH_domain P
  have hsymm := negLapH_isPositive.1 ⟨toL2 P, hP⟩ u
  rw [negLapH_toL2 P hP, inner_neg_left] at hsymm
  have h2 : inner ℂ (toL2 P) (negLapH u) = -inner ℂ (toL2 (lapTest P)) u := hsymm
  rw [h2, neg_neg]

/-! ### Products of test functions -/

/-- `c · P` for test functions `c, P`. -/
noncomputable def mulT (c P : testFn) : testFn :=
  ⟨fun w => (c : ℂ → ℂ) w * (P : ℂ → ℂ) w,
    isTestFn_mul_of_contDiffAt (fun _ _ => c.2.smooth.contDiffAt) P.2⟩

lemma mulT_coe (c P : testFn) (w : ℂ) :
    ((mulT c P : testFn) : ℂ → ℂ) w = (c : ℂ → ℂ) w * (P : ℂ → ℂ) w := rfl

/-- `y∂_v(cP) = (y∂_v c)P + c(y∂_v P)`. -/
lemma vf_mulT (v : ℂ) (c P : testFn) :
    vfTest v (mulT c P) = mulT (vfTest v c) P + mulT c (vfTest v P) := by
  apply Subtype.ext; funext w
  show ((w.im : ℝ) : ℂ) * fderiv ℝ (fun u => (c : ℂ → ℂ) u * (P : ℂ → ℂ) u) w v
    = ((w.im : ℝ) : ℂ) * fderiv ℝ (c : ℂ → ℂ) w v * (P : ℂ → ℂ) w
      + (c : ℂ → ℂ) w * (((w.im : ℝ) : ℂ) * fderiv ℝ (P : ℂ → ℂ) w v)
  have hc : DifferentiableAt ℝ (c : ℂ → ℂ) w := (c.2.smooth.differentiable (by simp)) w
  have hP : DifferentiableAt ℝ (P : ℂ → ℂ) w := (P.2.smooth.differentiable (by simp)) w
  have h : HasFDerivAt (fun u => (c : ℂ → ℂ) u * (P : ℂ → ℂ) u) _ w := hc.hasFDerivAt.mul hP.hasFDerivAt
  rw [h.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma mulT_add_left (a b P : testFn) : mulT (a + b) P = mulT a P + mulT b P := by
  apply Subtype.ext; funext w
  show ((a : ℂ → ℂ) w + (b : ℂ → ℂ) w) * (P : ℂ → ℂ) w = _
  rw [add_mul]; rfl

lemma mulT_sub_left (a b P : testFn) : mulT (a - b) P = mulT a P - mulT b P := by
  apply Subtype.ext; funext w
  show ((a : ℂ → ℂ) w - (b : ℂ → ℂ) w) * (P : ℂ → ℂ) w = _
  rw [sub_mul]; rfl

lemma mulT_add_right (c P Q : testFn) : mulT c (P + Q) = mulT c P + mulT c Q := by
  apply Subtype.ext; funext w
  show (c : ℂ → ℂ) w * ((P : ℂ → ℂ) w + (Q : ℂ → ℂ) w) = _
  rw [mul_add]; rfl

lemma mulT_sub_right (c P Q : testFn) : mulT c (P - Q) = mulT c P - mulT c Q := by
  apply Subtype.ext; funext w
  show (c : ℂ → ℂ) w * ((P : ℂ → ℂ) w - (Q : ℂ → ℂ) w) = _
  rw [mul_sub]; rfl

lemma mulT_smul_left (r : ℂ) (c P : testFn) : mulT (r • c) P = r • mulT c P := by
  apply Subtype.ext; funext w
  show r * (c : ℂ → ℂ) w * (P : ℂ → ℂ) w = r * ((c : ℂ → ℂ) w * (P : ℂ → ℂ) w)
  ring

lemma mulT_comm (c P : testFn) : mulT c P = mulT P c := by
  apply Subtype.ext; funext w
  show (c : ℂ → ℂ) w * (P : ℂ → ℂ) w = (P : ℂ → ℂ) w * (c : ℂ → ℂ) w
  ring

/-- `Δ(cP) = (Δc)P + cΔP + 2((Xc)(XP) + (Yc)(YP))`. -/
theorem lapTest_mulT (c P : testFn) :
    lapTest (mulT c P) = mulT (lapTest c) P + mulT c (lapTest P)
      + (2 : ℂ) • (mulT (vfTest 1 c) (vfTest 1 P) + mulT (vfTest Complex.I c) (vfTest Complex.I P)) := by
  rw [lapTest_eq_vf, lapTest_eq_vf, lapTest_eq_vf]
  simp only [vf_mulT, map_add, mulT_add_left, mulT_sub_left, mulT_add_right, mulT_sub_right]
  rw [mulT_comm (vfTest 1 c) (vfTest 1 P), mulT_comm (vfTest Complex.I c) (vfTest Complex.I P)]
  rw [show mulT (vfTest 1 P) (vfTest 1 c) = mulT (vfTest 1 c) (vfTest 1 P) from mulT_comm _ _,
    show mulT (vfTest Complex.I P) (vfTest Complex.I c) = mulT (vfTest Complex.I c) (vfTest Complex.I P)
      from mulT_comm _ _]
  rw [two_smul]
  abel

/-- **The localized Laplacian, weakly**: for test functions `χ, P` and `u ∈ Dom(-Δ)`,
`⟪χΔP, u⟫ = -⟪χP, (-Δ)u⟫ + 2⟪(Xχ)P, Xu⟫ + 2⟪(Yχ)P, Yu⟫ + ⟪(Δχ)P, u⟫`. -/
theorem inner_local_lap (χ P : testFn) (u : negLapH.domain) :
    inner ℂ (toL2 (mulT χ (lapTest P))) u
      = -inner ℂ (toL2 (mulT χ P)) (negLapH u)
        + 2 * inner ℂ (toL2 (mulT (vfTest 1 χ) P)) (domX u)
        + 2 * inner ℂ (toL2 (mulT (vfTest Complex.I χ) P)) (domY u)
        + inner ℂ (toL2 (mulT (lapTest χ) P)) u := by
  -- `χΔP = Δ(χP) - (Δχ)P - 2((Xχ)(XP) + (Yχ)(YP))`
  have hprod := lapTest_mulT χ P
  have e1 : mulT χ (lapTest P) = lapTest (mulT χ P) - mulT (lapTest χ) P
      - (2 : ℂ) • (mulT (vfTest 1 χ) (vfTest 1 P) + mulT (vfTest Complex.I χ) (vfTest Complex.I P)) := by
    rw [hprod]; abel
  -- `(Xχ)(XP) = X((Xχ)P) - (X²χ)P`, `(Yχ)(YP) = Y((Yχ)P) - (Y²χ)P`
  have eX : mulT (vfTest 1 χ) (vfTest 1 P) = vfTest 1 (mulT (vfTest 1 χ) P) - mulT (vfTest 1 (vfTest 1 χ)) P := by
    rw [vf_mulT]; abel
  have eY : mulT (vfTest Complex.I χ) (vfTest Complex.I P)
      = vfTest Complex.I (mulT (vfTest Complex.I χ) P) - mulT (vfTest Complex.I (vfTest Complex.I χ)) P := by
    rw [vf_mulT]; abel
  rw [e1, eX, eY]
  simp only [map_sub, map_add, map_smul, inner_sub_left, inner_add_left, inner_smul_left]
  rw [inner_lapTest_dom, inner_X_dom, inner_Y_dom]
  -- `Δχ = X²χ + Y²χ - Yχ`
  have hΔχ : toL2 (mulT (lapTest χ) P) = toL2 (mulT (vfTest 1 (vfTest 1 χ)) P)
      + toL2 (mulT (vfTest Complex.I (vfTest Complex.I χ)) P) - toL2 (mulT (vfTest Complex.I χ) P) := by
    rw [lapTest_eq_vf, mulT_sub_left, mulT_add_left, map_sub, map_add]
  rw [hΔχ, inner_sub_left, inner_add_left]
  simp only [map_ofNat]
  ring

end Qschubert
