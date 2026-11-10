import Qschubert.Bridge
import Qschubert.Boundary
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups

/-!
# Frozen statement of Theorem `cl:main` (the cusp factor is necessary)

Draft for freeze review (`lean/BLUEPRINT.md`, S5). Manuscript `paper/sec_cusp_lower.tex`, Theorem
`cl:main`: `Γ = PSL(2, ℤ)`, `x₀ = i`, `X₀ = cosh d(i, ·)`, `b = ∞` (`g = 1`), `φ = -log y`.

* `modGroup`: the image of `SL(2, ℤ)` in `PGL(2, ℝ)`; properly discontinuous and orientation-preserving
  (`Qschubert/Bridge.lean`, with Mathlib's discreteness of `SL(2, ℤ)` in `SL(2, ℝ)`).
* `ContRepLower`: the error vector has a continuous representative, and every continuous
  representative has modulus at least `B` at the projection of `z`.
* (i) `a = e^{-20 X₀}`; (ii) `a = e^{-αΛ} e^{-κ X₀}`, encoded as `0` if `e^{-κ X₀} ∉ L²` (that branch
  would make the lower bound false, not vacuous; obligation CL-L2: `e^{-κ X₀} ∈ L²` for `κ > 0`).
* In (i) nothing depends on `β` or `κ` (the amplitude is fixed); the manuscript's "constants depend on
  `α, β, κ`" is therefore read with `β, κ` dropped.
-/

namespace Qschubert

open MeasureTheory Matrix UpperHalfPlane
open scoped ENNReal MatrixGroups

/-- The image of `SL(2, ℤ)` in `SL(2, ℝ)`. -/
noncomputable def modSL : Subgroup SL(2, ℝ) := (SpecialLinearGroup.map (Int.castRingHom ℝ)).range

/-- `PSL(2, ℤ)` as a subgroup of `PGL(2, ℝ)`. -/
noncomputable def modGroup : Subgroup PGL(2, ℝ) := modSL.map SpecialLinearGroup.toPGL

instance : DiscreteTopology modSL :=
  Matrix.SpecialLinearGroup.discreteSpecialLinearGroupIntRangeSL

instance : ProperlyDiscontinuousSMul modGroup ℍ := properlyDiscontinuous_map_toPGL modSL

theorem modGroup_orientationPreserving : OrientationPreserving modGroup :=
  orientationPreserving_map_toPGL modSL

/-- The point `x + i e^t`. -/
noncomputable def ptXT (x t : ℝ) : ℍ := ⟨⟨x, Real.exp t⟩, Real.exp_pos t⟩

/-- The error vector has a continuous representative, and every continuous representative has
modulus at least `B` at the projection of `z`. -/
def ContRepLower (Γ : Subgroup PGL(2, ℝ)) (E : Lp ℂ 2 (surfMeasure Γ)) (z : ℍ) (B : ℝ) : Prop :=
  (∃ f : Surf Γ → ℂ, Continuous f ∧ f =ᵐ[surfMeasure Γ] ⇑E) ∧
    ∀ f : Surf Γ → ℂ, Continuous f → f =ᵐ[surfMeasure Γ] ⇑E → B ≤ ‖f (surfMk Γ z)‖

/-- The swapped-class amplitude `e^{-20 X₀}` of `cl:main` (i). -/
noncomputable def ampCl1 (z : ℍ) : ℂ := ((Real.exp (-20 * coshD I z) : ℝ) : ℂ)

open Classical in
/-- The printed-class amplitude `e^{-αΛ} e^{-κ X₀}` of `cl:main` (ii) (an `L²` class; `0` if
`e^{-κ X₀} ∉ L²`, see CL-L2). -/
noncomputable def ampCl2 (α κ : ℝ) (hα : 0 ≤ α) : ℍ → ℂ :=
  if hw : MemLp (fun z : ℍ => ((Real.exp (-κ * coshD I z) : ℝ) : ℂ)) 2 (volume : Measure ℍ) then
    ⇑(expLambda (-α) ⟨hw.toLp _, by rw [expLambda_domain_eq_top (by linarith)]; trivial⟩ :
      Lp ℂ 2 (volume : Measure ℍ))
  else 0

/-- The conclusion of `cl:main` at the point `x + i e^t`. -/
def ClConclusion (ħ' t x c : ℝ) (a : ℍ → ℂ) : Prop :=
  ∃ (hv : PerioConv modGroup (initState 1 ħ' a)) (hw : PerioConv modGroup (approxSolB 1 0 ħ' t a)),
    ContRepLower modGroup (errVec modGroup ħ' t hv hw) (ptXT x t)
        (c * Real.exp (t / 2) * ħ' ^ ((3 : ℝ) / 2) * t)
      ∧ (multM modGroup (surfMk modGroup (ptXT x t)) : ℝ≥0∞) ≤ ENNReal.ofReal (5 * Real.exp t)

/-- The time window `max(2 log(1/ħ), t*) ≤ t ≤ min(ħ^{-1/5}, δ(α/ħ)^{1/2})`. -/
def ClWindow (ħ' t t₀ δ α : ℝ) : Prop :=
  max (2 * Real.log (1 / ħ')) t₀ ≤ t ∧ t ≤ min (ħ' ^ (-(1 : ℝ) / 5)) (δ * Real.sqrt (α / ħ'))

/-- **Theorem `cl:main` (i)** (swapped class). -/
def Stmt_clmain1 : Prop :=
  ∃ α₀max : ℝ, 0 < α₀max ∧ α₀max < 1 / 2 ∧ ∀ α : ℝ, 0 < α → α ≤ α₀max →
  ∃ ħ₀ c t₀ δ : ℝ, 0 < ħ₀ ∧ 0 < c ∧ 0 < t₀ ∧ 0 < δ ∧
  ∀ ħ' t x : ℝ, 0 < ħ' → ħ' ≤ ħ₀ → ClWindow ħ' t t₀ δ α → ClConclusion ħ' t x c ampCl1

/-- **Theorem `cl:main` (ii)** (printed class), with `α*(κ) = min(α₀, c₁ κ^{-6})`. -/
def Stmt_clmain2 : Prop :=
  ∃ α₀max κs c₁ : ℝ, 0 < α₀max ∧ α₀max < 1 / 2 ∧ 0 < κs ∧ 0 < c₁ ∧
  ∀ κ α : ℝ, κs ≤ κ → (hα : 0 < α) → α ≤ min α₀max (c₁ * κ ^ (-(6 : ℤ))) →
  ∃ ħ₀ c t₀ δ : ℝ, 0 < ħ₀ ∧ 0 < c ∧ 0 < t₀ ∧ 0 < δ ∧
  ∀ ħ' t x : ℝ, 0 < ħ' → ħ' ≤ ħ₀ → ClWindow ħ' t t₀ δ α →
    ClConclusion ħ' t x c (ampCl2 α κ hα.le)

/-- **The printed Corollary 1.6 at `N = K = 0`** (Schubert, arXiv:0705.0134v1, Corollary
`cor:mainII`, (1.34), `refs/src_v1/schubert_time.tex` l.683-698), smooth-free form: for every
Fuchsian `Γ` and all `α, β` with `β > 1/2`, there are `C, δ > 0` such that for all `ħ > 0` with
`α³ ≥ β² ħ`, every amplitude of finite printed norm, every boundary point and every
`0 ≤ t ≤ δ α^{3/2} ħ^{-1/2}`, the error has a continuous representative, and every continuous
representative `f` (there is only one, by `eq_of_ae_eq_of_continuous`) satisfies
`|f| ≤ C (αħ)^{-8} ‖a‖_{α,β}` on `M` (R49: existence included, so this is the full pointwise claim). Reading choices: `C, δ` independent of `ħ` (a semiclassical
estimate; with `ħ`-dependent constants the printed bound is not refuted by the cusp example); base
point `x₀ = i` (Schubert's `0` in the disc); `b = g • ∞` with `g` fixing `x₀` (BND-1). -/
def Stmt_printedCor16_N0 : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (α β : ℝ), 0 < α → 1 / 2 < β →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (ħ' t : ℝ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
    0 < ħ' → β ^ 2 * ħ' ≤ α ^ 3 → g • I = I → 0 ≤ t → t ≤ δ * α ^ ((3 : ℝ) / 2) / Real.sqrt ħ' →
    prNormX I α β a < ⊤ →
    ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g 0 ħ' t a)),
      (∃ f : Surf Γ → ℂ, Continuous f ∧ f =ᵐ[surfMeasure Γ] ⇑(errVec Γ ħ' t hv hw)) ∧
      ∀ f : Surf Γ → ℂ, Continuous f → f =ᵐ[surfMeasure Γ] ⇑(errVec Γ ħ' t hv hw) →
        ∀ x, ENNReal.ofReal ‖f x‖ ≤ ENNReal.ofReal (C * (α * ħ')⁻¹ ^ 8) * prNormX I α β a

/-- **Remark `cl:relative`** (case (i), `a = e^{-20X₀}`): at the points of `cl:main`, the error is
small relative to the periodized approximation: `c ħt |u^{(0)}(t)_Γ(z)| ≤ |E_0(t)(z)| ≤ C ħt
|u^{(0)}(t)_Γ(z)|` at `z = x + i e^t`, where `u^{(0)}(t)_Γ(z)` is the (absolutely convergent) orbit sum
at `z` and is nonzero there, and `E_0(t)(z)` is the value of the continuous representative. -/
def Stmt_clrelative : Prop :=
  ∃ α₀max : ℝ, 0 < α₀max ∧ α₀max < 1 / 2 ∧ ∀ α : ℝ, 0 < α → α ≤ α₀max →
  ∃ ħ₀ c C t₀ δ : ℝ, 0 < ħ₀ ∧ 0 < c ∧ 0 < C ∧ 0 < t₀ ∧ 0 < δ ∧
  ∀ ħ' t x : ℝ, 0 < ħ' → ħ' ≤ ħ₀ → ClWindow ħ' t t₀ δ α →
    ∃ (hv : PerioConv modGroup (initState 1 ħ' ampCl1))
      (hw : PerioConv modGroup (approxSolB 1 0 ħ' t ampCl1)),
      Summable (fun γ : modGroup => ‖approxSolB 1 0 ħ' t ampCl1 (γ • ptXT x t)‖) ∧
      perio modGroup (approxSolB 1 0 ħ' t ampCl1) (surfMk modGroup (ptXT x t)) ≠ 0 ∧
      (∃ f : Surf modGroup → ℂ, Continuous f ∧ f =ᵐ[surfMeasure modGroup] ⇑(errVec modGroup ħ' t hv hw)) ∧
      ∀ f : Surf modGroup → ℂ, Continuous f → f =ᵐ[surfMeasure modGroup] ⇑(errVec modGroup ħ' t hv hw) →
        c * ħ' * t * ‖perio modGroup (approxSolB 1 0 ħ' t ampCl1) (surfMk modGroup (ptXT x t))‖
            ≤ ‖f (surfMk modGroup (ptXT x t))‖ ∧
          ‖f (surfMk modGroup (ptXT x t))‖
            ≤ C * ħ' * t * ‖perio modGroup (approxSolB 1 0 ħ' t ampCl1) (surfMk modGroup (ptXT x t))‖

end Qschubert
