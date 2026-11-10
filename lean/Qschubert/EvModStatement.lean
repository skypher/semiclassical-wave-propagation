import Qschubert.EvTransfer
import Qschubert.CuspLower
import Mathlib.NumberTheory.Modular

/-!
# Statement of Proposition `ev:mod` (modular surface), parts (i) and (ii)

Manuscript `paper/sec_expect.tex`, Proposition `ev:mod`: `Γ = PSL(2, ℤ)` (`modGroup`), `x₀ = i`, `b = ∞` (`g = 1`), and
`a = e^{-αΛ} h` with `h` a nonnegative test function whose periodization along `z ↦ z + n` does not depend on `x`.

This file contains the statement only (`Stmt_evmod`); it is not proved here. Part (iii) of the proposition (the classical
transport) is a cited theorem in the manuscript and is not part of this statement.

Reading choices.
* `h` is a test function on `ℍ` (`IsTestFn`, a `C^∞` function on `ℂ` with compact support inside the upper half-plane);
  `ModData h h₀` says that `h` is real and nonnegative, that `∑_n h(z + n) = h₀(Im z)` for all `z ∈ ℍ`, and that `h₀` is
  not identically zero on `(0, ∞)`.
* The amplitude is the `L²` class `e^{-αΛ} h` (`ampMod`), and the theorem produces its `C^∞` representative `a'`, as in
  `pcmain_half`.
* `μ₀ = ∫_0^∞ |a₀(y)|² dy/y²` with `a₀(y) = ∫_ℝ a'(x + iy) dx` (`zeroModeH`, `massMod`); since the periodization of `a'`
  along `z ↦ z + n` does not depend on `x`, this is the `a₀` of the manuscript.
* `M_Y` is the image in `M` of `{z ∈ 𝒟 : Im z ≤ Y}`, `𝒟` the standard fundamental domain (`compactPart`).
* "tends to `0` uniformly on the window": for every `η > 0` there is `ħ₀ > 0` such that the quantity is at most `η` for all
  `ħ ≤ ħ₀` and all `t` in the window.
* `T(ħ) = C₁ log(1/ħ) log log(1/ħ)` with an absolute constant `C₁`, chosen before everything else.
* The constants `C, δ` are those of `pc:main` for `β = κ = 1`; its bound at `N = 0` is part of the conclusion.
-/

namespace Qschubert

open MeasureTheory Complex UpperHalfPlane
open scoped ENNReal InnerProductSpace MatrixGroups Modular

/-- The hypotheses on the data `h` of Proposition `ev:mod`. -/
structure ModData (h : ℂ → ℂ) (h₀ : ℝ → ℝ) : Prop where
  test : IsTestFn h
  real_nonneg : ∀ z : ℍ, ∃ r : ℝ, 0 ≤ r ∧ h z = (r : ℂ)
  periodized : ∀ z : ℍ, HasSum (fun n : ℤ => h ((z : ℂ) + n)) ((h₀ z.im : ℝ) : ℂ)
  nonzero : ∃ y : ℝ, 0 < y ∧ h₀ y ≠ 0

/-- The amplitude `e^{-αΛ} h` as an `L²` class. -/
noncomputable def ampMod (α : ℝ) (hα : 0 ≤ α) {h : ℂ → ℂ} (hh : IsTestFn h) : Lp ℂ 2 (volume : Measure ℍ) :=
  expLambda (-α) ⟨toL2 ⟨h, hh⟩, by rw [expLambda_domain_eq_top (by linarith)]; trivial⟩

/-- The zero mode `a₀(y) = ∫_ℝ a(x + iy) dx` (`0` for `y ≤ 0`). -/
noncomputable def zeroModeH (a : ℍ → ℂ) (y : ℝ) : ℂ :=
  if hy : 0 < y then ∫ x : ℝ, a ⟨⟨x, y⟩, hy⟩ else 0

/-- `μ₀ = ∫_0^∞ |a₀(y)|² dy / y²`. -/
noncomputable def massMod (a : ℍ → ℂ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ), ‖zeroModeH a y‖ ^ 2 / y ^ 2

/-- `M_Y`: the image in `M` of the part of the standard fundamental domain below height `Y`. -/
def compactPart (Y : ℝ) : Set (Surf modGroup) :=
  surfMk modGroup '' {z : ℍ | z ∈ ModularGroup.fd ∧ z.im ≤ Y}

/-- The time `T(ħ) = C₁ log(1/ħ) log log(1/ħ)`. -/
noncomputable def escTime (C₁ ħ' : ℝ) : ℝ := C₁ * Real.log (1 / ħ') * Real.log (Real.log (1 / ħ'))

/-- **Proposition `ev:mod`, parts (i) and (ii).** `C₁` is absolute; `C, δ` are constants of `pc:main` for `β = κ = 1`. -/
def Stmt_evmod : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (hα : 0 < α) (_ : α ≤ 1 / 2) (h : ℂ → ℂ) (h₀ : ℝ → ℝ) (hd : ModData h h₀),
    prNormX I α 1 (ampMod α hα.le hd.test) < ⊤ ∧
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] ampMod α hα.le hd.test ∧
      0 < massMod a' ∧
      -- (i), the norm: `‖ψ(0)‖² = μ₀ + O(ħⁿ)` for every `n`
      (∀ n : ℕ, ∃ Cn : ℝ, ∀ ħ' : ℝ, 0 < ħ' → ħ' ≤ 1 → ħ' ≤ α ^ 3 →
        ∃ hv : PerioConv modGroup (initState 1 ħ' a'),
          |‖hv.2.toLp (perio modGroup (initState 1 ħ' a'))‖ ^ 2 - massMod a'| ≤ Cn * ħ' ^ n) ∧
      -- (i), accuracy: the bound of `pc:main` at `N = 0`
      (∀ (ħ' t : ℝ) (K : ℕ), 0 < ħ' → ħ' ≤ 1 → ħ' ≤ α ^ 3 → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
        ∃ (hv : PerioConv modGroup (initState 1 ħ' a')) (hw : PerioConv modGroup (approxSolB 1 K ħ' t a')),
          approxErr modGroup 0 ħ' t hv hw
            ≤ ENNReal.ofReal (ddBound C α ħ' t K 0) * prNormX I α 1 (ampMod α hα.le hd.test)) ∧
      -- (ii): the mass in `M_Y` tends to `0`, uniformly on the window
      ∀ (Y : ℝ), 1 ≤ Y → ∀ (K : ℕ) (η : ℝ), 0 < η → ∃ ħ₀ : ℝ, 0 < ħ₀ ∧
        ∀ (ħ' t : ℝ), 0 < ħ' → ħ' ≤ ħ₀ → escTime C₁ ħ' + Real.log Y ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
          ∃ (hv : PerioConv modGroup (initState 1 ħ' a')) (hw : PerioConv modGroup (approxSolB 1 K ħ' t a')),
            (∫ p in compactPart Y, ‖(solM modGroup ħ' t hv) p‖ ^ 2 ∂(surfMeasure modGroup))
              + (∫ p in compactPart Y,
                  ‖(hw.2.toLp (perio modGroup (approxSolB 1 K ħ' t a'))) p‖ ^ 2 ∂(surfMeasure modGroup)) ≤ η

end Qschubert
