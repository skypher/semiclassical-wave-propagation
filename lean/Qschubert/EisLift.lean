import Qschubert.EisUnfold
import Qschubert.PerioMean

/-!
# The incomplete Eisenstein series lifted to `ℍ`: measurability, periodicity and the mean over a horocycle

Stage E of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), part E5 (preparations). For a test function `g`
on `(0, ∞)` and `Ê_g(z) = perio modGroup (stripFn g) (surfMk modGroup z)`:

* `measurable_perio_stripFn_lift`: `Ê_g` is measurable on `ℍ`;
* `surfMk_transGL_int`: `π(z + n) = π(z)` for integers `n`;
* `mean_perio_stripFn`: `∫_0^1 Ê_g(x - s + iy) ds = g(y) + R_g(y)` for every real `x`.
-/

namespace Qschubert

open MeasureTheory Filter Topology UpperHalfPlane Set ModularGroup
open scoped MatrixGroups Real

lemma measurable_perio_stripFn_lift {g : ℝ → ℂ} (hg : IsKTest g) :
    Measurable fun z : ℍ => perio modGroup (stripFn g) (surfMk modGroup z) := by
  have ht : truncF modGroup (stripFn g) = stripFn g := by
    funext z
    exact Set.indicator_of_mem (mem_absSet_stripFn hg z) _
  have h := measurable_perio_truncF modGroup (measurable_stripFn hg)
  rw [ht] at h
  exact h

lemma surfMk_transGL_int (n : ℤ) (z : ℍ) : surfMk modGroup (transGL (n : ℝ) • z) = surfMk modGroup z := by
  have e : transGL (n : ℝ) • z = modQ (T ^ n) • z := by
    rw [modQ_smul]
    apply UpperHalfPlane.ext
    rw [coe_transGL_smul, coe_T_zpow_smul_eq, Complex.ofReal_intCast]
  rw [e]
  exact surfMk_smul modGroup (modQ (T ^ n)) z

/-- **The mean of the incomplete Eisenstein series over a closed horocycle.** -/
theorem mean_perio_stripFn {g : ℝ → ℂ} (hg : IsKTest g) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    ∫ s in (0 : ℝ)..1, perio modGroup (stripFn g) (surfMk modGroup ⟨⟨x - s, y⟩, hy⟩) = g y + eisR g y := by
  set ψ : ℝ → ℂ := fun u => perio modGroup (stripFn g) (surfMk modGroup ⟨⟨u, y⟩, hy⟩) with hψ
  have hper : Function.Periodic ψ 1 := by
    intro u
    have e : (⟨⟨u + 1, y⟩, hy⟩ : ℍ) = transGL ((1 : ℤ) : ℝ) • (⟨⟨u, y⟩, hy⟩ : ℍ) := by
      apply UpperHalfPlane.ext
      rw [coe_transGL_smul]
      apply Complex.ext <;> simp
    show perio modGroup (stripFn g) (surfMk modGroup ⟨⟨u + 1, y⟩, hy⟩) = _
    rw [e, surfMk_transGL_int]
  have h1 := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1) ψ x
  have h2 := hper.intervalIntegral_add_eq (x - 1) 0
  have h3 := zeroMode_perio_stripFn hg hy
  show ∫ s in (0 : ℝ)..1, ψ (x - s) = _
  rw [h1, sub_zero]
  have e2 : x = x - 1 + 1 := by ring
  rw [show (∫ u in (x - 1)..x, ψ u) = ∫ u in (x - 1)..(x - 1 + 1), ψ u by rw [← e2], h2, zero_add]
  exact h3

end Qschubert
