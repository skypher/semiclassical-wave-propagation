import Qschubert.EisBound
import Qschubert.PerioMeas

/-!
# Measurability of the incomplete Eisenstein series of a test function

Stage E of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). For a test function `g` on `(0, ∞)` the orbit sum
of `stripFn g` over `PSL(2, ℤ)` has only finitely many nonzero terms at every point (`mem_absSet_stripFn`), so
`E_g = perio modGroup (stripFn g)` is a.e. strongly measurable on `M` (`aestronglyMeasurable_perio_stripFn`).
-/

namespace Qschubert

open MeasureTheory Set Filter Topology Matrix UpperHalfPlane ModularGroup
open scoped Real MatrixGroups ENNReal

instance : Countable modGroup := countable_of_properlyDiscontinuous modGroup

lemma measurable_stripFn {g : ℝ → ℂ} (hg : IsKTest g) : Measurable (stripFn g) := by
  unfold stripFn
  refine Measurable.ite ?_ (hg.continuous.measurable.comp UpperHalfPlane.continuous_im.measurable) measurable_const
  exact (Int.measurable_floor.comp UpperHalfPlane.continuous_re.measurable) (measurableSet_singleton 0)

/-- The orbit sum of `stripFn g` converges absolutely at every point. -/
lemma mem_absSet_stripFn {g : ℝ → ℂ} (hg : IsKTest g) (z : ℍ) : z ∈ absSet modGroup (stripFn g) := by
  classical
  obtain ⟨a, ha, hga⟩ := hg.exists_pos_le
  show absSum modGroup (stripFn g) z < ∞
  rw [absSum, ← (Equiv.ofBijective npMap npMap_bijective).tsum_eq]
  set P₀ : Finset NPair := (finite_npair_im_ge z ha).toFinset with hP₀
  set ι : NPair → NPair × ℤ := fun p => (p, -⌊(npSec p • z).re⌋) with hι
  have hsupp : ∀ pn : NPair × ℤ, pn ∉ P₀.image ι →
      ‖stripFn g ((Equiv.ofBijective npMap npMap_bijective) pn • z)‖ₑ = 0 := by
    rintro ⟨p, n⟩ hpn
    have e : (Equiv.ofBijective npMap npMap_bijective) (p, n) • z = (T ^ n * npSec p) • z := by
      show npMap (p, n) • z = _
      rw [npMap, modQ_smul]
    rw [e, enorm_eq_zero, mul_smul, stripFn, re_T_zpow_smul, im_T_zpow_smul, Int.floor_add_intCast]
    by_cases h : n = -⌊(npSec p • z).re⌋
    · have hz : g ((npSec p • z).im) = 0 := by
        by_contra hne
        refine hpn ?_
        rw [Finset.mem_image]
        exact ⟨p, (finite_npair_im_ge z ha).mem_toFinset.2 (hga _ hne), by rw [hι, h]⟩
      rw [hz]
      split_ifs <;> rfl
    · rw [ite_eq_right (by omega)]
  rw [tsum_eq_sum hsupp]
  exact ENNReal.sum_lt_top.2 fun pn _ => enorm_lt_top

/-- **`E_g` is a.e. strongly measurable on `M`.** -/
theorem aestronglyMeasurable_perio_stripFn {g : ℝ → ℂ} (hg : IsKTest g) :
    AEStronglyMeasurable (perio modGroup (stripFn g)) (surfMeasure modGroup) :=
  aestronglyMeasurable_perio modGroup (measurable_stripFn hg) (Eventually.of_forall fun z => mem_absSet_stripFn hg z)

end Qschubert
