import Qschubert.EisMeas

/-!
# The absolute orbit sum of the strip function

Stage E of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). For a test function `g` on `(0, ∞)`:

* `absSum_stripFn_eq`: `∑_γ |stripFn g (γ z)| = ∑_p |g(Im σ(p) z)|`, over the bottom rows up to sign;
* `absSum_stripFn_le`: this sum is bounded on `ℍ`.
-/

namespace Qschubert

open MeasureTheory Set Filter Topology Matrix UpperHalfPlane ModularGroup
open scoped Real MatrixGroups ENNReal

lemma absSum_stripFn_eq {g : ℝ → ℂ} (hg : IsKTest g) (z : ℍ) :
    absSum modGroup (stripFn g) z = ∑' p : NPair, ‖g ((npSec p • z).im)‖ₑ := by
  classical
  obtain ⟨a, ha, hga⟩ := hg.exists_pos_le
  rw [absSum, ← (Equiv.ofBijective npMap npMap_bijective).tsum_eq]
  set P₀ : Finset NPair := (finite_npair_im_ge z ha).toFinset with hP₀
  have hP₀mem : ∀ p : NPair, p ∉ P₀ → ‖g ((npSec p • z).im)‖ₑ = 0 := by
    intro p hp
    rw [enorm_eq_zero]
    by_contra hne
    exact hp ((finite_npair_im_ge z ha).mem_toFinset.2 (hga _ hne))
  set ι : NPair → NPair × ℤ := fun p => (p, -⌊(npSec p • z).re⌋) with hι
  have hval : ∀ (p : NPair) (n : ℤ), ‖stripFn g ((Equiv.ofBijective npMap npMap_bijective) (p, n) • z)‖ₑ
      = if n = -⌊(npSec p • z).re⌋ then ‖g ((npSec p • z).im)‖ₑ else 0 := by
    intro p n
    have e : (Equiv.ofBijective npMap npMap_bijective) (p, n) • z = (T ^ n * npSec p) • z := by
      show npMap (p, n) • z = _
      rw [npMap, modQ_smul]
    rw [e, mul_smul, stripFn, re_T_zpow_smul, im_T_zpow_smul, Int.floor_add_intCast]
    by_cases h : n = -⌊(npSec p • z).re⌋
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega), enorm_zero]
  have hsupp : ∀ pn : NPair × ℤ, pn ∉ P₀.image ι →
      ‖stripFn g ((Equiv.ofBijective npMap npMap_bijective) pn • z)‖ₑ = 0 := by
    rintro ⟨p, n⟩ hpn
    rw [hval]
    by_cases h : n = -⌊(npSec p • z).re⌋
    · rw [ite_eq_left h]
      refine hP₀mem p fun hp => hpn ?_
      rw [Finset.mem_image]
      exact ⟨p, hp, by rw [hι, h]⟩
    · rw [ite_eq_right h]
  have hinj : Set.InjOn ι (P₀ : Set NPair) := fun p _ q _ h => congrArg Prod.fst h
  rw [tsum_eq_sum hsupp, Finset.sum_image hinj, tsum_eq_sum (s := P₀) (fun p hp => hP₀mem p hp)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hval, ite_eq_left rfl]

/-- **The absolute orbit sum of the strip function is bounded.** -/
theorem absSum_stripFn_le {g : ℝ → ℂ} (hg : IsKTest g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℍ, absSum modGroup (stripFn g) z ≤ ENNReal.ofReal M := by
  obtain ⟨D, hD, hdom⟩ := norm_test_npSec_le hg (y₀ := 1 / 2) (by norm_num)
  have hsumM : Summable fun p : NPair => D * ‖p.1‖ ^ (-(5 / 2 : ℝ)) := summable_npair_norm.mul_left D
  have hnn : ∀ p : NPair, 0 ≤ D * ‖p.1‖ ^ (-(5 / 2 : ℝ)) := fun p =>
    mul_nonneg hD (Real.rpow_nonneg (norm_nonneg _) _)
  refine ⟨∑' p : NPair, D * ‖p.1‖ ^ (-(5 / 2 : ℝ)), tsum_nonneg hnn, fun z => ?_⟩
  obtain ⟨A, hA⟩ := ModularGroup.exists_smul_mem_fd z
  have hinv : absSum modGroup (stripFn g) (A • z) = absSum modGroup (stripFn g) z := by
    rw [← modQ_smul]
    exact absSum_smul modGroup (stripFn g) (modQ A) z
  have hfd : 1 ≤ Complex.normSq (A • z : ℍ) ∧ |(A • z).re| ≤ 1 / 2 := hA
  have hre : |(A • z).re| ≤ 1 := hfd.2.trans (by norm_num)
  have him : (1 / 2 : ℝ) ≤ (A • z).im := by
    have h1 := hfd.1
    rw [Complex.normSq_apply] at h1
    have h2 : (A • z).re * (A • z).re ≤ 1 / 4 := by
      have := abs_le.1 hfd.2
      nlinarith [this.1, this.2]
    have h3 : (3 / 4 : ℝ) ≤ (A • z).im * (A • z).im := by
      have e1 : ((A • z : ℍ) : ℂ).re = (A • z).re := rfl
      have e2 : ((A • z : ℍ) : ℂ).im = (A • z).im := rfl
      rw [e1, e2] at h1
      linarith
    nlinarith [(A • z).im_pos]
  rw [← hinv, absSum_stripFn_eq hg, ENNReal.ofReal_tsum_of_nonneg hnn hsumM]
  refine ENNReal.tsum_le_tsum fun p => ?_
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hdom p (A • z) hre him)

end Qschubert
