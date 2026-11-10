import Qschubert.ModCosets
import Qschubert.MellinTest
import Qschubert.Periodize

/-!
# The incomplete Eisenstein series of a test function, pointwise

Stage E of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), part E2. For a test function `g` on `(0, ∞)` let
`u_g(z) = g(Im z)` on the strip `0 ≤ Re z < 1` and `0` elsewhere (`stripFn`). Its periodization over `PSL(2, ℤ)` is

`E_g(z) = ∑_{p} g(Im σ(p) z)`, `p = (c, d)` over the bottom rows up to sign (`perio_stripFn`),

a finite sum for each `z` (`finite_npair_im_ge`), with `Im σ(p) z = Im z / |c z + d|²` (`im_npSec_smul`).
-/

namespace Qschubert

open Matrix UpperHalfPlane ModularGroup Filter
open scoped MatrixGroups

/-- `u_g(z) = g(Im z)` on the strip `0 ≤ Re z < 1`, and `0` elsewhere. -/
noncomputable def stripFn (g : ℝ → ℂ) (z : ℍ) : ℂ := if ⌊z.re⌋ = 0 then g z.im else 0

/-- `Im σ(p) z = Im z / |c z + d|²`. -/
lemma im_npSec_smul (p : NPair) (z : ℍ) :
    (npSec p • z).im = z.im / Complex.normSq ((p.1 0 : ℂ) * z + p.1 1) := by
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply, congrFun (npSec_row p) 0,
    congrFun (npSec_row p) 1]

/-- Only finitely many bottom rows give height at least `m > 0`. -/
lemma finite_npair_im_ge (z : ℍ) {m : ℝ} (hm : 0 < m) : {p : NPair | m ≤ (npSec p • z).im}.Finite := by
  have h := (ModularGroup.tendsto_normSq_coprime_pair z).eventually (eventually_gt_atTop (z.im / m))
  rw [Filter.eventually_cofinite] at h
  have hinj : Function.Injective (fun p : NPair => p.1) := fun p q h => Subtype.ext h
  refine (h.preimage hinj.injOn).subset fun (p : NPair) hp => ?_
  have hp' : m ≤ (npSec p • z).im := hp
  rw [im_npSec_smul] at hp'
  show ¬ (z.im / m < Complex.normSq ((p.1 0 : ℂ) * z + p.1 1))
  intro hlt
  have hpos : 0 < Complex.normSq ((p.1 0 : ℂ) * z + p.1 1) := lt_trans (div_pos z.im_pos hm) hlt
  rw [le_div_iff₀ hpos] at hp'
  rw [div_lt_iff₀ hm] at hlt
  nlinarith

/-- **The incomplete Eisenstein series as a sum over bottom rows.** -/
theorem perio_stripFn {g : ℝ → ℂ} (hg : IsKTest g) (z : ℍ) :
    perio modGroup (stripFn g) (surfMk modGroup z) = ∑' p : NPair, g ((npSec p • z).im) := by
  classical
  obtain ⟨a, ha, hga⟩ := hg.exists_pos_le
  rw [perio_mk, tsum_modGroup_smul]
  set P₀ : Finset NPair := (finite_npair_im_ge z ha).toFinset with hP₀
  have hP₀mem : ∀ p : NPair, p ∉ P₀ → g ((npSec p • z).im) = 0 := by
    intro p hp
    by_contra hne
    exact hp ((finite_npair_im_ge z ha).mem_toFinset.2 (hga _ hne))
  set ι : NPair → NPair × ℤ := fun p => (p, -⌊(npSec p • z).re⌋) with hι
  have hval : ∀ (p : NPair) (n : ℤ), stripFn g ((T ^ n * npSec p) • z)
      = if n = -⌊(npSec p • z).re⌋ then g ((npSec p • z).im) else 0 := by
    intro p n
    rw [mul_smul, stripFn, re_T_zpow_smul, im_T_zpow_smul, Int.floor_add_intCast]
    by_cases h : n = -⌊(npSec p • z).re⌋
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega)]
  have hsupp : ∀ pn : NPair × ℤ, pn ∉ P₀.image ι → stripFn g ((T ^ pn.2 * npSec pn.1) • z) = 0 := by
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

end Qschubert
