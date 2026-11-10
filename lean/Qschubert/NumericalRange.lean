import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Numerical-range geometry for Lemma NR

Manuscript `paper/paper.tex`, Appendix H, Lemma NR. Its proof uses three facts
about the region `𝒫_η = {λ² : |Im λ| ≤ η}`, formalized here.

* `mem_parabolaRegion_of_form`: if `a ≥ 0`, `0 ≤ b ≤ η²` and `y² ≤ 4ab`, then
  `(a - b) + i y ∈ 𝒫_η`. With `a = ‖∇f‖²`, `b = ‖f ∇ψ‖²`, `Re⟨f, A_W f⟩ = a - b` and
  `|Im⟨f, A_W f⟩| ≤ 2√(ab)` this is the inclusion `NR(A_W) ⊂ 𝒫_η`.
* `mul_norm_le_norm_sq_sub` and `le_infDist_parabolaRegion`: if `Im λ = η + δ` with `δ ≥ 0`,
  then `dist(λ², 𝒫_η) ≥ δ |λ|`.
* `infDist_mul_norm_le`: if the numerical range of `T` lies in `S`, then
  `dist(ζ, S) ‖f‖ ≤ ‖(ζ - T) f‖` on the domain of `T`. This is the resolvent lower bound used
  on the contour.
-/

namespace Qschubert

open Complex Metric

/-- The region `𝒫_η = {λ² : |Im λ| ≤ η}` of the manuscript. -/
def parabolaRegion (η : ℝ) : Set ℂ := {z | ∃ q : ℂ, |q.im| ≤ η ∧ q ^ 2 = z}

lemma zero_mem_parabolaRegion {η : ℝ} (hη : 0 ≤ η) : (0 : ℂ) ∈ parabolaRegion η :=
  ⟨0, by simpa using hη, by simp⟩

/-- Inclusion step of Lemma NR: `a ≥ 0`, `0 ≤ b ≤ η²`, `y² ≤ 4ab` give `(a - b) + i y ∈ 𝒫_η`.
In fact every square root `q` of `(a - b) + i y` has `(Im q)² ≤ b`. -/
theorem mem_parabolaRegion_of_form {η a b y : ℝ} (hη : 0 ≤ η) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbη : b ≤ η ^ 2) (hy : y ^ 2 ≤ 4 * a * b) :
    ((a - b : ℝ) + (y : ℂ) * I) ∈ parabolaRegion η := by
  obtain ⟨q, hq⟩ := IsAlgClosed.exists_pow_nat_eq ((a - b : ℝ) + (y : ℂ) * I) (by norm_num : 0 < 2)
  refine ⟨q, ?_, hq⟩
  have hre : q.re ^ 2 - q.im ^ 2 = a - b := by
    have := congrArg Complex.re hq
    simpa [pow_two] using this
  have him : 2 * q.re * q.im = y := by
    have := congrArg Complex.im hq
    simp [pow_two] at this
    linarith
  -- `(a + t)(t - b) ≤ 0` with `t = (Im q)²`, hence `t ≤ b`.
  have key : (a + q.im ^ 2) * (q.im ^ 2 - b) ≤ 0 := by
    have h4 : 4 * (q.re ^ 2 * q.im ^ 2) ≤ 4 * a * b := by
      calc 4 * (q.re ^ 2 * q.im ^ 2) = (2 * q.re * q.im) ^ 2 := by ring
        _ = y ^ 2 := by rw [him]
        _ ≤ 4 * a * b := hy
    have hre' : q.re ^ 2 = a - b + q.im ^ 2 := by linarith
    rw [hre'] at h4
    nlinarith
  have ht : q.im ^ 2 ≤ b := by
    by_contra hcon
    push Not at hcon
    have h1 : 0 < q.im ^ 2 - b := by linarith
    have h2 : 0 < a + q.im ^ 2 := by nlinarith [sq_nonneg q.im]
    nlinarith
  have : q.im ^ 2 ≤ η ^ 2 := ht.trans hbη
  exact abs_le_of_sq_le_sq' this hη |> fun h => abs_le.mpr ⟨h.1, h.2⟩

/-- Distance step of Lemma NR: for `Im λ = η + δ` and `|Im q| ≤ η`,
`δ |λ| ≤ |λ² - q²|`. -/
theorem mul_norm_le_norm_sq_sub {η δ : ℝ} {l : ℂ} (hl : l.im = η + δ) {q : ℂ}
    (hq : |q.im| ≤ η) : δ * ‖l‖ ≤ ‖l ^ 2 - q ^ 2‖ := by
  have hqim := abs_le.mp hq
  have h1 : δ ≤ ‖l - q‖ := by
    have : (l - q).im = η + δ - q.im := by simp [hl]
    calc δ ≤ (l - q).im := by rw [this]; linarith [hqim.2]
      _ ≤ |(l - q).im| := le_abs_self _
      _ ≤ ‖l - q‖ := Complex.abs_im_le_norm _
  have h2 : δ ≤ ‖l + q‖ := by
    have : (l + q).im = η + δ + q.im := by simp [hl]
    calc δ ≤ (l + q).im := by rw [this]; linarith [hqim.1]
      _ ≤ |(l + q).im| := le_abs_self _
      _ ≤ ‖l + q‖ := Complex.abs_im_le_norm _
  have h3 : 2 * ‖l‖ ≤ ‖l - q‖ + ‖l + q‖ := by
    have e : (l - q) + (l + q) = (2 : ℂ) * l := by ring
    calc 2 * ‖l‖ = ‖(2 : ℂ) * l‖ := by simp
      _ = ‖(l - q) + (l + q)‖ := by rw [e]
      _ ≤ ‖l - q‖ + ‖l + q‖ := norm_add_le _ _
  have hfac : l ^ 2 - q ^ 2 = (l - q) * (l + q) := by ring
  rw [hfac, norm_mul]
  rcases le_total ‖l - q‖ ‖l + q‖ with h | h
  · have hl' : ‖l‖ ≤ ‖l + q‖ := by linarith
    exact mul_le_mul h1 hl' (norm_nonneg _) (norm_nonneg _)
  · have hl' : ‖l‖ ≤ ‖l - q‖ := by linarith
    calc δ * ‖l‖ ≤ ‖l + q‖ * ‖l - q‖ := mul_le_mul h2 hl' (norm_nonneg _) (norm_nonneg _)
      _ = ‖l - q‖ * ‖l + q‖ := mul_comm _ _

/-- `dist(λ², 𝒫_η) ≥ δ |λ|` for `Im λ = η + δ` and `η ≥ 0`. -/
theorem le_infDist_parabolaRegion {η δ : ℝ} (hη : 0 ≤ η) {l : ℂ}
    (hl : l.im = η + δ) : δ * ‖l‖ ≤ infDist (l ^ 2) (parabolaRegion η) := by
  refine (le_infDist ⟨0, zero_mem_parabolaRegion hη⟩).2 ?_
  rintro z ⟨q, hq, rfl⟩
  rw [dist_eq_norm]
  exact mul_norm_le_norm_sq_sub hl hq

/-- Numerical-range lower bound: if `⟪u, T u⟫ ∈ S` for every unit vector `u` of the domain,
then `dist(ζ, S) ‖f‖ ≤ ‖ζ f - T f‖` for every `f` in the domain. -/
theorem infDist_mul_norm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {D : Submodule ℂ E} (T : D →ₗ[ℂ] E) {S : Set ℂ}
    (hS : ∀ u : D, ‖(u : E)‖ = 1 → inner ℂ (u : E) (T u) ∈ S) (ζ : ℂ) (f : D) :
    infDist ζ S * ‖(f : E)‖ ≤ ‖ζ • (f : E) - T f‖ := by
  by_cases hf : (f : E) = 0
  · simp [hf]
  have hn : 0 < ‖(f : E)‖ := norm_pos_iff.mpr hf
  set c : ℂ := ((‖(f : E)‖⁻¹ : ℝ) : ℂ) with hc
  set u : D := c • f with hu_def
  have hcn : ‖c‖ = ‖(f : E)‖⁻¹ := by
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  have hu : ‖(u : E)‖ = 1 := by
    rw [hu_def, Submodule.coe_smul, norm_smul, hcn, inv_mul_cancel₀ hn.ne']
  have h1 : infDist ζ S ≤ ‖ζ - inner ℂ (u : E) (T u)‖ := by
    have := infDist_le_dist_of_mem (x := ζ) (hS u hu)
    rwa [dist_eq_norm] at this
  have h2 : ζ - inner ℂ (u : E) (T u) = inner ℂ (u : E) (ζ • (u : E) - T u) := by
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hu]
    simp
  have h3 : ‖inner ℂ (u : E) (ζ • (u : E) - T u)‖ ≤ ‖ζ • (u : E) - T u‖ := by
    calc _ ≤ ‖(u : E)‖ * ‖ζ • (u : E) - T u‖ := norm_inner_le_norm _ _
      _ = _ := by rw [hu, one_mul]
  have h4 : ζ • (u : E) - T u = c • (ζ • (f : E) - T f) := by
    rw [hu_def, map_smul, Submodule.coe_smul, smul_sub, smul_comm ζ c]
  have h5 : ‖ζ • (u : E) - T u‖ = ‖(f : E)‖⁻¹ * ‖ζ • (f : E) - T f‖ := by
    rw [h4, norm_smul, hcn]
  have h6 : infDist ζ S ≤ ‖(f : E)‖⁻¹ * ‖ζ • (f : E) - T f‖ := by
    rw [← h5]; exact h1.trans (h2 ▸ h3)
  calc infDist ζ S * ‖(f : E)‖ ≤ (‖(f : E)‖⁻¹ * ‖ζ • (f : E) - T f‖) * ‖(f : E)‖ :=
        mul_le_mul_of_nonneg_right h6 hn.le
    _ = ‖ζ • (f : E) - T f‖ := by field_simp

end Qschubert
