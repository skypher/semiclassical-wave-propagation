import Mathlib

/-!
# The critical-weight multiplier theorem, part 2: the discrete Schur test

`Kt c l n = ((1 + l)/(1 + n))^c (1 + |l - n|)^{-3/2}`, against `p n = (1 + n)^{-1/2}`, for `1/2 < c < 1`.
-/

namespace Qschubert

open Finset

/-- **Schur test on finite index sets.** -/
lemma schur_finite {L N : ℕ} {B : ℕ → ℕ → ℝ} {p a : ℕ → ℝ} {C₁ C₂ : ℝ} (hB : ∀ l n, 0 ≤ B l n) (hp : ∀ n, 0 < p n)
    (h1 : ∀ l, ∑ n ∈ range N, B l n * p n ≤ C₁ * p l) (h2 : ∀ n, ∑ l ∈ range L, B l n * p l ≤ C₂ * p n) (hC1 : 0 ≤ C₁) :
    ∑ l ∈ range L, (∑ n ∈ range N, B l n * a n) ^ 2 ≤ C₁ * C₂ * ∑ n ∈ range N, a n ^ 2 := by
  have hq : ∀ n, 0 ≤ a n ^ 2 / p n := fun n => div_nonneg (by positivity) (hp n).le
  have step : ∀ l, (∑ n ∈ range N, B l n * a n) ^ 2 ≤ C₁ * p l * ∑ n ∈ range N, B l n * (a n ^ 2 / p n) := fun l => by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (range N) (r := fun n => B l n * a n)
      (f := fun n => B l n * p n) (g := fun n => B l n * (a n ^ 2 / p n))
      (fun n _ => mul_nonneg (hB l n) (hp n).le) (fun n _ => mul_nonneg (hB l n) (hq n))
      (fun n _ => by
        have := (hp n).ne'
        field_simp)
    exact hcs.trans (mul_le_mul_of_nonneg_right (h1 l) (Finset.sum_nonneg fun n _ => mul_nonneg (hB l n) (hq n)))
  have e1 : ∑ l ∈ range L, C₁ * p l * ∑ n ∈ range N, B l n * (a n ^ 2 / p n)
      = C₁ * ∑ n ∈ range N, a n ^ 2 / p n * ∑ l ∈ range L, B l n * p l := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun l _ => by ring
  have e2 : ∑ n ∈ range N, a n ^ 2 / p n * ∑ l ∈ range L, B l n * p l ≤ ∑ n ∈ range N, C₂ * a n ^ 2 :=
    Finset.sum_le_sum fun n _ => by
      have h := mul_le_mul_of_nonneg_left (h2 n) (hq n)
      have e : a n ^ 2 / p n * (C₂ * p n) = C₂ * a n ^ 2 := by
        have := (hp n).ne'
        field_simp
      linarith
  calc _ ≤ ∑ l ∈ range L, C₁ * p l * ∑ n ∈ range N, B l n * (a n ^ 2 / p n) := Finset.sum_le_sum fun l _ => step l
    _ = C₁ * ∑ n ∈ range N, a n ^ 2 / p n * ∑ l ∈ range L, B l n * p l := e1
    _ ≤ C₁ * ∑ n ∈ range N, C₂ * a n ^ 2 := mul_le_mul_of_nonneg_left e2 hC1
    _ = C₁ * C₂ * ∑ n ∈ range N, a n ^ 2 := by rw [← Finset.mul_sum]; ring

lemma schur_r2 {x y w c s : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hw : 1 ≤ w) (hxy : x ≤ y * w) (hc1 : 1 / 2 < c) (hs : s ≤ 2 - c) :
    (x / y) ^ c * w ^ (-(3 / 2) : ℝ) * x ^ (-(1 / 2) : ℝ) ≤ w ^ (-s) * y ^ (-(1 / 2) : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hw0 : 0 < w := by linarith
  set r := x / y with hr
  have hr0 : 0 < r := div_pos hx0 hy0
  have hxr : x = r * y := by rw [hr]; field_simp
  have e1 : x ^ (-(1 / 2) : ℝ) = r ^ (-(1 / 2) : ℝ) * y ^ (-(1 / 2) : ℝ) := by
    rw [hxr, Real.mul_rpow hr0.le hy0.le]
  have e2 : r ^ c * r ^ (-(1 / 2) : ℝ) = r ^ (c - 1 / 2) := by
    rw [← Real.rpow_add hr0]
    congr 1
  have hrw : r ≤ w := by
    rw [hr, div_le_iff₀ hy0]
    linarith
  have h1 : r ^ (c - 1 / 2) ≤ w ^ (c - 1 / 2) := Real.rpow_le_rpow hr0.le hrw (by linarith)
  have h2 : w ^ (c - 1 / 2) * w ^ (-(3 / 2) : ℝ) = w ^ (c - 2) := by
    rw [← Real.rpow_add hw0]
    congr 1
    ring
  have h3 : w ^ (c - 2) ≤ w ^ (-s) := Real.rpow_le_rpow_of_exponent_le hw (by linarith)
  have hy1 : 0 < y ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hy0 _
  have hw3 : 0 < w ^ (-(3 / 2) : ℝ) := Real.rpow_pos_of_pos hw0 _
  rw [e1]
  have e3 : r ^ c * w ^ (-(3 / 2) : ℝ) * (r ^ (-(1 / 2) : ℝ) * y ^ (-(1 / 2) : ℝ))
      = r ^ (c - 1 / 2) * w ^ (-(3 / 2) : ℝ) * y ^ (-(1 / 2) : ℝ) := by
    rw [← e2]
    ring
  rw [e3]
  have h4 : r ^ (c - 1 / 2) * w ^ (-(3 / 2) : ℝ) ≤ w ^ (-s) := by
    have := mul_le_mul_of_nonneg_right h1 hw3.le
    rw [h2] at this
    exact this.trans h3
  exact mul_le_mul_of_nonneg_right h4 hy1.le

lemma schur_r1 {x y w c s : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hw : 1 ≤ w) (hxk : x ≤ y + w - 1) (hc1 : 1 / 2 < c) (hc2 : c < 1)
    (hs1 : s ≤ 3 / 2) (hs2 : s ≤ c + 1 / 2) :
    (x / y) ^ c * w ^ (-(3 / 2) : ℝ) * y ^ (-(1 / 2) : ℝ) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * (w ^ (-s) + y ^ (-s)) * x ^ (-(1 / 2) : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hw0 : 0 < w := by linarith
  set r := x / y with hr
  have hr0 : 0 < r := div_pos hx0 hy0
  have hxr : x = r * y := by rw [hr]; field_simp
  have e1 : y ^ (-(1 / 2) : ℝ) = r ^ (1 / 2 : ℝ) * x ^ (-(1 / 2) : ℝ) := by
    rw [hxr, Real.mul_rpow hr0.le hy0.le, ← mul_assoc, ← Real.rpow_add hr0]
    norm_num
  have e2 : r ^ c * r ^ (1 / 2 : ℝ) = r ^ (c + 1 / 2) := (Real.rpow_add hr0 _ _).symm
  have hw3 : 0 < w ^ (-(3 / 2) : ℝ) := Real.rpow_pos_of_pos hw0 _
  have hw4 : 0 < w ^ (-s) := Real.rpow_pos_of_pos hw0 _
  have hy4 : 0 < y ^ (-s) := Real.rpow_pos_of_pos hy0 _
  have h2 : (0 : ℝ) < 2 ^ (3 / 2 : ℝ) := by positivity
  have key : r ^ (c + 1 / 2) * w ^ (-(3 / 2) : ℝ) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * (w ^ (-s) + y ^ (-s)) := by
    by_cases hr2 : r ≤ 2
    · have a1 : r ^ (c + 1 / 2) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) :=
        (Real.rpow_le_rpow hr0.le hr2 (by linarith)).trans
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
      have a2 : w ^ (-(3 / 2) : ℝ) ≤ w ^ (-s) := Real.rpow_le_rpow_of_exponent_le hw (by linarith)
      calc _ ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * w ^ (-s) := mul_le_mul a1 a2 hw3.le h2.le
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) h2.le
    · have hr3 : 2 < r := not_le.1 hr2
      have hxy : 2 * y < x := by rw [hxr]; nlinarith
      have hwx : x / 2 ≤ w := by linarith
      have hx2 : 0 < x / 2 := by positivity
      have a1 : w ^ (-(3 / 2) : ℝ) ≤ (x / 2) ^ (-(3 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hx2 hwx (by norm_num)
      have a2 : (x / 2) ^ (-(3 / 2) : ℝ) = x ^ (-(3 / 2) : ℝ) * (2 : ℝ) ^ (3 / 2 : ℝ) := by
        rw [Real.div_rpow hx0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (3 / 2), div_inv_eq_mul]
      have a3 : r ^ (c + 1 / 2) = x ^ (c + 1 / 2) * (y ^ (c + 1 / 2))⁻¹ := by
        rw [hr, Real.div_rpow hx0.le hy0.le, div_eq_mul_inv]
      have a4 : x ^ (c + 1 / 2) * x ^ (-(3 / 2) : ℝ) = x ^ (c - 1) := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring
      have a5 : x ^ (c - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
      have a6 : (y ^ (c + 1 / 2))⁻¹ ≤ y ^ (-s) := by
        rw [← Real.rpow_neg hy0.le]
        exact Real.rpow_le_rpow_of_exponent_le hy (by linarith)
      have hrp : 0 < r ^ (c + 1 / 2) := Real.rpow_pos_of_pos hr0 _
      have hyi : 0 < (y ^ (c + 1 / 2))⁻¹ := inv_pos.2 (Real.rpow_pos_of_pos hy0 _)
      calc r ^ (c + 1 / 2) * w ^ (-(3 / 2) : ℝ) ≤ r ^ (c + 1 / 2) * (x ^ (-(3 / 2) : ℝ) * (2 : ℝ) ^ (3 / 2 : ℝ)) := by
            rw [← a2]; exact mul_le_mul_of_nonneg_left a1 hrp.le
        _ = (2 : ℝ) ^ (3 / 2 : ℝ) * (x ^ (c - 1) * (y ^ (c + 1 / 2))⁻¹) := by rw [a3, ← a4]; ring
        _ ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * (1 * y ^ (-s)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul a5 a6 hyi.le zero_le_one) h2.le
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) h2.le
  have hxp : 0 < x ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hx0 _
  rw [e1]
  have e3 : r ^ c * w ^ (-(3 / 2) : ℝ) * (r ^ (1 / 2 : ℝ) * x ^ (-(1 / 2) : ℝ))
      = r ^ (c + 1 / 2) * w ^ (-(3 / 2) : ℝ) * x ^ (-(1 / 2) : ℝ) := by
    rw [← e2]
    ring
  rw [e3]
  exact mul_le_mul_of_nonneg_right key hxp.le

/-- The distance on `ℕ`. -/
def kd (l n : ℕ) : ℕ := (l - n) + (n - l)

lemma kd_comm (l n : ℕ) : kd l n = kd n l := by
  unfold kd
  omega

lemma sum_kd_le {φ : ℕ → ℝ} (h0 : ∀ k, 0 ≤ φ k) (hs : Summable φ) (l N : ℕ) :
    ∑ n ∈ range N, φ (kd l n) ≤ 2 * ∑' k, φ k := by
  have hS : ∀ (s : Finset ℕ) (f : ℕ → ℕ), Set.InjOn f s → ∑ n ∈ s, φ (f n) ≤ ∑' k, φ k := fun s f hf => by
    rw [← Finset.sum_image (f := φ) hf]
    exact hs.sum_le_tsum _ fun k _ => h0 k
  rw [← Finset.sum_filter_add_sum_filter_not (range N) (· ≤ l)]
  have h1 : ∑ n ∈ (range N).filter (· ≤ l), φ (kd l n) = ∑ n ∈ (range N).filter (· ≤ l), φ (l - n) :=
    Finset.sum_congr rfl fun n hn => by
      have h := (Finset.mem_filter.1 hn).2
      unfold kd
      congr 1
      omega
  have h2 : ∑ n ∈ (range N).filter (fun n => ¬ n ≤ l), φ (kd l n) = ∑ n ∈ (range N).filter (fun n => ¬ n ≤ l), φ (n - l) :=
    Finset.sum_congr rfl fun n hn => by
      have h := (Finset.mem_filter.1 hn).2
      unfold kd
      congr 1
      omega
  rw [h1, h2]
  have a1 := hS ((range N).filter (· ≤ l)) (fun n => l - n) (fun a ha b hb e => by
    have h3 := (Finset.mem_filter.1 ha).2
    have h4 := (Finset.mem_filter.1 hb).2
    simp only at e
    omega)
  have a2 := hS ((range N).filter (fun n => ¬ n ≤ l)) (fun n => n - l) (fun a ha b hb e => by
    have h3 := (Finset.mem_filter.1 ha).2
    have h4 := (Finset.mem_filter.1 hb).2
    simp only at e
    omega)
  linarith

/-- `(1 + k)^{-s}`. -/
noncomputable def phiS (s : ℝ) (k : ℕ) : ℝ := (1 + (k : ℝ)) ^ (-s)

lemma phiS_nonneg (s : ℝ) (k : ℕ) : 0 ≤ phiS s k := by
  unfold phiS
  positivity

lemma summable_phiS {s : ℝ} (hs : 1 < s) : Summable (phiS s) := by
  have h : Summable fun k : ℕ => (((k + 1 : ℕ) : ℕ) : ℝ) ^ (-s) :=
    (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by linarith))
  refine h.congr fun k => ?_
  unfold phiS
  push_cast
  rw [add_comm]

/-- The model kernel. -/
noncomputable def Kt (c : ℝ) (l n : ℕ) : ℝ := ((1 + (l : ℝ)) / (1 + (n : ℝ))) ^ c * (1 + (kd l n : ℝ)) ^ (-(3 / 2) : ℝ)

/-- The Schur weight. -/
noncomputable def pS (n : ℕ) : ℝ := (1 + (n : ℝ)) ^ (-(1 / 2) : ℝ)

lemma pS_pos (n : ℕ) : 0 < pS n := by
  unfold pS
  positivity

lemma Kt_nonneg (c : ℝ) (l n : ℕ) : 0 ≤ Kt c l n := by
  unfold Kt
  positivity

lemma cast_kd_ge (l n : ℕ) : (l : ℝ) ≤ n + kd l n := by
  have : l ≤ n + kd l n := by
    unfold kd
    omega
  exact_mod_cast this

section sums

variable {c s : ℝ} (hc1 : 1 / 2 < c) (hc2 : c < 1) (hs : 1 < s) (hs1 : s ≤ 3 / 2) (hs2 : s ≤ 2 - c) (hs3 : s ≤ c + 1 / 2)
include hc1 hc2 hs hs1 hs3

lemma sum_Kt_n (l N : ℕ) :
    ∑ n ∈ range N, Kt c l n * pS n ≤ ((2 : ℝ) ^ (3 / 2 : ℝ) * (3 * ∑' k, phiS s k)) * pS l := by
  have h2 : (0 : ℝ) < 2 ^ (3 / 2 : ℝ) := by positivity
  have hb : ∀ n ∈ range N, Kt c l n * pS n ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * (phiS s (kd l n) + phiS s n) * pS l := fun n _ => by
    unfold Kt pS phiS
    have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hk : (0 : ℝ) ≤ kd l n := Nat.cast_nonneg _
    exact schur_r1 (by linarith) (by linarith) (by linarith) (by linarith [cast_kd_ge l n]) hc1 hc2 hs1 hs3
  have hZ := summable_phiS hs
  have h1 := sum_kd_le (phiS_nonneg s) hZ l N
  have h3 : ∑ n ∈ range N, phiS s n ≤ ∑' k, phiS s k := hZ.sum_le_tsum _ fun k _ => phiS_nonneg s k
  calc _ ≤ ∑ n ∈ range N, (2 : ℝ) ^ (3 / 2 : ℝ) * (phiS s (kd l n) + phiS s n) * pS l := Finset.sum_le_sum hb
    _ = (2 : ℝ) ^ (3 / 2 : ℝ) * (∑ n ∈ range N, phiS s (kd l n) + ∑ n ∈ range N, phiS s n) * pS l := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    _ ≤ _ := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ h2.le) (pS_pos l).le
      linarith

omit hs1 hs3 hc2 in
include hs2 in
lemma sum_Kt_l (n L : ℕ) : ∑ l ∈ range L, Kt c l n * pS l ≤ (2 * ∑' k, phiS s k) * pS n := by
  have hb : ∀ l ∈ range L, Kt c l n * pS l ≤ phiS s (kd n l) * pS n := fun l _ => by
    unfold Kt pS phiS
    rw [kd_comm n l]
    have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hk : (0 : ℝ) ≤ kd l n := Nat.cast_nonneg _
    refine schur_r2 (by linarith) (by linarith) (by linarith) ?_ hc1 hs2
    nlinarith [cast_kd_ge l n, mul_nonneg hn hk]
  have hZ := summable_phiS hs
  have h1 := sum_kd_le (phiS_nonneg s) hZ n L
  calc _ ≤ ∑ l ∈ range L, phiS s (kd n l) * pS n := Finset.sum_le_sum hb
    _ = (∑ l ∈ range L, phiS s (kd n l)) * pS n := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 (pS_pos n).le

end sums

end Qschubert
