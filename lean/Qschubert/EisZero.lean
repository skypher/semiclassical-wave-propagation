import Qschubert.EisZeroA
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

/-!
# The zero Fourier mode of the incomplete Eisenstein series of a test function

Stage E of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), part E3. For a test function `g` on `(0, ∞)`,
`E_g = perio modGroup (stripFn g)` and `y > 0` (`zeroMode_perio_stripFn`, the identity `ev:zero` of the manuscript):

`∫_0^1 E_g(x + iy) dx = g(y) + R_g(y)`, `R_g(y) = ∑_{c ≥ 1} φ(c) ∫_ℝ g(y / (c² (x² + y²))) dx` (`eisR`).

Proof: `E_g(z) = ∑_{(c,d)} g(Im z / |cz + d|²)` over the bottom rows up to sign (`perio_stripFn`). The sum is
dominated on the horocycle by `C ‖(c,d)‖^{-5/2}` (Mathlib's bound for Eisenstein sums on vertical strips), so sum
and integral may be exchanged. The row `(0, 1)` gives `g(y)`; for `c ≥ 1` write `d = d₀ + c n`, the sum over `n` of
the integrals over `[0, 1]` is the integral over `ℝ`, and the number of residues `d₀` prime to `c` is `φ(c)`.
-/

namespace Qschubert

open MeasureTheory Set Filter Topology Matrix UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

/-- `y / |c (x + iy) + d|²`. -/
noncomputable def hcd (c d : ℤ) (y x : ℝ) : ℝ := y / ((c * x + d) ^ 2 + (c * y) ^ 2)

lemma im_npSec_smul_mk (p : NPair) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    (npSec p • (⟨⟨x, y⟩, hy⟩ : ℍ)).im = hcd (p.1 0) (p.1 1) y x := by
  rw [im_npSec_smul, hcd, Complex.normSq_apply]
  congr 1
  simp
  ring

lemma hcd_zero_one (y x : ℝ) : hcd 0 1 y x = y := by
  simp [hcd]

lemma hcd_eq_hgt {c : ℕ} (hc : 0 < c) (d : ℤ) (y x : ℝ) :
    hcd (c : ℤ) d y x = hgt (c : ℝ) y (x + d / c) := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [hcd, hgt]
  congr 1
  push_cast
  field_simp

lemma continuous_hcd {c d : ℤ} (h : c ≠ 0 ∨ d ≠ 0) {y : ℝ} (hy : 0 < y) : Continuous (hcd c d y) := by
  unfold hcd
  refine continuous_const.div (by fun_prop) fun x => ?_
  rcases eq_or_ne c 0 with hc | hc
  · have hd : d ≠ 0 := h.resolve_left (not_not.2 hc)
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
    rw [hc]
    simp
    exact hd
  · have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    have : 0 < ((c : ℝ) * y) ^ 2 := by positivity
    positivity

lemma npair_ne_zero (p : NPair) : p.1 0 ≠ 0 ∨ p.1 1 ≠ 0 := by
  rcases p.2.2 with h | ⟨_, h⟩
  · exact Or.inl h.ne'
  · exact Or.inr (by rw [h]; exact one_ne_zero)

/-- The domination on the horocycle: `|g(Im σ(p) z)| ≤ D ‖p‖^{-5/2}` for `|Re z| ≤ 1`, `Im z = y`. -/
lemma norm_test_hcd_le {g : ℝ → ℂ} (hg : IsKTest g) {y : ℝ} (hy : 0 < y) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (p : NPair) (x : ℝ), |x| ≤ 1 →
      ‖g (hcd (p.1 0) (p.1 1) y x)‖ ≤ D * ‖p.1‖ ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := norm_test_le_exp_log hg
  set r₀ : ℝ := EisensteinSeries.r ⟨⟨1, y⟩, hy⟩ with hr₀
  have hr₀pos : 0 < r₀ := EisensteinSeries.r_pos _
  refine ⟨C * (Real.exp (5 / 4 * Real.log y) * r₀ ^ (-(5 / 2 : ℝ))), by positivity, fun p x hx => ?_⟩
  set z : ℍ := ⟨⟨x, y⟩, hy⟩ with hz
  have hstrip : z ∈ verticalStrip 1 y := ⟨hx, le_rfl⟩
  have hsb := EisensteinSeries.summand_bound_of_mem_verticalStrip (k := 5 / 2) (by norm_num) p.1 hy hstrip
  set N : ℝ := ‖((p.1 0 : ℤ) : ℂ) * (z : ℂ) + (p.1 1 : ℤ)‖ with hN
  have hNsq : (p.1 0 * x + p.1 1 : ℝ) ^ 2 + ((p.1 0 : ℝ) * y) ^ 2 = N ^ 2 := by
    rw [hN, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [hz]
    ring
  have hNpos : 0 < N := by
    rw [hN, norm_pos_iff]
    intro h0
    have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    simp [hz] at hre him
    rcases npair_ne_zero p with h | h
    · rcases him with h1 | h1
      · exact h h1
      · exact hy.ne' h1
    · rcases him with h1 | h1
      · rw [h1] at hre
        simp at hre
        exact h hre
      · exact hy.ne' h1
  have hpos : 0 < hcd (p.1 0) (p.1 1) y x := by
    rw [hcd, hNsq]
    positivity
  have hexp : Real.exp (5 / 4 * Real.log (hcd (p.1 0) (p.1 1) y x))
      = Real.exp (5 / 4 * Real.log y) * N ^ (-(5 / 2 : ℝ)) := by
    rw [hcd, hNsq, Real.log_div hy.ne' (by positivity), Real.log_pow, Real.rpow_def_of_pos hNpos, ← Real.exp_add]
    congr 1
    push_cast
    ring
  calc ‖g (hcd (p.1 0) (p.1 1) y x)‖ ≤ C * Real.exp (5 / 4 * Real.log (hcd (p.1 0) (p.1 1) y x)) := hb _ hpos
    _ = C * (Real.exp (5 / 4 * Real.log y) * N ^ (-(5 / 2 : ℝ))) := by rw [hexp]
    _ ≤ C * (Real.exp (5 / 4 * Real.log y) * (r₀ ^ (-(5 / 2 : ℝ)) * ‖p.1‖ ^ (-(5 / 2 : ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsb (Real.exp_pos _).le) hC
    _ = C * (Real.exp (5 / 4 * Real.log y) * r₀ ^ (-(5 / 2 : ℝ))) * ‖p.1‖ ^ (-(5 / 2 : ℝ)) := by ring

/-- The integral over the horocycle segment of the term with bottom row `(c, d)`. -/
noncomputable def eisA (g : ℝ → ℂ) (y : ℝ) (c d : ℤ) : ℂ := ∫ x in (0 : ℝ)..1, g (hcd c d y x)

/-- The terms indexed by `ℕ × ℤ`: zero unless `(c, d)` is a normalized coprime pair. -/
noncomputable def eisF (g : ℝ → ℂ) (y : ℝ) (cd : ℕ × ℤ) : ℂ :=
  open Classical in
  if IsCoprime (cd.1 : ℤ) cd.2 ∧ (0 < cd.1 ∨ (cd.1 = 0 ∧ cd.2 = 1)) then eisA g y cd.1 cd.2 else 0

/-- `p ↦ (c, d)` with `c` as a natural number. -/
noncomputable def npNat (p : NPair) : ℕ × ℤ := ((p.1 0).toNat, p.1 1)

lemma npair_nonneg (p : NPair) : 0 ≤ p.1 0 := by
  rcases p.2.2 with h | ⟨h, _⟩
  · exact h.le
  · exact h.ge

lemma npNat_fst (p : NPair) : ((npNat p).1 : ℤ) = p.1 0 := Int.toNat_of_nonneg (npair_nonneg p)

lemma npNat_injective : Function.Injective npNat := by
  intro p q h
  apply Subtype.ext
  funext i
  have h0 : p.1 0 = q.1 0 := by rw [← npNat_fst p, ← npNat_fst q, h]
  have h1 : p.1 1 = q.1 1 := congrArg Prod.snd h
  fin_cases i
  · exact h0
  · exact h1

lemma eisF_npNat (g : ℝ → ℂ) (y : ℝ) (p : NPair) : eisF g y (npNat p) = eisA g y (p.1 0) (p.1 1) := by
  have hc : IsCoprime ((npNat p).1 : ℤ) (npNat p).2 ∧ (0 < (npNat p).1 ∨ ((npNat p).1 = 0 ∧ (npNat p).2 = 1)) := by
    rw [npNat_fst]
    refine ⟨p.2.1, ?_⟩
    rcases p.2.2 with h | ⟨h, h'⟩
    · left
      have : (0 : ℤ) < ((npNat p).1 : ℤ) := by rw [npNat_fst]; exact h
      exact_mod_cast this
    · right
      refine ⟨?_, h'⟩
      have : ((npNat p).1 : ℤ) = 0 := by rw [npNat_fst]; exact h
      exact_mod_cast this
  rw [eisF, ite_eq_left hc, npNat_fst]
  rfl

lemma eisF_eq_zero_of_notMem (g : ℝ → ℂ) (y : ℝ) (cd : ℕ × ℤ) (h : cd ∉ Set.range npNat) : eisF g y cd = 0 := by
  rw [eisF]
  split_ifs with hc
  · exfalso
    apply h
    refine ⟨⟨![(cd.1 : ℤ), cd.2], ?_⟩, ?_⟩
    · refine ⟨by simpa using hc.1, ?_⟩
      rcases hc.2 with h1 | ⟨h1, h2⟩
      · left
        simpa using h1
      · right
        simp [h1, h2]
    · simp [npNat]
  · rfl

instance : Countable NPair := by
  unfold NPair
  infer_instance

lemma summable_npair_norm : Summable fun p : NPair => ‖p.1‖ ^ (-(5 / 2 : ℝ)) :=
  (EisensteinSeries.summable_one_div_norm_rpow (k := 5 / 2) (by norm_num)).comp_injective
    (fun p q h => Subtype.ext h)

/-- The terms with a fixed `c ≥ 1`: `∑_d F(c, d) = φ(c) ∫_ℝ g(y / (c² (x² + y²))) dx`. -/
lemma tsum_eisF_succ {g : ℝ → ℂ} (hg : IsKTest g) {y : ℝ} (hy : 0 < y) (hF_sum : Summable (eisF g y)) (k : ℕ) :
    ∑' d : ℤ, eisF g y (k + 1, d)
      = (Nat.totient (k + 1) : ℂ) * ∫ x : ℝ, g (hgt ((k + 1 : ℕ) : ℝ) y x) := by
  set c : ℕ := k + 1 with hc
  have hc0 : 0 < c := Nat.succ_pos k
  have : NeZero c := ⟨hc0.ne'⟩
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc0
  set A : ℂ := ∫ x : ℝ, g (hgt (c : ℝ) y x) with hA
  have hterm : ∀ d : ℤ, eisF g y (c, d) = if IsCoprime (c : ℤ) d then eisA g y c d else 0 := by
    intro d
    rw [eisF]
    by_cases h : IsCoprime (c : ℤ) d
    · rw [ite_eq_left (⟨h, Or.inl hc0⟩ : IsCoprime (c : ℤ) d ∧ (0 < c ∨ (c = 0 ∧ d = 1))), ite_eq_left h]
    · rw [ite_eq_right (fun h' : IsCoprime (c : ℤ) d ∧ (0 < c ∨ (c = 0 ∧ d = 1)) => h h'.1), ite_eq_right h]
  have hsd : Summable fun d : ℤ => eisF g y (c, d) := hF_sum.prod_factor c
  set e : ℤ × Fin c ≃ ℤ := (Int.divModEquiv c).symm with he
  have heval : ∀ (n : ℤ) (d₀ : Fin c), e (n, d₀) = n * c + ((d₀ : ℕ) : ℤ) := fun n d₀ => rfl
  have h1 : ∑' d : ℤ, eisF g y (c, d) = ∑' q : Fin c × ℤ, eisF g y (c, e (q.2, q.1)) := by
    rw [← e.tsum_eq, ← (Equiv.prodComm (Fin c) ℤ).tsum_eq]
    rfl
  have hsq : Summable fun q : Fin c × ℤ => eisF g y (c, e (q.2, q.1)) :=
    (Equiv.prodComm (Fin c) ℤ).summable_iff.2 (e.summable_iff.2 hsd)
  rw [h1, hsq.tsum_prod' fun d₀ => hsq.prod_factor d₀, tsum_fintype]
  have hinner : ∀ d₀ : Fin c, ∑' n : ℤ, eisF g y (c, e (n, d₀)) = if Nat.Coprime c d₀ then A else 0 := by
    intro d₀
    have hcop : ∀ n : ℤ, IsCoprime (c : ℤ) (e (n, d₀)) ↔ Nat.Coprime c d₀ := by
      intro n
      rw [heval, add_comm, IsCoprime.add_mul_right_right_iff, Nat.isCoprime_iff_coprime]
    by_cases hd : Nat.Coprime c d₀
    · rw [ite_eq_left hd]
      have hf : Integrable fun x : ℝ => g (hgt (c : ℝ) y (x + ((d₀ : ℕ) : ℝ) / c)) :=
        (integrable_test_hgt hg hcR hy).comp_add_right _
      have hs := hasSum_intervalIntegral_translates hf
      have hval : ∀ n : ℤ, eisF g y (c, e (n, d₀))
          = ∫ x in (0 : ℝ)..1, g (hgt (c : ℝ) y (x + n + ((d₀ : ℕ) : ℝ) / c)) := by
        intro n
        rw [hterm, ite_eq_left ((hcop n).2 hd), eisA]
        refine intervalIntegral.integral_congr fun x _ => ?_
        show g (hcd (c : ℤ) (e (n, d₀)) y x) = g (hgt (c : ℝ) y (x + n + ((d₀ : ℕ) : ℝ) / c))
        rw [hcd_eq_hgt hc0, heval]
        congr 2
        push_cast
        field_simp
        ring
      simp_rw [hval]
      rw [hs.tsum_eq, hA]
      exact integral_add_right_eq_self (fun x => g (hgt (c : ℝ) y x)) _
    · rw [ite_eq_right hd]
      have h0 : ∀ n : ℤ, eisF g y (c, e (n, d₀)) = 0 := fun n => by
        rw [hterm, ite_eq_right (fun h => hd ((hcop n).1 h))]
      simp_rw [h0]
      exact tsum_zero
  simp_rw [hinner]
  exact sum_coprime_fin c A

/-- **The zero Fourier mode of the incomplete Eisenstein series** (`ev:zero`). -/
theorem zeroMode_perio_stripFn {g : ℝ → ℂ} (hg : IsKTest g) {y : ℝ} (hy : 0 < y) :
    ∫ x in (0 : ℝ)..1, perio modGroup (stripFn g) (surfMk modGroup ⟨⟨x, y⟩, hy⟩) = g y + eisR g y := by
  obtain ⟨D, hD, hdom⟩ := norm_test_hcd_le hg hy
  have hsumM : Summable fun p : NPair => D * ‖p.1‖ ^ (-(5 / 2 : ℝ)) := summable_npair_norm.mul_left D
  have hpt : ∀ x : ℝ, perio modGroup (stripFn g) (surfMk modGroup ⟨⟨x, y⟩, hy⟩)
      = ∑' p : NPair, g (hcd (p.1 0) (p.1 1) y x) := fun x => by
    rw [perio_stripFn hg]
    exact tsum_congr fun p => by rw [im_npSec_smul_mk]
  simp_rw [hpt]
  have hcontp : ∀ p : NPair, Continuous fun x : ℝ => g (hcd (p.1 0) (p.1 1) y x) := fun p =>
    hg.continuous.comp (continuous_hcd (npair_ne_zero p) hy)
  have hx01 : ∀ x : ℝ, x ∈ Set.uIoc (0 : ℝ) 1 → |x| ≤ 1 := fun x hx => by
    rw [Set.uIoc_of_le zero_le_one] at hx
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hstep1 : HasSum (fun p : NPair => eisA g y (p.1 0) (p.1 1))
      (∫ x in (0 : ℝ)..1, ∑' p : NPair, g (hcd (p.1 0) (p.1 1) y x)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun p _ => D * ‖p.1‖ ^ (-(5 / 2 : ℝ)))
      (fun p => (hcontp p).aestronglyMeasurable) (fun p => Eventually.of_forall fun x hx => hdom p x (hx01 x hx))
      (Eventually.of_forall fun x _ => hsumM) intervalIntegrable_const
      (Eventually.of_forall fun x hx => ?_)
    exact (Summable.of_norm_bounded hsumM fun p => hdom p x (hx01 x hx)).hasSum
  rw [← hstep1.tsum_eq]
  have hF_eq : ∑' p : NPair, eisA g y (p.1 0) (p.1 1) = ∑' cd : ℕ × ℤ, eisF g y cd := by
    rw [← npNat_injective.tsum_eq (f := eisF g y) (fun cd hcd => by
      by_contra hne
      exact hcd (eisF_eq_zero_of_notMem g y cd hne))]
    exact tsum_congr fun p => (eisF_npNat g y p).symm
  have hF_sum : Summable (eisF g y) := by
    have h2 : Summable (eisF g y ∘ npNat) := hstep1.summable.congr fun p => (eisF_npNat g y p).symm
    exact (npNat_injective.summable_iff (fun cd hcd => eisF_eq_zero_of_notMem g y cd hcd)).1 h2
  rw [hF_eq, hF_sum.tsum_prod' fun c => hF_sum.prod_factor c]
  have hH0 : ∑' d : ℤ, eisF g y (0, d) = g y := by
    rw [tsum_eq_single 1]
    · have hc : IsCoprime ((0 : ℕ) : ℤ) (1 : ℤ) ∧ (0 < (0 : ℕ) ∨ ((0 : ℕ) = 0 ∧ (1 : ℤ) = 1)) :=
        ⟨isCoprime_one_right, Or.inr ⟨rfl, rfl⟩⟩
      rw [eisF, ite_eq_left hc, eisA]
      simp [hcd_zero_one]
    · intro d hd
      rw [eisF, ite_eq_right]
      rintro ⟨_, h | ⟨_, h⟩⟩
      · exact lt_irrefl _ h
      · exact hd h
  have hHc := tsum_eisF_succ hg hy hF_sum
  have hHsum : Summable fun c : ℕ => ∑' d : ℤ, eisF g y (c, d) := hF_sum.prod
  rw [hHsum.tsum_eq_zero_add, hH0]
  congr 1
  rw [eisR]
  have hs2 : Summable fun c : ℕ => (Nat.totient c : ℂ) * ∫ x : ℝ, g (hgt c y x) := by
    rw [← summable_nat_add_iff 1]
    exact ((summable_nat_add_iff 1).2 hHsum).congr fun k => hHc k
  rw [hs2.tsum_eq_zero_add]
  simp only [Nat.totient_zero, Nat.cast_zero, zero_mul, zero_add]
  exact tsum_congr fun k => hHc k

end Qschubert
