import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-!
# Complete Formal Proof of OEIS A227012

This file formally proves all four conjectured formulas on OEIS A227012
(Clark Kimberling, July 1, 2013; Franck Maminirina Ramaharo, April 12, 2018):

  `a(n) = floor(M(n))`, where `M(n) = (n^3 - (n-1)^3) / (H_{n^3} - H_{(n-1)^3})`,
  and `H_N = ∑_{k=1}^N 1/k`.

All four theorems are proved with zero `sorry`s and only standard axioms:
1. `a227012_ramaharo`: Ramaharo's floor formula for all `n ≥ 1`.
2. `a227012_trig`: Kimberling's trigonometric closed form for `a(k + 2)` (`k ≥ 1`).
3. `a227012_recurrence`: Kimberling's order-7 linear recurrence for all `n ≥ 10`.
4. `a227012_gf`: Kimberling's rational generating function identity in `PowerSeries ℤ`.
-/

namespace OEIS_A227012

open Real Finset

/-- The `N`-th harmonic number `H_N = ∑_{k=1}^N 1/k` (with `H_0 = 0`). -/
noncomputable def H (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ)

/-- The harmonic mean `M(n)` of the integers `(n-1)^3 + 1, ..., n^3`. -/
noncomputable def M (n : ℕ) : ℝ :=
  ((n : ℝ) ^ 3 - ((n - 1 : ℕ) : ℝ) ^ 3) / (H (n ^ 3) - H ((n - 1) ^ 3))

/-- OEIS A227012: `a(n) = ⌊M(n)⌋`. -/
noncomputable def a (n : ℕ) : ℤ :=
  ⌊M n⌋

/-- Ramaharo's closed-form expression for `a(n)`. -/
def aFormula (n : ℕ) : ℤ :=
  (2 * (n : ℤ) ^ 3 - 3 * (n : ℤ) ^ 2 + (n : ℤ) + 2) / 2 + max 0 ((n : ℤ) - 3) / 4

/-! ### Part 1: Elementary Derivative-Based Logarithm Bounds -/

private lemma hasDerivAt_log_ratio {x : ℝ} (hx0 : -1 < x) (hx1 : x < 1) :
    HasDerivAt (fun t => Real.log ((1 + t) / (1 - t))) (2 / (1 - x ^ 2)) x := by
  have h1 : 0 < 1 + x := by linarith
  have h2 : 0 < 1 - x := by linarith
  have hq : ((1 + x) / (1 - x)) ≠ 0 := (div_pos h1 h2).ne'
  have hd_num : HasDerivAt (fun t : ℝ => 1 + t) 1 x := (hasDerivAt_id x).const_add 1
  have hd_den : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have hd_div := hd_num.div hd_den h2.ne'
  have hd_log := hd_div.log hq
  convert hd_log using 1
  have h1x2 : 1 - x ^ 2 ≠ 0 := by nlinarith
  simp only [Pi.div_apply]
  field_simp [h1.ne', h2.ne', h1x2]
  ring

/-- Helper: if `f 0 = 0`, `f` is continuous on `[0, x]`, and `f' > 0` on `(0, x)`, then `f x > 0`. -/
private lemma pos_of_deriv_pos_on_Ioo {f f' : ℝ → ℝ} {x : ℝ} (hx : 0 < x)
    (hf0 : f 0 = 0)
    (hcont : ContinuousOn f (Set.Icc 0 x))
    (hderiv : ∀ t ∈ Set.Ioo 0 x, HasDerivAt f (f' t) t)
    (hpos : ∀ t ∈ Set.Ioo 0 x, 0 < f' t) :
    0 < f x := by
  have hmono : StrictMonoOn f (Set.Icc 0 x) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 x) hcont (fun t ht => by
      rw [interior_Icc] at ht
      rw [(hderiv t ht).deriv]
      exact hpos t ht)
  have := hmono (Set.left_mem_Icc.mpr hx.le) (Set.right_mem_Icc.mpr hx.le) hx
  linarith

/-- `2x < log((1+x)/(1-x))` for `0 < x < 1`. -/
lemma log_ratio_gt_two_mul {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    2 * x < Real.log ((1 + x) / (1 - x)) := by
  let f : ℝ → ℝ := fun t => Real.log ((1 + t) / (1 - t)) - 2 * t
  let f' : ℝ → ℝ := fun t => 2 * t ^ 2 / (1 - t ^ 2)
  have hderiv_all : ∀ t ∈ Set.Icc 0 x, HasDerivAt f (f' t) t := by
    intro t ht
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hx1
    have h1 : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht1]
    have hd_log := hasDerivAt_log_ratio (by linarith [ht.1]) ht1
    have hd_lin : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
      simpa using (hasDerivAt_id t).const_mul 2
    have hd := hd_log.sub hd_lin
    convert hd using 1
    dsimp [f']
    field_simp [h1]
    ring
  have hpos : 0 < f x := pos_of_deriv_pos_on_Ioo hx0 (by simp [f])
    (fun t ht => (hderiv_all t ht).continuousAt.continuousWithinAt)
    (fun t ht => hderiv_all t ⟨ht.1.le, ht.2.le⟩)
    (fun t ht => by
      have ht0 : 0 < t := ht.1
      have ht1 : t < 1 := lt_trans ht.2 hx1
      have h1 : 0 < 1 - t ^ 2 := by nlinarith
      dsimp [f']
      exact div_pos (by positivity) h1)
  dsimp [f] at hpos
  linarith

/-- `log((1+x)/(1-x)) < 2x + 2x^3 / (3(1 - x^2))` for `0 < x < 1`. -/
lemma log_ratio_lt_cubic {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Real.log ((1 + x) / (1 - x)) < 2 * x + 2 * x ^ 3 / (3 * (1 - x ^ 2)) := by
  let f : ℝ → ℝ := fun t => 2 * t + 2 * t ^ 3 / (3 * (1 - t ^ 2)) - Real.log ((1 + t) / (1 - t))
  let f' : ℝ → ℝ := fun t => 4 * t ^ 4 / (3 * (1 - t ^ 2) ^ 2)
  have hderiv_all : ∀ t ∈ Set.Icc 0 x, HasDerivAt f (f' t) t := by
    intro t ht
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hx1
    have hden : 3 * (1 - t ^ 2) ≠ 0 := by nlinarith [ht.1, ht1]
    have h1 : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht1]
    have hd_num : HasDerivAt (fun s : ℝ => 2 * s ^ 3) (6 * t ^ 2) t := by
      have := ((hasDerivAt_pow 3 t).const_mul 2)
      convert this using 1; ring
    have hd_den : HasDerivAt (fun s : ℝ => 3 * (1 - s ^ 2)) (-6 * t) t := by
      have := (((hasDerivAt_pow 2 t).const_sub 1).const_mul 3)
      convert this using 1; ring
    have hd_frac := hd_num.div hd_den hden
    have hd_lin : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
      simpa using (hasDerivAt_id t).const_mul 2
    have hd_log := hasDerivAt_log_ratio (by linarith [ht.1]) ht1
    have hd := (hd_lin.add hd_frac).sub hd_log
    convert hd using 1
    dsimp [f']
    field_simp [hden, h1]
    ring
  have hpos : 0 < f x := pos_of_deriv_pos_on_Ioo hx0 (by simp [f])
    (fun t ht => (hderiv_all t ht).continuousAt.continuousWithinAt)
    (fun t ht => hderiv_all t ⟨ht.1.le, ht.2.le⟩)
    (fun t ht => by
      have ht0 : 0 < t := ht.1
      have ht1 : t < 1 := lt_trans ht.2 hx1
      have h1 : 0 < 1 - t ^ 2 := by nlinarith
      dsimp [f']
      exact div_pos (by positivity) (by positivity))
  dsimp [f] at hpos
  linarith

/-- `2x + 2x^3/3 + 2x^5/5 < log((1+x)/(1-x))` for `0 < x < 1`. -/
lemma log_ratio_gt_quintic {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    2 * x + 2 * x ^ 3 / 3 + 2 * x ^ 5 / 5 < Real.log ((1 + x) / (1 - x)) := by
  let f : ℝ → ℝ := fun t => Real.log ((1 + t) / (1 - t)) - (2 * t + 2 * t ^ 3 / 3 + 2 * t ^ 5 / 5)
  let f' : ℝ → ℝ := fun t => 2 * t ^ 6 / (1 - t ^ 2)
  have hderiv_all : ∀ t ∈ Set.Icc 0 x, HasDerivAt f (f' t) t := by
    intro t ht
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hx1
    have h1 : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht1]
    have hd_log := hasDerivAt_log_ratio (by linarith [ht.1]) ht1
    have hd_p1 : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by simpa using (hasDerivAt_id t).const_mul 2
    have hd_p3 : HasDerivAt (fun s : ℝ => 2 * s ^ 3 / 3) (2 * t ^ 2) t := by
      have := ((hasDerivAt_pow 3 t).const_mul 2).div_const 3
      convert this using 1; ring
    have hd_p5 : HasDerivAt (fun s : ℝ => 2 * s ^ 5 / 5) (2 * t ^ 4) t := by
      have := ((hasDerivAt_pow 5 t).const_mul 2).div_const 5
      convert this using 1; ring
    have hd := hd_log.sub ((hd_p1.add hd_p3).add hd_p5)
    convert hd using 1
    dsimp [f']
    field_simp [h1]
    ring
  have hpos : 0 < f x := pos_of_deriv_pos_on_Ioo hx0 (by simp [f])
    (fun t ht => (hderiv_all t ht).continuousAt.continuousWithinAt)
    (fun t ht => hderiv_all t ⟨ht.1.le, ht.2.le⟩)
    (fun t ht => by
      have ht0 : 0 < t := ht.1
      have ht1 : t < 1 := lt_trans ht.2 hx1
      have h1 : 0 < 1 - t ^ 2 := by nlinarith
      dsimp [f']
      exact div_pos (by positivity) h1)
  dsimp [f] at hpos
  linarith

/-- `log((1+x)/(1-x)) < 2x + 2x^3/3 + 2x^5 / (5(1 - x^2))` for `0 < x < 1`. -/
lemma log_ratio_lt_quintic {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Real.log ((1 + x) / (1 - x)) < 2 * x + 2 * x ^ 3 / 3 + 2 * x ^ 5 / (5 * (1 - x ^ 2)) := by
  let f : ℝ → ℝ := fun t =>
    2 * t + 2 * t ^ 3 / 3 + 2 * t ^ 5 / (5 * (1 - t ^ 2)) - Real.log ((1 + t) / (1 - t))
  let f' : ℝ → ℝ := fun t => 4 * t ^ 6 / (5 * (1 - t ^ 2) ^ 2)
  have hderiv_all : ∀ t ∈ Set.Icc 0 x, HasDerivAt f (f' t) t := by
    intro t ht
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hx1
    have hden : 5 * (1 - t ^ 2) ≠ 0 := by nlinarith [ht.1, ht1]
    have h1 : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht1]
    have hd_p1 : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by simpa using (hasDerivAt_id t).const_mul 2
    have hd_p3 : HasDerivAt (fun s : ℝ => 2 * s ^ 3 / 3) (2 * t ^ 2) t := by
      have := ((hasDerivAt_pow 3 t).const_mul 2).div_const 3
      convert this using 1; ring
    have hd_num : HasDerivAt (fun s : ℝ => 2 * s ^ 5) (10 * t ^ 4) t := by
      have := ((hasDerivAt_pow 5 t).const_mul 2)
      convert this using 1; ring
    have hd_den : HasDerivAt (fun s : ℝ => 5 * (1 - s ^ 2)) (-10 * t) t := by
      have := (((hasDerivAt_pow 2 t).const_sub 1).const_mul 5)
      convert this using 1; ring
    have hd_frac := hd_num.div hd_den hden
    have hd_log := hasDerivAt_log_ratio (by linarith [ht.1]) ht1
    have hd := ((hd_p1.add hd_p3).add hd_frac).sub hd_log
    convert hd using 1
    dsimp [f']
    field_simp [hden, h1]
    ring
  have hpos : 0 < f x := pos_of_deriv_pos_on_Ioo hx0 (by simp [f])
    (fun t ht => (hderiv_all t ht).continuousAt.continuousWithinAt)
    (fun t ht => hderiv_all t ⟨ht.1.le, ht.2.le⟩)
    (fun t ht => by
      have ht0 : 0 < t := ht.1
      have ht1 : t < 1 := lt_trans ht.2 hx1
      have h1 : 0 < 1 - t ^ 2 := by nlinarith
      dsimp [f']
      exact div_pos (by positivity) (by positivity))
  dsimp [f] at hpos
  linarith

/-! ### Part 2: Lemma 3 (Telescoping Logarithm Bound on Harmonic Differences) -/

lemma harmonic_sub_eq_sum {p q : ℕ} (hpq : p ≤ q) :
    H q - H p = ∑ k ∈ Finset.Icc (p + 1) q, (1 : ℝ) / (k : ℝ) := by
  unfold H
  have hunion : Finset.Icc 1 q = Finset.Icc 1 p ∪ Finset.Icc (p + 1) q := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 p) (Finset.Icc (p + 1) q) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1 hk2
    omega
  rw [hunion, Finset.sum_union hdisj]
  ring

/-- Single-term telescoping step for `k ≥ 2`. -/
private lemma harmonic_step_bounds {k : ℕ} (hk : 2 ≤ k) :
    0 < Real.log (((k : ℝ) + 1 / 2) / ((k : ℝ) - 1 / 2)) - 1 / (k : ℝ) ∧
    Real.log (((k : ℝ) + 1 / 2) / ((k : ℝ) - 1 / 2)) - 1 / (k : ℝ) <
      (1 / 24 : ℝ) * (1 / (((k : ℝ) - 1) * (k : ℝ)) - 1 / ((k : ℝ) * ((k : ℝ) + 1))) := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hx0 : 0 < (1 : ℝ) / (2 * (k : ℝ)) := by positivity
  have hx1 : (1 : ℝ) / (2 * (k : ℝ)) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have hratio : (1 + (1 : ℝ) / (2 * (k : ℝ))) / (1 - (1 : ℝ) / (2 * (k : ℝ))) =
      ((k : ℝ) + 1 / 2) / ((k : ℝ) - 1 / 2) := by
    have h1 : (k : ℝ) - 1 / 2 ≠ 0 := by linarith
    field_simp [hkpos.ne', h1]
  have hlo := log_ratio_gt_two_mul hx0 hx1
  have hhi := log_ratio_lt_cubic hx0 hx1
  rw [hratio] at hlo hhi
  have h2x : 2 * ((1 : ℝ) / (2 * (k : ℝ))) = 1 / (k : ℝ) := by
    field_simp [hkpos.ne']
  rw [h2x] at hlo hhi
  refine ⟨by linarith, ?_⟩
  have hterm : 2 * ((1 : ℝ) / (2 * (k : ℝ))) ^ 3 / (3 * (1 - ((1 : ℝ) / (2 * (k : ℝ))) ^ 2)) =
      1 / (3 * (k : ℝ) * (4 * (k : ℝ) ^ 2 - 1)) := by
    have h1 : 4 * (k : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp [hkpos.ne', h1]
    ring
  rw [hterm] at hhi
  have hcomp : 1 / (3 * (k : ℝ) * (4 * (k : ℝ) ^ 2 - 1)) <
      (1 / 24 : ℝ) * (1 / (((k : ℝ) - 1) * (k : ℝ)) - 1 / ((k : ℝ) * ((k : ℝ) + 1))) := by
    have hpf : (1 / 24 : ℝ) * (1 / (((k : ℝ) - 1) * (k : ℝ)) - 1 / ((k : ℝ) * ((k : ℝ) + 1))) =
        1 / (12 * ((k : ℝ) - 1) * (k : ℝ) * ((k : ℝ) + 1)) := by
      have hkm1 : (k : ℝ) - 1 ≠ 0 := by linarith
      have hkp1 : (k : ℝ) + 1 ≠ 0 := by linarith
      field_simp [hkm1, hkpos.ne', hkp1]
      ring
    rw [hpf]
    apply one_div_lt_one_div_of_lt
    · nlinarith
    · nlinarith
  linarith

/-- Telescoping sum of `log((k + 1/2)/(k - 1/2))` over `k ∈ [p + 1, q]`. -/
private lemma sum_log_telescope {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    ∑ k ∈ Finset.Icc (p + 1) q, Real.log (((k : ℝ) + 1 / 2) / ((k : ℝ) - 1 / 2)) =
      Real.log (((q : ℝ) + 1 / 2) / ((p : ℝ) + 1 / 2)) := by
  induction q, hpq using Nat.le_induction with
  | base =>
    simp
  | succ m hm ih =>
    have hIcc : Finset.Icc (p + 1) (m + 1) = insert (m + 1) (Finset.Icc (p + 1) m) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnotmem : m + 1 ∉ Finset.Icc (p + 1) m := by simp
    rw [hIcc, Finset.sum_insert hnotmem, ih]
    have hp_pos : (0 : ℝ) < (p : ℝ) + 1 / 2 := by positivity
    have hm_pos : (0 : ℝ) < (m : ℝ) + 1 / 2 := by positivity
    have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) + 1 / 2 := by positivity
    have hsub : ((m + 1 : ℕ) : ℝ) - 1 / 2 = (m : ℝ) + 1 / 2 := by push_cast; ring
    rw [hsub, ← Real.log_mul (div_pos hm1_pos hm_pos).ne' (div_pos hm_pos hp_pos).ne']
    congr 1
    field_simp [hm_pos.ne', hp_pos.ne']

/-- Telescoping sum of `1/((k-1)k) - 1/(k(k+1))` over `k ∈ [p + 1, q]`. -/
private lemma sum_inv_telescope {p q : ℕ} (_hp : 1 ≤ p) (hpq : p ≤ q) :
    ∑ k ∈ Finset.Icc (p + 1) q,
        (1 / (((k : ℝ) - 1) * (k : ℝ)) - 1 / ((k : ℝ) * ((k : ℝ) + 1))) =
      1 / ((p : ℝ) * ((p : ℝ) + 1)) - 1 / ((q : ℝ) * ((q : ℝ) + 1)) := by
  induction q, hpq using Nat.le_induction with
  | base =>
    simp
  | succ m hm ih =>
    have hIcc : Finset.Icc (p + 1) (m + 1) = insert (m + 1) (Finset.Icc (p + 1) m) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnotmem : m + 1 ∉ Finset.Icc (p + 1) m := by simp
    rw [hIcc, Finset.sum_insert hnotmem, ih]
    push_cast
    ring

/-- **Lemma 3 (Telescoping Logarithm Bound)**: For all integers `q > p ≥ 1`,
`0 < log((q + 1/2)/(p + 1/2)) - (H q - H p) < (1/24) * (1/(p(p+1)) - 1/(q(q+1)))`. -/
theorem harmonic_log_bounds {p q : ℕ} (hp : 1 ≤ p) (hpq : p < q) :
    0 < Real.log (((q : ℝ) + 1 / 2) / ((p : ℝ) + 1 / 2)) - (H q - H p) ∧
    Real.log (((q : ℝ) + 1 / 2) / ((p : ℝ) + 1 / 2)) - (H q - H p) <
      (1 / 24 : ℝ) * (1 / ((p : ℝ) * ((p : ℝ) + 1)) - 1 / ((q : ℝ) * ((q : ℝ) + 1))) := by
  have hne : (Finset.Icc (p + 1) q).Nonempty := ⟨p + 1, Finset.mem_Icc.mpr ⟨le_rfl, hpq⟩⟩
  rw [harmonic_sub_eq_sum hpq.le, ← sum_log_telescope hp hpq.le, ← Finset.sum_sub_distrib]
  constructor
  · exact Finset.sum_pos (fun k hk => (harmonic_step_bounds (by
      have := (Finset.mem_Icc.mp hk).1; omega)).1) hne
  · rw [← sum_inv_telescope hp hpq.le, Finset.mul_sum]
    exact Finset.sum_lt_sum_of_nonempty hne (fun k hk => (harmonic_step_bounds (by
      have := (Finset.mem_Icc.mp hk).1; omega)).2)

/-! ### Part 3: Analytic Bounds on `M(n)` for `n ≥ 2` -/

/-- For every `n ≥ 2`, `M(n)` is strictly sandwiched between explicit rational bounds. -/
lemma M_analytic_sandwich {n : ℕ} (hn : 2 ≤ n) :
    let u : ℝ := (n : ℝ) - 1 / 2
    let twoD : ℝ := 3 * u ^ 2 + 1 / 4
    let S : ℝ := u ^ 3 + 3 / 4 * u + 1 / 2
    let t : ℝ := twoD / (2 * S)
    let p : ℝ := ((n - 1 : ℕ) : ℝ) ^ 3
    let L_hi : ℝ := 2 * t + 2 * t ^ 3 / 3 + 2 * t ^ 5 / (5 * (1 - t ^ 2))
    let L_lo : ℝ := 2 * t + 2 * t ^ 3 / 3 + 2 * t ^ 5 / 5
    let E_hi : ℝ := 1 / (24 * p * (p + 1))
    twoD / L_hi < M n ∧ (0 < L_lo - E_hi → M n < twoD / (L_lo - E_hi)) := by
  intro u twoD S t p L_hi L_lo E_hi
  have hp_nat : 1 ≤ (n - 1) ^ 3 := Nat.one_le_pow 3 (n - 1) (by omega)
  have hpq_nat : (n - 1) ^ 3 < n ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have hu : (3 / 2 : ℝ) ≤ u := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    dsimp [u]; linarith
  have hu0 : 0 < u := by linarith
  have hnm1 : ((n - 1 : ℕ) : ℝ) = u - 1 / 2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; dsimp [u]; ring
  have hn_eq : (n : ℝ) = u + 1 / 2 := by dsimp [u]; ring
  have htwoD_eq : ((n : ℝ) ^ 3 - ((n - 1 : ℕ) : ℝ) ^ 3) = twoD := by
    rw [hn_eq, hnm1]; dsimp [twoD]; ring
  have htwoD_pos : 0 < twoD := by dsimp [twoD]; positivity
  have hS_pos : 0 < S := by dsimp [S]; positivity
  have ht_pos : 0 < t := by dsimp [t]; positivity
  have hSD : S - twoD / 2 = p + 1 / 2 := by
    dsimp [S, twoD, p]; rw [hnm1]; ring
  have hSD_add : S + twoD / 2 = (n : ℝ) ^ 3 + 1 / 2 := by
    dsimp [S, twoD]; rw [hn_eq]; ring
  have hp_pos : 0 < p := by dsimp [p]; rw [hnm1]; exact pow_pos (by linarith) 3
  have ht_lt_one : t < 1 := by
    dsimp [t]
    rw [div_lt_one (by linarith)]
    linarith [hSD]
  have hratio : (1 + t) / (1 - t) = (((n ^ 3 : ℕ) : ℝ) + 1 / 2) / ((((n - 1) ^ 3 : ℕ) : ℝ) + 1 / 2) := by
    have h1t : 1 - t = (p + 1 / 2) / S := by
      dsimp [t]; field_simp [hS_pos.ne']; linarith [hSD]
    have h1pt : 1 + t = ((n : ℝ) ^ 3 + 1 / 2) / S := by
      dsimp [t]; field_simp [hS_pos.ne']; linarith [hSD_add]
    rw [h1pt, h1t, div_div_div_cancel_right₀ hS_pos.ne']
    push_cast; rfl
  have hH_bounds := harmonic_log_bounds hp_nat hpq_nat
  have hH_pos : 0 < H (n ^ 3) - H ((n - 1) ^ 3) := by
    rw [harmonic_sub_eq_sum hpq_nat.le]
    exact Finset.sum_pos (fun k hk => by
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (by have := (Finset.mem_Icc.mp hk).1; omega : 1 ≤ k)
      positivity) ⟨(n - 1) ^ 3 + 1, Finset.mem_Icc.mpr ⟨le_rfl, hpq_nat⟩⟩
  have hL_hi : Real.log ((1 + t) / (1 - t)) < L_hi := log_ratio_lt_quintic ht_pos ht_lt_one
  have hL_lo : L_lo < Real.log ((1 + t) / (1 - t)) := log_ratio_gt_quintic ht_pos ht_lt_one
  have hE_lt : Real.log ((1 + t) / (1 - t)) - (H (n ^ 3) - H ((n - 1) ^ 3)) < E_hi := by
    rw [hratio]
    have h2 := hH_bounds.2
    have hq_pos : (0 : ℝ) < ((n ^ 3 : ℕ) : ℝ) * (((n ^ 3 : ℕ) : ℝ) + 1) := by positivity
    have hsub_pos : (0 : ℝ) < 1 / (((n ^ 3 : ℕ) : ℝ) * (((n ^ 3 : ℕ) : ℝ) + 1)) := by positivity
    have hp_cast : (((n - 1) ^ 3 : ℕ) : ℝ) = p := by push_cast; rfl
    rw [hp_cast] at h2 ⊢
    have hE_eq : (1 / 24 : ℝ) * (1 / (p * (p + 1))) = E_hi := by
      dsimp [E_hi]; field_simp
    linarith
  have hH_lt_Lhi : H (n ^ 3) - H ((n - 1) ^ 3) < L_hi := by
    have h1 := hH_bounds.1
    rw [← hratio] at h1
    linarith
  have hLlo_lt_H : L_lo - E_hi < H (n ^ 3) - H ((n - 1) ^ 3) := by linarith
  unfold M
  rw [htwoD_eq]
  constructor
  · exact div_lt_div_of_pos_left htwoD_pos hH_pos hH_lt_Lhi
  · intro hpos
    exact div_lt_div_of_pos_left htwoD_pos hpos hLlo_lt_H

/-! ### Part 4: Propositions 4 & 5 (`|M(n) - (u^3 + 1/2)| < 1/8` for all `n ≥ 12`) -/

/-- **Proposition 4 (Lower Bound)**: `u^3 + 3/8 < M(n)` for all `n ≥ 12`. -/
lemma M_gt_lower {n : ℕ} (hn : 12 ≤ n) :
    ((n : ℝ) - 1 / 2) ^ 3 + 3 / 8 < M n := by
  have hsand := (M_analytic_sandwich (by omega : 2 ≤ n)).1
  set u : ℝ := (n : ℝ) - 1 / 2
  set twoD : ℝ := 3 * u ^ 2 + 1 / 4
  set S : ℝ := u ^ 3 + 3 / 4 * u + 1 / 2
  set t : ℝ := twoD / (2 * S)
  set L_hi : ℝ := 2 * t + 2 * t ^ 3 / 3 + 2 * t ^ 5 / (5 * (1 - t ^ 2))
  have hu : (23 / 2 : ℝ) ≤ u := by
    have : (12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    dsimp [u]; linarith
  have hu0 : 0 < u := by linarith
  have hS_pos : 0 < S := by dsimp [S]; positivity
  have htwoD_pos : 0 < twoD := by dsimp [twoD]; positivity
  have ht_pos : 0 < t := by dsimp [t]; positivity
  have ht_upper : t < 3 / (2 * u) := by
    dsimp [t]
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    dsimp [twoD, S]; nlinarith
  have ht_half : t < 1 / 2 := by
    have : 3 / (2 * u) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have h1t2 : (3 / 4 : ℝ) < 1 - t ^ 2 := by nlinarith
  have hL_hi_pos : 0 < L_hi := by dsimp [L_hi]; positivity
  have hbracket : t ^ 2 / 3 + t ^ 4 / (5 * (1 - t ^ 2)) <
      (3 / 4 * u + 1 / 8) / (u ^ 3 + 3 / 8) := by
    have ht2 : t ^ 2 / 3 < 3 / (4 * u ^ 2) := by
      have : t ^ 2 < (3 / (2 * u)) ^ 2 := sq_lt_sq' (by linarith) ht_upper
      have hsq : (3 / (2 * u)) ^ 2 / 3 = 3 / (4 * u ^ 2) := by
        field_simp [hu0.ne']; ring
      linarith
    have ht4 : t ^ 4 / (5 * (1 - t ^ 2)) < 27 / (20 * u ^ 4) := by
      have ht4_num : t ^ 4 < (3 / (2 * u)) ^ 4 := by
        have h1 : t ^ 2 < (3 / (2 * u)) ^ 2 := sq_lt_sq' (by linarith) ht_upper
        nlinarith [sq_nonneg t]
      have h5 : (15 / 4 : ℝ) < 5 * (1 - t ^ 2) := by linarith
      have hstep : t ^ 4 / (5 * (1 - t ^ 2)) < (3 / (2 * u)) ^ 4 / (15 / 4) :=
        div_lt_div₀ ht4_num h5.le (by positivity) (by positivity)
      have hval : (3 / (2 * u)) ^ 4 / (15 / 4) = 27 / (20 * u ^ 4) := by
        field_simp [hu0.ne']; ring
      linarith
    have hdiff : (3 / 4 * u + 1 / 8) / (u ^ 3 + 3 / 8) - (3 / (4 * u ^ 2) + 27 / (20 * u ^ 4)) =
        (20 * u ^ 4 - 216 * u ^ 3 - 45 * u ^ 2 - 81) / (20 * u ^ 4 * (8 * u ^ 3 + 3)) := by
      have hd1 : u ^ 3 + 3 / 8 ≠ 0 := by positivity
      have hd2 : 8 * u ^ 3 + 3 ≠ 0 := by positivity
      field_simp [hu0.ne', hd1, hd2]
      ring
    have hnum_pos : 0 < 20 * u ^ 4 - 216 * u ^ 3 - 45 * u ^ 2 - 81 := by
      have h1 : 14 * u ^ 3 ≤ 20 * u ^ 4 - 216 * u ^ 3 := by
        have := mul_le_mul_of_nonneg_right (show (14 : ℝ) ≤ 20 * u - 216 by linarith) (pow_nonneg hu0.le 3)
        linarith
      have h2 : 116 * u ^ 2 ≤ 14 * u ^ 3 - 45 * u ^ 2 := by
        have := mul_le_mul_of_nonneg_right (show (116 : ℝ) ≤ 14 * u - 45 by linarith) (sq_nonneg u)
        linarith
      nlinarith
    have hden_pos : 0 < 20 * u ^ 4 * (8 * u ^ 3 + 3) := by positivity
    have : 0 < (3 / 4 * u + 1 / 8) / (u ^ 3 + 3 / 8) - (3 / (4 * u ^ 2) + 27 / (20 * u ^ 4)) := by
      rw [hdiff]; exact div_pos hnum_pos hden_pos
    linarith
  have hgoal : u ^ 3 + 3 / 8 < twoD / L_hi := by
    rw [lt_div_iff₀ hL_hi_pos]
    have hL_eq : L_hi = (twoD / S) * (1 + t ^ 2 / 3 + t ^ 4 / (5 * (1 - t ^ 2))) := by
      dsimp [L_hi, t]; field_simp [hS_pos.ne', show 1 - t ^ 2 ≠ 0 by linarith]
    rw [hL_eq]
    have hu3_pos : 0 < u ^ 3 + 3 / 8 := by positivity
    have h1 : 1 + t ^ 2 / 3 + t ^ 4 / (5 * (1 - t ^ 2)) < S / (u ^ 3 + 3 / 8) := by
      have hS_split : S / (u ^ 3 + 3 / 8) = 1 + (3 / 4 * u + 1 / 8) / (u ^ 3 + 3 / 8) := by
        dsimp [S]; field_simp [hu3_pos.ne']; ring
      linarith
    have h2 : (u ^ 3 + 3 / 8) * (1 + t ^ 2 / 3 + t ^ 4 / (5 * (1 - t ^ 2))) < S := by
      have := mul_lt_mul_of_pos_left h1 hu3_pos
      rwa [mul_div_cancel₀ _ hu3_pos.ne'] at this
    have h3 : (u ^ 3 + 3 / 8) * ((twoD / S) * (1 + t ^ 2 / 3 + t ^ 4 / (5 * (1 - t ^ 2)))) <
        (twoD / S) * S := by
      have := mul_lt_mul_of_pos_left h2 (div_pos htwoD_pos hS_pos)
      linarith
    rwa [div_mul_cancel₀ _ hS_pos.ne'] at h3
  exact lt_trans hgoal hsand

/-- **Proposition 5 (Upper Bound)**: `M(n) < u^3 + 5/8` for all `n ≥ 12`. -/
lemma M_lt_upper {n : ℕ} (hn : 12 ≤ n) :
    M n < ((n : ℝ) - 1 / 2) ^ 3 + 5 / 8 := by
  have hsand := (M_analytic_sandwich (by omega : 2 ≤ n)).2
  set u : ℝ := (n : ℝ) - 1 / 2
  set twoD : ℝ := 3 * u ^ 2 + 1 / 4
  set S : ℝ := u ^ 3 + 3 / 4 * u + 1 / 2
  set t : ℝ := twoD / (2 * S)
  set p : ℝ := ((n - 1 : ℕ) : ℝ) ^ 3
  set L_lo : ℝ := 2 * t + 2 * t ^ 3 / 3 + 2 * t ^ 5 / 5
  set E_hi : ℝ := 1 / (24 * p * (p + 1))
  have hu : (23 / 2 : ℝ) ≤ u := by
    have : (12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    dsimp [u]; linarith
  have hu0 : 0 < u := by linarith
  have hu_half : 0 < u - 1 / 2 := by linarith
  have hnm1 : ((n - 1 : ℕ) : ℝ) = u - 1 / 2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; dsimp [u]; ring
  have hp_eq : p = (u - 1 / 2) ^ 3 := by dsimp [p]; rw [hnm1]
  have hS_pos : 0 < S := by dsimp [S]; positivity
  have htwoD_pos : 0 < twoD := by dsimp [twoD]; positivity
  have ht_pos : 0 < t := by dsimp [t]; positivity
  have ht_lower : 1 / u < t := by
    dsimp [t]
    rw [div_lt_div_iff₀ hu0 (by linarith)]
    dsimp [twoD, S]
    have hu2 : 0 < u - 2 := by linarith
    have : 0 < (u - 2) * (u ^ 2 + 2 * u + 3) := by positivity
    nlinarith
  -- Step 1: Error absorption t^4 / 5 > E_hi / (2t)
  have h_err : E_hi / (2 * t) < t ^ 4 / 5 := by
    have hp_pos : 0 < p := by rw [hp_eq]; positivity
    have hE_le : E_hi < 1 / (24 * (u - 1 / 2) ^ 6) := by
      dsimp [E_hi]
      apply one_div_lt_one_div_of_lt (by positivity)
      rw [hp_eq]
      have hcube : 0 < (u - 1 / 2) ^ 3 := by positivity
      nlinarith [show (u - 1 / 2) ^ 6 = ((u - 1 / 2) ^ 3) ^ 2 by ring]
    have hE_2t : E_hi / (2 * t) < u / (48 * (u - 1 / 2) ^ 6) := by
      have h1 : E_hi / (2 * t) < (1 / (24 * (u - 1 / 2) ^ 6)) / (2 * (1 / u)) :=
        div_lt_div₀ hE_le (by linarith) (by positivity) (by positivity)
      have h2 : (1 / (24 * (u - 1 / 2) ^ 6)) / (2 * (1 / u)) = u / (48 * (u - 1 / 2) ^ 6) := by
        field_simp [hu0.ne', hu_half.ne']; ring
      linarith
    have ht4 : 1 / (5 * u ^ 4) < t ^ 4 / 5 := by
      have h1 : (1 / u) ^ 2 < t ^ 2 := sq_lt_sq' (by linarith [div_pos one_pos hu0]) ht_lower
      have h2 : (1 / u) ^ 4 < t ^ 4 := by nlinarith [sq_nonneg (1 / u), sq_nonneg t]
      have h3 : (1 / u) ^ 4 / 5 = 1 / (5 * u ^ 4) := by field_simp [hu0.ne']
      linarith
    have hcomp : u / (48 * (u - 1 / 2) ^ 6) < 1 / (5 * u ^ 4) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      have h22 : (22 / 23 : ℝ) * u ≤ u - 1 / 2 := by linarith
      have hpow : ((22 / 23 : ℝ) * u) ^ 6 ≤ (u - 1 / 2) ^ 6 :=
        pow_le_pow_left₀ (by positivity) h22 6
      have hconst : (5 : ℝ) * u ^ 5 < 48 * ((22 / 23 : ℝ) * u) ^ 6 := by
        have hnum : (5 : ℝ) < 48 * (22 / 23 : ℝ) ^ 6 * (23 / 2) := by norm_num
        have hnum2 : (5 : ℝ) < 48 * (22 / 23 : ℝ) ^ 6 * u := by
          have : 48 * (22 / 23 : ℝ) ^ 6 * (23 / 2) ≤ 48 * (22 / 23 : ℝ) ^ 6 * u := by
            nlinarith [pow_pos (show (0 : ℝ) < 22 / 23 by norm_num) 6]
          linarith
        have hmul := mul_lt_mul_of_pos_right hnum2 (pow_pos hu0 5)
        have heq : 48 * (22 / 23 : ℝ) ^ 6 * u * u ^ 5 = 48 * ((22 / 23 : ℝ) * u) ^ 6 := by ring
        linarith
      have h48 : 48 * ((22 / 23 : ℝ) * u) ^ 6 ≤ 48 * (u - 1 / 2) ^ 6 := by linarith
      have h5eq : u * (5 * u ^ 4) = 5 * u ^ 5 := by ring
      linarith
    linarith
  -- Step 2: Main quadratic term t^2 / 3 > (3/4 u - 1/8) / (u^3 + 5/8)
  have h_quad : (3 / 4 * u - 1 / 8) / (u ^ 3 + 5 / 8) < t ^ 2 / 3 := by
    have hu3_pos : 0 < u ^ 3 + 5 / 8 := by positivity
    have hq_pos : 0 < 2 * u ^ 2 - u + 2 := by nlinarith
    have hden_pos : 0 < 1536 * S ^ 2 * (u ^ 3 + 5 / 8) := by positivity
    have hdiff : t ^ 2 / 3 - (3 / 4 * u - 1 / 8) / (u ^ 3 + 5 / 8) =
        (192 * u ^ 6 - 1536 * u ^ 5 - 144 * u ^ 4 - 448 * u ^ 3 - 636 * u ^ 2 - 144 * u + 53) /
          (1536 * S ^ 2 * (u ^ 3 + 5 / 8)) := by
      rw [eq_div_iff hden_pos.ne']
      have hS_ne : S ≠ 0 := hS_pos.ne'
      dsimp [t]
      field_simp [hS_ne, hu3_pos.ne']
      dsimp [twoD, S]
      ring
    have hnum_pos : 0 < 192 * u ^ 6 - 1536 * u ^ 5 - 144 * u ^ 4 - 448 * u ^ 3 - 636 * u ^ 2 - 144 * u + 53 := by
      have hlead : 672 * u ^ 5 ≤ 192 * u ^ 6 - 1536 * u ^ 5 := by
        have := mul_le_mul_of_nonneg_right (show (672 : ℝ) ≤ 192 * u - 1536 by linarith) (pow_nonneg hu0.le 5)
        linarith
      have hu1 : u ≤ u ^ 4 := by
        have : (1 : ℝ) ≤ u ^ 3 := one_le_pow₀ (by linarith)
        nlinarith
      have hu2 : u ^ 2 ≤ u ^ 4 := by
        have : (1 : ℝ) ≤ u ^ 2 := one_le_pow₀ (by linarith)
        nlinarith [sq_nonneg u]
      have hu3 : u ^ 3 ≤ u ^ 4 := by
        have : 0 ≤ u ^ 3 := by positivity
        nlinarith
      have hlin : 1372 * u ^ 4 < 672 * u ^ 5 := by
        have := mul_lt_mul_of_pos_right (show (1372 : ℝ) < 672 * u by linarith) (pow_pos hu0 4)
        linarith
      linarith
    have : 0 < t ^ 2 / 3 - (3 / 4 * u - 1 / 8) / (u ^ 3 + 5 / 8) := by
      rw [hdiff]; exact div_pos hnum_pos hden_pos
    linarith
  have hLlo_pos : 0 < L_lo - E_hi := by
    have : L_lo - E_hi = 2 * t * (1 + t ^ 2 / 3 + t ^ 4 / 5 - E_hi / (2 * t)) := by
      dsimp [L_lo]; field_simp [ht_pos.ne']
    rw [this]
    have hbr : 0 < 1 + t ^ 2 / 3 + t ^ 4 / 5 - E_hi / (2 * t) := by
      have hq0 : 0 < (3 / 4 * u - 1 / 8) / (u ^ 3 + 5 / 8) := div_pos (by linarith) (by positivity)
      linarith
    exact mul_pos (by positivity) hbr
  have hgoal : twoD / (L_lo - E_hi) < u ^ 3 + 5 / 8 := by
    rw [div_lt_iff₀ hLlo_pos]
    have hL_eq : L_lo - E_hi = (twoD / S) * (1 + t ^ 2 / 3 + t ^ 4 / 5 - E_hi / (2 * t)) := by
      dsimp [L_lo, t]; field_simp [hS_pos.ne', htwoD_pos.ne']
    rw [hL_eq]
    have hu3_pos : 0 < u ^ 3 + 5 / 8 := by positivity
    have h1 : S / (u ^ 3 + 5 / 8) < 1 + t ^ 2 / 3 + t ^ 4 / 5 - E_hi / (2 * t) := by
      have hS_split : S / (u ^ 3 + 5 / 8) = 1 + (3 / 4 * u - 1 / 8) / (u ^ 3 + 5 / 8) := by
        dsimp [S]; field_simp [hu3_pos.ne']; ring
      linarith
    have h2 : S < (u ^ 3 + 5 / 8) * (1 + t ^ 2 / 3 + t ^ 4 / 5 - E_hi / (2 * t)) := by
      have := mul_lt_mul_of_pos_left h1 hu3_pos
      rwa [mul_div_cancel₀ _ hu3_pos.ne'] at this
    have h3 : (twoD / S) * S <
        (u ^ 3 + 5 / 8) * ((twoD / S) * (1 + t ^ 2 / 3 + t ^ 4 / 5 - E_hi / (2 * t))) := by
      have := mul_lt_mul_of_pos_left h2 (div_pos htwoD_pos hS_pos)
      linarith
    rwa [div_mul_cancel₀ _ hS_pos.ne'] at h3
  exact lt_trans (hsand hLlo_pos) hgoal

/-! ### Part 5: Base Cases `1 ≤ n ≤ 11` and Theorem 1 (Ramaharo's Formula) -/

private lemma floor_eq_of_bounds {x : ℝ} {m : ℤ} (h1 : (m : ℝ) ≤ x) (h2 : x < (m : ℝ) + 1) :
    ⌊x⌋ = m :=
  Int.floor_eq_iff.mpr ⟨h1, h2⟩

private lemma a_base_analytic (n : ℕ) (hn : 2 ≤ n) (m : ℤ)
    (hlo : (m : ℝ) ≤
      let u : ℝ := (n : ℝ) - 1 / 2
      let twoD : ℝ := 3 * u ^ 2 + 1 / 4
      let S : ℝ := u ^ 3 + 3 / 4 * u + 1 / 2
      let t : ℝ := twoD / (2 * S)
      twoD / (2 * t + 2 * t ^ 3 / 3 + 2 * t ^ 5 / (5 * (1 - t ^ 2))))
    (hpos :
      let u : ℝ := (n : ℝ) - 1 / 2
      let twoD : ℝ := 3 * u ^ 2 + 1 / 4
      let S : ℝ := u ^ 3 + 3 / 4 * u + 1 / 2
      let t : ℝ := twoD / (2 * S)
      let p : ℝ := ((n - 1 : ℕ) : ℝ) ^ 3
      0 < (2 * t + 2 * t ^ 3 / 3 + 2 * t ^ 5 / 5) - 1 / (24 * p * (p + 1)))
    (hhi :
      let u : ℝ := (n : ℝ) - 1 / 2
      let twoD : ℝ := 3 * u ^ 2 + 1 / 4
      let S : ℝ := u ^ 3 + 3 / 4 * u + 1 / 2
      let t : ℝ := twoD / (2 * S)
      let p : ℝ := ((n - 1 : ℕ) : ℝ) ^ 3
      twoD / ((2 * t + 2 * t ^ 3 / 3 + 2 * t ^ 5 / 5) - 1 / (24 * p * (p + 1))) < (m : ℝ) + 1) :
    a n = m := by
  have hs := M_analytic_sandwich hn
  exact floor_eq_of_bounds (le_trans hlo hs.1.le) (lt_trans (hs.2 hpos) hhi)

private lemma a_eq_1 : a 1 = 1 := by
  have hH1 : H 1 = 1 := by
    unfold H
    have hIcc : Finset.Icc 1 1 = {1} := by decide
    rw [hIcc]; norm_num
  have hH0 : H 0 = 0 := by
    unfold H
    have hIcc : Finset.Icc 1 0 = ∅ := by decide
    rw [hIcc]; norm_num
  have hM : M 1 = 1 := by
    unfold M
    norm_num [hH1, hH0]
  unfold a
  rw [hM]
  norm_num

private lemma a_eq_2 : a 2 = 4 := by
  have hH : H 8 - H 1 = 481 / 280 := by
    rw [harmonic_sub_eq_sum (by norm_num : 1 ≤ 8)]
    have hIcc : Finset.Icc 2 8 = {2, 3, 4, 5, 6, 7, 8} := by decide
    rw [hIcc]
    norm_num
  have hM : M 2 = 1960 / 481 := by
    unfold M
    norm_num [hH]
  unfold a
  rw [hM]
  exact floor_eq_of_bounds (by norm_num) (by norm_num)

/-- **Theorem 1a (Ramaharo's Floor Formula, OEIS A227012)**:
For every integer `n ≥ 1`,
`a(n) = (2n^3 - 3n^2 + n + 2) / 2 + ⌊max(0, n - 3) / 4⌋`. -/
theorem a227012_ramaharo (n : ℕ) (hn : 1 ≤ n) : a n = aFormula n := by
  by_cases h12 : 12 ≤ n
  · -- General case n ≥ 12 via Propositions 4 & 5 and the 1/8-buffer
    have hlo := M_gt_lower h12
    have hhi := M_lt_upper h12
    have hmax : max (0 : ℤ) ((n : ℤ) - 3) = (n : ℤ) - 3 := max_eq_right (by omega)
    have hQ : 2 ∣ (2 * (n : ℤ) ^ 3 - 3 * (n : ℤ) ^ 2 + (n : ℤ) + 2) := by
      have : 2 * (n : ℤ) ^ 3 - 3 * (n : ℤ) ^ 2 + (n : ℤ) + 2 =
          2 * ((n : ℤ) ^ 3 - 2 * (n : ℤ) ^ 2 + 1) + (n : ℤ) * ((n : ℤ) + 1) := by ring
      rw [this]
      exact dvd_add (dvd_mul_right 2 _) (Int.even_mul_succ_self (n : ℤ)).two_dvd
    set q : ℤ := ((n : ℤ) - 3) / 4
    set r : ℤ := ((n : ℤ) - 3) % 4
    have hqr : (n : ℤ) - 3 = 4 * q + r := (Int.mul_ediv_add_emod ((n : ℤ) - 3) 4).symm
    have hr0 : 0 ≤ r := Int.emod_nonneg _ (by norm_num)
    have hr4 : r < 4 := Int.emod_lt_of_pos _ (by norm_num)
    have hQ_cast : (((2 * (n : ℤ) ^ 3 - 3 * (n : ℤ) ^ 2 + (n : ℤ) + 2) / 2 : ℤ) : ℝ) =
        (2 * (n : ℝ) ^ 3 - 3 * (n : ℝ) ^ 2 + (n : ℝ) + 2) / 2 := by
      obtain ⟨k, hk⟩ := hQ
      rw [hk, Int.mul_ediv_cancel_left _ (by norm_num)]
      have hkR : (2 * (n : ℝ) ^ 3 - 3 * (n : ℝ) ^ 2 + (n : ℝ) + 2) = 2 * (k : ℝ) := by
        exact_mod_cast hk
      linarith
    have hP_split : ((n : ℝ) - 1 / 2) ^ 3 + 1 / 2 =
        ((aFormula n : ℤ) : ℝ) + (2 * (r : ℝ) + 1) / 8 := by
      unfold aFormula
      rw [hmax]
      push_cast
      rw [hQ_cast]
      have hqrR : (n : ℝ) - 3 = 4 * (q : ℝ) + (r : ℝ) := by exact_mod_cast hqr
      linarith [show ((n : ℝ) - 1 / 2) ^ 3 + 1 / 2 =
        (2 * (n : ℝ) ^ 3 - 3 * (n : ℝ) ^ 2 + (n : ℝ) + 2) / 2 + ((n : ℝ) - 3) / 4 + 1 / 8 by ring]
    have hr0R : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
    have hr3R : (r : ℝ) ≤ 3 := by exact_mod_cast (by omega : r ≤ 3)
    apply floor_eq_of_bounds
    · linarith
    · linarith
  · -- Base cases 1 ≤ n ≤ 11
    interval_cases n
    · rw [a_eq_1]; decide
    · rw [a_eq_2]; decide
    · rw [a_base_analytic 3 (by omega) 16 (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [a_base_analytic 4 (by omega) 43 (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [a_base_analytic 5 (by omega) 91 (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [a_base_analytic 6 (by omega) 166 (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [a_base_analytic 7 (by omega) 275 (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [a_base_analytic 8 (by omega) 422 (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [a_base_analytic 9 (by omega) 614 (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [a_base_analytic 10 (by omega) 857 (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [a_base_analytic 11 (by omega) 1158 (by norm_num) (by norm_num) (by norm_num)]; decide

/-! ### Part 6: Remaining Three Conjectured Formulas on OEIS A227012 -/

/-- Exact integer identity `4 * aFormula n = 4n^3 - 6n^2 + 3n + 1 - ((n - 3) % 4)` for `n ≥ 3`. -/
private lemma four_mul_aFormula {n : ℕ} (hn : 3 ≤ n) :
    4 * aFormula n = 4 * (n : ℤ) ^ 3 - 6 * (n : ℤ) ^ 2 + 3 * (n : ℤ) + 1 - ((n : ℤ) - 3) % 4 := by
  unfold aFormula
  have hmax : max (0 : ℤ) ((n : ℤ) - 3) = (n : ℤ) - 3 := max_eq_right (by omega)
  rw [hmax]
  have hQ : 2 ∣ (2 * (n : ℤ) ^ 3 - 3 * (n : ℤ) ^ 2 + (n : ℤ) + 2) := by
    have : 2 * (n : ℤ) ^ 3 - 3 * (n : ℤ) ^ 2 + (n : ℤ) + 2 =
        2 * ((n : ℤ) ^ 3 - 2 * (n : ℤ) ^ 2 + 1) + (n : ℤ) * ((n : ℤ) + 1) := by ring
    rw [this]
    exact dvd_add (dvd_mul_right 2 _) (Int.even_mul_succ_self (n : ℤ)).two_dvd
  obtain ⟨k, hk⟩ := hQ
  rw [hk, Int.mul_ediv_cancel_left _ (by norm_num)]
  have hdiv : 4 * (((n : ℤ) - 3) / 4) + ((n : ℤ) - 3) % 4 = (n : ℤ) - 3 :=
    Int.mul_ediv_add_emod ((n : ℤ) - 3) 4
  linarith

private lemma trig_mod4 (k : ℕ) :
    (-1 : ℝ) ^ k + 2 * Real.cos ((k : ℝ) * Real.pi / 2) - 2 * Real.sin ((k : ℝ) * Real.pi / 2) =
      2 * ((((k : ℤ) - 1) % 4 : ℤ) : ℝ) - 3 := by
  have hk_split : k = 4 * (k / 4) + k % 4 := (Nat.div_add_mod k 4).symm
  set m := k / 4
  set r := k % 4
  have hr : r < 4 := Nat.mod_lt k (by norm_num)
  have harg : (k : ℝ) * Real.pi / 2 = (r : ℝ) * Real.pi / 2 + (m : ℝ) * (2 * Real.pi) := by
    have : (k : ℝ) = 4 * (m : ℝ) + (r : ℝ) := by exact_mod_cast hk_split
    rw [this]; ring
  have hcos : Real.cos ((k : ℝ) * Real.pi / 2) = Real.cos ((r : ℝ) * Real.pi / 2) := by
    rw [harg, Real.cos_add_nat_mul_two_pi]
  have hsin : Real.sin ((k : ℝ) * Real.pi / 2) = Real.sin ((r : ℝ) * Real.pi / 2) := by
    rw [harg, Real.sin_add_nat_mul_two_pi]
  have hpow : (-1 : ℝ) ^ k = (-1 : ℝ) ^ r := by
    rw [hk_split, pow_add, pow_mul]
    norm_num
  have hmod : ((k : ℤ) - 1) % 4 = ((r : ℤ) - 1) % 4 := by
    have : (k : ℤ) = 4 * (m : ℤ) + (r : ℤ) := by exact_mod_cast hk_split
    omega
  rw [hcos, hsin, hpow, hmod]
  interval_cases r
  · norm_num [Real.cos_zero, Real.sin_zero]
  · norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two]
  · push_cast
    have h2 : (2 : ℝ) * Real.pi / 2 = Real.pi := by ring
    rw [h2]; norm_num [Real.cos_pi, Real.sin_pi]
  · push_cast
    have h3 : (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
    rw [h3, Real.cos_add, Real.sin_add]
    norm_num [Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- **Theorem 1b (Kimberling's Trigonometric Closed Form, OEIS A227012)**:
For every integer `k ≥ 1`,
`a(k + 2) = (1/8) * (27 - (-1)^k - 2 cos(kπ/2) + 2 sin(kπ/2) + 2k(4k^2 + 18k + 27))`. -/
theorem a227012_trig (k : ℕ) (hk : 1 ≤ k) :
    (a (k + 2) : ℝ) =
      (1 / 8 : ℝ) * (27 - (-1 : ℝ) ^ k - 2 * Real.cos ((k : ℝ) * Real.pi / 2) +
        2 * Real.sin ((k : ℝ) * Real.pi / 2) +
        2 * (k : ℝ) * (4 * (k : ℝ) ^ 2 + 18 * (k : ℝ) + 27)) := by
  rw [a227012_ramaharo (k + 2) (by omega)]
  have h4 := four_mul_aFormula (by omega : 3 ≤ k + 2)
  have h4R : 4 * ((aFormula (k + 2) : ℤ) : ℝ) =
      4 * ((k : ℝ) + 2) ^ 3 - 6 * ((k : ℝ) + 2) ^ 2 + 3 * ((k : ℝ) + 2) + 1 -
        ((((k : ℤ) - 1) % 4 : ℤ) : ℝ) := by
    have hsub : ((k + 2 : ℕ) : ℤ) - 3 = (k : ℤ) - 1 := by push_cast; ring
    rw [hsub] at h4
    have hcast : ((4 * aFormula (k + 2) : ℤ) : ℝ) =
        ((4 * ((k + 2 : ℕ) : ℤ) ^ 3 - 6 * ((k + 2 : ℕ) : ℤ) ^ 2 + 3 * ((k + 2 : ℕ) : ℤ) + 1 -
          ((k : ℤ) - 1) % 4 : ℤ) : ℝ) := by exact_mod_cast h4
    push_cast at hcast
    exact hcast
  linarith [h4R, trig_mod4 k]

/-- **Theorem 1c (Kimberling's Order-7 Linear Recurrence, OEIS A227012)**:
For every integer `n ≥ 10`,
`a(n) = 3a(n-1) - 3a(n-2) + a(n-3) + a(n-4) - 3a(n-5) + 3a(n-6) - a(n-7)`. -/
private lemma aFormula_recurrence (n : ℕ) (hn : 10 ≤ n) :
    aFormula n = 3 * aFormula (n - 1) - 3 * aFormula (n - 2) + aFormula (n - 3) +
      aFormula (n - 4) - 3 * aFormula (n - 5) + 3 * aFormula (n - 6) - aFormula (n - 7) := by
  have c1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by exact_mod_cast Int.ofNat_sub (by omega : 1 ≤ n)
  have c2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by exact_mod_cast Int.ofNat_sub (by omega : 2 ≤ n)
  have c3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by exact_mod_cast Int.ofNat_sub (by omega : 3 ≤ n)
  have c4 : ((n - 4 : ℕ) : ℤ) = (n : ℤ) - 4 := by exact_mod_cast Int.ofNat_sub (by omega : 4 ≤ n)
  have c5 : ((n - 5 : ℕ) : ℤ) = (n : ℤ) - 5 := by exact_mod_cast Int.ofNat_sub (by omega : 5 ≤ n)
  have c6 : ((n - 6 : ℕ) : ℤ) = (n : ℤ) - 6 := by exact_mod_cast Int.ofNat_sub (by omega : 6 ≤ n)
  have c7 : ((n - 7 : ℕ) : ℤ) = (n : ℤ) - 7 := by exact_mod_cast Int.ofNat_sub (by omega : 7 ≤ n)
  have hge0 : 3 ≤ n := by omega
  have hge1 : 3 ≤ n - 1 := by omega
  have hge2 : 3 ≤ n - 2 := by omega
  have hge3 : 3 ≤ n - 3 := by omega
  have hge4 : 3 ≤ n - 4 := by omega
  have hge5 : 3 ≤ n - 5 := by omega
  have hge6 : 3 ≤ n - 6 := by omega
  have hge7 : 3 ≤ n - 7 := by omega
  have f0 := four_mul_aFormula hge0
  have f1 := four_mul_aFormula hge1
  have f2 := four_mul_aFormula hge2
  have f3 := four_mul_aFormula hge3
  have f4 := four_mul_aFormula hge4
  have f5 := four_mul_aFormula hge5
  have f6 := four_mul_aFormula hge6
  have f7 := four_mul_aFormula hge7
  have m04 : ((n : ℤ) - 4 - 3) % 4 = ((n : ℤ) - 3) % 4 := by
    have : (n : ℤ) - 4 - 3 = ((n : ℤ) - 3) + (-1) * 4 := by ring
    rw [this, Int.add_mul_emod_self_right]
  have m15 : ((n : ℤ) - 5 - 3) % 4 = ((n : ℤ) - 1 - 3) % 4 := by
    have : (n : ℤ) - 5 - 3 = ((n : ℤ) - 1 - 3) + (-1) * 4 := by ring
    rw [this, Int.add_mul_emod_self_right]
  have m26 : ((n : ℤ) - 6 - 3) % 4 = ((n : ℤ) - 2 - 3) % 4 := by
    have : (n : ℤ) - 6 - 3 = ((n : ℤ) - 2 - 3) + (-1) * 4 := by ring
    rw [this, Int.add_mul_emod_self_right]
  have m37 : ((n : ℤ) - 7 - 3) % 4 = ((n : ℤ) - 3 - 3) % 4 := by
    have : (n : ℤ) - 7 - 3 = ((n : ℤ) - 3 - 3) + (-1) * 4 := by ring
    rw [this, Int.add_mul_emod_self_right]
  rw [c1] at f1; rw [c2] at f2; rw [c3] at f3; rw [c4] at f4
  rw [c5] at f5; rw [c6] at f6; rw [c7] at f7
  rw [m04] at f4; rw [m15] at f5; rw [m26] at f6; rw [m37] at f7
  have hpoly :
      (4 * (n : ℤ) ^ 3 - 6 * (n : ℤ) ^ 2 + 3 * (n : ℤ) + 1) =
        3 * (4 * ((n : ℤ) - 1) ^ 3 - 6 * ((n : ℤ) - 1) ^ 2 + 3 * ((n : ℤ) - 1) + 1) -
        3 * (4 * ((n : ℤ) - 2) ^ 3 - 6 * ((n : ℤ) - 2) ^ 2 + 3 * ((n : ℤ) - 2) + 1) +
        (4 * ((n : ℤ) - 3) ^ 3 - 6 * ((n : ℤ) - 3) ^ 2 + 3 * ((n : ℤ) - 3) + 1) +
        (4 * ((n : ℤ) - 4) ^ 3 - 6 * ((n : ℤ) - 4) ^ 2 + 3 * ((n : ℤ) - 4) + 1) -
        3 * (4 * ((n : ℤ) - 5) ^ 3 - 6 * ((n : ℤ) - 5) ^ 2 + 3 * ((n : ℤ) - 5) + 1) +
        3 * (4 * ((n : ℤ) - 6) ^ 3 - 6 * ((n : ℤ) - 6) ^ 2 + 3 * ((n : ℤ) - 6) + 1) -
        (4 * ((n : ℤ) - 7) ^ 3 - 6 * ((n : ℤ) - 7) ^ 2 + 3 * ((n : ℤ) - 7) + 1) := by ring
  linarith

theorem a227012_recurrence (n : ℕ) (hn : 10 ≤ n) :
    a n = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) + a (n - 4) -
      3 * a (n - 5) + 3 * a (n - 6) - a (n - 7) := by
  rw [a227012_ramaharo n (by omega),
      a227012_ramaharo (n - 1) (by omega),
      a227012_ramaharo (n - 2) (by omega),
      a227012_ramaharo (n - 3) (by omega),
      a227012_ramaharo (n - 4) (by omega),
      a227012_ramaharo (n - 5) (by omega),
      a227012_ramaharo (n - 6) (by omega),
      a227012_ramaharo (n - 7) (by omega)]
  exact aFormula_recurrence n hn

/-- The formal power series `A(X) = ∑_{n≥1} a(n) X^n` (with constant term `0`). -/
noncomputable def A_series : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 0 else a n

/-- **Theorem 1d (Kimberling's Rational Generating Function, OEIS A227012)**:
In `PowerSeries ℤ`,
`((X - 1)^4 * (1 + X + X^2 + X^3)) * A(X) = X * (1 + X + 7X^2 + 6X^3 + 5X^4 + 5X^5 - 2X^7 + X^8)`. -/
private lemma poly_den_eq {R : Type*} [CommRing R] (y : R) :
    (y - 1) ^ 4 * (1 + y + y ^ 2 + y ^ 3) =
      1 - 3 * y ^ 1 + 3 * y ^ 2 - y ^ 3 - y ^ 4 + 3 * y ^ 5 - 3 * y ^ 6 + y ^ 7 := by
  ring

private lemma poly_num_eq {R : Type*} [CommRing R] (y : R) :
    y * (1 + y + 7 * y ^ 2 + 6 * y ^ 3 + 5 * y ^ 4 + 5 * y ^ 5 - 2 * y ^ 7 + y ^ 8) =
      y ^ 1 + y ^ 2 + 7 * y ^ 3 + 6 * y ^ 4 + 5 * y ^ 5 + 5 * y ^ 6 - 2 * y ^ 8 + y ^ 9 := by
  ring

theorem a227012_gf :
    ((PowerSeries.X - 1) ^ 4 * (1 + PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3)) *
      A_series =
    PowerSeries.X * (1 + PowerSeries.X + 7 * PowerSeries.X ^ 2 + 6 * PowerSeries.X ^ 3 +
      5 * PowerSeries.X ^ 4 + 5 * PowerSeries.X ^ 5 - 2 * PowerSeries.X ^ 7 + PowerSeries.X ^ 8) := by
  have hden :
      ((PowerSeries.X - 1 : PowerSeries ℤ) ^ 4 *
        (1 + PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3)) * A_series =
      A_series - PowerSeries.C 3 * (PowerSeries.X ^ 1 * A_series) +
        PowerSeries.C 3 * (PowerSeries.X ^ 2 * A_series) - (PowerSeries.X ^ 3 * A_series) -
        (PowerSeries.X ^ 4 * A_series) + PowerSeries.C 3 * (PowerSeries.X ^ 5 * A_series) -
        PowerSeries.C 3 * (PowerSeries.X ^ 6 * A_series) + (PowerSeries.X ^ 7 * A_series) := by
    rw [poly_den_eq (PowerSeries.X : PowerSeries ℤ)]
    simp only [map_ofNat, add_mul, sub_mul, one_mul, mul_assoc]
  have hnum :
      (PowerSeries.X : PowerSeries ℤ) * (1 + PowerSeries.X + 7 * PowerSeries.X ^ 2 +
        6 * PowerSeries.X ^ 3 + 5 * PowerSeries.X ^ 4 + 5 * PowerSeries.X ^ 5 -
        2 * PowerSeries.X ^ 7 + PowerSeries.X ^ 8) =
      PowerSeries.X ^ 1 + PowerSeries.X ^ 2 + PowerSeries.C 7 * PowerSeries.X ^ 3 +
        PowerSeries.C 6 * PowerSeries.X ^ 4 + PowerSeries.C 5 * PowerSeries.X ^ 5 +
        PowerSeries.C 5 * PowerSeries.X ^ 6 - PowerSeries.C 2 * PowerSeries.X ^ 8 +
        PowerSeries.X ^ 9 := by
    rw [poly_num_eq (PowerSeries.X : PowerSeries ℤ)]
    simp only [map_ofNat]
  rw [hden, hnum]
  ext n
  have hcoeff_A : ∀ k : ℕ, PowerSeries.coeff k A_series = if k = 0 then 0 else a k := by
    intro k; simp [A_series]
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow]
  by_cases hn10 : 10 ≤ n
  · simp only [show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
      show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega,
      show n ≠ 8 by omega, show n ≠ 9 by omega, ↓reduceIte, mul_zero, add_zero, sub_zero,
      show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega,
      hcoeff_A, show n ≠ 0 by omega, show n - 1 ≠ 0 by omega,
      show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega,
      show n - 5 ≠ 0 by omega, show n - 6 ≠ 0 by omega, show n - 7 ≠ 0 by omega]
    linarith [a227012_recurrence n hn10]
  · have hvals : a 1 = 1 ∧ a 2 = 4 ∧ a 3 = 16 ∧ a 4 = 43 ∧ a 5 = 91 ∧
        a 6 = 166 ∧ a 7 = 275 ∧ a 8 = 422 ∧ a 9 = 614 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals (rw [a227012_ramaharo _ (by omega)]; decide)
    interval_cases n <;> simp [hcoeff_A, hvals]

end OEIS_A227012

#print axioms OEIS_A227012.a227012_ramaharo
#print axioms OEIS_A227012.a227012_trig
#print axioms OEIS_A227012.a227012_recurrence
#print axioms OEIS_A227012.a227012_gf
