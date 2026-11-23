import A227012
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Formal Proof of Theorem 2 & Corollary 8 (Kimberling's General Cubic Recurrence Conjecture)

This file formally proves Theorem 2 and Corollary 8 of the manuscript:
For EVERY integer cubic polynomial `g(n) = a*n^3 + b*n^2 + c*n + d` with `a > 0`,
letting `M_g(n) = (g(n) - g(n-1)) / (H_{g(n)} - H_{g(n-1)})` and `m_g(n) = ⌊M_g(n)⌋`:

1. `nonvanishing_c1_c2_c3` (Lemma 7): The three rational asymptotic invariants `(c₁, c₂, c₃)`
   never vanish simultaneously for any `a > 0`; specifically `c₁ = c₂ = 0 → c₃ = (9a² + 350)/(4200a) > 0`.
2. `M_g_asymptotic_limit` (Lemma 6): As `n → ∞` (with `u = n - 1/2`),
   `u³ * (M_g(n) - P_g(n) - c₁/u - c₂/u²) → c₃`, where `P_g(n) = g(n - 1/2) + 1/2`.
3. `kimberling_general_cubic_floor` & `kimberling_general_cubic_recurrence` (Theorem 2):
   There exists `N₀` such that for all `n ≥ N₀`, `m_g(n) = ⌊P_g(n)⌋` (if `σ = +1`) or
   `⌈P_g(n)⌉ - 1` (if `σ = -1`), and for all `n ≥ N₀ + 7`, `m_g(n)` satisfies Kimberling's
   order-7 linear recurrence `(3, -3, 1, 1, -3, 3, -1)`.
4. `kimberling_even_order5` & `kimberling_div4_order4` (Corollary 8):
   When `2 ∣ a`, `m_g(n)` eventually satisfies the order-5 recurrence `(3, -2, -2, 3, -1)`;
   when `4 ∣ a`, `m_g(n)` eventually satisfies the order-4 recurrence `(4, -6, 4, -1)`.
-/

namespace GeneralCubic

open Real Finset Filter Topology OEIS_A227012

/-! ### Part 1: Degree-7 Logarithm Bounds & Elementary Telescoping Euler-Maclaurin Difference -/

private lemma hasDerivAt_log_ratio' {x : ℝ} (hx0 : -1 < x) (hx1 : x < 1) :
    HasDerivAt (fun t => Real.log ((1 + t) / (1 - t))) (2 / (1 - x ^ 2)) x := by
  have h1 : 0 < 1 + x := by linarith
  have h2 : 0 < 1 - x := by linarith
  have hq : ((1 + x) / (1 - x)) ≠ 0 := (div_pos h1 h2).ne'
  have hd_num : HasDerivAt (fun t : ℝ => 1 + t) 1 x := (hasDerivAt_id x).const_add 1
  have hd_den : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have hd_log := (hd_num.div hd_den h2.ne').log hq
  convert hd_log using 1
  have h1x2 : 1 - x ^ 2 ≠ 0 := by nlinarith
  simp only [Pi.div_apply]
  field_simp [h1.ne', h2.ne', h1x2]
  ring

private lemma pos_of_deriv_pos_on_Ioo' {f f' : ℝ → ℝ} {x : ℝ} (hx : 0 < x)
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

/-- `2x + 2x^3/3 + 2x^5/5 + 2x^7/7 < log((1+x)/(1-x))` for `0 < x < 1`. -/
lemma log_ratio_gt_7 {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    2 * x + 2 * x ^ 3 / 3 + 2 * x ^ 5 / 5 + 2 * x ^ 7 / 7 < Real.log ((1 + x) / (1 - x)) := by
  let f : ℝ → ℝ := fun t =>
    Real.log ((1 + t) / (1 - t)) - (2 * t + 2 * t ^ 3 / 3 + 2 * t ^ 5 / 5 + 2 * t ^ 7 / 7)
  let f' : ℝ → ℝ := fun t => 2 * t ^ 8 / (1 - t ^ 2)
  have hderiv_all : ∀ t ∈ Set.Icc 0 x, HasDerivAt f (f' t) t := by
    intro t ht
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hx1
    have h1 : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht1]
    have hd_log := hasDerivAt_log_ratio' (by linarith [ht.1]) ht1
    have hd1 : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by simpa using (hasDerivAt_id t).const_mul 2
    have hd3 : HasDerivAt (fun s : ℝ => 2 * s ^ 3 / 3) (2 * t ^ 2) t := by
      have := ((hasDerivAt_pow 3 t).const_mul 2).div_const 3; convert this using 1; ring
    have hd5 : HasDerivAt (fun s : ℝ => 2 * s ^ 5 / 5) (2 * t ^ 4) t := by
      have := ((hasDerivAt_pow 5 t).const_mul 2).div_const 5; convert this using 1; ring
    have hd7 : HasDerivAt (fun s : ℝ => 2 * s ^ 7 / 7) (2 * t ^ 6) t := by
      have := ((hasDerivAt_pow 7 t).const_mul 2).div_const 7; convert this using 1; ring
    have hd := hd_log.sub (((hd1.add hd3).add hd5).add hd7)
    convert hd using 1
    dsimp [f']
    field_simp [h1]
    ring
  have hpos : 0 < f x := pos_of_deriv_pos_on_Ioo' hx0 (by simp [f])
    (fun t ht => (hderiv_all t ht).continuousAt.continuousWithinAt)
    (fun t ht => hderiv_all t ⟨ht.1.le, ht.2.le⟩)
    (fun t ht => by
      have ht0 : 0 < t := ht.1
      have ht1 : t < 1 := lt_trans ht.2 hx1
      have h1 : 0 < 1 - t ^ 2 := by nlinarith
      dsimp [f']; exact div_pos (by positivity) h1)
  dsimp [f] at hpos; linarith

/-- `log((1+x)/(1-x)) < 2x + 2x^3/3 + 2x^5/5 + 2x^7/7 + 2x^9 / (9(1 - x^2))` for `0 < x < 1`. -/
lemma log_ratio_lt_7 {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Real.log ((1 + x) / (1 - x)) <
      2 * x + 2 * x ^ 3 / 3 + 2 * x ^ 5 / 5 + 2 * x ^ 7 / 7 + 2 * x ^ 9 / (9 * (1 - x ^ 2)) := by
  let f : ℝ → ℝ := fun t =>
    2 * t + 2 * t ^ 3 / 3 + 2 * t ^ 5 / 5 + 2 * t ^ 7 / 7 + 2 * t ^ 9 / (9 * (1 - t ^ 2)) -
      Real.log ((1 + t) / (1 - t))
  let f' : ℝ → ℝ := fun t => 4 * t ^ 10 / (9 * (1 - t ^ 2) ^ 2)
  have hderiv_all : ∀ t ∈ Set.Icc 0 x, HasDerivAt f (f' t) t := by
    intro t ht
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hx1
    have hden : 9 * (1 - t ^ 2) ≠ 0 := by nlinarith [ht.1, ht1]
    have h1 : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht1]
    have hd1 : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by simpa using (hasDerivAt_id t).const_mul 2
    have hd3 : HasDerivAt (fun s : ℝ => 2 * s ^ 3 / 3) (2 * t ^ 2) t := by
      have := ((hasDerivAt_pow 3 t).const_mul 2).div_const 3; convert this using 1; ring
    have hd5 : HasDerivAt (fun s : ℝ => 2 * s ^ 5 / 5) (2 * t ^ 4) t := by
      have := ((hasDerivAt_pow 5 t).const_mul 2).div_const 5; convert this using 1; ring
    have hd7 : HasDerivAt (fun s : ℝ => 2 * s ^ 7 / 7) (2 * t ^ 6) t := by
      have := ((hasDerivAt_pow 7 t).const_mul 2).div_const 7; convert this using 1; ring
    have hd_num : HasDerivAt (fun s : ℝ => 2 * s ^ 9) (18 * t ^ 8) t := by
      have := (hasDerivAt_pow 9 t).const_mul 2; convert this using 1; ring
    have hd_den : HasDerivAt (fun s : ℝ => 9 * (1 - s ^ 2)) (-18 * t) t := by
      have := ((hasDerivAt_pow 2 t).const_sub 1).const_mul 9; convert this using 1; ring
    have hd_frac := hd_num.div hd_den hden
    have hd_log := hasDerivAt_log_ratio' (by linarith [ht.1]) ht1
    have hd := ((((hd1.add hd3).add hd5).add hd7).add hd_frac).sub hd_log
    convert hd using 1
    dsimp [f']; field_simp [hden, h1]; ring
  have hpos : 0 < f x := pos_of_deriv_pos_on_Ioo' hx0 (by simp [f])
    (fun t ht => (hderiv_all t ht).continuousAt.continuousWithinAt)
    (fun t ht => hderiv_all t ⟨ht.1.le, ht.2.le⟩)
    (fun t ht => by
      have ht0 : 0 < t := ht.1
      have ht1 : t < 1 := lt_trans ht.2 hx1
      have h1 : 0 < 1 - t ^ 2 := by nlinarith
      dsimp [f']; exact div_pos (by positivity) (by positivity))
  dsimp [f] at hpos; linarith

/-- Single-step Euler-Maclaurin bound for `k ≥ 2`:
`|(log((k+1/2)/(k-1/2)) - 1/k) - (1/24)*(1/(k-1/2)^2 - 1/(k+1/2)^2)| ≤ 1 / k^5`. -/
private lemma em_step_bound {k : ℕ} (hk : 2 ≤ k) :
    |(Real.log (((k : ℝ) + 1 / 2) / ((k : ℝ) - 1 / 2)) - 1 / (k : ℝ)) -
      (1 / 24 : ℝ) * (1 / ((k : ℝ) - 1 / 2) ^ 2 - 1 / ((k : ℝ) + 1 / 2) ^ 2)| ≤
      1 / (k : ℝ) ^ 5 := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hx0 : 0 < (1 : ℝ) / (2 * (k : ℝ)) := by positivity
  have hx1 : (1 : ℝ) / (2 * (k : ℝ)) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have hratio : (1 + (1 : ℝ) / (2 * (k : ℝ))) / (1 - (1 : ℝ) / (2 * (k : ℝ))) =
      ((k : ℝ) + 1 / 2) / ((k : ℝ) - 1 / 2) := by
    have h1 : (k : ℝ) - 1 / 2 ≠ 0 := by linarith
    field_simp [hk0.ne', h1]
  have hlo := log_ratio_gt_quintic hx0 hx1
  have hhi := log_ratio_lt_quintic hx0 hx1
  rw [hratio] at hlo hhi
  -- Rewrite log bounds in terms of 1/k, 1/(12 k^3), and 1/k^5
  have h_log_lo : 1 / (12 * (k : ℝ) ^ 3) <
      Real.log (((k : ℝ) + 1 / 2) / ((k : ℝ) - 1 / 2)) - 1 / (k : ℝ) := by
    have hsimp : 2 * ((1 : ℝ) / (2 * (k : ℝ))) + 2 * ((1 : ℝ) / (2 * (k : ℝ))) ^ 3 / 3 =
        1 / (k : ℝ) + 1 / (12 * (k : ℝ) ^ 3) := by field_simp [hk0.ne']; ring
    have h5 : 0 < 2 * ((1 : ℝ) / (2 * (k : ℝ))) ^ 5 / 5 := by positivity
    linarith
  have h_log_hi : Real.log (((k : ℝ) + 1 / 2) / ((k : ℝ) - 1 / 2)) - 1 / (k : ℝ) <
      1 / (12 * (k : ℝ) ^ 3) + 1 / (12 * (k : ℝ) ^ 5) := by
    have hsimp : 2 * ((1 : ℝ) / (2 * (k : ℝ))) + 2 * ((1 : ℝ) / (2 * (k : ℝ))) ^ 3 / 3 =
        1 / (k : ℝ) + 1 / (12 * (k : ℝ) ^ 3) := by field_simp [hk0.ne']; ring
    have htail : 2 * ((1 : ℝ) / (2 * (k : ℝ))) ^ 5 / (5 * (1 - ((1 : ℝ) / (2 * (k : ℝ))) ^ 2)) <
        1 / (12 * (k : ℝ) ^ 5) := by
      have h1 : 0 < 4 * (k : ℝ) ^ 2 - 1 := by nlinarith
      have heq : 2 * ((1 : ℝ) / (2 * (k : ℝ))) ^ 5 / (5 * (1 - ((1 : ℝ) / (2 * (k : ℝ))) ^ 2)) =
          1 / (20 * (k : ℝ) ^ 3 * (4 * (k : ℝ) ^ 2 - 1)) := by
        field_simp [hk0.ne', h1.ne']; ring
      rw [heq]
      apply one_div_lt_one_div_of_lt (by positivity)
      have : 12 * (k : ℝ) ^ 2 < 20 * (4 * (k : ℝ) ^ 2 - 1) := by nlinarith
      nlinarith [pow_pos hk0 3]
    linarith
  -- Compare telescoping term with 1/(12 k^3)
  have htele_eq : (1 / 24 : ℝ) * (1 / ((k : ℝ) - 1 / 2) ^ 2 - 1 / ((k : ℝ) + 1 / 2) ^ 2) -
      1 / (12 * (k : ℝ) ^ 3) =
      (8 * (k : ℝ) ^ 2 - 1) / (12 * (k : ℝ) ^ 3 * (4 * (k : ℝ) ^ 2 - 1) ^ 2) := by
    have h1 : (k : ℝ) - 1 / 2 ≠ 0 := by linarith
    have h2 : (k : ℝ) + 1 / 2 ≠ 0 := by linarith
    have h3 : 4 * (k : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have h4 : (k : ℝ) - 1 / 2 = (2 * (k : ℝ) - 1) / 2 := by ring
    have h5 : (k : ℝ) + 1 / 2 = (2 * (k : ℝ) + 1) / 2 := by ring
    have h6 : 4 * (k : ℝ) ^ 2 - 1 = (2 * (k : ℝ) - 1) * (2 * (k : ℝ) + 1) := by ring
    have hm : 2 * (k : ℝ) - 1 ≠ 0 := by linarith
    have hp : 2 * (k : ℝ) + 1 ≠ 0 := by linarith
    rw [h4, h5, h6]
    field_simp [hk0.ne', hm, hp]
    ring
  have htele_pos : 0 ≤ (8 * (k : ℝ) ^ 2 - 1) / (12 * (k : ℝ) ^ 3 * (4 * (k : ℝ) ^ 2 - 1) ^ 2) := by
    have h1 : 0 ≤ 8 * (k : ℝ) ^ 2 - 1 := by nlinarith
    have h2 : 0 < 4 * (k : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  have htele_le : (8 * (k : ℝ) ^ 2 - 1) / (12 * (k : ℝ) ^ 3 * (4 * (k : ℝ) ^ 2 - 1) ^ 2) ≤
      1 / (k : ℝ) ^ 5 := by
    have h2 : 0 < 4 * (k : ℝ) ^ 2 - 1 := by nlinarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hk2 : 4 ≤ (k : ℝ) ^ 2 := by nlinarith
    have hmul : (8 * (k : ℝ) ^ 2 - 1) * (k : ℝ) ^ 2 ≤ 12 * (4 * (k : ℝ) ^ 2 - 1) ^ 2 := by
      nlinarith [sq_nonneg ((k : ℝ) ^ 2 - 4)]
    have := mul_le_mul_of_nonneg_right hmul (pow_nonneg hk0.le 3)
    linarith [show (8 * (k : ℝ) ^ 2 - 1) * (k : ℝ) ^ 5 = ((8 * (k : ℝ) ^ 2 - 1) * (k : ℝ) ^ 2) * (k : ℝ) ^ 3 by ring,
              show 1 * (12 * (k : ℝ) ^ 3 * (4 * (k : ℝ) ^ 2 - 1) ^ 2) = (12 * (4 * (k : ℝ) ^ 2 - 1) ^ 2) * (k : ℝ) ^ 3 by ring]
  have h12_le : 1 / (12 * (k : ℝ) ^ 5) ≤ 1 / (k : ℝ) ^ 5 := by
    have hk5 : 0 < (k : ℝ) ^ 5 := pow_pos hk0 5
    exact one_div_le_one_div_of_le hk5 (by linarith)
  rw [abs_le]
  constructor <;> linarith

private lemma sum_log_tele' {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    ∑ k ∈ Finset.Icc (p + 1) q, Real.log (((k : ℝ) + 1 / 2) / ((k : ℝ) - 1 / 2)) =
      Real.log (((q : ℝ) + 1 / 2) / ((p : ℝ) + 1 / 2)) := by
  induction q, hpq using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hIcc : Finset.Icc (p + 1) (m + 1) = insert (m + 1) (Finset.Icc (p + 1) m) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp), ih]
    have hp_pos : (0 : ℝ) < (p : ℝ) + 1 / 2 := by positivity
    have hm_pos : (0 : ℝ) < (m : ℝ) + 1 / 2 := by positivity
    have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) + 1 / 2 := by positivity
    have hsub : ((m + 1 : ℕ) : ℝ) - 1 / 2 = (m : ℝ) + 1 / 2 := by push_cast; ring
    rw [hsub, ← Real.log_mul (div_pos hm1_pos hm_pos).ne' (div_pos hm_pos hp_pos).ne']
    congr 1; field_simp [hm_pos.ne', hp_pos.ne']

private lemma sum_sq_tele {p q : ℕ} (hpq : p ≤ q) :
    ∑ k ∈ Finset.Icc (p + 1) q, (1 / ((k : ℝ) - 1 / 2) ^ 2 - 1 / ((k : ℝ) + 1 / 2) ^ 2) =
      1 / ((p : ℝ) + 1 / 2) ^ 2 - 1 / ((q : ℝ) + 1 / 2) ^ 2 := by
  induction q, hpq using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hIcc : Finset.Icc (p + 1) (m + 1) = insert (m + 1) (Finset.Icc (p + 1) m) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp), ih]
    push_cast; ring

/-- Elementary Euler-Maclaurin difference bound for all integers `q > p ≥ 1`:
`|(log((q+1/2)/(p+1/2)) - (H q - H p)) - (1/24)*(1/(p+1/2)^2 - 1/(q+1/2)^2)| ≤ (q - p) / (p + 1)^5`. -/
lemma harmonic_em_diff_bound {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    |(Real.log (((q : ℝ) + 1 / 2) / ((p : ℝ) + 1 / 2)) - (H q - H p)) -
      (1 / 24 : ℝ) * (1 / ((p : ℝ) + 1 / 2) ^ 2 - 1 / ((q : ℝ) + 1 / 2) ^ 2)| ≤
      ((q : ℝ) - (p : ℝ)) / ((p : ℝ) + 1) ^ 5 := by
  rw [harmonic_sub_eq_sum hpq, ← sum_log_tele' hp hpq, ← sum_sq_tele hpq,
      Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ Finset.Icc (p + 1) q,
        ((Real.log (((k : ℝ) + 1 / 2) / ((k : ℝ) - 1 / 2)) - 1 / (k : ℝ)) -
          (1 / 24 : ℝ) * (1 / ((k : ℝ) - 1 / 2) ^ 2 - 1 / ((k : ℝ) + 1 / 2) ^ 2))|
      ≤ ∑ k ∈ Finset.Icc (p + 1) q,
        |(Real.log (((k : ℝ) + 1 / 2) / ((k : ℝ) - 1 / 2)) - 1 / (k : ℝ)) -
          (1 / 24 : ℝ) * (1 / ((k : ℝ) - 1 / 2) ^ 2 - 1 / ((k : ℝ) + 1 / 2) ^ 2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Icc (p + 1) q, (1 / ((p : ℝ) + 1) ^ 5) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk_ge : p + 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hk2 : 2 ≤ k := by omega
        have hkR : (p : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk_ge
        have hstep := em_step_bound hk2
        have hpow : ((p : ℝ) + 1) ^ 5 ≤ (k : ℝ) ^ 5 := pow_le_pow_left₀ (by positivity) hkR 5
        exact le_trans hstep (one_div_le_one_div_of_le (by positivity) hpow)
    _ = ((q : ℝ) - (p : ℝ)) / ((p : ℝ) + 1) ^ 5 := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        have hcard : (q + 1 - (p + 1) : ℕ) = q - p := by omega
        rw [hcard, Nat.cast_sub hpq, mul_one_div]

/-! ### Part 2: Cubic Polynomial Setup & Lemma 7 (Algebraic Non-Vanishing) -/

/-- An integer cubic polynomial `g(x) = a x^3 + b x^2 + c x + d` with `a > 0`. -/
structure IntCubic where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  ha : 0 < a

namespace IntCubic

noncomputable section

def evalZ (g : IntCubic) (n : ℤ) : ℤ :=
  g.a * n ^ 3 + g.b * n ^ 2 + g.c * n + g.d

def evalR (g : IntCubic) (x : ℝ) : ℝ :=
  (g.a : ℝ) * x ^ 3 + (g.b : ℝ) * x ^ 2 + (g.c : ℝ) * x + (g.d : ℝ)

/-- Comparison polynomial `P_g(n) = g(n - 1/2) + 1/2`. -/
def P (g : IntCubic) (n : ℤ) : ℝ :=
  g.evalR ((n : ℝ) - 1 / 2) + 1 / 2

/-- Block harmonic mean `M_g(n) = (g(n) - g(n-1)) / (H_{g(n)} - H_{g(n-1)})` for `n : ℕ`. -/
noncomputable def M (g : IntCubic) (n : ℕ) : ℝ :=
  (g.evalR n - g.evalR ((n : ℝ) - 1)) /
    (H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat)

/-- Floored block harmonic mean `m_g(n) = ⌊M_g(n)⌋`. -/
noncomputable def m (g : IntCubic) (n : ℕ) : ℤ :=
  ⌊g.M n⌋

/-- First asymptotic error invariant `c₁`. -/
def c1 (g : IntCubic) : ℝ :=
  -(20 * (g.b : ℝ) ^ 2 - 60 * (g.a : ℝ) * (g.c : ℝ) + 3 * (g.a : ℝ) ^ 2) / (240 * (g.a : ℝ))

/-- Second asymptotic error invariant `c₂`. -/
def c2 (g : IntCubic) : ℝ :=
  (20 * (g.b : ℝ) ^ 3 - 80 * (g.a : ℝ) * (g.b : ℝ) * (g.c : ℝ) + (g.a : ℝ) ^ 2 * (g.b : ℝ) +
    180 * (g.a : ℝ) ^ 2 * (g.d : ℝ) + 90 * (g.a : ℝ) ^ 2) / (240 * (g.a : ℝ) ^ 2)

/-- Third asymptotic error invariant `c₃`. -/
def c3 (g : IntCubic) : ℝ :=
  -(140 * (g.b : ℝ) ^ 4 - 700 * (g.a : ℝ) * (g.b : ℝ) ^ 2 * (g.c : ℝ) +
    49 * (g.a : ℝ) ^ 2 * (g.b : ℝ) ^ 2 + 840 * (g.a : ℝ) ^ 2 * (g.b : ℝ) * (g.d : ℝ) +
    420 * (g.a : ℝ) ^ 2 * (g.b : ℝ) + 560 * (g.a : ℝ) ^ 2 * (g.c : ℝ) ^ 2 -
    140 * (g.a : ℝ) ^ 3 * (g.c : ℝ) + 2 * (g.a : ℝ) ^ 4 - 140 * (g.a : ℝ) ^ 2) /
    (1680 * (g.a : ℝ) ^ 3)

lemma ha_pos (g : IntCubic) : (0 : ℝ) < (g.a : ℝ) := by exact_mod_cast g.ha

/-- **Lemma 7 (Algebraic Non-Vanishing of `(c₁, c₂, c₃)`)**:
If `c₁ = 0` and `c₂ = 0`, then `c₃ = (9a² + 350) / (4200a) > 0`. -/
theorem nonvanishing_c1_c2_c3 (g : IntCubic) (h1 : g.c1 = 0) (h2 : g.c2 = 0) :
    g.c3 = (9 * (g.a : ℝ) ^ 2 + 350) / (4200 * (g.a : ℝ)) ∧ 0 < g.c3 := by
  have ha : (0 : ℝ) < (g.a : ℝ) := g.ha_pos
  have hc : (g.c : ℝ) = (g.b : ℝ) ^ 2 / (3 * (g.a : ℝ)) + (g.a : ℝ) / 20 := by
    unfold c1 at h1
    rw [div_eq_zero_iff] at h1
    have hnum : -(20 * (g.b : ℝ) ^ 2 - 60 * (g.a : ℝ) * (g.c : ℝ) + 3 * (g.a : ℝ) ^ 2) = 0 :=
      h1.resolve_right (by positivity)
    field_simp [ha.ne']
    linarith
  have hd : (g.d : ℝ) = (g.b : ℝ) ^ 3 / (27 * (g.a : ℝ) ^ 2) + (g.b : ℝ) / 60 - 1 / 2 := by
    unfold c2 at h2
    rw [div_eq_zero_iff] at h2
    have hnum := h2.resolve_right (by positivity)
    rw [hc] at hnum
    field_simp [ha.ne'] at hnum ⊢
    linarith
  have hc3 : g.c3 = (9 * (g.a : ℝ) ^ 2 + 350) / (4200 * (g.a : ℝ)) := by
    unfold c3
    rw [hc, hd]
    field_simp [ha.ne']
    ring
  refine ⟨hc3, ?_⟩
  rw [hc3]
  positivity

/-! ### Part 3: Lemma 6 (Asymptotic Expansion of `M_g(n)` via `z = 1/u → 0`) -/

/-- Eventually `g(n) > g(n-1) ≥ 1` and `n ≥ 2`. -/
lemma eventually_monotone_pos (g : IntCubic) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 1 ≤ g.evalZ ((n : ℤ) - 1) ∧ g.evalZ ((n : ℤ) - 1) < g.evalZ n := by
  have h1 : Tendsto (fun n : ℕ => (g.evalR ((n : ℝ) - 1))) atTop atTop := by
    have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hlim : Tendsto (fun n : ℕ => (g.a : ℝ) * (1 - 1 / (n : ℝ)) ^ 3 +
        (g.b : ℝ) * (1 - 1 / (n : ℝ)) ^ 2 / (n : ℝ) +
        (g.c : ℝ) * (1 - 1 / (n : ℝ)) / (n : ℝ) ^ 2 + (g.d : ℝ) / (n : ℝ) ^ 3)
        atTop (nhds (g.a : ℝ)) := by
      have h1m : Tendsto (fun n : ℕ => 1 - (1 : ℝ) / (n : ℝ)) atTop (nhds 1) := by
        simpa using tendsto_const_nhds.sub hinv
      have hterm1 : Tendsto (fun n : ℕ => (g.a : ℝ) * (1 - 1 / (n : ℝ)) ^ 3) atTop (nhds (g.a : ℝ)) := by
        simpa using (tendsto_const_nhds.mul (h1m.pow 3))
      have hterm2 : Tendsto (fun n : ℕ => (g.b : ℝ) * (1 - 1 / (n : ℝ)) ^ 2 / (n : ℝ)) atTop (nhds 0) := by
        have := (tendsto_const_nhds (x := (g.b : ℝ))).mul (h1m.pow 2) |>.mul hinv
        simpa [div_eq_mul_inv] using this
      have hterm3 : Tendsto (fun n : ℕ => (g.c : ℝ) * (1 - 1 / (n : ℝ)) / (n : ℝ) ^ 2) atTop (nhds 0) := by
        have := (tendsto_const_nhds (x := (g.c : ℝ))).mul h1m |>.mul (hinv.pow 2)
        simpa [div_eq_mul_inv, one_div_pow] using this
      have hterm4 : Tendsto (fun n : ℕ => (g.d : ℝ) / (n : ℝ) ^ 3) atTop (nhds 0) := by
        have := (tendsto_const_nhds (x := (g.d : ℝ))).mul (hinv.pow 3)
        simpa [div_eq_mul_inv, one_div_pow] using this
      simpa using ((hterm1.add hterm2).add hterm3).add hterm4
    have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ 3) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp tendsto_natCast_atTop_atTop
    have hprod := Filter.Tendsto.atTop_mul_pos g.ha_pos hpow hlim
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    unfold evalR; field_simp [hnR]
  have h2 : Tendsto (fun n : ℕ => g.evalR n - g.evalR ((n : ℝ) - 1)) atTop atTop := by
    have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hlim : Tendsto (fun n : ℕ => 3 * (g.a : ℝ) +
        (2 * (g.b : ℝ) - 3 * (g.a : ℝ)) * (1 / (n : ℝ)) +
        ((g.a : ℝ) - (g.b : ℝ) + (g.c : ℝ)) * (1 / (n : ℝ)) ^ 2) atTop (nhds (3 * (g.a : ℝ))) := by
      simpa using (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)).add
        (tendsto_const_nhds.mul (hinv.pow 2))
    have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
    have hprod := Filter.Tendsto.atTop_mul_pos (by linarith [g.ha_pos] : 0 < 3 * (g.a : ℝ)) hpow hlim
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    unfold evalR; field_simp [hnR]; ring
  filter_upwards [eventually_ge_atTop 2, h1.eventually (eventually_ge_atTop 1),
      h2.eventually (eventually_gt_atTop 0)] with n hn hge1 hdiff
  refine ⟨hn, ?_, ?_⟩
  · have hcast : ((g.evalZ ((n : ℤ) - 1) : ℤ) : ℝ) = g.evalR ((n : ℝ) - 1) := by
      unfold evalZ evalR; push_cast; ring
    have : (1 : ℝ) ≤ ((g.evalZ ((n : ℤ) - 1) : ℤ) : ℝ) := by linarith
    exact_mod_cast this
  · have hcast1 : ((g.evalZ ((n : ℤ) - 1) : ℤ) : ℝ) = g.evalR ((n : ℝ) - 1) := by
      unfold evalZ evalR; push_cast; ring
    have hcast2 : ((g.evalZ n : ℤ) : ℝ) = g.evalR n := by
      unfold evalZ evalR; push_cast; ring
    have : ((g.evalZ ((n : ℤ) - 1) : ℤ) : ℝ) < ((g.evalZ n : ℤ) : ℝ) := by linarith
    exact_mod_cast this

/-- **Lemma 6 (Exact Asymptotic Expansion of `M_g(n)` through `u⁻³`)**:
With `u = n - 1/2`, `u³ * (M_g(n) - P_g(n) - c₁/u - c₂/u²) → c₃` as `n → ∞`. -/
private lemma Q_poly_div7_gen (t1 t2 t3 t4 t5 q2 q3 q4 q5 q6 : ℝ)
    (hc2 : t1 ^ 2 / 3 = q2)
    (hc3 : 2 * t1 * t2 / 3 = q3)
    (hc4 : (2 * t1 * t3 + t2 ^ 2) / 3 + t1 ^ 4 / 5 = q4)
    (hc5 : (2 * t1 * t4 + 2 * t2 * t3) / 3 + 4 * t1 ^ 3 * t2 / 5 = q5)
    (hc6 : (2 * t1 * t5 + 2 * t2 * t4 + t3 ^ 2) / 3 +
      (4 * t1 ^ 3 * t3 + 6 * t1 ^ 2 * t2 ^ 2) / 5 + t1 ^ 6 / 7 = q6) :
    ∃ P7 : ℝ → ℝ, Continuous P7 ∧ ∀ w : ℝ,
      let tp := t1 * w + t2 * w ^ 2 + t3 * w ^ 3 + t4 * w ^ 4 + t5 * w ^ 5
      (1 + tp ^ 2 / 3 + tp ^ 4 / 5 + tp ^ 6 / 7) -
        (1 + q2 * w ^ 2 + q3 * w ^ 3 + q4 * w ^ 4 + q5 * w ^ 5 + q6 * w ^ 6) =
      w ^ 7 * P7 w := by
  let U : ℝ → ℝ := fun w => t1 + t2 * w + t3 * w ^ 2 + t4 * w ^ 3 + t5 * w ^ 4
  let U3 : ℝ → ℝ := fun w => t1 + t2 * w + t3 * w ^ 2
  let r4 : ℝ → ℝ := fun w => t4 + t5 * w
  let r6 : ℝ → ℝ := fun w => t2 + t3 * w + t4 * w ^ 2 + t5 * w ^ 3
  let q_err2 : ℝ → ℝ := fun w =>
    (2 * t2 * t5 + 2 * t3 * t4) + (2 * t3 * t5 + t4 ^ 2) * w + (2 * t4 * t5) * w ^ 2 + t5 ^ 2 * w ^ 3
  let q_err4 : ℝ → ℝ := fun w =>
    r4 w * (U w ^ 3 + U w ^ 2 * U3 w + U w * U3 w ^ 2 + U3 w ^ 3) +
    (4 * t1 * t2 ^ 3 + 12 * t1 ^ 2 * t2 * t3) +
    (t2 ^ 4 + 12 * t1 * t2 ^ 2 * t3 + 6 * t1 ^ 2 * t3 ^ 2) * w +
    (4 * t2 ^ 3 * t3 + 12 * t1 * t2 * t3 ^ 2) * w ^ 2 +
    (6 * t2 ^ 2 * t3 ^ 2 + 4 * t1 * t3 ^ 3) * w ^ 3 +
    (4 * t2 * t3 ^ 3) * w ^ 4 + t3 ^ 4 * w ^ 5
  let q_err6 : ℝ → ℝ := fun w =>
    r6 w * (U w ^ 5 + U w ^ 4 * t1 + U w ^ 3 * t1 ^ 2 + U w ^ 2 * t1 ^ 3 + U w * t1 ^ 4 + t1 ^ 5)
  refine ⟨fun w => q_err2 w / 3 + q_err4 w / 5 + q_err6 w / 7, by fun_prop, fun w => ?_⟩
  dsimp only
  have hsq : (t1 * w + t2 * w ^ 2 + t3 * w ^ 3 + t4 * w ^ 4 + t5 * w ^ 5) ^ 2 =
      (t1 ^ 2 * w ^ 2 + 2 * t1 * t2 * w ^ 3 + (2 * t1 * t3 + t2 ^ 2) * w ^ 4 +
        (2 * t1 * t4 + 2 * t2 * t3) * w ^ 5 + (2 * t1 * t5 + 2 * t2 * t4 + t3 ^ 2) * w ^ 6) +
        w ^ 7 * q_err2 w := by dsimp only [q_err2]; ring
  have h4 : (t1 * w + t2 * w ^ 2 + t3 * w ^ 3 + t4 * w ^ 4 + t5 * w ^ 5) ^ 4 =
      (t1 ^ 4 * w ^ 4 + 4 * t1 ^ 3 * t2 * w ^ 5 + (4 * t1 ^ 3 * t3 + 6 * t1 ^ 2 * t2 ^ 2) * w ^ 6) +
        w ^ 7 * q_err4 w := by
    have hstep1 : (t1 * w + t2 * w ^ 2 + t3 * w ^ 3 + t4 * w ^ 4 + t5 * w ^ 5) ^ 4 -
        (t1 * w + t2 * w ^ 2 + t3 * w ^ 3) ^ 4 =
        w ^ 7 * (r4 w * (U w ^ 3 + U w ^ 2 * U3 w + U w * U3 w ^ 2 + U3 w ^ 3)) := by
      have htU : t1 * w + t2 * w ^ 2 + t3 * w ^ 3 + t4 * w ^ 4 + t5 * w ^ 5 = w * U w := by
        dsimp only [U]; ring
      have hpU : t1 * w + t2 * w ^ 2 + t3 * w ^ 3 = w * U3 w := by dsimp only [U3]; ring
      have hsub : U w - U3 w = w ^ 3 * r4 w := by dsimp only [U, U3, r4]; ring
      rw [htU, hpU]
      calc (w * U w) ^ 4 - (w * U3 w) ^ 4
          = w ^ 4 * ((U w - U3 w) * (U w ^ 3 + U w ^ 2 * U3 w + U w * U3 w ^ 2 + U3 w ^ 3)) := by ring
        _ = w ^ 7 * (r4 w * (U w ^ 3 + U w ^ 2 * U3 w + U w * U3 w ^ 2 + U3 w ^ 3)) := by rw [hsub]; ring
    have hstep2 : (t1 * w + t2 * w ^ 2 + t3 * w ^ 3) ^ 4 =
        (t1 ^ 4 * w ^ 4 + 4 * t1 ^ 3 * t2 * w ^ 5 + (4 * t1 ^ 3 * t3 + 6 * t1 ^ 2 * t2 ^ 2) * w ^ 6) +
        w ^ 7 * ((4 * t1 * t2 ^ 3 + 12 * t1 ^ 2 * t2 * t3) +
          (t2 ^ 4 + 12 * t1 * t2 ^ 2 * t3 + 6 * t1 ^ 2 * t3 ^ 2) * w +
          (4 * t2 ^ 3 * t3 + 12 * t1 * t2 * t3 ^ 2) * w ^ 2 +
          (6 * t2 ^ 2 * t3 ^ 2 + 4 * t1 * t3 ^ 3) * w ^ 3 +
          (4 * t2 * t3 ^ 3) * w ^ 4 + t3 ^ 4 * w ^ 5) := by ring
    dsimp only [q_err4]
    linarith
  have h6 : (t1 * w + t2 * w ^ 2 + t3 * w ^ 3 + t4 * w ^ 4 + t5 * w ^ 5) ^ 6 =
      t1 ^ 6 * w ^ 6 + w ^ 7 * q_err6 w := by
    have htU : t1 * w + t2 * w ^ 2 + t3 * w ^ 3 + t4 * w ^ 4 + t5 * w ^ 5 = w * U w := by
      dsimp only [U]; ring
    have hsub : U w - t1 = w * r6 w := by dsimp only [U, r6]; ring
    rw [htU]
    calc (w * U w) ^ 6
        = t1 ^ 6 * w ^ 6 + w ^ 6 * ((U w - t1) *
            (U w ^ 5 + U w ^ 4 * t1 + U w ^ 3 * t1 ^ 2 + U w ^ 2 * t1 ^ 3 + U w * t1 ^ 4 + t1 ^ 5)) := by ring
      _ = t1 ^ 6 * w ^ 6 + w ^ 7 * q_err6 w := by rw [hsub]; dsimp only [q_err6]; ring
  rw [hsq, h4, h6]
  linear_combination hc2 * w ^ 2 + hc3 * w ^ 3 + hc4 * w ^ 4 + hc5 * w ^ 5 + hc6 * w ^ 6

private def Sz (g : IntCubic) (w : ℝ) : ℝ :=
  (g.a : ℝ) + (g.b : ℝ) * w + ((g.c : ℝ) + 3 / 4 * (g.a : ℝ)) * w ^ 2 +
    ((g.d : ℝ) + 1 / 4 * (g.b : ℝ) + 1 / 2) * w ^ 3

private def Dz (g : IntCubic) (w : ℝ) : ℝ :=
  3 / 2 * (g.a : ℝ) * w + (g.b : ℝ) * w ^ 2 + (1 / 2 * (g.c : ℝ) + 1 / 8 * (g.a : ℝ)) * w ^ 3

private def Dz1 (g : IntCubic) (w : ℝ) : ℝ :=
  3 / 2 * (g.a : ℝ) + (g.b : ℝ) * w + (1 / 2 * (g.c : ℝ) + 1 / 8 * (g.a : ℝ)) * w ^ 2

private def Q_of_t (x : ℝ) : ℝ := 1 + x ^ 2 / 3 + x ^ 4 / 5 + x ^ 6 / 7

private def Rlogz (g : IntCubic) (w : ℝ) : ℝ :=
  (g.a : ℝ) + (g.b : ℝ) * w + (g.c : ℝ) * w ^ 2 + ((g.d : ℝ) + 1 / 2) * w ^ 3 +
    g.c1 * w ^ 4 + g.c2 * w ^ 5 + (g.c3 - 1 / (12 * (g.a : ℝ))) * w ^ 6

private lemma M_g_partA (g : IntCubic) :
    let z : ℕ → ℝ := fun n => 1 / ((n : ℝ) - 1 / 2)
    let t : ℕ → ℝ := fun n => g.Dz (z n) / g.Sz (z n)
    Tendsto (fun n => (g.Rlogz (z n) * Q_of_t (t n) - g.Sz (z n)) / (z n) ^ 6) atTop (nhds 0) := by
  intro z t
  have ha : (0 : ℝ) < (g.a : ℝ) := g.ha_pos
  have hz_tendsto : Tendsto z atTop (nhds 0) := by
    have hu : Tendsto (fun n : ℕ => (n : ℝ) - 1 / 2) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact tendsto_const_nhds.div_atTop hu
  have hz_pos : ∀ n : ℕ, 2 ≤ n → 0 < z n := fun n hn => by
    dsimp [z]
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact div_pos one_pos (by linarith)
  have hSz_lim : Tendsto (fun n => g.Sz (z n)) atTop (nhds (g.a : ℝ)) := by
    have hcont : Continuous g.Sz := by unfold Sz; fun_prop
    have h0 : g.Sz 0 = (g.a : ℝ) := by unfold Sz; ring
    simpa [Function.comp_def, h0] using (hcont.tendsto 0).comp hz_tendsto
  have hDz1_lim : Tendsto (fun n => g.Dz1 (z n)) atTop (nhds (3 / 2 * (g.a : ℝ))) := by
    have hcont : Continuous g.Dz1 := by unfold Dz1; fun_prop
    have h0 : g.Dz1 0 = 3 / 2 * (g.a : ℝ) := by unfold Dz1; ring
    simpa [Function.comp_def, h0] using (hcont.tendsto 0).comp hz_tendsto
  have ht_over_z : Tendsto (fun n => t n / z n) atTop (nhds (3 / 2 : ℝ)) := by
    have hq : Tendsto (fun n => g.Dz1 (z n) / g.Sz (z n)) atTop (nhds (3 / 2 : ℝ)) := by
      have := hDz1_lim.div hSz_lim ha.ne'
      convert this using 1; field_simp [ha.ne']
    refine hq.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hz0 : z n ≠ 0 := (hz_pos n hn).ne'
    dsimp [t, Dz, Dz1]; field_simp [hz0]
  have ht_lim : Tendsto t atTop (nhds 0) := by
    have := ht_over_z.mul hz_tendsto
    simp only [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hz0 : z n ≠ 0 := (hz_pos n hn).ne'
    field_simp [hz0]
  let c3_log : ℝ := g.c3 - 1 / (12 * (g.a : ℝ))
  let t1 : ℝ := 3 / 2
  let t2 : ℝ := -(g.b : ℝ) / (2 * (g.a : ℝ))
  let t3 : ℝ := -(2 * (g.a : ℝ) ^ 2 + 2 * (g.a : ℝ) * (g.c : ℝ) - (g.b : ℝ) ^ 2) / (2 * (g.a : ℝ) ^ 2)
  let t4 : ℝ := (4 * (g.a : ℝ) ^ 2 * (g.b : ℝ) - 6 * (g.a : ℝ) ^ 2 * (g.d : ℝ) -
      3 * (g.a : ℝ) ^ 2 + 6 * (g.a : ℝ) * (g.b : ℝ) * (g.c : ℝ) - 2 * (g.b : ℝ) ^ 3) / (4 * (g.a : ℝ) ^ 3)
  let t5 : ℝ := (3 * (g.a : ℝ) ^ 4 + 7 * (g.a : ℝ) ^ 3 * (g.c : ℝ) - 5 * (g.a : ℝ) ^ 2 * (g.b : ℝ) ^ 2 +
      8 * (g.a : ℝ) ^ 2 * (g.b : ℝ) * (g.d : ℝ) + 4 * (g.a : ℝ) ^ 2 * (g.b : ℝ) +
      4 * (g.a : ℝ) ^ 2 * (g.c : ℝ) ^ 2 - 8 * (g.a : ℝ) * (g.b : ℝ) ^ 2 * (g.c : ℝ) + 2 * (g.b : ℝ) ^ 4) /
      (4 * (g.a : ℝ) ^ 4)
  let tPoly : ℝ → ℝ := fun w => t1 * w + t2 * w ^ 2 + t3 * w ^ 3 + t4 * w ^ 4 + t5 * w ^ 5
  have ht_err : Tendsto (fun n => (t n - tPoly (z n)) / (z n) ^ 5) atTop (nhds 0) := by
    let rem : ℝ → ℝ := fun w =>
      -((g.b : ℝ) * t5 + ((g.c : ℝ) + 3 / 4 * (g.a : ℝ)) * t4 +
          ((g.d : ℝ) + 1 / 4 * (g.b : ℝ) + 1 / 2) * t3) -
        (((g.c : ℝ) + 3 / 4 * (g.a : ℝ)) * t5 +
          ((g.d : ℝ) + 1 / 4 * (g.b : ℝ) + 1 / 2) * t4) * w -
        (((g.d : ℝ) + 1 / 4 * (g.b : ℝ) + 1 / 2) * t5) * w ^ 2
    have hrem_id : ∀ w : ℝ, g.Dz w - g.Sz w * tPoly w = w ^ 6 * rem w := by
      intro w
      dsimp only [Dz, Sz, tPoly, rem, t1, t2, t3, t4, t5]
      field_simp [ha.ne']
      ring
    have hcont_rem : Continuous rem := by fun_prop
    have hlim : Tendsto (fun n => z n * rem (z n) / g.Sz (z n)) atTop (nhds 0) := by
      have h1 := hz_tendsto.mul ((hcont_rem.tendsto 0).comp hz_tendsto)
      have h2 := h1.div hSz_lim ha.ne'
      rw [zero_mul, zero_div] at h2
      exact h2
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 2, hSz_lim.eventually (eventually_gt_nhds (show (g.a : ℝ) / 2 < (g.a : ℝ) by linarith))] with n hn hSpos
    have hz0 : z n ≠ 0 := (hz_pos n hn).ne'
    have hS0 : g.Sz (z n) ≠ 0 := by linarith
    dsimp [t]
    have hsub : g.Dz (z n) / g.Sz (z n) - tPoly (z n) = (g.Dz (z n) - g.Sz (z n) * tPoly (z n)) / g.Sz (z n) := by
      field_simp [hS0]
    rw [hsub, hrem_id (z n)]
    field_simp [hz0, hS0]
  let q2 : ℝ := 3 / 4
  let q3 : ℝ := -(g.b : ℝ) / (2 * (g.a : ℝ))
  let q4 : ℝ := (3 * (g.a : ℝ) ^ 2 - 240 * (g.a : ℝ) * (g.c : ℝ) + 140 * (g.b : ℝ) ^ 2) / (240 * (g.a : ℝ) ^ 2)
  let q5 : ℝ := -((g.a : ℝ) ^ 2 * (g.b : ℝ) + 90 * (g.a : ℝ) ^ 2 * (g.d : ℝ) +
      45 * (g.a : ℝ) ^ 2 - 110 * (g.a : ℝ) * (g.b : ℝ) * (g.c : ℝ) + 40 * (g.b : ℝ) ^ 3) / (60 * (g.a : ℝ) ^ 3)
  let q6 : ℝ := (71 * (g.a : ℝ) ^ 4 - 1904 * (g.a : ℝ) ^ 3 * (g.c : ℝ) +
      728 * (g.a : ℝ) ^ 2 * (g.b : ℝ) ^ 2 + 16800 * (g.a : ℝ) ^ 2 * (g.b : ℝ) * (g.d : ℝ) +
      8400 * (g.a : ℝ) ^ 2 * (g.b : ℝ) + 8960 * (g.a : ℝ) ^ 2 * (g.c : ℝ) ^ 2 -
      19040 * (g.a : ℝ) * (g.b : ℝ) ^ 2 * (g.c : ℝ) + 5040 * (g.b : ℝ) ^ 4) / (6720 * (g.a : ℝ) ^ 4)
  let QPoly : ℝ → ℝ := fun w => 1 + q2 * w ^ 2 + q3 * w ^ 3 + q4 * w ^ 4 + q5 * w ^ 5 + q6 * w ^ 6
  have hQ_t_diff : Tendsto (fun n => (Q_of_t (t n) - Q_of_t (tPoly (z n))) / (z n) ^ 6) atTop (nhds 0) := by
    have htP_over_z : Tendsto (fun n => tPoly (z n) / z n) atTop (nhds (3 / 2 : ℝ)) := by
      let tp1 : ℝ → ℝ := fun w => t1 + t2 * w + t3 * w ^ 2 + t4 * w ^ 3 + t5 * w ^ 4
      have hcont : Continuous tp1 := by fun_prop
      have hlim : Tendsto (fun n => tp1 (z n)) atTop (nhds (3 / 2 : ℝ)) := by
        convert (hcont.tendsto 0).comp hz_tendsto using 2; dsimp [tp1, t1]; ring
      refine hlim.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hz0 : z n ≠ 0 := (hz_pos n hn).ne'
      dsimp [tp1, tPoly]; field_simp [hz0]
    have hfactor : Tendsto (fun n =>
        (t n / z n + tPoly (z n) / z n) / 3 +
        ((t n / z n + tPoly (z n) / z n) * ((t n) ^ 2 + (tPoly (z n)) ^ 2)) / 5 +
        ((t n / z n + tPoly (z n) / z n) * ((t n) ^ 4 + (t n) ^ 2 * (tPoly (z n)) ^ 2 + (tPoly (z n)) ^ 4)) / 7)
        atTop (nhds (1 : ℝ)) := by
      have htP_lim : Tendsto (fun n => tPoly (z n)) atTop (nhds 0) := by
        have hcont : Continuous tPoly := by fun_prop
        convert (hcont.tendsto 0).comp hz_tendsto using 2; dsimp [tPoly]; ring
      have hsum := ht_over_z.add htP_over_z
      have h1 : Tendsto (fun n => (t n / z n + tPoly (z n) / z n) / 3) atTop (nhds 1) := by
        convert hsum.div_const 3 using 1; norm_num
      have h2 : Tendsto (fun n => ((t n / z n + tPoly (z n) / z n) * ((t n) ^ 2 + (tPoly (z n)) ^ 2)) / 5)
          atTop (nhds 0) := by
        have := (hsum.mul ((ht_lim.pow 2).add (htP_lim.pow 2))).div_const 5
        simpa using this
      have h3 : Tendsto (fun n => ((t n / z n + tPoly (z n) / z n) *
          ((t n) ^ 4 + (t n) ^ 2 * (tPoly (z n)) ^ 2 + (tPoly (z n)) ^ 4)) / 7) atTop (nhds 0) := by
        have := (hsum.mul (((ht_lim.pow 4).add ((ht_lim.pow 2).mul (htP_lim.pow 2))).add (htP_lim.pow 4))).div_const 7
        simpa using this
      simpa using (h1.add h2).add h3
    have hprod := ht_err.mul hfactor
    simp only [zero_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hz0 : z n ≠ 0 := (hz_pos n hn).ne'
    dsimp [Q_of_t]
    generalize t n = x
    generalize tPoly (z n) = y
    generalize z n = w at hz0 ⊢
    field_simp [hz0]
    ring
  have hQ_poly_diff : Tendsto (fun n => (Q_of_t (tPoly (z n)) - QPoly (z n)) / (z n) ^ 6) atTop (nhds 0) := by
    have hc2 : t1 ^ 2 / 3 = q2 := by dsimp only [t1, q2]; norm_num
    have hc3 : 2 * t1 * t2 / 3 = q3 := by dsimp only [t1, t2, q3]; field_simp [ha.ne']
    have hc4 : (2 * t1 * t3 + t2 ^ 2) / 3 + t1 ^ 4 / 5 = q4 := by
      dsimp only [t1, t2, t3, q4]; field_simp [ha.ne']; ring
    have hc5 : (2 * t1 * t4 + 2 * t2 * t3) / 3 + 4 * t1 ^ 3 * t2 / 5 = q5 := by
      dsimp only [t1, t2, t3, t4, q5]; field_simp [ha.ne']; ring
    have hc6 : (2 * t1 * t5 + 2 * t2 * t4 + t3 ^ 2) / 3 +
        (4 * t1 ^ 3 * t3 + 6 * t1 ^ 2 * t2 ^ 2) / 5 + t1 ^ 6 / 7 = q6 := by
      dsimp only [t1, t2, t3, t4, t5, q6]; field_simp [ha.ne']; ring
    have hdiv7 : ∃ P7 : ℝ → ℝ, Continuous P7 ∧ ∀ w : ℝ, Q_of_t (tPoly w) - QPoly w = w ^ 7 * P7 w :=
      Q_poly_div7_gen t1 t2 t3 t4 t5 q2 q3 q4 q5 q6 hc2 hc3 hc4 hc5 hc6
    obtain ⟨P7, hP7_cont, hP7_eq⟩ := hdiv7
    have hlim : Tendsto (fun n => z n * P7 (z n)) atTop (nhds 0) := by
      simpa using hz_tendsto.mul ((hP7_cont.tendsto 0).comp hz_tendsto)
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hz0 : z n ≠ 0 := (hz_pos n hn).ne'
    rw [hP7_eq (z n)]; field_simp [hz0]
  have hRQ_diff : Tendsto (fun n => (g.Rlogz (z n) * QPoly (z n) - g.Sz (z n)) / (z n) ^ 6) atTop (nhds 0) := by
    let PR : ℝ → ℝ := fun w =>
      ((g.b : ℝ) * q6 + (g.c : ℝ) * q5 + ((g.d : ℝ) + 1 / 2) * q4 + g.c1 * q3 + g.c2 * q2) +
      ((g.c : ℝ) * q6 + ((g.d : ℝ) + 1 / 2) * q5 + g.c1 * q4 + g.c2 * q3 + c3_log * q2) * w +
      (((g.d : ℝ) + 1 / 2) * q6 + g.c1 * q5 + g.c2 * q4 + c3_log * q3) * w ^ 2 +
      (g.c1 * q6 + g.c2 * q5 + c3_log * q4) * w ^ 3 +
      (g.c2 * q6 + c3_log * q5) * w ^ 4 +
      (c3_log * q6) * w ^ 5
    have hPR_eq : ∀ w : ℝ, g.Rlogz w * QPoly w - g.Sz w = w ^ 7 * PR w := by
      intro w
      dsimp only [Rlogz, QPoly, Sz, PR]
      have he0 : (g.a : ℝ) * q2 + (g.c : ℝ) = (g.c : ℝ) + 3 / 4 * (g.a : ℝ) := by dsimp only [q2]; ring
      have he3 : (g.a : ℝ) * q3 + (g.b : ℝ) * q2 + ((g.d : ℝ) + 1 / 2) =
          (g.d : ℝ) + 1 / 4 * (g.b : ℝ) + 1 / 2 := by dsimp only [q2, q3]; field_simp [ha.ne']; ring
      have he4 : (g.a : ℝ) * q4 + (g.b : ℝ) * q3 + (g.c : ℝ) * q2 + g.c1 = 0 := by
        dsimp only [q2, q3, q4, c1]; field_simp [ha.ne']; ring
      have he5 : (g.a : ℝ) * q5 + (g.b : ℝ) * q4 + (g.c : ℝ) * q3 +
          ((g.d : ℝ) + 1 / 2) * q2 + g.c2 = 0 := by
        dsimp only [q2, q3, q4, q5, c2]; field_simp [ha.ne']; ring
      have he6 : (g.a : ℝ) * q6 + (g.b : ℝ) * q5 + (g.c : ℝ) * q4 +
          ((g.d : ℝ) + 1 / 2) * q3 + g.c1 * q2 + c3_log = 0 := by
        dsimp only [q2, q3, q4, q5, q6, c1, c3_log, c3]; field_simp [ha.ne']; ring
      have hr_gen : ∀ (va vb vc vd vc1 vc2 vc3 b2 b3 b4 b5 b6 x : ℝ),
          va * b2 + vc = vc + 3 / 4 * va →
          va * b3 + vb * b2 + (vd + 1 / 2) = vd + 1 / 4 * vb + 1 / 2 →
          va * b4 + vb * b3 + vc * b2 + vc1 = 0 →
          va * b5 + vb * b4 + vc * b3 + (vd + 1 / 2) * b2 + vc2 = 0 →
          va * b6 + vb * b5 + vc * b4 + (vd + 1 / 2) * b3 + vc1 * b2 + vc3 = 0 →
          (va + vb * x + vc * x ^ 2 + (vd + 1 / 2) * x ^ 3 + vc1 * x ^ 4 + vc2 * x ^ 5 + vc3 * x ^ 6) *
            (1 + b2 * x ^ 2 + b3 * x ^ 3 + b4 * x ^ 4 + b5 * x ^ 5 + b6 * x ^ 6) -
            (va + vb * x + (vc + 3 / 4 * va) * x ^ 2 + (vd + 1 / 4 * vb + 1 / 2) * x ^ 3) =
          x ^ 7 * ((vb * b6 + vc * b5 + (vd + 1 / 2) * b4 + vc1 * b3 + vc2 * b2) +
            (vc * b6 + (vd + 1 / 2) * b5 + vc1 * b4 + vc2 * b3 + vc3 * b2) * x +
            ((vd + 1 / 2) * b6 + vc1 * b5 + vc2 * b4 + vc3 * b3) * x ^ 2 +
            (vc1 * b6 + vc2 * b5 + vc3 * b4) * x ^ 3 +
            (vc2 * b6 + vc3 * b5) * x ^ 4 + (vc3 * b6) * x ^ 5) := by
        intro va vb vc vd vc1 vc2 vc3 b2 b3 b4 b5 b6 x h0 h3 h4 h5 h6
        linear_combination h0 * x ^ 2 + h3 * x ^ 3 + h4 * x ^ 4 + h5 * x ^ 5 + h6 * x ^ 6
      exact hr_gen (g.a : ℝ) (g.b : ℝ) (g.c : ℝ) (g.d : ℝ) g.c1 g.c2 c3_log q2 q3 q4 q5 q6 w he0 he3 he4 he5 he6
    have hcont : Continuous PR := by fun_prop
    have hlim : Tendsto (fun n => z n * PR (z n)) atTop (nhds 0) := by
      simpa using hz_tendsto.mul ((hcont.tendsto 0).comp hz_tendsto)
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hz0 : z n ≠ 0 := (hz_pos n hn).ne'
    rw [hPR_eq (z n)]; field_simp [hz0]
  have hR_lim : Tendsto (fun n => g.Rlogz (z n)) atTop (nhds (g.a : ℝ)) := by
    have hcont : Continuous g.Rlogz := by unfold Rlogz; fun_prop
    have h0 : g.Rlogz 0 = (g.a : ℝ) := by unfold Rlogz; ring
    simpa [Function.comp_def, h0] using (hcont.tendsto 0).comp hz_tendsto
  have hsum := (hR_lim.mul (hQ_t_diff.add hQ_poly_diff)).add hRQ_diff
  simp only [add_zero, mul_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hz0 : z n ≠ 0 := (hz_pos n hn).ne'
  generalize g.Rlogz (z n) = R_v
  generalize Q_of_t (t n) = Q1
  generalize Q_of_t (tPoly (z n)) = Q2
  generalize QPoly (z n) = Q3
  generalize g.Sz (z n) = S_v
  generalize z n = w at hz0 ⊢
  field_simp [hz0]; ring

private lemma M_g_partC (g : IntCubic) :
    let z : ℕ → ℝ := fun n => 1 / ((n : ℝ) - 1 / 2)
    let t : ℕ → ℝ := fun n => g.Dz (z n) / g.Sz (z n)
    Tendsto (fun n =>
      (Real.log ((1 + t n) / (1 - t n)) -
        (H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat)) / (z n) ^ 7)
      atTop (nhds (1 / (4 * (g.a : ℝ) ^ 2))) := by
  intro z t
  have ha : (0 : ℝ) < (g.a : ℝ) := g.ha_pos
  have hz_tendsto : Tendsto z atTop (nhds 0) := by
    have hu : Tendsto (fun n : ℕ => (n : ℝ) - 1 / 2) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact tendsto_const_nhds.div_atTop hu
  have hz_pos : ∀ n : ℕ, 2 ≤ n → 0 < z n := fun n hn => by
    dsimp [z]
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact div_pos one_pos (by linarith)
  have hSz_lim : Tendsto (fun n => g.Sz (z n)) atTop (nhds (g.a : ℝ)) := by
    have hcont : Continuous g.Sz := by unfold Sz; fun_prop
    have h0 : g.Sz 0 = (g.a : ℝ) := by unfold Sz; ring
    simpa [Function.comp_def, h0] using (hcont.tendsto 0).comp hz_tendsto
  have hDz1_lim : Tendsto (fun n => g.Dz1 (z n)) atTop (nhds (3 / 2 * (g.a : ℝ))) := by
    have hcont : Continuous g.Dz1 := by unfold Dz1; fun_prop
    have h0 : g.Dz1 0 = 3 / 2 * (g.a : ℝ) := by unfold Dz1; ring
    simpa [Function.comp_def, h0] using (hcont.tendsto 0).comp hz_tendsto
  have hDz_lim : Tendsto (fun n => g.Dz (z n)) atTop (nhds 0) := by
    have hcont : Continuous g.Dz := by unfold Dz; fun_prop
    have h0 : g.Dz 0 = 0 := by unfold Dz; ring
    simpa [Function.comp_def, h0] using (hcont.tendsto 0).comp hz_tendsto
  have hSmD_eq : ∀ n : ℕ, 2 ≤ n → g.Sz (z n) - g.Dz (z n) = (z n) ^ 3 * (g.evalR ((n : ℝ) - 1) + 1 / 2) := by
    intro n hn
    have hz0 : z n ≠ 0 := (hz_pos n hn).ne'
    have hinv : (n : ℝ) - 1 = 1 / z n - 1 / 2 := by
      dsimp [z]; rw [one_div_one_div]; ring
    rw [hinv]; dsimp [Sz, Dz, evalR]; field_simp [hz0]; ring
  have hSpD_eq : ∀ n : ℕ, 2 ≤ n → g.Sz (z n) + g.Dz (z n) = (z n) ^ 3 * (g.evalR n + 1 / 2) := by
    intro n hn
    have hz0 : z n ≠ 0 := (hz_pos n hn).ne'
    have hinv : (n : ℝ) = 1 / z n + 1 / 2 := by
      dsimp [z]; rw [one_div_one_div]; ring
    rw [hinv]; dsimp [Sz, Dz, evalR]; field_simp [hz0]; ring
  let E1 : ℕ → ℝ := fun n =>
    (1 / 24 : ℝ) * (1 / (g.evalR ((n : ℝ) - 1) + 1 / 2) ^ 2 - 1 / (g.evalR n + 1 / 2) ^ 2)
  have hE1_lim : Tendsto (fun n => E1 n / (z n) ^ 7) atTop (nhds (1 / (4 * (g.a : ℝ) ^ 2))) := by
    have hnum := hSz_lim.mul hDz1_lim
    have hden : Tendsto (fun n => 6 * (g.Sz (z n) - g.Dz (z n)) ^ 2 * (g.Sz (z n) + g.Dz (z n)) ^ 2)
        atTop (nhds (6 * (g.a : ℝ) ^ 4)) := by
      have h1 := (hSz_lim.sub hDz_lim).pow 2
      have h2 := (hSz_lim.add hDz_lim).pow 2
      have h3 := ((tendsto_const_nhds (x := (6 : ℝ))).mul h1).mul h2
      convert h3 using 2; ring
    have hquot : Tendsto (fun n =>
        (g.Sz (z n) * g.Dz1 (z n)) / (6 * (g.Sz (z n) - g.Dz (z n)) ^ 2 * (g.Sz (z n) + g.Dz (z n)) ^ 2))
        atTop (nhds (1 / (4 * (g.a : ℝ) ^ 2))) := by
      have := hnum.div hden (by positivity)
      convert this using 2; field_simp [ha.ne']; ring
    refine hquot.congr' ?_
    filter_upwards [eventually_ge_atTop 2, g.eventually_monotone_pos] with n hn ⟨_, hp1, hpq⟩
    have hz0 : z n ≠ 0 := (hz_pos n hn).ne'
    have hSmD := hSmD_eq n hn
    have hSpD := hSpD_eq n hn
    have hDz_eq : g.Dz (z n) = z n * g.Dz1 (z n) := by dsimp [Dz, Dz1]; ring
    have hp_pos : (0 : ℝ) < g.evalR ((n : ℝ) - 1) + 1 / 2 := by
      have hcast : ((g.evalZ ((n : ℤ) - 1) : ℤ) : ℝ) = g.evalR ((n : ℝ) - 1) := by
        unfold evalZ evalR; push_cast; ring
      have : (1 : ℝ) ≤ ((g.evalZ ((n : ℤ) - 1) : ℤ) : ℝ) := by exact_mod_cast hp1
      linarith
    have hq_pos : (0 : ℝ) < g.evalR n + 1 / 2 := by
      have hcast1 : ((g.evalZ ((n : ℤ) - 1) : ℤ) : ℝ) = g.evalR ((n : ℝ) - 1) := by
        unfold evalZ evalR; push_cast; ring
      have hcast2 : ((g.evalZ n : ℤ) : ℝ) = g.evalR n := by
        unfold evalZ evalR; push_cast; ring
      have : ((g.evalZ ((n : ℤ) - 1) : ℤ) : ℝ) < ((g.evalZ n : ℤ) : ℝ) := by exact_mod_cast hpq
      linarith
    rw [hSmD, hSpD]
    dsimp [E1]
    have h2SD : (g.evalR n + 1 / 2) ^ 2 - (g.evalR ((n : ℝ) - 1) + 1 / 2) ^ 2 =
        4 * g.Sz (z n) * g.Dz (z n) / (z n) ^ 6 := by
      have hsum : (g.evalR n + 1 / 2) + (g.evalR ((n : ℝ) - 1) + 1 / 2) = 2 * g.Sz (z n) / (z n) ^ 3 := by
        field_simp [hz0]; linarith [hSmD, hSpD]
      have hdif : (g.evalR n + 1 / 2) - (g.evalR ((n : ℝ) - 1) + 1 / 2) = 2 * g.Dz (z n) / (z n) ^ 3 := by
        field_simp [hz0]; linarith [hSmD, hSpD]
      calc (g.evalR n + 1 / 2) ^ 2 - (g.evalR ((n : ℝ) - 1) + 1 / 2) ^ 2
          = ((g.evalR n + 1 / 2) + (g.evalR ((n : ℝ) - 1) + 1 / 2)) *
            ((g.evalR n + 1 / 2) - (g.evalR ((n : ℝ) - 1) + 1 / 2)) := by ring
        _ = (2 * g.Sz (z n) / (z n) ^ 3) * (2 * g.Dz (z n) / (z n) ^ 3) := by rw [hsum, hdif]
        _ = 4 * g.Sz (z n) * g.Dz (z n) / (z n) ^ 6 := by ring
    have hnum_eq : 1 / (g.evalR ((n : ℝ) - 1) + 1 / 2) ^ 2 - 1 / (g.evalR n + 1 / 2) ^ 2 =
        ((g.evalR n + 1 / 2) ^ 2 - (g.evalR ((n : ℝ) - 1) + 1 / 2) ^ 2) /
          ((g.evalR ((n : ℝ) - 1) + 1 / 2) ^ 2 * (g.evalR n + 1 / 2) ^ 2) := by
      generalize g.evalR ((n : ℝ) - 1) + 1 / 2 = p at hp_pos ⊢
      generalize g.evalR n + 1 / 2 = q at hq_pos ⊢
      field_simp [hp_pos.ne', hq_pos.ne']
    rw [hnum_eq, h2SD, hDz_eq]
    field_simp [hz0, hp_pos.ne', hq_pos.ne']
    ring
  have hE_rem : Tendsto (fun n =>
      ((Real.log ((1 + t n) / (1 - t n)) -
        (H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat)) - E1 n) / (z n) ^ 7)
      atTop (nhds 0) := by
    have hbound_lim : Tendsto (fun n : ℕ =>
        ((g.evalR n - g.evalR ((n : ℝ) - 1)) / (g.evalR ((n : ℝ) - 1) + 1) ^ 5) / (z n) ^ 7)
        atTop (nhds 0) := by
      have h1 : Tendsto (fun n =>
          (2 * g.Dz1 (z n) * (z n) ^ 6) / (g.Sz (z n) - g.Dz (z n) + (1 / 2) * (z n) ^ 3) ^ 5)
          atTop (nhds 0) := by
        have hnum : Tendsto (fun n => 2 * g.Dz1 (z n) * (z n) ^ 6) atTop (nhds 0) := by
          simpa using (((tendsto_const_nhds (x := (2 : ℝ))).mul hDz1_lim).mul (hz_tendsto.pow 6))
        have hden : Tendsto (fun n => (g.Sz (z n) - g.Dz (z n) + (1 / 2) * (z n) ^ 3) ^ 5)
            atTop (nhds ((g.a : ℝ) ^ 5)) := by
          have := ((hSz_lim.sub hDz_lim).add ((tendsto_const_nhds (x := (1 / 2 : ℝ))).mul (hz_tendsto.pow 3))).pow 5
          simpa using this
        simpa [Pi.div_def] using hnum.div hden (by positivity)
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hz0 : z n ≠ 0 := (hz_pos n hn).ne'
      have hinv1 : (n : ℝ) = 1 / z n + 1 / 2 := by dsimp [z]; rw [one_div_one_div]; ring
      have hinv2 : (n : ℝ) - 1 = 1 / z n - 1 / 2 := by dsimp [z]; rw [one_div_one_div]; ring
      have hqmp : g.evalR n - g.evalR ((n : ℝ) - 1) = 2 * g.Dz1 (z n) / (z n) ^ 2 := by
        rw [hinv2, hinv1]; dsimp [evalR, Dz1]; field_simp [hz0]; ring
      have hp1 : g.evalR ((n : ℝ) - 1) + 1 =
          (g.Sz (z n) - g.Dz (z n) + 1 / 2 * (z n) ^ 3) / (z n) ^ 3 := by
        rw [hinv2]; dsimp [evalR, Sz, Dz]; field_simp [hz0]; ring
      rw [hqmp, hp1]
      field_simp [hz0]
    refine squeeze_zero_norm' ?_ hbound_lim
    filter_upwards [eventually_ge_atTop 2, g.eventually_monotone_pos] with n hn ⟨_, hp1, hpq⟩
    have hz0 : 0 < z n := hz_pos n hn
    have hp_nat : 1 ≤ (g.evalZ ((n : ℤ) - 1)).toNat := by omega
    have hpq_nat : (g.evalZ ((n : ℤ) - 1)).toNat ≤ (g.evalZ n).toNat := by omega
    have hp_cast : (((g.evalZ ((n : ℤ) - 1)).toNat : ℕ) : ℝ) = g.evalR ((n : ℝ) - 1) := by
      have hnn : 0 ≤ g.evalZ ((n : ℤ) - 1) := by omega
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
      unfold evalZ evalR; push_cast; ring
    have hq_cast : (((g.evalZ n).toNat : ℕ) : ℝ) = g.evalR n := by
      have hnn : 0 ≤ g.evalZ n := by omega
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
      unfold evalZ evalR; push_cast; ring
    have hratio : (1 + t n) / (1 - t n) = (g.evalR n + 1 / 2) / (g.evalR ((n : ℝ) - 1) + 1 / 2) := by
      have hSmD := hSmD_eq n hn
      have hSpD := hSpD_eq n hn
      have hSpos : 0 < g.Sz (z n) := by
        have hp_pos : (0 : ℝ) < g.evalR ((n : ℝ) - 1) + 1 / 2 := by
          have : (1 : ℝ) ≤ g.evalR ((n : ℝ) - 1) := by rw [← hp_cast]; exact_mod_cast hp_nat
          linarith
        have hq_pos : (0 : ℝ) < g.evalR n + 1 / 2 := by
          have : g.evalR ((n : ℝ) - 1) ≤ g.evalR n := by
            rw [← hp_cast, ← hq_cast]; exact_mod_cast hpq_nat
          linarith
        have : 2 * g.Sz (z n) = (z n) ^ 3 * (g.evalR n + 1 / 2 + (g.evalR ((n : ℝ) - 1) + 1 / 2)) := by
          linarith [hSmD, hSpD]
        have : 0 < 2 * g.Sz (z n) := by rw [this]; positivity
        linarith
      dsimp [t]
      rw [show 1 + g.Dz (z n) / g.Sz (z n) = (g.Sz (z n) + g.Dz (z n)) / g.Sz (z n) by field_simp [hSpos.ne'],
          show 1 - g.Dz (z n) / g.Sz (z n) = (g.Sz (z n) - g.Dz (z n)) / g.Sz (z n) by field_simp [hSpos.ne'],
          div_div_div_cancel_right₀ hSpos.ne', hSpD, hSmD,
          mul_div_mul_left _ _ (pow_ne_zero 3 hz0.ne')]
    have hbd := harmonic_em_diff_bound hp_nat hpq_nat
    rw [hp_cast, hq_cast] at hbd
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hz0 7), hratio]
    exact div_le_div_of_nonneg_right hbd (pow_nonneg hz0.le 7)
  have hadd := hE1_lim.add hE_rem
  simp only [add_zero] at hadd
  refine hadd.congr' (Eventually.of_forall fun n => by ring)

theorem M_g_asymptotic_limit (g : IntCubic) :
    Tendsto (fun n : ℕ =>
      let u : ℝ := (n : ℝ) - 1 / 2
      u ^ 3 * (g.M n - g.P n - g.c1 / u - g.c2 / u ^ 2)) atTop (nhds g.c3) := by
  have ha : (0 : ℝ) < (g.a : ℝ) := g.ha_pos
  let z : ℕ → ℝ := fun n => 1 / ((n : ℝ) - 1 / 2)
  have hz_tendsto : Tendsto z atTop (nhds 0) := by
    have hu : Tendsto (fun n : ℕ => (n : ℝ) - 1 / 2) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact tendsto_const_nhds.div_atTop hu
  have hz_pos : ∀ n : ℕ, 2 ≤ n → 0 < z n := fun n hn => by
    dsimp [z]
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact div_pos one_pos (by linarith)
  have hSz_lim : Tendsto (fun n => g.Sz (z n)) atTop (nhds (g.a : ℝ)) := by
    have hcont : Continuous g.Sz := by unfold Sz; fun_prop
    have h0 : g.Sz 0 = (g.a : ℝ) := by unfold Sz; ring
    simpa [Function.comp_def, h0] using (hcont.tendsto 0).comp hz_tendsto
  have hDz1_lim : Tendsto (fun n => g.Dz1 (z n)) atTop (nhds (3 / 2 * (g.a : ℝ))) := by
    have hcont : Continuous g.Dz1 := by unfold Dz1; fun_prop
    have h0 : g.Dz1 0 = 3 / 2 * (g.a : ℝ) := by unfold Dz1; ring
    simpa [Function.comp_def, h0] using (hcont.tendsto 0).comp hz_tendsto
  let t : ℕ → ℝ := fun n => g.Dz (z n) / g.Sz (z n)
  have ht_over_z : Tendsto (fun n => t n / z n) atTop (nhds (3 / 2 : ℝ)) := by
    have hq : Tendsto (fun n => g.Dz1 (z n) / g.Sz (z n)) atTop (nhds (3 / 2 : ℝ)) := by
      have := hDz1_lim.div hSz_lim ha.ne'
      convert this using 1; field_simp [ha.ne']
    refine hq.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hz0 : z n ≠ 0 := (hz_pos n hn).ne'
    dsimp [t, Dz, Dz1]; field_simp [hz0]
  have ht_lim : Tendsto t atTop (nhds 0) := by
    have := ht_over_z.mul hz_tendsto
    simp only [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hz0 : z n ≠ 0 := (hz_pos n hn).ne'
    field_simp [hz0]
  let c3_log : ℝ := g.c3 - 1 / (12 * (g.a : ℝ))
  -- Part A: Pure algebraic Taylor expansion of Q_log(t) = 1 + t^2/3 + t^4/5 + t^6/7
  have hA_comb : Tendsto (fun n => (g.Rlogz (z n) * Q_of_t (t n) - g.Sz (z n)) / (z n) ^ 6) atTop (nhds 0) :=
    g.M_g_partA
  -- Part B: Log tail bound: (log((1+t)/(1-t)) - 2*t*Q_of_t(t)) / z^7 → 0
  have hlog_tail : Tendsto (fun n =>
      (Real.log ((1 + t n) / (1 - t n)) - 2 * t n * Q_of_t (t n)) / (z n) ^ 7) atTop (nhds 0) := by
    have hupper : Tendsto (fun n =>
        (2 * (t n) ^ 9 / (9 * (1 - (t n) ^ 2))) / (z n) ^ 7) atTop (nhds 0) := by
      have h1 : Tendsto (fun n => 2 * (t n / z n) ^ 7 * (t n) ^ 2 / (9 * (1 - (t n) ^ 2))) atTop (nhds 0) := by
        have hnum := ((tendsto_const_nhds (x := (2 : ℝ))).mul (ht_over_z.pow 7)).mul (ht_lim.pow 2)
        have hden : Tendsto (fun n => 9 * (1 - (t n) ^ 2)) atTop (nhds 9) := by
          simpa using ((tendsto_const_nhds (x := (9 : ℝ))).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub (ht_lim.pow 2)))
        have := hnum.div hden (by norm_num)
        simpa [Pi.div_def] using this
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hz0 : z n ≠ 0 := (hz_pos n hn).ne'
      field_simp [hz0]
    refine squeeze_zero' ?_ ?_ hupper
    · filter_upwards [eventually_ge_atTop 2, ht_over_z.eventually (eventually_gt_nhds (by norm_num : (1 : ℝ) < 3 / 2)),
          ht_lim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn ht1 ht2
      have hz0 : 0 < z n := hz_pos n hn
      have ht_pos : 0 < t n := by
        have := (lt_div_iff₀ hz0).mp ht1; linarith
      have hlo := log_ratio_gt_7 ht_pos (by linarith)
      have hQeq : 2 * t n * Q_of_t (t n) =
          2 * t n + 2 * (t n) ^ 3 / 3 + 2 * (t n) ^ 5 / 5 + 2 * (t n) ^ 7 / 7 := by
        dsimp [Q_of_t]; ring
      rw [hQeq]
      exact div_nonneg (by linarith) (pow_nonneg hz0.le 7)
    · filter_upwards [eventually_ge_atTop 2, ht_over_z.eventually (eventually_gt_nhds (by norm_num : (1 : ℝ) < 3 / 2)),
          ht_lim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn ht1 ht2
      have hz0 : 0 < z n := hz_pos n hn
      have ht_pos : 0 < t n := by
        have := (lt_div_iff₀ hz0).mp ht1; linarith
      have hhi := log_ratio_lt_7 ht_pos (by linarith)
      have hQeq : 2 * t n * Q_of_t (t n) =
          2 * t n + 2 * (t n) ^ 3 / 3 + 2 * (t n) ^ 5 / 5 + 2 * (t n) ^ 7 / 7 := by
        dsimp [Q_of_t]; ring
      rw [hQeq]
      exact div_le_div_of_nonneg_right (by linarith) (pow_nonneg hz0.le 7)
  -- Part C: Euler-Maclaurin difference E(n) / z(n)^7 → 1 / (4 a^2)
  have hE_lim : Tendsto (fun n =>
      (Real.log ((1 + t n) / (1 - t n)) -
        (H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat)) / (z n) ^ 7)
      atTop (nhds (1 / (4 * (g.a : ℝ) ^ 2))) := g.M_g_partC
  -- Final assembly
  have hH_over_z : Tendsto (fun n : ℕ =>
      (H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat) / z n) atTop (nhds 3) := by
    have hL_over_z : Tendsto (fun n => Real.log ((1 + t n) / (1 - t n)) / z n) atTop (nhds 3) := by
      have h1 : Tendsto (fun n =>
          2 * (t n / z n) * Q_of_t (t n) +
          ((Real.log ((1 + t n) / (1 - t n)) - 2 * t n * Q_of_t (t n)) / (z n) ^ 7) * (z n) ^ 6)
          atTop (nhds 3) := by
        have hQ1 : Tendsto (fun n => Q_of_t (t n)) atTop (nhds 1) := by
          have hcont : Continuous Q_of_t := by unfold Q_of_t; fun_prop
          have h0 : Q_of_t 0 = 1 := by unfold Q_of_t; ring
          simpa [Function.comp_def, h0] using (hcont.tendsto 0).comp ht_lim
        have hmain : Tendsto (fun n => 2 * (t n / z n) * Q_of_t (t n)) atTop (nhds 3) := by
          have := ((tendsto_const_nhds (x := (2 : ℝ))).mul ht_over_z).mul hQ1
          convert this using 1; norm_num
        have htail : Tendsto (fun n =>
            ((Real.log ((1 + t n) / (1 - t n)) - 2 * t n * Q_of_t (t n)) / (z n) ^ 7) * (z n) ^ 6)
            atTop (nhds 0) := by
          simpa using hlog_tail.mul (hz_tendsto.pow 6)
        simpa using hmain.add htail
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hz0 : z n ≠ 0 := (hz_pos n hn).ne'
      field_simp [hz0]; ring
    have hsub : Tendsto (fun n =>
        Real.log ((1 + t n) / (1 - t n)) / z n -
        ((Real.log ((1 + t n) / (1 - t n)) -
          (H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat)) / (z n) ^ 7) * (z n) ^ 6)
        atTop (nhds 3) := by
      have hE0 : Tendsto (fun n =>
          ((Real.log ((1 + t n) / (1 - t n)) -
            (H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat)) / (z n) ^ 7) * (z n) ^ 6)
          atTop (nhds 0) := by
        simpa using hE_lim.mul (hz_tendsto.pow 6)
      simpa using hL_over_z.sub hE0
    refine hsub.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hz0 : z n ≠ 0 := (hz_pos n hn).ne'
    field_simp [hz0]; ring
  have hR_lim : Tendsto (fun n => g.Rlogz (z n)) atTop (nhds (g.a : ℝ)) := by
    have hcont : Continuous g.Rlogz := by unfold Rlogz; fun_prop
    have h0 : g.Rlogz 0 = (g.a : ℝ) := by unfold Rlogz; ring
    simpa [Function.comp_def, h0] using (hcont.tendsto 0).comp hz_tendsto
  have hnum_lim : Tendsto (fun n =>
      -2 * (t n / z n) * ((g.Rlogz (z n) * Q_of_t (t n) - g.Sz (z n)) / (z n) ^ 6) -
      g.Rlogz (z n) * ((Real.log ((1 + t n) / (1 - t n)) - 2 * t n * Q_of_t (t n)) / (z n) ^ 7) +
      g.Rlogz (z n) * ((Real.log ((1 + t n) / (1 - t n)) -
        (H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat)) / (z n) ^ 7))
      atTop (nhds (1 / (4 * (g.a : ℝ)))) := by
    have h1 : Tendsto (fun n =>
        -2 * (t n / z n) * ((g.Rlogz (z n) * Q_of_t (t n) - g.Sz (z n)) / (z n) ^ 6)) atTop (nhds 0) := by
      simpa using ((tendsto_const_nhds (x := (-2 : ℝ))).mul ht_over_z).mul hA_comb
    have h2 : Tendsto (fun n =>
        g.Rlogz (z n) * ((Real.log ((1 + t n) / (1 - t n)) - 2 * t n * Q_of_t (t n)) / (z n) ^ 7))
        atTop (nhds 0) := by
      simpa using hR_lim.mul hlog_tail
    have h3 : Tendsto (fun n =>
        g.Rlogz (z n) * ((Real.log ((1 + t n) / (1 - t n)) -
          (H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat)) / (z n) ^ 7))
        atTop (nhds (1 / (4 * (g.a : ℝ)))) := by
      have := hR_lim.mul hE_lim
      convert this using 2; field_simp [ha.ne']
    simpa using (h1.sub h2).add h3
  have hfinal : Tendsto (fun n =>
      c3_log + (-2 * (t n / z n) * ((g.Rlogz (z n) * Q_of_t (t n) - g.Sz (z n)) / (z n) ^ 6) -
        g.Rlogz (z n) * ((Real.log ((1 + t n) / (1 - t n)) - 2 * t n * Q_of_t (t n)) / (z n) ^ 7) +
        g.Rlogz (z n) * ((Real.log ((1 + t n) / (1 - t n)) -
          (H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat)) / (z n) ^ 7)) /
        ((H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat) / z n))
      atTop (nhds g.c3) := by
    have hq := hnum_lim.div hH_over_z (by norm_num)
    have hadd := (tendsto_const_nhds (x := c3_log)).add hq
    convert hadd using 2
    dsimp [c3_log]; field_simp [ha.ne']; ring
  refine hfinal.congr' ?_
  filter_upwards [eventually_ge_atTop 2, hH_over_z.eventually (eventually_gt_nhds (by norm_num : (1 : ℝ) < 3)),
      hSz_lim.eventually (eventually_gt_nhds (show (g.a : ℝ) / 2 < (g.a : ℝ) by linarith))] with n hn hHz hSpos
  have hu0 : (n : ℝ) - 1 / 2 ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hz0 : z n ≠ 0 := by dsimp [z]; exact one_div_ne_zero hu0
  have hH0 : H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat ≠ 0 := by
    have hz_pos' : 0 < z n := hz_pos n hn
    have := (lt_div_iff₀ hz_pos').mp hHz
    linarith
  have hS0 : g.Sz (z n) ≠ 0 := by linarith
  have hu_eq : (n : ℝ) - 1 / 2 = 1 / z n := by dsimp [z]; rw [one_div_one_div]
  have hinv1 : (n : ℝ) = 1 / z n + 1 / 2 := by linarith [hu_eq]
  have hinv2 : (n : ℝ) - 1 = 1 / z n - 1 / 2 := by linarith [hu_eq]
  have h2D : g.evalR n - g.evalR ((n : ℝ) - 1) = 2 * g.Dz (z n) / (z n) ^ 3 := by
    rw [hinv2, hinv1]; dsimp [evalR, Dz]; field_simp [hz0]; ring
  have hRlog_eq : g.Rlogz (z n) / (z n) ^ 3 =
      g.P n + g.c1 * z n + g.c2 * (z n) ^ 2 + c3_log * (z n) ^ 3 := by
    dsimp [Rlogz, P, evalR, c3_log]; push_cast; rw [hu_eq]; field_simp [hz0]; ring
  have hM_eq : g.M n = (2 * g.Dz (z n) / (z n) ^ 3) /
      (H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat) := by
    unfold M; rw [h2D]
  rw [hM_eq]
  have hP_eq : g.P n + g.c1 / ((n : ℝ) - 1 / 2) + g.c2 / ((n : ℝ) - 1 / 2) ^ 2 +
      c3_log / ((n : ℝ) - 1 / 2) ^ 3 = g.Rlogz (z n) / (z n) ^ 3 := by
    rw [hRlog_eq, hu_eq]; field_simp [hz0]
  dsimp only [t]
  have hkey : ((n : ℝ) - 1 / 2) ^ 3 *
      ((2 * g.Dz (z n) / (z n) ^ 3) / (H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat) -
        g.P n - g.c1 / ((n : ℝ) - 1 / 2) - g.c2 / ((n : ℝ) - 1 / 2) ^ 2) - c3_log =
      (2 * g.Dz (z n) - g.Rlogz (z n) * (H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat)) /
        ((z n) ^ 6 * (H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat)) := by
    have : ((n : ℝ) - 1 / 2) ^ 3 *
        ((2 * g.Dz (z n) / (z n) ^ 3) / (H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat) -
          (g.P n + g.c1 / ((n : ℝ) - 1 / 2) + g.c2 / ((n : ℝ) - 1 / 2) ^ 2 +
            c3_log / ((n : ℝ) - 1 / 2) ^ 3)) =
        ((n : ℝ) - 1 / 2) ^ 3 *
          ((2 * g.Dz (z n) / (z n) ^ 3) / (H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat) -
            g.P n - g.c1 / ((n : ℝ) - 1 / 2) - g.c2 / ((n : ℝ) - 1 / 2) ^ 2) - c3_log := by
      rw [hu_eq]; field_simp [hz0]; ring
    rw [← this, hP_eq, hu_eq]
    field_simp [hz0, hH0]
  linarith [hkey, show
    (-2 * (g.Dz (z n) / g.Sz (z n) / z n) * ((g.Rlogz (z n) * Q_of_t (g.Dz (z n) / g.Sz (z n)) - g.Sz (z n)) / (z n) ^ 6) -
      g.Rlogz (z n) * ((Real.log ((1 + g.Dz (z n) / g.Sz (z n)) / (1 - g.Dz (z n) / g.Sz (z n))) -
        2 * (g.Dz (z n) / g.Sz (z n)) * Q_of_t (g.Dz (z n) / g.Sz (z n))) / (z n) ^ 7) +
      g.Rlogz (z n) * ((Real.log ((1 + g.Dz (z n) / g.Sz (z n)) / (1 - g.Dz (z n) / g.Sz (z n))) -
        (H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat)) / (z n) ^ 7)) /
      ((H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat) / z n) =
    (2 * g.Dz (z n) - g.Rlogz (z n) * (H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat)) /
      ((z n) ^ 6 * (H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat)) by
    generalize g.Dz (z n) = D_v
    generalize g.Sz (z n) = S_v at hS0 ⊢
    generalize g.Rlogz (z n) = R_v
    generalize H (g.evalZ n).toNat - H (g.evalZ ((n : ℤ) - 1)).toNat = H_v at hH0 ⊢
    generalize Real.log ((1 + D_v / S_v) / (1 - D_v / S_v)) = L_v
    generalize Q_of_t (D_v / S_v) = Q_v
    generalize z n = w at hz0 ⊢
    field_simp [hz0, hS0, hH0]
    ring]

/-- Eventual sign `σ(g) ∈ {-1, 1}` of `M_g(n) - P_g(n)`: sign of the first nonvanishing
coefficient among `(c₁, c₂, c₃)` (with `c₃ > 0` whenever `c₁ = c₂ = 0` by Lemma 7). -/
noncomputable def sigma (g : IntCubic) : ℝ :=
  if g.c1 ≠ 0 then (if 0 < g.c1 then 1 else -1)
  else if g.c2 ≠ 0 then (if 0 < g.c2 then 1 else -1)
  else 1

lemma eventually_sign_and_small (g : IntCubic) :
    ∀ᶠ n : ℕ in atTop, 0 < g.sigma * (g.M n - g.P n) ∧ g.sigma * (g.M n - g.P n) < 1 / 8 := by
  have hlim := g.M_g_asymptotic_limit
  have hu : Tendsto (fun n : ℕ => (n : ℝ) - 1 / 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) - 1 / 2)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hu
  have hdiff0 : Tendsto (fun n : ℕ => g.M n - g.P n) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ =>
        (((n : ℝ) - 1 / 2) ^ 3 * (g.M n - g.P n - g.c1 / ((n : ℝ) - 1 / 2) -
          g.c2 / ((n : ℝ) - 1 / 2) ^ 2)) * (1 / ((n : ℝ) - 1 / 2)) ^ 3 +
        g.c1 * (1 / ((n : ℝ) - 1 / 2)) + g.c2 * (1 / ((n : ℝ) - 1 / 2)) ^ 2) atTop (nhds 0) := by
      simpa using ((hlim.mul (hinv.pow 3)).add (tendsto_const_nhds.mul hinv)).add
        (tendsto_const_nhds.mul (hinv.pow 2))
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    set u : ℝ := (n : ℝ) - 1 / 2
    have hu0 : u ≠ 0 := by
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      dsimp [u]; linarith
    field_simp [hu0]; ring
  have hsmall : ∀ᶠ n : ℕ in atTop, g.sigma * (g.M n - g.P n) < 1 / 8 := by
    have : Tendsto (fun n => g.sigma * (g.M n - g.P n)) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hdiff0
    exact this.eventually (eventually_lt_nhds (by norm_num))
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < g.sigma * (g.M n - g.P n) := by
    by_cases h1 : g.c1 ≠ 0
    · have h1lim : Tendsto (fun n : ℕ => ((n : ℝ) - 1 / 2) * (g.M n - g.P n)) atTop (nhds g.c1) := by
        have hstep : Tendsto (fun n : ℕ =>
            (((n : ℝ) - 1 / 2) ^ 3 * (g.M n - g.P n - g.c1 / ((n : ℝ) - 1 / 2) -
              g.c2 / ((n : ℝ) - 1 / 2) ^ 2)) * (1 / ((n : ℝ) - 1 / 2)) ^ 2 +
            g.c1 + g.c2 * (1 / ((n : ℝ) - 1 / 2))) atTop (nhds g.c1) := by
          simpa using ((hlim.mul (hinv.pow 2)).add tendsto_const_nhds).add (tendsto_const_nhds.mul hinv)
        refine hstep.congr' ?_
        filter_upwards [eventually_ge_atTop 2] with n hn
        set u : ℝ := (n : ℝ) - 1 / 2
        have hu0 : u ≠ 0 := by
          have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          dsimp [u]; linarith
        field_simp [hu0]; ring
      have hsig : g.sigma = if 0 < g.c1 then 1 else -1 := by unfold sigma; simp [h1]
      have hsc_pos : 0 < g.sigma * g.c1 := by
        rw [hsig]; split_ifs with hlt
        · linarith
        · have : g.c1 < 0 := lt_of_le_of_ne (le_of_not_gt hlt) h1
          linarith
      filter_upwards [eventually_ge_atTop 2,
          (tendsto_const_nhds.mul h1lim).eventually (eventually_gt_nhds hsc_pos)] with n hn hgt
      have hu_pos : 0 < (n : ℝ) - 1 / 2 := by
        have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      have : 0 < ((n : ℝ) - 1 / 2) * (g.sigma * (g.M n - g.P n)) := by linarith
      exact pos_of_mul_pos_right this hu_pos.le
    · push Not at h1
      by_cases h2 : g.c2 ≠ 0
      · have h2lim : Tendsto (fun n : ℕ => ((n : ℝ) - 1 / 2) ^ 2 * (g.M n - g.P n)) atTop (nhds g.c2) := by
          have hstep : Tendsto (fun n : ℕ =>
              (((n : ℝ) - 1 / 2) ^ 3 * (g.M n - g.P n - g.c1 / ((n : ℝ) - 1 / 2) -
                g.c2 / ((n : ℝ) - 1 / 2) ^ 2)) * (1 / ((n : ℝ) - 1 / 2)) + g.c2)
              atTop (nhds g.c2) := by
            simpa using (hlim.mul hinv).add tendsto_const_nhds
          refine hstep.congr' ?_
          filter_upwards [eventually_ge_atTop 2] with n hn
          set u : ℝ := (n : ℝ) - 1 / 2
          have hu0 : u ≠ 0 := by
            have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            dsimp [u]; linarith
          rw [h1]; field_simp [hu0]; ring
        have hsig : g.sigma = if 0 < g.c2 then 1 else -1 := by unfold sigma; simp [h1, h2]
        have hsc_pos : 0 < g.sigma * g.c2 := by
          rw [hsig]; split_ifs with hlt
          · linarith
          · have : g.c2 < 0 := lt_of_le_of_ne (le_of_not_gt hlt) h2
            linarith
        filter_upwards [eventually_ge_atTop 2,
            (tendsto_const_nhds.mul h2lim).eventually (eventually_gt_nhds hsc_pos)] with n hn hgt
        have hu_pos : 0 < ((n : ℝ) - 1 / 2) ^ 2 := by
          have h1 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          have h2 : 0 < (n : ℝ) - 1 / 2 := by linarith
          positivity
        have : 0 < ((n : ℝ) - 1 / 2) ^ 2 * (g.sigma * (g.M n - g.P n)) := by linarith
        exact pos_of_mul_pos_right this hu_pos.le
      · push Not at h2
        have hc3_pos : 0 < g.c3 := (g.nonvanishing_c1_c2_c3 h1 h2).2
        have hsig : g.sigma = 1 := by unfold sigma; simp [h1, h2]
        filter_upwards [eventually_ge_atTop 2, hlim.eventually (eventually_gt_nhds hc3_pos)] with n hn hgt
        have hu_pos : 0 < ((n : ℝ) - 1 / 2) ^ 3 := by
          have h1 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          have h2 : 0 < (n : ℝ) - 1 / 2 := by linarith
          positivity
        rw [h1, h2] at hgt
        simp only [zero_div, sub_zero] at hgt
        rw [hsig, one_mul]
        exact pos_of_mul_pos_right hgt hu_pos.le
  exact hpos.and hsmall

private lemma eight_mul_P_eq_int (g : IntCubic) (n : ℤ) :
    8 * g.P n = ((8 * g.a * n ^ 3 + (8 * g.b - 12 * g.a) * n ^ 2 +
      (6 * g.a - 8 * g.b + 8 * g.c) * n + (-g.a + 2 * g.b - 4 * g.c + 8 * g.d + 4) : ℤ) : ℝ) := by
  unfold P evalR; push_cast; ring

private lemma floor_eighth_pos {x δ : ℝ} {K : ℤ} (hx : 8 * x = (K : ℝ))
    (h0 : 0 < δ) (h8 : δ < 1 / 8) :
    ⌊x + δ⌋ = ⌊x⌋ := by
  have hk : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have h1 : (⌊x⌋ : ℝ) ≤ x + δ := by linarith
  have h2 : x + δ < (⌊x⌋ : ℝ) + 1 := by
    have hK_lt : K < 8 * (⌊x⌋ + 1) := by
      have : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
      have : (K : ℝ) < ((8 * (⌊x⌋ + 1) : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hK_le : K ≤ 8 * ⌊x⌋ + 7 := by omega
    have hK_leR : (K : ℝ) ≤ 8 * (⌊x⌋ : ℝ) + 7 := by exact_mod_cast hK_le
    linarith
  exact Int.floor_eq_iff.mpr ⟨h1, h2⟩

private lemma floor_eighth_neg {x δ : ℝ} {K : ℤ} (hx : 8 * x = (K : ℝ))
    (h0 : 0 < δ) (h8 : δ < 1 / 8) :
    ⌊x - δ⌋ = ⌈x⌉ - 1 := by
  have h2 : x - δ < ((⌈x⌉ - 1 : ℤ) : ℝ) + 1 := by
    push_cast; linarith [Int.le_ceil x]
  have h1 : ((⌈x⌉ - 1 : ℤ) : ℝ) ≤ x - δ := by
    have hK_gt : 8 * (⌈x⌉ - 1) < K := by
      have : (⌈x⌉ : ℝ) - 1 < x := by linarith [Int.ceil_lt_add_one x]
      have : ((8 * (⌈x⌉ - 1) : ℤ) : ℝ) < (K : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hK_ge : 8 * (⌈x⌉ - 1) + 1 ≤ K := by omega
    have hK_geR : 8 * ((⌈x⌉ : ℝ) - 1) + 1 ≤ (K : ℝ) := by exact_mod_cast hK_ge
    push_cast; linarith
  exact Int.floor_eq_iff.mpr ⟨h1, h2⟩

/-- **Theorem 2a (Eventually Exact Floor/Ceiling Formula)**:
There exists `N₀` such that for all `n ≥ N₀`,
`m_g(n) = ⌊P_g(n)⌋` if `σ = +1`, and `m_g(n) = ⌈P_g(n)⌉ - 1` if `σ = -1`. -/
theorem kimberling_general_cubic_floor (g : IntCubic) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      g.m n = if g.sigma = 1 then ⌊g.P n⌋ else ⌈g.P n⌉ - 1 := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp g.eventually_sign_and_small
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨hpos, hlt⟩ := hN₀ n hn
  have hsig_cases : g.sigma = 1 ∨ g.sigma = -1 := by
    unfold sigma; split_ifs <;> simp
  unfold m
  rcases hsig_cases with h1 | hm1
  · rw [ite_eq_left_iff.mpr (fun h => absurd h1 h)]
    rw [h1, one_mul] at hpos hlt
    have hrew : g.M n = g.P n + (g.M n - g.P n) := by ring
    rw [hrew]
    exact floor_eighth_pos (g.eight_mul_P_eq_int n) hpos hlt
  · rw [ite_eq_right_iff.mpr (fun h => by linarith)]
    rw [hm1] at hpos hlt
    have hrew : g.M n = g.P n - (g.P n - g.M n) := by ring
    rw [hrew]
    exact floor_eighth_neg (g.eight_mul_P_eq_int n) (by linarith) (by linarith)

/-- Periodicity of `P_g(n + k) - P_g(n)` when `4 ∣ k * a`. -/
private lemma P_shift_int (g : IntCubic) (n : ℤ) (k : ℕ) (hdiv : (4 : ℤ) ∣ (k : ℤ) * g.a) :
    ∃ K : ℤ, g.P (n + k) = g.P n + (K : ℝ) := by
  obtain ⟨q, hq⟩ := hdiv
  -- P_g(n + k) - P_g(n) = a*(3*k*n^2 + (3*k^2 - 3*k)*n + k^3 - 3/2*k^2 + 3/4*k) + b*(2*k*n + k^2 - k) + c*k
  -- Wait: check the half-integer term: -3/2 * a * k^2 + 3/4 * a * k = (3*k*a)*(1 - 2*k)/4 = 3*q*(1 - 2*k) ∈ ℤ!
  refine ⟨g.a * (3 * (k : ℤ) * n ^ 2 + (3 * (k : ℤ) ^ 2 - 3 * (k : ℤ)) * n + (k : ℤ) ^ 3) +
      3 * q * (1 - 2 * (k : ℤ)) + g.b * (2 * (k : ℤ) * n + (k : ℤ) ^ 2 - (k : ℤ)) + g.c * (k : ℤ), ?_⟩
  have hqR : (k : ℝ) * (g.a : ℝ) = 4 * (q : ℝ) := by exact_mod_cast hq
  unfold P evalR
  push_cast
  linear_combination (3 / 4 - 3 / 2 * (k : ℝ)) * hqR

private lemma floor_ceil_shift (g : IntCubic) (n : ℤ) (k : ℕ) (hdiv : (4 : ℤ) ∣ (k : ℤ) * g.a) :
    ((if g.sigma = 1 then ⌊g.P (n + k)⌋ else ⌈g.P (n + k)⌉ - 1 : ℤ) : ℝ) - g.P (n + k) =
    ((if g.sigma = 1 then ⌊g.P n⌋ else ⌈g.P n⌉ - 1 : ℤ) : ℝ) - g.P n := by
  obtain ⟨K, hK⟩ := g.P_shift_int n k hdiv
  rw [hK]
  split_ifs
  · rw [Int.floor_add_intCast]; push_cast; ring
  · rw [Int.ceil_add_intCast]; push_cast; ring

/-- **Theorem 2b (Kimberling's General Cubic Recurrence Conjecture)**:
For every integer cubic `g(n) = a*n^3 + b*n^2 + c*n + d` (`a > 0`), there exists `N₀` such that
for all `n ≥ N₀ + 7`,
`m_g(n) = 3 m_g(n-1) - 3 m_g(n-2) + m_g(n-3) + m_g(n-4) - 3 m_g(n-5) + 3 m_g(n-6) - m_g(n-7)`. -/
theorem kimberling_general_cubic_recurrence (g : IntCubic) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ + 7 ≤ n →
      g.m n = 3 * g.m (n - 1) - 3 * g.m (n - 2) + g.m (n - 3) + g.m (n - 4) -
        3 * g.m (n - 5) + 3 * g.m (n - 6) - g.m (n - 7) := by
  obtain ⟨N₀, hN₀⟩ := g.kimberling_general_cubic_floor
  refine ⟨N₀, fun n hn => ?_⟩
  let f : ℤ → ℤ := fun x => if g.sigma = 1 then ⌊g.P x⌋ else ⌈g.P x⌉ - 1
  have hm_eq : ∀ j ≤ 7, g.m (n - j) = f ((n : ℤ) - j) := by
    intro j hj
    have hge : N₀ ≤ n - j := by omega
    have hcast : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by exact_mod_cast Int.ofNat_sub (by omega)
    rw [hN₀ (n - j) hge, hcast]
  have h0 := hm_eq 0 (by omega); simp only [Nat.sub_zero, Nat.cast_zero, sub_zero] at h0
  have h1 := hm_eq 1 (by omega)
  have h2 := hm_eq 2 (by omega)
  have h3 := hm_eq 3 (by omega)
  have h4 := hm_eq 4 (by omega)
  have h5 := hm_eq 5 (by omega)
  have h6 := hm_eq 6 (by omega)
  have h7 := hm_eq 7 (by omega)
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  -- Check equality in ℝ via Δ(x) = f(x) - P_g(x) (period 4) and cubic P_g(x) (order 4)
  have hdiv4 : (4 : ℤ) ∣ ((4 : ℕ) : ℤ) * g.a := ⟨g.a, by push_cast; ring⟩
  have d04 := g.floor_ceil_shift ((n : ℤ) - 4) 4 hdiv4
  have d15 := g.floor_ceil_shift ((n : ℤ) - 5) 4 hdiv4
  have d26 := g.floor_ceil_shift ((n : ℤ) - 6) 4 hdiv4
  have d37 := g.floor_ceil_shift ((n : ℤ) - 7) 4 hdiv4
  have e0 : (n : ℤ) - 4 + (4 : ℕ) = (n : ℤ) := by push_cast; ring
  have e1 : (n : ℤ) - 5 + (4 : ℕ) = (n : ℤ) - 1 := by push_cast; ring
  have e2 : (n : ℤ) - 6 + (4 : ℕ) = (n : ℤ) - 2 := by push_cast; ring
  have e3 : (n : ℤ) - 7 + (4 : ℕ) = (n : ℤ) - 3 := by push_cast; ring
  rw [e0] at d04; rw [e1] at d15; rw [e2] at d26; rw [e3] at d37
  have hP_rec : g.P n = 3 * g.P ((n : ℤ) - 1) - 3 * g.P ((n : ℤ) - 2) + g.P ((n : ℤ) - 3) +
      g.P ((n : ℤ) - 4) - 3 * g.P ((n : ℤ) - 5) + 3 * g.P ((n : ℤ) - 6) - g.P ((n : ℤ) - 7) := by
    unfold P evalR; push_cast; ring
  have hR : ((f n : ℤ) : ℝ) =
      ((3 * f ((n : ℤ) - 1) - 3 * f ((n : ℤ) - 2) + f ((n : ℤ) - 3) + f ((n : ℤ) - 4) -
        3 * f ((n : ℤ) - 5) + 3 * f ((n : ℤ) - 6) - f ((n : ℤ) - 7) : ℤ) : ℝ) := by
    push_cast
    dsimp only [f] at *
    linarith
  exact_mod_cast hR

/-! ### Part 5: Corollary 8 (Exact Smaller Eventual Recurrences for Even `a`) -/

/-- **Corollary 8a (`a ≡ 0 mod 2`)**: When `2 ∣ a`, `m_g(n)` eventually satisfies the
order-5 linear recurrence `(3, -2, -2, 3, -1)`. -/
theorem kimberling_even_order5 (g : IntCubic) (h2a : (2 : ℤ) ∣ g.a) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ + 5 ≤ n →
      g.m n = 3 * g.m (n - 1) - 2 * g.m (n - 2) - 2 * g.m (n - 3) +
        3 * g.m (n - 4) - g.m (n - 5) := by
  obtain ⟨N₀, hN₀⟩ := g.kimberling_general_cubic_floor
  refine ⟨N₀, fun n hn => ?_⟩
  let f : ℤ → ℤ := fun x => if g.sigma = 1 then ⌊g.P x⌋ else ⌈g.P x⌉ - 1
  have hm_eq : ∀ j ≤ 5, g.m (n - j) = f ((n : ℤ) - j) := by
    intro j hj
    have hge : N₀ ≤ n - j := by omega
    have hcast : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by exact_mod_cast Int.ofNat_sub (by omega)
    rw [hN₀ (n - j) hge, hcast]
  have h0 := hm_eq 0 (by omega); simp only [Nat.sub_zero, Nat.cast_zero, sub_zero] at h0
  have h1 := hm_eq 1 (by omega); have h2 := hm_eq 2 (by omega)
  have h3 := hm_eq 3 (by omega); have h4 := hm_eq 4 (by omega); have h5 := hm_eq 5 (by omega)
  rw [h0, h1, h2, h3, h4, h5]
  obtain ⟨k, hk⟩ := h2a
  have hdiv2 : (4 : ℤ) ∣ ((2 : ℕ) : ℤ) * g.a := ⟨k, by rw [hk]; push_cast; ring⟩
  have d02 := g.floor_ceil_shift ((n : ℤ) - 2) 2 hdiv2
  have d13 := g.floor_ceil_shift ((n : ℤ) - 3) 2 hdiv2
  have d24 := g.floor_ceil_shift ((n : ℤ) - 4) 2 hdiv2
  have d35 := g.floor_ceil_shift ((n : ℤ) - 5) 2 hdiv2
  have e0 : (n : ℤ) - 2 + (2 : ℕ) = (n : ℤ) := by push_cast; ring
  have e1 : (n : ℤ) - 3 + (2 : ℕ) = (n : ℤ) - 1 := by push_cast; ring
  have e2 : (n : ℤ) - 4 + (2 : ℕ) = (n : ℤ) - 2 := by push_cast; ring
  have e3 : (n : ℤ) - 5 + (2 : ℕ) = (n : ℤ) - 3 := by push_cast; ring
  rw [e0] at d02; rw [e1] at d13; rw [e2] at d24; rw [e3] at d35
  have hP_rec : g.P n = 3 * g.P ((n : ℤ) - 1) - 2 * g.P ((n : ℤ) - 2) -
      2 * g.P ((n : ℤ) - 3) + 3 * g.P ((n : ℤ) - 4) - g.P ((n : ℤ) - 5) := by
    unfold P evalR; push_cast; ring
  have hR : ((f n : ℤ) : ℝ) =
      ((3 * f ((n : ℤ) - 1) - 2 * f ((n : ℤ) - 2) - 2 * f ((n : ℤ) - 3) +
        3 * f ((n : ℤ) - 4) - f ((n : ℤ) - 5) : ℤ) : ℝ) := by
    push_cast; dsimp only [f] at *; linarith
  exact_mod_cast hR

/-- **Corollary 8b (`a ≡ 0 mod 4`)**: When `4 ∣ a`, `m_g(n)` eventually satisfies the
order-4 linear recurrence `(4, -6, 4, -1)`. -/
theorem kimberling_div4_order4 (g : IntCubic) (h4a : (4 : ℤ) ∣ g.a) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ + 4 ≤ n →
      g.m n = 4 * g.m (n - 1) - 6 * g.m (n - 2) + 4 * g.m (n - 3) - g.m (n - 4) := by
  obtain ⟨N₀, hN₀⟩ := g.kimberling_general_cubic_floor
  refine ⟨N₀, fun n hn => ?_⟩
  let f : ℤ → ℤ := fun x => if g.sigma = 1 then ⌊g.P x⌋ else ⌈g.P x⌉ - 1
  have hm_eq : ∀ j ≤ 4, g.m (n - j) = f ((n : ℤ) - j) := by
    intro j hj
    have hge : N₀ ≤ n - j := by omega
    have hcast : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by exact_mod_cast Int.ofNat_sub (by omega)
    rw [hN₀ (n - j) hge, hcast]
  have h0 := hm_eq 0 (by omega); simp only [Nat.sub_zero, Nat.cast_zero, sub_zero] at h0
  have h1 := hm_eq 1 (by omega); have h2 := hm_eq 2 (by omega)
  have h3 := hm_eq 3 (by omega); have h4 := hm_eq 4 (by omega)
  rw [h0, h1, h2, h3, h4]
  have hdiv1 : (4 : ℤ) ∣ ((1 : ℕ) : ℤ) * g.a := by simpa using h4a
  have d01 := g.floor_ceil_shift ((n : ℤ) - 1) 1 hdiv1
  have d12 := g.floor_ceil_shift ((n : ℤ) - 2) 1 hdiv1
  have d23 := g.floor_ceil_shift ((n : ℤ) - 3) 1 hdiv1
  have d34 := g.floor_ceil_shift ((n : ℤ) - 4) 1 hdiv1
  have e0 : (n : ℤ) - 1 + (1 : ℕ) = (n : ℤ) := by push_cast; ring
  have e1 : (n : ℤ) - 2 + (1 : ℕ) = (n : ℤ) - 1 := by push_cast; ring
  have e2 : (n : ℤ) - 3 + (1 : ℕ) = (n : ℤ) - 2 := by push_cast; ring
  have e3 : (n : ℤ) - 4 + (1 : ℕ) = (n : ℤ) - 3 := by push_cast; ring
  rw [e0] at d01; rw [e1] at d12; rw [e2] at d23; rw [e3] at d34
  have hP_rec : g.P n = 4 * g.P ((n : ℤ) - 1) - 6 * g.P ((n : ℤ) - 2) +
      4 * g.P ((n : ℤ) - 3) - g.P ((n : ℤ) - 4) := by
    unfold P evalR; push_cast; ring
  have hR : ((f n : ℤ) : ℝ) =
      ((4 * f ((n : ℤ) - 1) - 6 * f ((n : ℤ) - 2) + 4 * f ((n : ℤ) - 3) - f ((n : ℤ) - 4) : ℤ) : ℝ) := by
    push_cast; dsimp only [f] at *; linarith
  exact_mod_cast hR

/-! ### Lemma 7 (Full Real-Coefficient Version) and Corollary 8 (Exact Minimal Recurrence Order) -/

/-- **Lemma 7 (Real-Coefficient Non-Vanishing of `(c₁, c₂, c₃)`)**:
For *any* real cubic `a x³ + b x² + c x + d` with `a > 0`, if `c₁ = c₂ = 0` then
`c₃ = (9 a² + 350) / (4200 a) > 0`. -/
theorem nonvanishing_c1_c2_c3_real (a b c d : ℝ) (ha : 0 < a)
    (h1 : -(20 * b ^ 2 - 60 * a * c + 3 * a ^ 2) / (240 * a) = 0)
    (h2 : (20 * b ^ 3 - 80 * a * b * c + a ^ 2 * b + 180 * a ^ 2 * d + 90 * a ^ 2) / (240 * a ^ 2) = 0) :
    let c3 := -(140 * b ^ 4 - 700 * a * b ^ 2 * c + 49 * a ^ 2 * b ^ 2 +
        840 * a ^ 2 * b * d + 420 * a ^ 2 * b + 560 * a ^ 2 * c ^ 2 -
        140 * a ^ 3 * c + 2 * a ^ 4 - 140 * a ^ 2) / (1680 * a ^ 3)
    c3 = (9 * a ^ 2 + 350) / (4200 * a) ∧ 0 < c3 := by
  intro c3
  have ha0 : a ≠ 0 := ha.ne'
  have hc1 : 20 * b ^ 2 - 60 * a * c + 3 * a ^ 2 = 0 := by
    have := (div_eq_zero_iff.mp h1).resolve_right (by positivity)
    linarith
  have hc2 : 20 * b ^ 3 - 80 * a * b * c + a ^ 2 * b + 180 * a ^ 2 * d + 90 * a ^ 2 = 0 :=
    (div_eq_zero_iff.mp h2).resolve_right (by positivity)
  have hc_val : c = (20 * b ^ 2 + 3 * a ^ 2) / (60 * a) := by
    field_simp [ha0]; linarith
  have hd_val : d = -(20 * b ^ 3 - 80 * a * b * c + a ^ 2 * b + 90 * a ^ 2) / (180 * a ^ 2) := by
    field_simp [ha0]; linarith
  have hc3_eq : c3 = (9 * a ^ 2 + 350) / (4200 * a) := by
    dsimp only [c3]
    rw [hd_val, hc_val]
    field_simp [ha0]
    ring
  refine ⟨hc3_eq, ?_⟩
  rw [hc3_eq]
  positivity

/-- A sequence `f : ℕ → ℤ` satisfies an eventual linear recurrence of order `k` (over `ℝ`)
if there exist `N` and coefficients `coef : Fin k → ℝ` such that
`f(n) = ∑_{i=0}^{k-1} coef(i) * f(n - (i + 1))` for all `n ≥ N + k`. -/
def SatisfiesEventualRecurrence (f : ℕ → ℤ) (k : ℕ) : Prop :=
  ∃ (N : ℕ) (coef : Fin k → ℝ), ∀ n : ℕ, N + k ≤ n →
    (f n : ℝ) = ∑ i : Fin k, coef i * (f (n - (i.1 + 1)) : ℝ)

/-- Monotonicity of eventual linear recurrence order: any order-`k₁` recurrence also yields
an order-`k₂` recurrence for `k₁ ≤ k₂` by padding trailing coefficients with `0`. -/
lemma recurrence_mono (f : ℕ → ℤ) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    (h : SatisfiesEventualRecurrence f k₁) : SatisfiesEventualRecurrence f k₂ := by
  obtain ⟨N, coef, hN⟩ := h
  refine ⟨N, fun i => if hi : i.1 < k₁ then coef ⟨i.1, hi⟩ else 0, fun n hn => ?_⟩
  have h1 := hN n (by omega)
  rw [h1]
  have hsum : (∑ i : Fin k₂, (if hi : i.1 < k₁ then coef ⟨i.1, hi⟩ else 0) * (f (n - (i.1 + 1)) : ℝ)) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin k₂ => i.1 < k₁),
        (if hi : i.1 < k₁ then coef ⟨i.1, hi⟩ else 0) * (f (n - (i.1 + 1)) : ℝ) := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) (fun i _ hi => ?_)
    have hnot : ¬ i.1 < k₁ := by simpa using hi
    simp [hnot]
  rw [hsum]
  refine Finset.sum_bij (fun i _ => ⟨i.1, lt_of_lt_of_le i.2 hk⟩) ?_ ?_ ?_ ?_
  · intro i _; simp
  · intro i₁ _ i₂ _ heq; ext; simpa using congrArg Fin.val heq
  · intro j hj
    have hj' : j.1 < k₁ := (Finset.mem_filter.mp hj).2
    exact ⟨⟨j.1, hj'⟩, Finset.mem_univ _, by ext; rfl⟩
  · intro i _; simp [i.2]

private lemma floor_div8_diff (x : ℤ) :
    (⌊(x : ℝ) / 8⌋ : ℝ) - (x : ℝ) / 8 = -((x % 8 : ℤ) : ℝ) / 8 := by
  have hdiv : (x : ℝ) = 8 * ((x / 8 : ℤ) : ℝ) + ((x % 8 : ℤ) : ℝ) := by
    have : x = 8 * (x / 8) + x % 8 := by omega
    exact_mod_cast this
  have hrem_lo : (0 : ℝ) ≤ ((x % 8 : ℤ) : ℝ) := by
    exact_mod_cast Int.emod_nonneg x (by norm_num)
  have hrem_hi : ((x % 8 : ℤ) : ℝ) < 8 := by
    exact_mod_cast Int.emod_lt_of_pos x (by norm_num)
  have hfl : ⌊(x : ℝ) / 8⌋ = x / 8 := by
    rw [Int.floor_eq_iff]
    constructor <;> linarith
  rw [hfl]
  linarith

private lemma ceil_sub1_div8_diff (x : ℤ) :
    (((⌈(x : ℝ) / 8⌉ - 1 : ℤ) : ℝ) - (x : ℝ) / 8) =
      if x % 8 = 0 then -1 else -((x % 8 : ℤ) : ℝ) / 8 := by
  have hdiv : (x : ℝ) = 8 * ((x / 8 : ℤ) : ℝ) + ((x % 8 : ℤ) : ℝ) := by
    have : x = 8 * (x / 8) + x % 8 := by omega
    exact_mod_cast this
  have hrem_lo : (0 : ℝ) ≤ ((x % 8 : ℤ) : ℝ) := by
    exact_mod_cast Int.emod_nonneg x (by norm_num)
  have hrem_hi : ((x % 8 : ℤ) : ℝ) < 8 := by
    exact_mod_cast Int.emod_lt_of_pos x (by norm_num)
  split_ifs with h0
  · have h0R : ((x % 8 : ℤ) : ℝ) = 0 := by exact_mod_cast h0
    have hce : ⌈(x : ℝ) / 8⌉ = x / 8 := by
      rw [Int.ceil_eq_iff]; constructor <;> linarith
    rw [hce]; push_cast; linarith
  · have hpos : (1 : ℝ) ≤ ((x % 8 : ℤ) : ℝ) := by
      have : 1 ≤ x % 8 := by omega
      exact_mod_cast this
    have hce : ⌈(x : ℝ) / 8⌉ = x / 8 + 1 := by
      rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
    rw [hce]; push_cast; linarith

/-- The integer `K_g(n) = 8 * P_g(n)`. -/
private def K_int (g : IntCubic) (n : ℤ) : ℤ :=
  8 * g.a * n ^ 3 + (8 * g.b - 12 * g.a) * n ^ 2 + (6 * g.a - 8 * g.b + 8 * g.c) * n +
    (-g.a + 2 * g.b - 4 * g.c + 8 * g.d + 4)

private lemma P_eq_K_div8 (g : IntCubic) (n : ℤ) : g.P n = (g.K_int n : ℝ) / 8 := by
  unfold P evalR K_int; push_cast; ring

private lemma K_int_step (g : IntCubic) (n : ℤ) :
    g.K_int (n + 1) - g.K_int n = 8 * (3 * g.a * n ^ 2 + 2 * g.b * n + g.c) + 2 * g.a := by
  unfold K_int; ring

private lemma delta_nondeg_mod8 (g : IntCubic) (N : ℕ)
    (hfl : ∀ n : ℕ, N ≤ n → g.m n = if g.sigma = 1 then ⌊g.P n⌋ else ⌈g.P n⌉ - 1) :
    let Δ : ℕ → ℝ := fun n => (g.m n : ℝ) - g.P n
    (∀ n : ℕ, N ≤ n → Δ (n + 4) = Δ n) ∧
    (¬ (4 : ℤ) ∣ g.a → Δ N - Δ (N + 1) + Δ (N + 2) - Δ (N + 3) ≠ 0) ∧
    (¬ (2 : ℤ) ∣ g.a → Δ N - Δ (N + 2) ≠ 0) := by
  intro Δ
  have hper : ∀ n : ℕ, N ≤ n → Δ (n + 4) = Δ n := by
    intro n hn
    dsimp only [Δ]
    rw [hfl (n + 4) (by omega), hfl n hn]
    have hdiv4 : (4 : ℤ) ∣ ((4 : ℕ) : ℤ) * g.a := ⟨g.a, by ring⟩
    have hsh := g.floor_ceil_shift (n : ℤ) 4 hdiv4
    push_cast at hsh ⊢
    split_ifs at hsh ⊢ <;> linarith
  -- Compute 8 * Δ (N + j) in terms of (K_int N % 8) and (2 * g.a % 8)
  let r : ℤ := g.K_int N % 8
  let s : ℤ := (2 * g.a) % 8
  have hK_mod : ∀ j : ℕ, g.K_int ((N + j : ℕ) : ℤ) % 8 = (r + (j : ℤ) * s) % 8 := by
    intro j
    induction j with
    | zero => simp [r]
    | succ j ih =>
      have hcast : ((N + (j + 1) : ℕ) : ℤ) = ((N + j : ℕ) : ℤ) + 1 := by push_cast; ring
      rw [hcast]
      have hstep := g.K_int_step ((N + j : ℕ) : ℤ)
      have hEq : g.K_int (((N + j : ℕ) : ℤ) + 1) =
          g.K_int ((N + j : ℕ) : ℤ) + 8 * (3 * g.a * ((N + j : ℕ) : ℤ) ^ 2 +
            2 * g.b * ((N + j : ℕ) : ℤ) + g.c) + 2 * g.a := by linarith
      rw [hEq]
      have h1 : (g.K_int ((N + j : ℕ) : ℤ) + 8 * (3 * g.a * ((N + j : ℕ) : ℤ) ^ 2 +
          2 * g.b * ((N + j : ℕ) : ℤ) + g.c) + 2 * g.a) % 8 =
          (g.K_int ((N + j : ℕ) : ℤ) % 8 + (2 * g.a) % 8) % 8 := by omega
      rw [h1, ih]
      have hcast2 : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
      rw [hcast2, show r + ((j : ℤ) + 1) * s = (r + (j : ℤ) * s) + s by ring]
      dsimp only [s]
      rw [Int.emod_add_emod]
  have hΔ_val : ∀ j : ℕ,
      8 * Δ (N + j) = if g.sigma = 1 then -(((r + (j : ℤ) * s) % 8 : ℤ) : ℝ)
        else (if (r + (j : ℤ) * s) % 8 = 0 then -8 else -(((r + (j : ℤ) * s) % 8 : ℤ) : ℝ)) := by
    intro j
    dsimp only [Δ]
    rw [hfl (N + j) (by omega), g.P_eq_K_div8 ((N + j : ℕ) : ℤ)]
    split_ifs with hs h0
    · have := floor_div8_diff (g.K_int ((N + j : ℕ) : ℤ))
      rw [hK_mod j] at this; linarith
    · have := ceil_sub1_div8_diff (g.K_int ((N + j : ℕ) : ℤ))
      simp only [hK_mod j, h0, ↓reduceIte] at this; linarith
    · have := ceil_sub1_div8_diff (g.K_int ((N + j : ℕ) : ℤ))
      simp only [hK_mod j, h0, ↓reduceIte] at this; linarith
  have hr_lo : 0 ≤ r := Int.emod_nonneg _ (by norm_num)
  have hr_hi : r < 8 := Int.emod_lt_of_pos _ (by norm_num)
  have hs_even : s = 0 ∨ s = 2 ∨ s = 4 ∨ s = 6 := by dsimp [s]; omega
  refine ⟨hper, ?_, ?_⟩
  · intro hnot4 hzero
    have hs_ne0 : s ≠ 0 := by
      intro h0; apply hnot4
      have : (2 * g.a) % 8 = 0 := h0
      omega
    have h8 : 8 * Δ (N + 0) - 8 * Δ (N + 1) + 8 * Δ (N + 2) - 8 * Δ (N + 3) = 0 := by
      simp only [Nat.add_zero]; linarith
    rw [hΔ_val 0, hΔ_val 1, hΔ_val 2, hΔ_val 3] at h8
    rcases hs_even with hs0 | hs2 | hs4 | hs6
    · exact hs_ne0 hs0
    · by_cases hsig : g.sigma = 1
      · simp only [hsig, ↓reduceIte, hs2] at h8
        interval_cases r <;> norm_num at h8
      · simp only [hsig, ↓reduceIte, hs2] at h8
        interval_cases r <;> norm_num at h8
    · by_cases hsig : g.sigma = 1
      · simp only [hsig, ↓reduceIte, hs4] at h8
        interval_cases r <;> norm_num at h8
      · simp only [hsig, ↓reduceIte, hs4] at h8
        interval_cases r <;> norm_num at h8
    · by_cases hsig : g.sigma = 1
      · simp only [hsig, ↓reduceIte, hs6] at h8
        interval_cases r <;> norm_num at h8
      · simp only [hsig, ↓reduceIte, hs6] at h8
        interval_cases r <;> norm_num at h8
  · intro hnot2 hzero
    have hs_odd : s = 2 ∨ s = 6 := by
      dsimp [s] at *
      have : g.a % 2 = 1 := by omega
      omega
    have h8 : 8 * Δ (N + 0) - 8 * Δ (N + 2) = 0 := by
      simp only [Nat.add_zero]; linarith
    rw [hΔ_val 0, hΔ_val 2] at h8
    rcases hs_odd with hs2 | hs6
    · by_cases hsig : g.sigma = 1
      · simp only [hsig, ↓reduceIte, hs2] at h8
        interval_cases r <;> norm_num at h8
      · simp only [hsig, ↓reduceIte, hs2] at h8
        interval_cases r <;> norm_num at h8
    · by_cases hsig : g.sigma = 1
      · simp only [hsig, ↓reduceIte, hs6] at h8
        interval_cases r <;> norm_num at h8
      · simp only [hsig, ↓reduceIte, hs6] at h8
        interval_cases r <;> norm_num at h8

/-- A cubic polynomial `A n³ + B n² + C n + D` that is 4-periodic for `n ≥ N` must be constant. -/
private lemma cubic_periodic4_const (A B C D : ℝ) (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n →
      A * ((n + 4 : ℕ) : ℝ) ^ 3 + B * ((n + 4 : ℕ) : ℝ) ^ 2 + C * ((n + 4 : ℕ) : ℝ) + D =
      A * (n : ℝ) ^ 3 + B * (n : ℝ) ^ 2 + C * (n : ℝ) + D) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  have h0 := h N (le_refl N)
  have h1 := h (N + 1) (by omega)
  have h2 := h (N + 2) (by omega)
  push_cast at h0 h1 h2
  have hA : A = 0 := by linarith
  subst hA
  have hB : B = 0 := by linarith
  subst hB
  exact ⟨rfl, rfl, by linarith⟩

/-- No integer cubic sequence `m_g(n)` satisfies an eventual linear recurrence of order `3`
(or any order `< 4`). -/
theorem not_recurrence_3 (g : IntCubic) : ¬ SatisfiesEventualRecurrence g.m 3 := by
  rintro ⟨N₁, coef, hrec⟩
  obtain ⟨N₀, hfl⟩ := g.kimberling_general_cubic_floor
  let N := max N₀ N₁
  have hflN : ∀ n : ℕ, N ≤ n → g.m n = if g.sigma = 1 then ⌊g.P n⌋ else ⌈g.P n⌉ - 1 :=
    fun n hn => hfl n (le_trans (le_max_left _ _) hn)
  obtain ⟨hper, _, _⟩ := g.delta_nondeg_mod8 N hflN
  let Δ : ℕ → ℝ := fun n => (g.m n : ℝ) - g.P n
  let c0 : ℝ := coef 0
  let c1 : ℝ := coef 1
  let c2 : ℝ := coef 2
  let LP : ℕ → ℝ := fun n =>
    g.P n - c0 * g.P ((n : ℤ) - 1) - c1 * g.P ((n : ℤ) - 2) - c2 * g.P ((n : ℤ) - 3)
  let LΔ : ℕ → ℝ := fun n =>
    Δ n - c0 * Δ (n - 1) - c1 * Δ (n - 2) - c2 * Δ (n - 3)
  have hsum0 : ∀ n : ℕ, N + 3 ≤ n → LP n + LΔ n = 0 := by
    intro n hn
    have hr := hrec n (by omega)
    rw [Fin.sum_univ_three] at hr
    have hcast : ∀ j : ℕ, j ≤ 3 → (((n - j : ℕ) : ℤ) : ℝ) = (n : ℝ) - (j : ℝ) := by
      intro j hj; push_cast [Nat.cast_sub (by omega : j ≤ n)]; ring
    have hPeq : ∀ j : ℕ, j ≤ 3 → g.P ((n - j : ℕ) : ℤ) = g.P ((n : ℤ) - (j : ℤ)) := by
      intro j hj; unfold P evalR; push_cast [Nat.cast_sub (by omega : j ≤ n)]; ring
    have h1 := hPeq 1 (by omega); have h2 := hPeq 2 (by omega); have h3 := hPeq 3 (by omega)
    dsimp only [LP, LΔ, Δ, c0, c1, c2] at hr ⊢
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at hr
    norm_num at hr h1 h2 h3
    rw [h1, h2, h3]; linarith
  have hLP_per : ∀ n : ℕ, N + 3 ≤ n → LP (n + 4) = LP n := by
    intro n hn
    have h1 := hsum0 n hn
    have h2 := hsum0 (n + 4) (by omega)
    have hΔeq : LΔ (n + 4) = LΔ n := by
      dsimp only [LΔ]
      have e0 : Δ (n + 4) = Δ n := hper n (by omega)
      have e1 : Δ (n + 4 - 1) = Δ (n - 1) := by
        rw [show n + 4 - 1 = (n - 1) + 4 by omega]; exact hper (n - 1) (by omega)
      have e2 : Δ (n + 4 - 2) = Δ (n - 2) := by
        rw [show n + 4 - 2 = (n - 2) + 4 by omega]; exact hper (n - 2) (by omega)
      have e3 : Δ (n + 4 - 3) = Δ (n - 3) := by
        rw [show n + 4 - 3 = (n - 3) + 4 by omega]; exact hper (n - 3) (by omega)
      rw [e0, e1, e2, e3]
    linarith
  -- Expand LP n as A n^3 + B n^2 + C n + D
  let aR : ℝ := (g.a : ℝ)
  let bR : ℝ := (g.b : ℝ)
  let cR : ℝ := (g.c : ℝ)
  let dR : ℝ := (g.d : ℝ)
  let s0 : ℝ := 1 - c0 - c1 - c2
  let s1 : ℝ := c0 + 2 * c1 + 3 * c2
  let s2 : ℝ := c0 + 4 * c1 + 9 * c2
  let s3 : ℝ := c0 + 8 * c1 + 27 * c2
  have hLP_poly : ∀ n : ℕ, LP n =
      (aR * s0) * (n : ℝ) ^ 3 +
      (3 * aR * s1 + (bR - 3 / 2 * aR) * s0) * (n : ℝ) ^ 2 +
      (-3 * aR * s2 + (2 * bR - 3 * aR) * s1 + (cR - bR + 3 / 4 * aR) * s0) * (n : ℝ) +
      (aR * s3 + (3 / 2 * aR - bR) * s2 + (3 / 4 * aR - bR + cR) * s1 +
        (-1 / 8 * aR + 1 / 4 * bR - 1 / 2 * cR + dR + 1 / 2) * s0) := by
    intro n; dsimp only [LP, P, evalR, aR, bR, cR, dR, s0, s1, s2, s3]; push_cast; ring
  have hconst := cubic_periodic4_const _ _ _ _ (N + 3) (fun n hn => by
    have := hLP_per n hn; rw [hLP_poly (n + 4), hLP_poly n] at this; exact this)
  have ha0 : aR ≠ 0 := g.ha_pos.ne'
  have hs0 : s0 = 0 := (mul_eq_zero.mp hconst.1).resolve_left ha0
  have hs1 : s1 = 0 := by
    have hB := hconst.2.1; rw [hs0, mul_zero, add_zero] at hB
    have : (3 * aR) * s1 = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (by positivity)
  have hs2 : s2 = 0 := by
    have hC := hconst.2.2; rw [hs0, hs1] at hC
    have : (-3 * aR) * s2 = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (by linarith [g.ha_pos])
  -- Unique solution: c0 = 3, c1 = -3, c2 = 1, so s3 = 6!
  have hc_sol : c0 = 3 ∧ c1 = -3 ∧ c2 = 1 := by
    dsimp only [s0, s1, s2] at hs0 hs1 hs2
    exact ⟨by linarith, by linarith, by linarith⟩
  have hLP_val : ∀ n : ℕ, LP n = 6 * aR := by
    intro n; rw [hLP_poly n, hs0, hs1, hs2]
    have hs3 : s3 = 6 := by dsimp only [s3]; linarith [hc_sol.1, hc_sol.2.1, hc_sol.2.2]
    rw [hs3]; ring
  -- Sum LΔ over one full period (N+3, N+4, N+5, N+6) = 0, contradicting 4 * 6a = 0!
  have e0 := hsum0 (N + 3) (by omega)
  have e1 := hsum0 (N + 4) (by omega)
  have e2 := hsum0 (N + 5) (by omega)
  have e3 := hsum0 (N + 6) (by omega)
  rw [hLP_val] at e0 e1 e2 e3
  have hp0 := hper N (by omega)
  have hp1 := hper (N + 1) (by omega)
  have hp2 := hper (N + 2) (by omega)
  dsimp only [LΔ] at e0 e1 e2 e3
  simp only [show N + 3 - 1 = N + 2 by omega, show N + 3 - 2 = N + 1 by omega,
    show N + 3 - 3 = N by omega, show N + 4 - 1 = N + 3 by omega,
    show N + 4 - 2 = N + 2 by omega, show N + 4 - 3 = N + 1 by omega,
    show N + 5 - 1 = N + 4 by omega, show N + 5 - 2 = N + 3 by omega,
    show N + 5 - 3 = N + 2 by omega, show N + 6 - 1 = N + 5 by omega,
    show N + 6 - 2 = N + 4 by omega, show N + 6 - 3 = N + 3 by omega] at e0 e1 e2 e3
  rw [hc_sol.1, hc_sol.2.1, hc_sol.2.2] at e0 e1 e2 e3
  have : 24 * aR = 0 := by linarith [e0, e1, e2, e3, hp0, hp1, hp2]
  linarith [g.ha_pos]

/-- When `4 ∤ a`, `m_g(n)` satisfies no eventual linear recurrence of order `4`. -/
theorem not_recurrence_4_of_not_div4 (g : IntCubic) (hnot4 : ¬ (4 : ℤ) ∣ g.a) :
    ¬ SatisfiesEventualRecurrence g.m 4 := by
  rintro ⟨N₁, coef, hrec⟩
  obtain ⟨N₀, hfl⟩ := g.kimberling_general_cubic_floor
  let N := max N₀ N₁
  have hflN : ∀ n : ℕ, N ≤ n → g.m n = if g.sigma = 1 then ⌊g.P n⌋ else ⌈g.P n⌉ - 1 :=
    fun n hn => hfl n (le_trans (le_max_left _ _) hn)
  obtain ⟨hper, halt, _⟩ := g.delta_nondeg_mod8 N hflN
  let Δ : ℕ → ℝ := fun n => (g.m n : ℝ) - g.P n
  let c0 : ℝ := coef 0
  let c1 : ℝ := coef 1
  let c2 : ℝ := coef 2
  let c3 : ℝ := coef 3
  let LP : ℕ → ℝ := fun n =>
    g.P n - c0 * g.P ((n : ℤ) - 1) - c1 * g.P ((n : ℤ) - 2) -
      c2 * g.P ((n : ℤ) - 3) - c3 * g.P ((n : ℤ) - 4)
  let LΔ : ℕ → ℝ := fun n =>
    Δ n - c0 * Δ (n - 1) - c1 * Δ (n - 2) - c2 * Δ (n - 3) - c3 * Δ (n - 4)
  have hsum0 : ∀ n : ℕ, N + 4 ≤ n → LP n + LΔ n = 0 := by
    intro n hn
    have hr := hrec n (by omega)
    rw [Fin.sum_univ_four] at hr
    have hPeq : ∀ j : ℕ, j ≤ 4 → g.P ((n - j : ℕ) : ℤ) = g.P ((n : ℤ) - (j : ℤ)) := by
      intro j hj; unfold P evalR; push_cast [Nat.cast_sub (by omega : j ≤ n)]; ring
    have h1 := hPeq 1 (by omega); have h2 := hPeq 2 (by omega)
    have h3 := hPeq 3 (by omega); have h4 := hPeq 4 (by omega)
    dsimp only [LP, LΔ, Δ, c0, c1, c2, c3] at hr ⊢
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 4).val = 3 from rfl] at hr
    norm_num at hr h1 h2 h3 h4
    rw [h1, h2, h3, h4]; linarith
  have hLP_per : ∀ n : ℕ, N + 4 ≤ n → LP (n + 4) = LP n := by
    intro n hn
    have h1 := hsum0 n hn; have h2 := hsum0 (n + 4) (by omega)
    have hΔeq : LΔ (n + 4) = LΔ n := by
      dsimp only [LΔ]
      have e0 : Δ (n + 4) = Δ n := hper n (by omega)
      have e1 : Δ (n + 4 - 1) = Δ (n - 1) := by
        rw [show n + 4 - 1 = (n - 1) + 4 by omega]; exact hper (n - 1) (by omega)
      have e2 : Δ (n + 4 - 2) = Δ (n - 2) := by
        rw [show n + 4 - 2 = (n - 2) + 4 by omega]; exact hper (n - 2) (by omega)
      have e3 : Δ (n + 4 - 3) = Δ (n - 3) := by
        rw [show n + 4 - 3 = (n - 3) + 4 by omega]; exact hper (n - 3) (by omega)
      have e4 : Δ (n + 4 - 4) = Δ (n - 4) := by
        rw [show n + 4 - 4 = (n - 4) + 4 by omega]; exact hper (n - 4) (by omega)
      rw [e0, e1, e2, e3, e4]
    linarith
  let aR : ℝ := (g.a : ℝ); let bR : ℝ := (g.b : ℝ)
  let cR : ℝ := (g.c : ℝ); let dR : ℝ := (g.d : ℝ)
  let s0 : ℝ := 1 - c0 - c1 - c2 - c3
  let s1 : ℝ := c0 + 2 * c1 + 3 * c2 + 4 * c3
  let s2 : ℝ := c0 + 4 * c1 + 9 * c2 + 16 * c3
  let s3 : ℝ := c0 + 8 * c1 + 27 * c2 + 64 * c3
  have hLP_poly : ∀ n : ℕ, LP n =
      (aR * s0) * (n : ℝ) ^ 3 +
      (3 * aR * s1 + (bR - 3 / 2 * aR) * s0) * (n : ℝ) ^ 2 +
      (-3 * aR * s2 + (2 * bR - 3 * aR) * s1 + (cR - bR + 3 / 4 * aR) * s0) * (n : ℝ) +
      (aR * s3 + (3 / 2 * aR - bR) * s2 + (3 / 4 * aR - bR + cR) * s1 +
        (-1 / 8 * aR + 1 / 4 * bR - 1 / 2 * cR + dR + 1 / 2) * s0) := by
    intro n; dsimp only [LP, P, evalR, aR, bR, cR, dR, s0, s1, s2, s3]; push_cast; ring
  have hconst := cubic_periodic4_const _ _ _ _ (N + 4) (fun n hn => by
    have := hLP_per n hn; rw [hLP_poly (n + 4), hLP_poly n] at this; exact this)
  have ha0 : aR ≠ 0 := g.ha_pos.ne'
  have hs0 : s0 = 0 := (mul_eq_zero.mp hconst.1).resolve_left ha0
  have hs1 : s1 = 0 := by
    have hB := hconst.2.1; rw [hs0, mul_zero, add_zero] at hB
    exact (mul_eq_zero.mp (show (3 * aR) * s1 = 0 by linarith)).resolve_left (by positivity)
  have hs2 : s2 = 0 := by
    have hC := hconst.2.2; rw [hs0, hs1] at hC
    exact (mul_eq_zero.mp (show (-3 * aR) * s2 = 0 by linarith)).resolve_left (by linarith [g.ha_pos])
  have hLP_val : ∀ n : ℕ, LP n = aR * s3 := by
    intro n; rw [hLP_poly n, hs0, hs1, hs2]; ring
  have e0 := hsum0 (N + 4) (by omega)
  have e1 := hsum0 (N + 5) (by omega)
  have e2 := hsum0 (N + 6) (by omega)
  have e3 := hsum0 (N + 7) (by omega)
  rw [hLP_val] at e0 e1 e2 e3
  have hp0 : Δ (N + 4) = Δ N := hper N (by omega)
  have hp1 : Δ (N + 5) = Δ (N + 1) := hper (N + 1) (by omega)
  have hp2 : Δ (N + 6) = Δ (N + 2) := hper (N + 2) (by omega)
  have hp3 : Δ (N + 7) = Δ (N + 3) := hper (N + 3) (by omega)
  dsimp only [LΔ] at e0 e1 e2 e3
  simp only [show N + 4 - 1 = N + 3 by omega, show N + 4 - 2 = N + 2 by omega,
    show N + 4 - 3 = N + 1 by omega, show N + 4 - 4 = N by omega,
    show N + 5 - 1 = N + 4 by omega, show N + 5 - 2 = N + 3 by omega,
    show N + 5 - 3 = N + 2 by omega, show N + 5 - 4 = N + 1 by omega,
    show N + 6 - 1 = N + 5 by omega, show N + 6 - 2 = N + 4 by omega,
    show N + 6 - 3 = N + 3 by omega, show N + 6 - 4 = N + 2 by omega,
    show N + 7 - 1 = N + 6 by omega, show N + 7 - 2 = N + 5 by omega,
    show N + 7 - 3 = N + 4 by omega, show N + 7 - 4 = N + 3 by omega] at e0 e1 e2 e3
  simp only [hp0, hp1, hp2, hp3] at e0 e1 e2 e3
  -- Sum e0 + e1 + e2 + e3 = 4 * aR * s3 + s0 * (Δ N + Δ (N+1) + Δ (N+2) + Δ (N+3)) = 0
  have h4a : 4 * aR * s3 = 0 := by
    have hadd : (aR * s3 + (Δ N - c0 * Δ (N + 3) - c1 * Δ (N + 2) - c2 * Δ (N + 1) - c3 * Δ N)) +
        (aR * s3 + (Δ (N + 1) - c0 * Δ N - c1 * Δ (N + 3) - c2 * Δ (N + 2) - c3 * Δ (N + 1))) +
        (aR * s3 + (Δ (N + 2) - c0 * Δ (N + 1) - c1 * Δ N - c2 * Δ (N + 3) - c3 * Δ (N + 2))) +
        (aR * s3 + (Δ (N + 3) - c0 * Δ (N + 2) - c1 * Δ (N + 1) - c2 * Δ N - c3 * Δ (N + 3))) = 0 := by
      linarith
    have hfac : (aR * s3 + (Δ N - c0 * Δ (N + 3) - c1 * Δ (N + 2) - c2 * Δ (N + 1) - c3 * Δ N)) +
        (aR * s3 + (Δ (N + 1) - c0 * Δ N - c1 * Δ (N + 3) - c2 * Δ (N + 2) - c3 * Δ (N + 1))) +
        (aR * s3 + (Δ (N + 2) - c0 * Δ (N + 1) - c1 * Δ N - c2 * Δ (N + 3) - c3 * Δ (N + 2))) +
        (aR * s3 + (Δ (N + 3) - c0 * Δ (N + 2) - c1 * Δ (N + 1) - c2 * Δ N - c3 * Δ (N + 3))) =
        4 * aR * s3 + s0 * (Δ N + Δ (N + 1) + Δ (N + 2) + Δ (N + 3)) := by
      dsimp only [s0]; ring
    rw [hfac, hs0, zero_mul, add_zero] at hadd
    exact hadd
  have hs3 : s3 = 0 := (mul_eq_zero.mp h4a).resolve_left (by positivity)
  have hc_sol : c0 = 4 ∧ c1 = -6 ∧ c2 = 4 ∧ c3 = -1 := by
    dsimp only [s0, s1, s2, s3] at hs0 hs1 hs2 hs3
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  rw [hs3, mul_zero, zero_add, hc_sol.1, hc_sol.2.1, hc_sol.2.2.1, hc_sol.2.2.2] at e0 e1 e2 e3
  have halt0 : 16 * (Δ N - Δ (N + 1) + Δ (N + 2) - Δ (N + 3)) = 0 := by linarith
  exact halt hnot4 (by linarith)

private lemma no_order6_period4_aux (c0 c1 c2 c3 c4 c5 d0 d1 d2 d3 : ℝ)
    (hs0 : 1 - c0 - c1 - c2 - c3 - c4 - c5 = 0)
    (hs1 : c0 + 2 * c1 + 3 * c2 + 4 * c3 + 5 * c4 + 6 * c5 = 0)
    (hs2 : c0 + 4 * c1 + 9 * c2 + 16 * c3 + 25 * c4 + 36 * c5 = 0)
    (hs3 : c0 + 8 * c1 + 27 * c2 + 64 * c3 + 125 * c4 + 216 * c5 = 0)
    (e0 : d0 - c0 * d3 - c1 * d2 - c2 * d1 - c3 * d0 - c4 * d3 - c5 * d2 = 0)
    (e1 : d1 - c0 * d0 - c1 * d3 - c2 * d2 - c3 * d1 - c4 * d0 - c5 * d3 = 0)
    (e2 : d2 - c0 * d1 - c1 * d0 - c2 * d3 - c3 * d2 - c4 * d1 - c5 * d0 = 0)
    (e3 : d3 - c0 * d2 - c1 * d1 - c2 * d0 - c3 * d3 - c4 * d2 - c5 * d1 = 0)
    (halt : d0 - d1 + d2 - d3 ≠ 0)
    (h02 : d0 - d2 ≠ 0) : False := by
  let α : ℝ := 4 - c0
  let β : ℝ := -c5
  have hc0 : c0 = 4 - α := by dsimp [α]; ring
  have hc5 : c5 = -β := by dsimp [β]; ring
  have hc1 : c1 = -(6 - 4 * α + β) := by dsimp only [α, β]; linarith
  have hc2 : c2 = 4 - 6 * α + 4 * β := by dsimp only [α, β]; linarith
  have hc3 : c3 = -(1 - 4 * α + 6 * β) := by dsimp only [α, β]; linarith
  have hc4 : c4 = -α + 4 * β := by dsimp only [α, β]; linarith
  have halt_eq : 16 * (1 - α + β) * (d0 - d1 + d2 - d3) = 0 := by
    have : (d0 - c0 * d3 - c1 * d2 - c2 * d1 - c3 * d0 - c4 * d3 - c5 * d2) -
        (d1 - c0 * d0 - c1 * d3 - c2 * d2 - c3 * d1 - c4 * d0 - c5 * d3) +
        (d2 - c0 * d1 - c1 * d0 - c2 * d3 - c3 * d2 - c4 * d1 - c5 * d0) -
        (d3 - c0 * d2 - c1 * d1 - c2 * d0 - c3 * d3 - c4 * d2 - c5 * d1) =
        16 * (1 - α + β) * (d0 - d1 + d2 - d3) := by
      rw [hc0, hc1, hc2, hc3, hc4, hc5]; ring
    linarith
  have hβ : β = α - 1 := by
    have h1 := (mul_eq_zero.mp halt_eq).resolve_right halt
    linarith
  have h1 : (2 - α) * (d0 - d2) - α * (d1 - d3) = 0 := by
    have : (d0 - c0 * d3 - c1 * d2 - c2 * d1 - c3 * d0 - c4 * d3 - c5 * d2) -
        (d2 - c0 * d1 - c1 * d0 - c2 * d3 - c3 * d2 - c4 * d1 - c5 * d0) =
        -4 * ((2 - α) * (d0 - d2) - α * (d1 - d3)) := by
      rw [hc0, hc1, hc2, hc3, hc4, hc5, hβ]; ring
    linarith
  have h2 : (2 - α) * (d1 - d3) + α * (d0 - d2) = 0 := by
    have : (d1 - c0 * d0 - c1 * d3 - c2 * d2 - c3 * d1 - c4 * d0 - c5 * d3) -
        (d3 - c0 * d2 - c1 * d1 - c2 * d0 - c3 * d3 - c4 * d2 - c5 * d1) =
        -4 * ((2 - α) * (d1 - d3) + α * (d0 - d2)) := by
      rw [hc0, hc1, hc2, hc3, hc4, hc5, hβ]; ring
    linarith
  have hsq : ((2 - α) ^ 2 + α ^ 2) * ((d0 - d2) ^ 2 + (d1 - d3) ^ 2) = 0 := by
    linear_combination ((2 - α) * (d0 - d2) - α * (d1 - d3)) * h1 +
      ((2 - α) * (d1 - d3) + α * (d0 - d2)) * h2
  have hpos1 : 0 < (2 - α) ^ 2 + α ^ 2 := by
    have : (2 - α) ^ 2 + α ^ 2 = 2 * (α - 1) ^ 2 + 2 := by ring
    rw [this]; positivity
  have hpos2 : 0 < (d0 - d2) ^ 2 + (d1 - d3) ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h02) (sq_nonneg _)
  exact (mul_pos hpos1 hpos2).ne' hsq

/-- When `a` is odd (`2 ∤ a`), `m_g(n)` satisfies no eventual linear recurrence of order `6`
(or any order `< 7`). -/
theorem not_recurrence_6_of_not_div2 (g : IntCubic) (hnot2 : ¬ (2 : ℤ) ∣ g.a) :
    ¬ SatisfiesEventualRecurrence g.m 6 := by
  rintro ⟨N₁, coef, hrec⟩
  obtain ⟨N₀, hfl⟩ := g.kimberling_general_cubic_floor
  let N := max N₀ N₁
  have hflN : ∀ n : ℕ, N ≤ n → g.m n = if g.sigma = 1 then ⌊g.P n⌋ else ⌈g.P n⌉ - 1 :=
    fun n hn => hfl n (le_trans (le_max_left _ _) hn)
  have hnot4 : ¬ (4 : ℤ) ∣ g.a := fun h4 => hnot2 (dvd_trans (by norm_num : (2 : ℤ) ∣ 4) h4)
  obtain ⟨hper, halt, h02⟩ := g.delta_nondeg_mod8 N hflN
  let Δ : ℕ → ℝ := fun n => (g.m n : ℝ) - g.P n
  let c0 : ℝ := coef 0; let c1 : ℝ := coef 1; let c2 : ℝ := coef 2
  let c3 : ℝ := coef 3; let c4 : ℝ := coef 4; let c5 : ℝ := coef 5
  let LP : ℕ → ℝ := fun n =>
    g.P n - c0 * g.P ((n : ℤ) - 1) - c1 * g.P ((n : ℤ) - 2) - c2 * g.P ((n : ℤ) - 3) -
      c3 * g.P ((n : ℤ) - 4) - c4 * g.P ((n : ℤ) - 5) - c5 * g.P ((n : ℤ) - 6)
  let LΔ : ℕ → ℝ := fun n =>
    Δ n - c0 * Δ (n - 1) - c1 * Δ (n - 2) - c2 * Δ (n - 3) -
      c3 * Δ (n - 4) - c4 * Δ (n - 5) - c5 * Δ (n - 6)
  have hsum0 : ∀ n : ℕ, N + 6 ≤ n → LP n + LΔ n = 0 := by
    intro n hn
    have hr := hrec n (by omega)
    rw [Fin.sum_univ_six] at hr
    have hPeq : ∀ j : ℕ, j ≤ 6 → g.P ((n - j : ℕ) : ℤ) = g.P ((n : ℤ) - (j : ℤ)) := by
      intro j hj; unfold P evalR; push_cast [Nat.cast_sub (by omega : j ≤ n)]; ring
    have h1 := hPeq 1 (by omega); have h2 := hPeq 2 (by omega); have h3 := hPeq 3 (by omega)
    have h4 := hPeq 4 (by omega); have h5 := hPeq 5 (by omega); have h6 := hPeq 6 (by omega)
    dsimp only [LP, LΔ, Δ, c0, c1, c2, c3, c4, c5] at hr ⊢
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two,
      show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl,
      show (5 : Fin 6).val = 5 from rfl] at hr
    norm_num at hr h1 h2 h3 h4 h5 h6
    rw [h1, h2, h3, h4, h5, h6]; linarith
  have hLP_per : ∀ n : ℕ, N + 6 ≤ n → LP (n + 4) = LP n := by
    intro n hn
    have h1 := hsum0 n hn; have h2 := hsum0 (n + 4) (by omega)
    have hΔeq : LΔ (n + 4) = LΔ n := by
      dsimp only [LΔ]
      have e0 : Δ (n + 4) = Δ n := hper n (by omega)
      have e1 : Δ (n + 4 - 1) = Δ (n - 1) := by
        rw [show n + 4 - 1 = (n - 1) + 4 by omega]; exact hper (n - 1) (by omega)
      have e2 : Δ (n + 4 - 2) = Δ (n - 2) := by
        rw [show n + 4 - 2 = (n - 2) + 4 by omega]; exact hper (n - 2) (by omega)
      have e3 : Δ (n + 4 - 3) = Δ (n - 3) := by
        rw [show n + 4 - 3 = (n - 3) + 4 by omega]; exact hper (n - 3) (by omega)
      have e4 : Δ (n + 4 - 4) = Δ (n - 4) := by
        rw [show n + 4 - 4 = (n - 4) + 4 by omega]; exact hper (n - 4) (by omega)
      have e5 : Δ (n + 4 - 5) = Δ (n - 5) := by
        rw [show n + 4 - 5 = (n - 5) + 4 by omega]; exact hper (n - 5) (by omega)
      have e6 : Δ (n + 4 - 6) = Δ (n - 6) := by
        rw [show n + 4 - 6 = (n - 6) + 4 by omega]; exact hper (n - 6) (by omega)
      rw [e0, e1, e2, e3, e4, e5, e6]
    linarith
  let aR : ℝ := (g.a : ℝ); let bR : ℝ := (g.b : ℝ)
  let cR : ℝ := (g.c : ℝ); let dR : ℝ := (g.d : ℝ)
  let s0 : ℝ := 1 - c0 - c1 - c2 - c3 - c4 - c5
  let s1 : ℝ := c0 + 2 * c1 + 3 * c2 + 4 * c3 + 5 * c4 + 6 * c5
  let s2 : ℝ := c0 + 4 * c1 + 9 * c2 + 16 * c3 + 25 * c4 + 36 * c5
  let s3 : ℝ := c0 + 8 * c1 + 27 * c2 + 64 * c3 + 125 * c4 + 216 * c5
  have hLP_poly : ∀ n : ℕ, LP n =
      (aR * s0) * (n : ℝ) ^ 3 +
      (3 * aR * s1 + (bR - 3 / 2 * aR) * s0) * (n : ℝ) ^ 2 +
      (-3 * aR * s2 + (2 * bR - 3 * aR) * s1 + (cR - bR + 3 / 4 * aR) * s0) * (n : ℝ) +
      (aR * s3 + (3 / 2 * aR - bR) * s2 + (3 / 4 * aR - bR + cR) * s1 +
        (-1 / 8 * aR + 1 / 4 * bR - 1 / 2 * cR + dR + 1 / 2) * s0) := by
    intro n; dsimp only [LP, P, evalR, aR, bR, cR, dR, s0, s1, s2, s3]; push_cast; ring
  have hconst := cubic_periodic4_const _ _ _ _ (N + 6) (fun n hn => by
    have := hLP_per n hn; rw [hLP_poly (n + 4), hLP_poly n] at this; exact this)
  have ha0 : aR ≠ 0 := g.ha_pos.ne'
  have hs0 : s0 = 0 := (mul_eq_zero.mp hconst.1).resolve_left ha0
  have hs1 : s1 = 0 := by
    have hB := hconst.2.1; rw [hs0, mul_zero, add_zero] at hB
    exact (mul_eq_zero.mp (show (3 * aR) * s1 = 0 by linarith)).resolve_left (by positivity)
  have hs2 : s2 = 0 := by
    have hC := hconst.2.2; rw [hs0, hs1] at hC
    exact (mul_eq_zero.mp (show (-3 * aR) * s2 = 0 by linarith)).resolve_left (by linarith [g.ha_pos])
  have hLP_val : ∀ n : ℕ, LP n = aR * s3 := by
    intro n; rw [hLP_poly n, hs0, hs1, hs2]; ring
  -- Evaluate at N+8, N+9, N+10, N+11 so all indices are ≥ N+2 and reduce mod 4 cleanly!
  have e0 := hsum0 (N + 8) (by omega)
  have e1 := hsum0 (N + 9) (by omega)
  have e2 := hsum0 (N + 10) (by omega)
  have e3 := hsum0 (N + 11) (by omega)
  rw [hLP_val] at e0 e1 e2 e3
  have hp : ∀ j : ℕ, Δ (N + j + 4) = Δ (N + j) := fun j => hper (N + j) (by omega)
  have hp8 : ∀ j : ℕ, Δ (N + j + 8) = Δ (N + j) := fun j => by
    rw [show N + j + 8 = (N + (j + 4)) + 4 by omega, hp (j + 4),
        show N + (j + 4) = (N + j) + 4 by omega, hp j]
  dsimp only [LΔ] at e0 e1 e2 e3
  have r0 : Δ (N + 8) = Δ N := by simpa using hp8 0
  have r1 : Δ (N + 9) = Δ (N + 1) := by simpa using hp8 1
  have r2 : Δ (N + 10) = Δ (N + 2) := by simpa using hp8 2
  have r3 : Δ (N + 11) = Δ (N + 3) := by simpa using hp8 3
  have r4 : Δ (N + 4) = Δ N := by simpa using hp 0
  have r5 : Δ (N + 5) = Δ (N + 1) := by simpa using hp 1
  have r6 : Δ (N + 6) = Δ (N + 2) := by simpa using hp 2
  have r7 : Δ (N + 7) = Δ (N + 3) := by simpa using hp 3
  simp only [show N + 8 - 1 = N + 7 by omega, show N + 8 - 2 = N + 6 by omega,
    show N + 8 - 3 = N + 5 by omega, show N + 8 - 4 = N + 4 by omega,
    show N + 8 - 5 = N + 3 by omega, show N + 8 - 6 = N + 2 by omega,
    show N + 9 - 1 = N + 8 by omega, show N + 9 - 2 = N + 7 by omega,
    show N + 9 - 3 = N + 6 by omega, show N + 9 - 4 = N + 5 by omega,
    show N + 9 - 5 = N + 4 by omega, show N + 9 - 6 = N + 3 by omega,
    show N + 10 - 1 = N + 9 by omega, show N + 10 - 2 = N + 8 by omega,
    show N + 10 - 3 = N + 7 by omega, show N + 10 - 4 = N + 6 by omega,
    show N + 10 - 5 = N + 5 by omega, show N + 10 - 6 = N + 4 by omega,
    show N + 11 - 1 = N + 10 by omega, show N + 11 - 2 = N + 9 by omega,
    show N + 11 - 3 = N + 8 by omega, show N + 11 - 4 = N + 7 by omega,
    show N + 11 - 5 = N + 6 by omega, show N + 11 - 6 = N + 5 by omega] at e0 e1 e2 e3
  simp only [r0, r1, r2, r3, r4, r5, r6, r7] at e0 e1 e2 e3
  -- Sum e0 + e1 + e2 + e3 gives 4 * aR * s3 = 0, hence s3 = 0
  have h4a : 4 * aR * s3 = 0 := by
    have hadd : (aR * s3 + (Δ N - c0 * Δ (N + 3) - c1 * Δ (N + 2) - c2 * Δ (N + 1) -
          c3 * Δ N - c4 * Δ (N + 3) - c5 * Δ (N + 2))) +
        (aR * s3 + (Δ (N + 1) - c0 * Δ N - c1 * Δ (N + 3) - c2 * Δ (N + 2) -
          c3 * Δ (N + 1) - c4 * Δ N - c5 * Δ (N + 3))) +
        (aR * s3 + (Δ (N + 2) - c0 * Δ (N + 1) - c1 * Δ N - c2 * Δ (N + 3) -
          c3 * Δ (N + 2) - c4 * Δ (N + 1) - c5 * Δ N)) +
        (aR * s3 + (Δ (N + 3) - c0 * Δ (N + 2) - c1 * Δ (N + 1) - c2 * Δ N -
          c3 * Δ (N + 3) - c4 * Δ (N + 2) - c5 * Δ (N + 1))) = 0 := by linarith
    have hfac : (aR * s3 + (Δ N - c0 * Δ (N + 3) - c1 * Δ (N + 2) - c2 * Δ (N + 1) -
          c3 * Δ N - c4 * Δ (N + 3) - c5 * Δ (N + 2))) +
        (aR * s3 + (Δ (N + 1) - c0 * Δ N - c1 * Δ (N + 3) - c2 * Δ (N + 2) -
          c3 * Δ (N + 1) - c4 * Δ N - c5 * Δ (N + 3))) +
        (aR * s3 + (Δ (N + 2) - c0 * Δ (N + 1) - c1 * Δ N - c2 * Δ (N + 3) -
          c3 * Δ (N + 2) - c4 * Δ (N + 1) - c5 * Δ N)) +
        (aR * s3 + (Δ (N + 3) - c0 * Δ (N + 2) - c1 * Δ (N + 1) - c2 * Δ N -
          c3 * Δ (N + 3) - c4 * Δ (N + 2) - c5 * Δ (N + 1))) =
        4 * aR * s3 + s0 * (Δ N + Δ (N + 1) + Δ (N + 2) + Δ (N + 3)) := by
      dsimp only [s0]; ring
    rw [hfac, hs0, zero_mul, add_zero] at hadd
    exact hadd
  have hs3 : s3 = 0 := (mul_eq_zero.mp h4a).resolve_left (by positivity)
  rw [hs3, mul_zero, zero_add] at e0 e1 e2 e3
  exact no_order6_period4_aux c0 c1 c2 c3 c4 c5 (Δ N) (Δ (N + 1)) (Δ (N + 2)) (Δ (N + 3))
    hs0 hs1 hs2 hs3 e0 e1 e2 e3 (halt hnot4) (h02 hnot2)

/-- **Corollary 8 (Complete Exact Minimal Eventual Recurrence Order Classification)**:
For every integer cubic `g(n) = a n³ + b n² + c n + d` (`a > 0`):
1. `m_g(n)` never satisfies an eventual linear recurrence of order `< 4`.
2. `m_g(n)` satisfies an eventual order-4 recurrence iff `4 ∣ a`.
3. `m_g(n)` satisfies an eventual order-5 recurrence iff `2 ∣ a`.
4. `m_g(n)` always satisfies an eventual order-7 recurrence, and order 7 is minimal iff `a` is odd. -/
theorem kimberling_minimal_order (g : IntCubic) :
    (∀ k < 4, ¬ SatisfiesEventualRecurrence g.m k) ∧
    (SatisfiesEventualRecurrence g.m 4 ↔ (4 : ℤ) ∣ g.a) ∧
    (SatisfiesEventualRecurrence g.m 5 ↔ (2 : ℤ) ∣ g.a) ∧
    (SatisfiesEventualRecurrence g.m 7 ∧
      ((∀ k < 7, ¬ SatisfiesEventualRecurrence g.m k) ↔ ¬ (2 : ℤ) ∣ g.a)) := by
  have h7 : SatisfiesEventualRecurrence g.m 7 := by
    obtain ⟨N₀, hN₀⟩ := g.kimberling_general_cubic_recurrence
    refine ⟨N₀, fun i => match i.1 with
        | 0 => 3 | 1 => -3 | 2 => 1 | 3 => 1 | 4 => -3 | 5 => 3 | _ => -1, fun n hn => ?_⟩
    have hr := hN₀ n hn
    have hrR : (g.m n : ℝ) =
        3 * (g.m (n - 1) : ℝ) - 3 * (g.m (n - 2) : ℝ) + (g.m (n - 3) : ℝ) +
        (g.m (n - 4) : ℝ) - 3 * (g.m (n - 5) : ℝ) + 3 * (g.m (n - 6) : ℝ) - (g.m (n - 7) : ℝ) := by
      exact_mod_cast hr
    rw [Fin.sum_univ_seven]
    norm_num
    linarith
  have h5_of : (2 : ℤ) ∣ g.a → SatisfiesEventualRecurrence g.m 5 := by
    intro h2
    obtain ⟨N₀, hN₀⟩ := g.kimberling_even_order5 h2
    refine ⟨N₀, fun i => match i.1 with
        | 0 => 3 | 1 => -2 | 2 => -2 | 3 => 3 | _ => -1, fun n hn => ?_⟩
    have hr := hN₀ n hn
    have hrR : (g.m n : ℝ) =
        3 * (g.m (n - 1) : ℝ) - 2 * (g.m (n - 2) : ℝ) - 2 * (g.m (n - 3) : ℝ) +
        3 * (g.m (n - 4) : ℝ) - (g.m (n - 5) : ℝ) := by
      exact_mod_cast hr
    rw [Fin.sum_univ_five]
    norm_num
    linarith
  have h4_of : (4 : ℤ) ∣ g.a → SatisfiesEventualRecurrence g.m 4 := by
    intro h4
    obtain ⟨N₀, hN₀⟩ := g.kimberling_div4_order4 h4
    refine ⟨N₀, fun i => match i.1 with
        | 0 => 4 | 1 => -6 | 2 => 4 | _ => -1, fun n hn => ?_⟩
    have hr := hN₀ n hn
    have hrR : (g.m n : ℝ) =
        4 * (g.m (n - 1) : ℝ) - 6 * (g.m (n - 2) : ℝ) +
        4 * (g.m (n - 3) : ℝ) - (g.m (n - 4) : ℝ) := by
      exact_mod_cast hr
    rw [Fin.sum_univ_four]
    norm_num
    linarith
  refine ⟨fun k hk hrec => g.not_recurrence_3 (recurrence_mono g.m (by omega) hrec),
    ⟨fun hrec => by_contra fun hnot4 => g.not_recurrence_4_of_not_div4 hnot4 hrec, h4_of⟩,
    ⟨fun hrec => by_contra fun hnot2 =>
        g.not_recurrence_6_of_not_div2 hnot2 (recurrence_mono g.m (by omega) hrec), h5_of⟩,
    h7, ⟨fun hmin h2 => hmin 5 (by omega) (h5_of h2),
         fun hnot2 k hk hrec => g.not_recurrence_6_of_not_div2 hnot2 (recurrence_mono g.m (by omega) hrec)⟩⟩

end

end IntCubic

end GeneralCubic

#print axioms GeneralCubic.IntCubic.nonvanishing_c1_c2_c3
#print axioms GeneralCubic.IntCubic.M_g_asymptotic_limit
#print axioms GeneralCubic.IntCubic.kimberling_general_cubic_floor
#print axioms GeneralCubic.IntCubic.kimberling_general_cubic_recurrence
#print axioms GeneralCubic.IntCubic.kimberling_even_order5
#print axioms GeneralCubic.IntCubic.kimberling_div4_order4
#print axioms GeneralCubic.IntCubic.nonvanishing_c1_c2_c3_real
#print axioms GeneralCubic.IntCubic.kimberling_minimal_order
