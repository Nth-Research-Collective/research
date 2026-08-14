import Mathlib.Tactic

/-!
Machine-checked algebra for the positive-body reduction from Dynamic MoE
Serving.  The external positive-body competitive theorem is not reproved here;
the final assembly theorem takes its movement guarantee as an explicit premise.
-/

namespace DynamicMoePositiveBody

theorem reciprocal_tangent_gap
    (r q p : ℝ) (hq : 0 < q) (hp : 0 < p) :
    r / q - r * (2 * p - q) / p ^ 2 =
      r * (q - p) ^ 2 / (q * p ^ 2) := by
  field_simp [ne_of_gt hq, ne_of_gt hp]
  ring

theorem reciprocal_tangent_underestimate
    (r q p : ℝ) (hr : 0 ≤ r) (hq : 0 < q) (hp : 0 < p) :
    r * (2 * p - q) / p ^ 2 ≤ r / q := by
  rw [← sub_nonneg]
  rw [reciprocal_tangent_gap r q p hq hp]
  positivity

theorem geometric_ratio_three_quarters
    (q p : ℝ) (hp : 0 < p) (hpq : p ≤ q) (hqp : 2 * q ≤ 3 * p) :
    (3 / 4 : ℝ) ≤ (q / p) * (2 - q / p) := by
  have hz0 : 0 ≤ q / p - 1 := by
    have : (1 : ℝ) ≤ q / p := (le_div_iff₀ hp).2 (by simpa using hpq)
    linarith
  have hzhalf : q / p - 1 ≤ (1 / 2 : ℝ) := by
    have : q / p ≤ (3 / 2 : ℝ) := by
      apply (div_le_iff₀ hp).2
      nlinarith
    linarith
  have hproduct : 0 ≤ (q / p - 1) * (1 / 2 - (q / p - 1)) :=
    mul_nonneg hz0 (sub_nonneg.mpr hzhalf)
  nlinarith

theorem tangent_captures_three_quarters
    (r q p : ℝ) (hr : 0 ≤ r) (hq : 0 < q) (hp : 0 < p)
    (hpq : p ≤ q) (hqp : 2 * q ≤ 3 * p) :
    (3 / 4 : ℝ) * (r / q) ≤ r * (2 * p - q) / p ^ 2 := by
  have hratio := geometric_ratio_three_quarters q p hp hpq hqp
  have hrq : 0 ≤ r / q := div_nonneg hr (le_of_lt hq)
  have hmul := mul_le_mul_of_nonneg_left hratio hrq
  calc
    (3 / 4 : ℝ) * (r / q)
        ≤ (r / q) * ((q / p) * (2 - q / p)) := by
          simpa [mul_comm] using hmul
    _ = r * (2 * p - q) / p ^ 2 := by
      field_simp [ne_of_gt hq, ne_of_gt hp]

theorem exists_three_halves_grid_scale (q : ℝ) (hq : 1 ≤ q) :
    ∃ n : ℕ, (3 / 2 : ℝ) ^ n ≤ q ∧
      2 * q < 3 * (3 / 2 : ℝ) ^ n := by
  obtain ⟨n, hnle, hnlt⟩ :=
    exists_nat_pow_near hq (by norm_num : (1 : ℝ) < 3 / 2)
  refine ⟨n, hnle, ?_⟩
  rw [pow_succ] at hnlt
  nlinarith

theorem finite_grid_tangent_captures_three_quarters
    (r q k : ℝ) (hr : 0 ≤ r) (hq : 1 ≤ q) (hqk : q ≤ 1 + 2 * k) :
    ∃ n : ℕ,
      (3 / 2 : ℝ) ^ n ≤ 1 + 2 * k ∧
      (3 / 4 : ℝ) * (r / q) ≤
        r * (2 * (3 / 2 : ℝ) ^ n - q) / ((3 / 2 : ℝ) ^ n) ^ 2 := by
  obtain ⟨n, hnle, hnratio⟩ := exists_three_halves_grid_scale q hq
  have hp : 0 < (3 / 2 : ℝ) ^ n := by positivity
  refine ⟨n, hnle.trans hqk, ?_⟩
  exact tangent_captures_three_quarters
    r q ((3 / 2 : ℝ) ^ n) hr (lt_of_lt_of_le zero_lt_one hq) hp
    hnle (le_of_lt hnratio)

/-- A finite integer tangent grid is enough for the same `3/4` envelope.
Choosing `p = ceil q` puts `q / p` in `[1/2, 1]`; unlike the geometric grid,
this representation has the elementary finite index set `1, ..., 2k+1`. -/
theorem integer_grid_tangent_captures_three_quarters
    (r q : ℝ) (k : ℕ) (hr : 0 ≤ r) (hq : 1 ≤ q)
    (hqk : q ≤ 1 + 2 * k) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 1 + 2 * k ∧
      (3 / 4 : ℝ) * (r / q) ≤
        r * (2 * (n : ℝ) - q) / (n : ℝ) ^ 2 := by
  let n := ⌈q⌉₊
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqnonneg : 0 ≤ q := le_of_lt hqpos
  have hqn : q ≤ (n : ℝ) := by
    exact Nat.le_ceil q
  have hnlt : (n : ℝ) < q + 1 := by
    exact Nat.ceil_lt_add_one hqnonneg
  have hn_le_two_q : (n : ℝ) ≤ 2 * q := by
    have hqplus : q + 1 ≤ 2 * q := by linarith
    exact (le_of_lt hnlt).trans hqplus
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le hqpos hqn
  have hn_one : 1 ≤ n := by exact_mod_cast hnpos
  have hn_bound : n ≤ 1 + 2 * k := by
    apply Nat.ceil_le.mpr
    simpa using hqk
  refine ⟨n, hn_one, hn_bound, ?_⟩
  have hzhalf : (1 / 2 : ℝ) ≤ q / (n : ℝ) := by
    apply (le_div_iff₀ hnpos).2
    linarith
  have hzone : q / (n : ℝ) ≤ 1 := by
    exact (div_le_one hnpos).2 hqn
  have hproduct : 0 ≤
      (q / (n : ℝ) - 1 / 2) * (3 / 2 - q / (n : ℝ)) :=
    mul_nonneg (sub_nonneg.mpr hzhalf) (sub_nonneg.mpr (by linarith))
  have hratio : (3 / 4 : ℝ) ≤
      (q / (n : ℝ)) * (2 - q / (n : ℝ)) := by
    nlinarith
  have hrq : 0 ≤ r / q := div_nonneg hr (le_of_lt hqpos)
  have hmul := mul_le_mul_of_nonneg_left hratio hrq
  calc
    (3 / 4 : ℝ) * (r / q)
        ≤ (r / q) * ((q / (n : ℝ)) * (2 - q / (n : ℝ))) := by
          simpa [mul_comm] using hmul
    _ = r * (2 * (n : ℝ) - q) / (n : ℝ) ^ 2 := by
      field_simp [ne_of_gt hqpos, ne_of_gt hnpos]

theorem reservoir_coordinate_dominates_half
    (k reservoirMass otherMass : ℝ)
    (hbudget : reservoirMass + otherMass ≤ 2 * k) :
    reservoirMass / 2 ≤ k - otherMass / 2 := by
  linarith

theorem reservoir_map_one_lipschitz
    (otherL1 signedOther totalL1 : ℝ)
    (hsigned : |signedOther| ≤ otherL1)
    (htotal : otherL1 ≤ totalL1) :
    otherL1 / 2 + |signedOther| / 2 ≤ totalL1 := by
  linarith

theorem shrinking_reset_charges_height (s previous following : ℝ) :
    2 * s ≤ |s - previous| + |s - following| + previous + following := by
  have hprevious : s - previous ≤ |s - previous| := le_abs_self (s - previous)
  have hfollowing : s - following ≤ |s - following| := le_abs_self (s - following)
  linarith

theorem shrinking_reset_charges_moe_service
    (s previous following δPrevious δFollowing : ℝ)
    (hprevious : previous ≤ 2 * δPrevious)
    (hfollowing : following ≤ 2 * δFollowing) :
    (8 / 3 : ℝ) * s ≤
      (4 / 3 : ℝ) * (|s - previous| + |s - following|) +
        (8 / 3 : ℝ) * (δPrevious + δFollowing) := by
  have hheight := shrinking_reset_charges_height s previous following
  linarith

theorem integral_competitive_from_positive_body
    (C k opt M movement service integralCost : ℝ)
    (hbody : M ≤ C * (k + 2 * opt))
    (hmovement : movement ≤ M + 2 * k)
    (hservice : service ≤ (4 / 3 : ℝ) * M + 16 / 3)
    (hround : integralCost ≤ movement + 3 * service) :
    integralCost ≤ 10 * C * opt + (5 * C + 2) * k + 16 := by
  have hfive : integralCost ≤ 5 * M + 2 * k + 16 := by
    linarith
  have hbody5 : 5 * M ≤ 5 * (C * (k + 2 * opt)) := by
    linarith
  calc
    integralCost ≤ 5 * M + 2 * k + 16 := hfive
    _ ≤ 5 * (C * (k + 2 * opt)) + 2 * k + 16 := by linarith
    _ = 10 * C * opt + (5 * C + 2) * k + 16 := by ring

end DynamicMoePositiveBody
