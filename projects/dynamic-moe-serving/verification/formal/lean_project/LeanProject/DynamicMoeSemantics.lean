import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/-!
Semantic surface for the Dynamic MoE competitive claim.

The theorem at the end is deliberately named `..._of_reduction_witness`: it
formalizes the online algorithm, causality, expectation, instance quantifiers,
offline optimum, and horizon-independent additive term, but it does not pretend
that the cited positive-body chaser and lazy-threshold rounding have already
been formalized. Their remaining obligation is isolated in
`HasReductionWitness`.
-/

open scoped BigOperators
open MeasureTheory

namespace DynamicMoeSemantics

structure Workload (m : ℕ) where
  value : Fin m → ℝ
  nonnegative : ∀ i, 0 ≤ value i

structure IntegralAllocation (m k : ℕ) where
  value : Fin m → ℕ
  budget : ∑ i, value i = k

structure FractionalAllocation (m k : ℕ) where
  value : Fin m → ℝ
  nonnegative : ∀ i, 0 ≤ value i
  budget : ∑ i, value i = k

structure AugmentedAllocation (m k : ℕ) where
  value : Fin m → ℝ
  nonnegative : ∀ i, 0 ≤ value i
  budget : ∑ i, value i ≤ 2 * k

/-- Divide the augmented allocation by two and distribute the unused budget
uniformly. This is the symmetric replacement for a distinguished reservoir
expert. -/
noncomputable def AugmentedAllocation.toBalancedFractional {m k : ℕ}
    (allocation : AugmentedAllocation m k) (hm : 0 < m) :
    FractionalAllocation m k := by
  let total := ∑ i, allocation.value i
  let slack := ((k : ℝ) - total / 2) / m
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hslack : 0 ≤ slack := by
    dsimp [slack, total]
    have hhalf : (∑ i, allocation.value i) / 2 ≤ (k : ℝ) := by
      linarith [allocation.budget]
    exact div_nonneg (sub_nonneg.mpr hhalf) (le_of_lt hmReal)
  refine {
    value := fun i ↦ allocation.value i / 2 + slack
    nonnegative := fun i ↦ add_nonneg (div_nonneg (allocation.nonnegative i) (by norm_num)) hslack
    budget := ?_
  }
  dsimp [slack, total]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_div]
  simp
  field_simp [ne_of_gt hmReal]
  ring

def IntegralAllocation.toFractional {m k : ℕ}
    (allocation : IntegralAllocation m k) : FractionalAllocation m k where
  value i := allocation.value i
  nonnegative i := by positivity
  budget := by exact_mod_cast allocation.budget

noncomputable def latency {m k : ℕ} (request : Workload m)
    (allocation : IntegralAllocation m k) : ℝ :=
  (List.ofFn fun i : Fin m ↦
    request.value i / (1 + allocation.value i : ℕ)).foldl max 0

def movement {m k : ℕ} (first second : IntegralAllocation m k) : ℝ :=
  ∑ i, |(first.value i : ℝ) - second.value i|

noncomputable def fractionalLatency {m k : ℕ} (request : Workload m)
    (allocation : FractionalAllocation m k) : ℝ :=
  (List.ofFn fun i : Fin m ↦
    request.value i / (1 + allocation.value i)).foldl max 0

def fractionalMovement {m k : ℕ}
    (first second : FractionalAllocation m k) : ℝ :=
  ∑ i, |first.value i - second.value i|

theorem balanced_coordinate_dominates_half {m k : ℕ}
    (allocation : AugmentedAllocation m k) (hm : 0 < m) (i : Fin m) :
    allocation.value i / 2 ≤ (allocation.toBalancedFractional hm).value i := by
  change allocation.value i / 2 ≤ allocation.value i / 2 +
    (((k : ℝ) - (∑ j, allocation.value j) / 2) / m)
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hhalf : (∑ j, allocation.value j) / 2 ≤ (k : ℝ) := by
    linarith [allocation.budget]
  have hslack : 0 ≤ ((k : ℝ) - (∑ j, allocation.value j) / 2) / m :=
    div_nonneg (sub_nonneg.mpr hhalf) (le_of_lt hmReal)
  linarith

theorem balanced_map_one_lipschitz {m k : ℕ}
    (first second : AugmentedAllocation m k) (hm : 0 < m) :
    fractionalMovement (first.toBalancedFractional hm)
        (second.toBalancedFractional hm) ≤
      ∑ i, |first.value i - second.value i| := by
  let firstTotal := ∑ i, first.value i
  let secondTotal := ∑ i, second.value i
  let firstSlack := ((k : ℝ) - firstTotal / 2) / m
  let secondSlack := ((k : ℝ) - secondTotal / 2) / m
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hcoordinate : ∀ i : Fin m,
      |(first.toBalancedFractional hm).value i -
          (second.toBalancedFractional hm).value i| ≤
        |first.value i - second.value i| / 2 +
          |firstSlack - secondSlack| := by
    intro i
    change |(first.value i / 2 + firstSlack) -
        (second.value i / 2 + secondSlack)| ≤ _
    calc
      |(first.value i / 2 + firstSlack) -
          (second.value i / 2 + secondSlack)|
          = |(first.value i - second.value i) / 2 +
              (firstSlack - secondSlack)| := by ring_nf
      _ ≤ |(first.value i - second.value i) / 2| +
          |firstSlack - secondSlack| := abs_add_le _ _
      _ = |first.value i - second.value i| / 2 +
          |firstSlack - secondSlack| := by rw [abs_div]; norm_num
  have habssum :
      |∑ i, (first.value i - second.value i)| ≤
        ∑ i, |first.value i - second.value i| := by
    simpa using Finset.abs_sum_le_sum_abs
      (fun i : Fin m ↦ first.value i - second.value i) Finset.univ
  have hslack :
      (m : ℝ) * |firstSlack - secondSlack| ≤
        (∑ i, |first.value i - second.value i|) / 2 := by
    have hidentity : firstSlack - secondSlack =
        -(∑ i, (first.value i - second.value i)) / (2 * m) := by
      dsimp [firstSlack, secondSlack, firstTotal, secondTotal]
      rw [Finset.sum_sub_distrib]
      field_simp [ne_of_gt hmReal]
      ring
    rw [hidentity, abs_div, abs_neg, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hmReal]
    have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmReal
    have hcancel : (m : ℝ) *
        (|∑ i, (first.value i - second.value i)| / (2 * m)) =
        |∑ i, (first.value i - second.value i)| / 2 := by
      field_simp [hmne]
    rw [hcancel]
    linarith
  unfold fractionalMovement
  calc
    (∑ i, |(first.toBalancedFractional hm).value i -
        (second.toBalancedFractional hm).value i|)
        ≤ ∑ i, (|first.value i - second.value i| / 2 +
          |firstSlack - secondSlack|) :=
            Finset.sum_le_sum fun i _ ↦ hcoordinate i
    _ = (∑ i, |first.value i - second.value i|) / 2 +
        (m : ℝ) * |firstSlack - secondSlack| := by
          rw [Finset.sum_add_distrib, Finset.sum_div]
          simp
    _ ≤ ∑ i, |first.value i - second.value i| := by linarith

theorem balanced_map_reciprocal_loss_two {m k : ℕ}
    (request : Workload m) (allocation : AugmentedAllocation m k)
    (hm : 0 < m) (i : Fin m) :
    request.value i /
        (1 + (allocation.toBalancedFractional hm).value i) ≤
      (2 * request.value i) / (1 + allocation.value i) := by
  have hx : allocation.value i / 2 ≤
      (allocation.toBalancedFractional hm).value i :=
    balanced_coordinate_dominates_half allocation hm i
  have hleft : 0 < 1 + (allocation.toBalancedFractional hm).value i := by
    have := (allocation.toBalancedFractional hm).nonnegative i
    linarith
  have hright : 0 < 1 + allocation.value i := by
    have := allocation.nonnegative i
    linarith
  apply (div_le_div_iff₀ hleft hright).2
  have hr := request.nonnegative i
  nlinarith

theorem foldl_max_le_of_forall_mem_le (values : List ℝ)
    (initial bound : ℝ) (hinitial : initial ≤ bound)
    (hvalues : ∀ value ∈ values, value ≤ bound) :
    values.foldl max initial ≤ bound := by
  induction values generalizing initial with
  | nil => simpa using hinitial
  | cons value values inductionHypothesis =>
      apply inductionHypothesis (max initial value)
      · exact max_le hinitial (hvalues value (by simp))
      · intro candidate hcandidate
        exact hvalues candidate (by simp [hcandidate])

theorem balanced_map_service_loss_eight_thirds {m k : ℕ}
    (request : Workload m) (allocation : AugmentedAllocation m k)
    (hm : 0 < m) (height : ℝ) (hheight : 0 ≤ height)
    (henvelope : ∀ i : Fin m,
      (3 / 4 : ℝ) *
          (request.value i / (1 + allocation.value i)) ≤ height) :
    fractionalLatency request (allocation.toBalancedFractional hm) ≤
      (8 / 3 : ℝ) * height := by
  unfold fractionalLatency
  apply foldl_max_le_of_forall_mem_le
  · positivity
  · rw [List.forall_mem_ofFn_iff]
    intro i
    have hmap := balanced_map_reciprocal_loss_two request allocation hm i
    have hmap' : request.value i /
        (1 + (allocation.toBalancedFractional hm).value i) ≤
        2 * (request.value i / (1 + allocation.value i)) := by
      simpa [mul_div_assoc] using hmap
    linarith [henvelope i]

noncomputable def fractionalServiceFrom {m k : ℕ} :
    List (Workload m) → List (FractionalAllocation m k) → ℝ
  | [], [] => 0
  | request :: requests, allocation :: allocations =>
      fractionalLatency request allocation +
        fractionalServiceFrom requests allocations
  | _, _ => 0

def fractionalMovementFrom {m k : ℕ}
    (initial : FractionalAllocation m k) :
    List (FractionalAllocation m k) → ℝ
  | [] => 0
  | allocation :: allocations =>
      fractionalMovement initial allocation +
        fractionalMovementFrom allocation allocations

structure FractionalOnlineAlgorithm (m k : ℕ) where
  /-- The allocation depends only on the revealed history, including the
  current request. -/
  choose : List (Workload m) → FractionalAllocation m k

def FractionalOnlineAlgorithm.run {m k : ℕ}
    (algorithm : FractionalOnlineAlgorithm m k)
    (requests : List (Workload m)) : List (FractionalAllocation m k) :=
  (List.range requests.length).map fun t ↦
    algorithm.choose (requests.take (t + 1))

noncomputable def FractionalOnlineAlgorithm.serviceCost {m k : ℕ}
    (algorithm : FractionalOnlineAlgorithm m k)
    (requests : List (Workload m)) : ℝ :=
  fractionalServiceFrom requests (algorithm.run requests)

def FractionalOnlineAlgorithm.movementCost {m k : ℕ}
    (algorithm : FractionalOnlineAlgorithm m k)
    (initial : IntegralAllocation m k)
    (requests : List (Workload m)) : ℝ :=
  fractionalMovementFrom initial.toFractional (algorithm.run requests)

noncomputable def pathCostFrom {m k : ℕ} (initial : IntegralAllocation m k) :
    List (Workload m) → List (IntegralAllocation m k) → ℝ
  | [], [] => 0
  | request :: requests, allocation :: allocations =>
      latency request allocation + movement initial allocation +
        pathCostFrom allocation requests allocations
  | _, _ => 0

noncomputable def offlineOpt {m k : ℕ} (initial : IntegralAllocation m k)
    (requests : List (Workload m)) : ℝ :=
  sInf {cost : ℝ | ∃ path : List (IntegralAllocation m k),
    path.length = requests.length ∧ cost = pathCostFrom initial requests path}

structure RandomizedOnlineAlgorithm (m k : ℕ) where
  Seed : Type
  measurableSeed : MeasurableSpace Seed
  seedMeasure : @Measure Seed measurableSeed
  probability : @IsProbabilityMeasure Seed measurableSeed seedMeasure
  /-- Depending only on the revealed request history is the causality
  condition. The seed is sampled once and shared across all rounds. -/
  choose : Seed → List (Workload m) → IntegralAllocation m k

def RandomizedOnlineAlgorithm.run {m k : ℕ}
    (algorithm : RandomizedOnlineAlgorithm m k) (seed : algorithm.Seed)
    (requests : List (Workload m)) : List (IntegralAllocation m k) :=
  (List.range requests.length).map fun t ↦
    algorithm.choose seed (requests.take (t + 1))

noncomputable def RandomizedOnlineAlgorithm.realizedCost {m k : ℕ}
    (algorithm : RandomizedOnlineAlgorithm m k)
    (initial : IntegralAllocation m k) (requests : List (Workload m))
    (seed : algorithm.Seed) : ℝ :=
  pathCostFrom initial requests (algorithm.run seed requests)

noncomputable def RandomizedOnlineAlgorithm.expectedCost {m k : ℕ}
    (algorithm : RandomizedOnlineAlgorithm m k)
    (initial : IntegralAllocation m k) (requests : List (Workload m)) : ℝ := by
  letI : MeasurableSpace algorithm.Seed := algorithm.measurableSeed
  exact ∫ seed, algorithm.realizedCost initial requests seed ∂algorithm.seedMeasure

/-- Rules out the Bochner-integral convention that assigns zero to an
unmeasurable or non-integrable cost. -/
def RandomizedOnlineAlgorithm.HasIntegrableCost {m k : ℕ}
    (algorithm : RandomizedOnlineAlgorithm m k) : Prop := by
  letI : MeasurableSpace algorithm.Seed := algorithm.measurableSeed
  exact ∀ initial : IntegralAllocation m k, ∀ requests : List (Workload m),
    Integrable (fun seed ↦ algorithm.realizedCost initial requests seed)
      algorithm.seedMeasure

def HasCompetitiveUpperForK (k : ℕ) (Γ : ℝ) : Prop :=
  ∀ m : ℕ, 0 < m → ∃ additive : ℝ, 0 ≤ additive ∧
    ∀ initial : IntegralAllocation m k,
      ∃ algorithm : RandomizedOnlineAlgorithm m k,
        algorithm.HasIntegrableCost ∧ ∀ requests : List (Workload m),
          algorithm.expectedCost initial requests ≤
            Γ * offlineOpt initial requests + additive

def HasUniformConstantUpper : Prop :=
  ∃ Γ : ℝ, 1 ≤ Γ ∧ ∀ k : ℕ, 1 ≤ k → HasCompetitiveUpperForK k Γ

/-- The positive-body construction's deterministic fractional output. Movement
and service are computed from the stated causal fractional path. -/
structure FractionalReductionWitness (C : ℝ) (m k : ℕ)
    (initial : IntegralAllocation m k) where
  algorithm : FractionalOnlineAlgorithm m k
  bodyMovement : List (Workload m) → ℝ
  bodyBound : ∀ requests,
    bodyMovement requests ≤ C * ((k : ℝ) + 2 * offlineOpt initial requests)
  movementBridge : ∀ requests,
    algorithm.movementCost initial requests ≤ bodyMovement requests + 2 * k
  serviceBridge : ∀ requests,
    algorithm.serviceCost requests ≤
      (4 / 3 : ℝ) * bodyMovement requests + 16 / 3

def HasPositiveBodyFractionalReduction (C : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ m : ℕ, 0 < m →
    ∀ initial : IntegralAllocation m k,
      Nonempty (FractionalReductionWitness C m k initial)

/-- The exact all-parameter surface of lazy threshold rounding, specialized to
a causal exact-budget fractional algorithm. -/
def HasLazyThresholdRounding : Prop :=
  ∀ k m : ℕ, ∀ initial : IntegralAllocation m k,
    ∀ fractional : FractionalOnlineAlgorithm m k,
      ∃ algorithm : RandomizedOnlineAlgorithm m k,
        algorithm.HasIntegrableCost ∧ ∀ requests,
          algorithm.expectedCost initial requests ≤
            fractional.movementCost initial requests +
              3 * fractional.serviceCost requests

/-- Composition witness whose fractional costs are definitionally tied to one
causal path, rather than supplied as unconstrained summaries. -/
structure ReductionWitness (C : ℝ) (m k : ℕ)
    (initial : IntegralAllocation m k) where
  fractional : FractionalOnlineAlgorithm m k
  algorithm : RandomizedOnlineAlgorithm m k
  integrableCost : algorithm.HasIntegrableCost
  bodyMovement : List (Workload m) → ℝ
  bodyBound : ∀ requests,
    bodyMovement requests ≤ C * ((k : ℝ) + 2 * offlineOpt initial requests)
  movementBridge : ∀ requests,
    fractional.movementCost initial requests ≤ bodyMovement requests + 2 * k
  serviceBridge : ∀ requests,
    fractional.serviceCost requests ≤
      (4 / 3 : ℝ) * bodyMovement requests + 16 / 3
  roundingBridge : ∀ requests,
    algorithm.expectedCost initial requests ≤
      fractional.movementCost initial requests +
        3 * fractional.serviceCost requests

def HasReductionWitness (C : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ m : ℕ, 0 < m →
    ∀ initial : IntegralAllocation m k, Nonempty (ReductionWitness C m k initial)

theorem has_reduction_witness_of_interfaces
    (C : ℝ) (hpositive : HasPositiveBodyFractionalReduction C)
    (hrounding : HasLazyThresholdRounding) :
    HasReductionWitness C := by
  intro k hk m hm initial
  obtain ⟨fractional⟩ := hpositive k hk m hm initial
  obtain ⟨algorithm, hintegrable, hround⟩ :=
    hrounding k m initial fractional.algorithm
  exact ⟨{
    fractional := fractional.algorithm
    algorithm := algorithm
    integrableCost := hintegrable
    bodyMovement := fractional.bodyMovement
    bodyBound := fractional.bodyBound
    movementBridge := fractional.movementBridge
    serviceBridge := fractional.serviceBridge
    roundingBridge := hround
  }⟩

theorem uniform_constant_upper_of_reduction_witness
    (C : ℝ) (hC : 1 ≤ C) (hwitness : HasReductionWitness C) :
    HasUniformConstantUpper := by
  refine ⟨10 * C, by nlinarith, ?_⟩
  intro k hk m hm
  refine ⟨(5 * C + 2) * k + 16, ?_, ?_⟩
  · positivity
  intro initial
  obtain ⟨witness⟩ := hwitness k hk m hm initial
  refine ⟨witness.algorithm, witness.integrableCost, ?_⟩
  intro requests
  have hfive :
      witness.algorithm.expectedCost initial requests ≤
        5 * witness.bodyMovement requests + 2 * k + 16 := by
    linarith [witness.movementBridge requests,
      witness.serviceBridge requests, witness.roundingBridge requests]
  have hbody :
      5 * witness.bodyMovement requests ≤
        5 * (C * ((k : ℝ) + 2 * offlineOpt initial requests)) := by
    linarith [witness.bodyBound requests]
  calc
    witness.algorithm.expectedCost initial requests
        ≤ 5 * witness.bodyMovement requests + 2 * k + 16 := hfive
    _ ≤ 5 * (C * ((k : ℝ) + 2 * offlineOpt initial requests)) +
        2 * k + 16 := by linarith
    _ = 10 * C * offlineOpt initial requests +
        ((5 * C + 2) * k + 16) := by ring

theorem uniform_constant_upper_of_interfaces
    (C : ℝ) (hC : 1 ≤ C)
    (hpositive : HasPositiveBodyFractionalReduction C)
    (hrounding : HasLazyThresholdRounding) :
    HasUniformConstantUpper :=
  uniform_constant_upper_of_reduction_witness C hC
    (has_reduction_witness_of_interfaces C hpositive hrounding)

end DynamicMoeSemantics
