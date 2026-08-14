import LeanProject.DynamicMoeSemantics

/-!
Primitive path-level boundary for Huang--Lou--Xiao Lazy Threshold Rounding.
The seed in `RandomizedOnlineAlgorithm` is sampled once and shared by every
round. Exact budgets and the integral initial state are carried by the types.
-/

open scoped BigOperators
open MeasureTheory

namespace DynamicMoeLazyThresholdInterface

open DynamicMoeSemantics

noncomputable def integralServiceFrom {m k : ℕ} :
    List (Workload m) → List (IntegralAllocation m k) → ℝ
  | [], [] => 0
  | request :: requests, allocation :: allocations =>
      latency request allocation + integralServiceFrom requests allocations
  | _, _ => 0

def integralMovementFrom {m k : ℕ} (initial : IntegralAllocation m k) :
    List (IntegralAllocation m k) → ℝ
  | [] => 0
  | allocation :: allocations =>
      movement initial allocation + integralMovementFrom allocation allocations

noncomputable def realizedIntegralService {m k : ℕ}
    (algorithm : RandomizedOnlineAlgorithm m k) (requests : List (Workload m))
    (seed : algorithm.Seed) : ℝ :=
  integralServiceFrom requests (algorithm.run seed requests)

def realizedIntegralMovement {m k : ℕ}
    (algorithm : RandomizedOnlineAlgorithm m k) (initial : IntegralAllocation m k)
    (requests : List (Workload m)) (seed : algorithm.Seed) : ℝ :=
  integralMovementFrom initial (algorithm.run seed requests)

theorem pathCostFrom_eq_service_add_movement {m k : ℕ}
    (initial : IntegralAllocation m k) :
    ∀ (requests : List (Workload m)) (allocations : List (IntegralAllocation m k)),
      allocations.length = requests.length →
      pathCostFrom initial requests allocations =
        integralServiceFrom requests allocations +
          integralMovementFrom initial allocations := by
  intro requests
  induction requests generalizing initial with
  | nil =>
      intro allocations hlength
      cases allocations with
      | nil => simp [pathCostFrom, integralServiceFrom, integralMovementFrom]
      | cons allocation allocations => simp at hlength
  | cons request requests inductionHypothesis =>
      intro allocations hlength
      cases allocations with
      | nil => simp at hlength
      | cons allocation allocations =>
          have htail : allocations.length = requests.length := by
            simp only [List.length_cons] at hlength
            omega
          simp only [pathCostFrom, integralServiceFrom, integralMovementFrom]
          rw [inductionHypothesis allocation allocations htail]
          ring

theorem randomized_run_length {m k : ℕ}
    (algorithm : RandomizedOnlineAlgorithm m k) (seed : algorithm.Seed)
    (requests : List (Workload m)) :
    (algorithm.run seed requests).length = requests.length := by
  simp [RandomizedOnlineAlgorithm.run]

theorem realizedCost_eq_service_add_movement {m k : ℕ}
    (algorithm : RandomizedOnlineAlgorithm m k)
    (initial : IntegralAllocation m k) (requests : List (Workload m))
    (seed : algorithm.Seed) :
    algorithm.realizedCost initial requests seed =
      realizedIntegralService algorithm requests seed +
        realizedIntegralMovement algorithm initial requests seed := by
  exact pathCostFrom_eq_service_add_movement initial requests
    (algorithm.run seed requests) (randomized_run_length algorithm seed requests)

structure LazyThresholdRoundingWitness (m k : ℕ)
    (initial : IntegralAllocation m k)
    (fractional : FractionalOnlineAlgorithm m k) where
  algorithm : RandomizedOnlineAlgorithm m k
  integrableCost : algorithm.HasIntegrableCost
  initialChoice : ∀ seed, algorithm.choose seed [] = initial
  integrableService : ∀ requests : List (Workload m), by
    letI : MeasurableSpace algorithm.Seed := algorithm.measurableSeed
    exact Integrable (fun seed ↦ realizedIntegralService algorithm requests seed)
      algorithm.seedMeasure
  integrableMovement : ∀ requests : List (Workload m), by
    letI : MeasurableSpace algorithm.Seed := algorithm.measurableSeed
    exact Integrable (fun seed ↦ realizedIntegralMovement algorithm initial requests seed)
      algorithm.seedMeasure
  pointwiseService : ∀ seed, ∀ request : Workload m,
    ∀ requests : List (Workload m),
      latency ((request :: requests).getLast (by simp))
          (algorithm.choose seed (request :: requests)) ≤
        3 * fractionalLatency ((request :: requests).getLast (by simp))
          (fractional.choose (request :: requests))
  /-- Lemma 4.4's per-step expected movement guarantee, represented as the
  difference of consecutive prefix costs. The same sampled seed is used in
  both prefixes. -/
  expectedStepMovement : ∀ requests : List (Workload m), requests ≠ [] → by
    letI : MeasurableSpace algorithm.Seed := algorithm.measurableSeed
    exact
      (∫ seed, realizedIntegralMovement algorithm initial requests seed
          ∂algorithm.seedMeasure) -
        (∫ seed, realizedIntegralMovement algorithm initial requests.dropLast seed
          ∂algorithm.seedMeasure) ≤
      fractional.movementCost initial requests -
        fractional.movementCost initial requests.dropLast

/-- The exact source projection used here comprises Lemma 4.4's latency and
per-step movement items. Its polynomial-running-time conjunct is deliberately
outside this semantic competitive-ratio interface. The concrete source
construction samples one independent uniform threshold per coordinate. -/
def HasLazyThresholdRoundingPrimitive : Prop :=
  ∀ k m : ℕ, ∀ initial : IntegralAllocation m k,
    ∀ fractional : FractionalOnlineAlgorithm m k,
      Nonempty (LazyThresholdRoundingWitness m k initial fractional)

theorem expectedMovement_of_expectedStepMovement {m k : ℕ}
    {initial : IntegralAllocation m k}
    {fractional : FractionalOnlineAlgorithm m k}
    (witness : LazyThresholdRoundingWitness m k initial fractional)
    (requests : List (Workload m)) : by
    letI : MeasurableSpace witness.algorithm.Seed :=
      witness.algorithm.measurableSeed
    exact (∫ seed, realizedIntegralMovement witness.algorithm initial requests seed
      ∂witness.algorithm.seedMeasure) ≤ fractional.movementCost initial requests := by
  induction requests using List.reverseRecOn with
  | nil =>
      simp [realizedIntegralMovement, integralMovementFrom,
        RandomizedOnlineAlgorithm.run, FractionalOnlineAlgorithm.movementCost,
        FractionalOnlineAlgorithm.run, fractionalMovementFrom]
  | append_singleton requests request inductionHypothesis =>
      have hstep := witness.expectedStepMovement (requests ++ [request]) (by simp)
      simp only [List.dropLast_concat] at hstep
      linarith

abbrev NonemptyWorkloadHistory (m : ℕ) :=
  {history : List (Workload m) // history ≠ []}

theorem take_current_nonempty {α : Type*} (values : List α) (round : ℕ)
    (hround : round < values.length) : values.take (round + 1) ≠ [] := by
  intro hempty
  have hlength := congrArg List.length hempty
  rw [List.length_take, Nat.min_eq_left (Nat.succ_le_iff.mpr hround)] at hlength
  simp at hlength

theorem getLast_take_current {α : Type*} (values : List α) (round : ℕ)
    (hround : round < values.length) :
    (values.take (round + 1)).getLast
        (take_current_nonempty values round hround) = values[round] := by
  rw [List.getLast_eq_getElem]
  simp [List.length_take, Nat.min_eq_left (Nat.succ_le_iff.mpr hround)]

def revealedHistories {m : ℕ} (requests : List (Workload m)) :
    List (NonemptyWorkloadHistory m) :=
  List.ofFn fun round : Fin requests.length ↦
    ⟨requests.take (round.val + 1),
      take_current_nonempty requests round.val round.isLt⟩

def revealedRequest {m : ℕ} (history : NonemptyWorkloadHistory m) :
    Workload m := history.val.getLast history.property

theorem revealedRequests_eq {m : ℕ} (requests : List (Workload m)) :
    (revealedHistories requests).map revealedRequest = requests := by
  apply List.ext_getElem
  · simp [revealedHistories]
  · intro round hleft hright
    simp [revealedHistories, revealedRequest]
    simpa using getLast_take_current requests round hright

theorem revealedRandomizedRun_eq {m k : ℕ}
    (algorithm : RandomizedOnlineAlgorithm m k) (seed : algorithm.Seed)
    (requests : List (Workload m)) :
    (revealedHistories requests).map
        (fun history ↦ algorithm.choose seed history.val) =
      algorithm.run seed requests := by
  unfold RandomizedOnlineAlgorithm.run
  apply List.ext_getElem
  · simp [revealedHistories]
  · intro round hleft hright
    simp [revealedHistories]

theorem revealedFractionalRun_eq {m k : ℕ}
    (algorithm : FractionalOnlineAlgorithm m k)
    (requests : List (Workload m)) :
    (revealedHistories requests).map
        (fun history ↦ algorithm.choose history.val) =
      algorithm.run requests := by
  unfold FractionalOnlineAlgorithm.run
  apply List.ext_getElem
  · simp [revealedHistories]
  · intro round hleft hright
    simp [revealedHistories]

theorem integralServiceFrom_revealed {m k : ℕ}
    (algorithm : RandomizedOnlineAlgorithm m k) (seed : algorithm.Seed) :
    ∀ histories : List (NonemptyWorkloadHistory m),
    integralServiceFrom (histories.map revealedRequest)
        (histories.map fun history ↦ algorithm.choose seed history.val) =
      (histories.map fun history ↦
        latency (revealedRequest history)
          (algorithm.choose seed history.val)).sum := by
  intro histories
  induction histories with
  | nil => simp [integralServiceFrom]
  | cons history histories inductionHypothesis =>
      simp only [List.map_cons, integralServiceFrom, List.sum_cons]
      rw [inductionHypothesis]

theorem fractionalServiceFrom_revealed {m k : ℕ}
    (algorithm : FractionalOnlineAlgorithm m k) :
    ∀ histories : List (NonemptyWorkloadHistory m),
    fractionalServiceFrom (histories.map revealedRequest)
        (histories.map fun history ↦ algorithm.choose history.val) =
      (histories.map fun history ↦
        fractionalLatency (revealedRequest history)
          (algorithm.choose history.val)).sum := by
  intro histories
  induction histories with
  | nil => simp [fractionalServiceFrom]
  | cons history histories inductionHypothesis =>
      simp only [List.map_cons, fractionalServiceFrom, List.sum_cons]
      rw [inductionHypothesis]

theorem history_pointwiseService {m k : ℕ}
    {initial : IntegralAllocation m k}
    {fractional : FractionalOnlineAlgorithm m k}
    (witness : LazyThresholdRoundingWitness m k initial fractional)
    (seed : witness.algorithm.Seed) (history : NonemptyWorkloadHistory m) :
    latency (revealedRequest history)
        (witness.algorithm.choose seed history.val) ≤
      3 * fractionalLatency (revealedRequest history)
        (fractional.choose history.val) := by
  rcases history with ⟨history, hnonempty⟩
  cases history with
  | nil => exact (hnonempty rfl).elim
  | cons request requests =>
      simpa [revealedRequest] using
        witness.pointwiseService seed request requests

theorem serviceTerms_le {m k : ℕ}
    {initial : IntegralAllocation m k}
    {fractional : FractionalOnlineAlgorithm m k}
    (witness : LazyThresholdRoundingWitness m k initial fractional)
    (seed : witness.algorithm.Seed) :
    ∀ histories : List (NonemptyWorkloadHistory m),
    (histories.map fun history ↦
        latency (revealedRequest history)
          (witness.algorithm.choose seed history.val)).sum ≤
      3 * (histories.map fun history ↦
        fractionalLatency (revealedRequest history)
          (fractional.choose history.val)).sum := by
  intro histories
  induction histories with
  | nil => simp
  | cons history histories inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      have hhead := history_pointwiseService witness seed history
      linarith

theorem realizedService_le {m k : ℕ}
    {initial : IntegralAllocation m k}
    {fractional : FractionalOnlineAlgorithm m k}
    (witness : LazyThresholdRoundingWitness m k initial fractional)
    (seed : witness.algorithm.Seed) (requests : List (Workload m)) :
    realizedIntegralService witness.algorithm requests seed ≤
      3 * fractional.serviceCost requests := by
  unfold realizedIntegralService FractionalOnlineAlgorithm.serviceCost
  calc
    integralServiceFrom requests (witness.algorithm.run seed requests) =
        ((revealedHistories requests).map fun history ↦
          latency (revealedRequest history)
            (witness.algorithm.choose seed history.val)).sum := by
      calc
        integralServiceFrom requests (witness.algorithm.run seed requests) =
            integralServiceFrom
              ((revealedHistories requests).map revealedRequest)
              ((revealedHistories requests).map fun history ↦
                witness.algorithm.choose seed history.val) := by
          rw [revealedRequests_eq requests,
            revealedRandomizedRun_eq witness.algorithm seed requests]
        _ = _ := integralServiceFrom_revealed witness.algorithm seed
          (revealedHistories requests)
    _ ≤ 3 * ((revealedHistories requests).map fun history ↦
        fractionalLatency (revealedRequest history)
          (fractional.choose history.val)).sum :=
      serviceTerms_le witness seed (revealedHistories requests)
    _ = 3 * fractionalServiceFrom requests (fractional.run requests) := by
      congr 1
      symm
      calc
        fractionalServiceFrom requests (fractional.run requests) =
            fractionalServiceFrom
              ((revealedHistories requests).map revealedRequest)
              ((revealedHistories requests).map fun history ↦
                fractional.choose history.val) := by
          rw [revealedRequests_eq requests,
            revealedFractionalRun_eq fractional requests]
        _ = _ := fractionalServiceFrom_revealed fractional
          (revealedHistories requests)

theorem expectedCost_le_fractional {m k : ℕ}
    {initial : IntegralAllocation m k}
    {fractional : FractionalOnlineAlgorithm m k}
    (witness : LazyThresholdRoundingWitness m k initial fractional)
    (requests : List (Workload m)) :
    witness.algorithm.expectedCost initial requests ≤
      fractional.movementCost initial requests +
        3 * fractional.serviceCost requests := by
  letI : MeasurableSpace witness.algorithm.Seed :=
    witness.algorithm.measurableSeed
  letI : IsProbabilityMeasure witness.algorithm.seedMeasure :=
    witness.algorithm.probability
  have hserviceIntegrable := witness.integrableService requests
  have hmovementIntegrable := witness.integrableMovement requests
  have hserviceExpected :
      (∫ seed, realizedIntegralService witness.algorithm requests seed
          ∂witness.algorithm.seedMeasure) ≤
        3 * fractional.serviceCost requests := by
    have hconstant : Integrable
        (fun _ : witness.algorithm.Seed ↦ 3 * fractional.serviceCost requests)
        witness.algorithm.seedMeasure := integrable_const _
    have hmono := integral_mono hserviceIntegrable hconstant
      (fun seed ↦ realizedService_le witness seed requests)
    simpa using hmono
  have hmovementExpected := expectedMovement_of_expectedStepMovement witness requests
  have hsplit :
      (∫ seed, witness.algorithm.realizedCost initial requests seed
          ∂witness.algorithm.seedMeasure) =
        (∫ seed, realizedIntegralService witness.algorithm requests seed
          ∂witness.algorithm.seedMeasure) +
        (∫ seed, realizedIntegralMovement witness.algorithm initial requests seed
          ∂witness.algorithm.seedMeasure) := by
    calc
      (∫ seed, witness.algorithm.realizedCost initial requests seed
          ∂witness.algorithm.seedMeasure) =
          ∫ seed, (realizedIntegralService witness.algorithm requests seed +
            realizedIntegralMovement witness.algorithm initial requests seed)
              ∂witness.algorithm.seedMeasure := by
        apply integral_congr_ae
        filter_upwards [] with seed
        exact realizedCost_eq_service_add_movement
          witness.algorithm initial requests seed
      _ = _ := integral_add hserviceIntegrable hmovementIntegrable
  unfold RandomizedOnlineAlgorithm.expectedCost
  rw [hsplit]
  linarith

theorem hasLazyThresholdRounding_of_primitive
    (hprimitive : HasLazyThresholdRoundingPrimitive) :
    HasLazyThresholdRounding := by
  intro k m initial fractional
  obtain ⟨witness⟩ := hprimitive k m initial fractional
  exact ⟨witness.algorithm, witness.integrableCost,
    fun requests ↦ expectedCost_le_fractional witness requests⟩

end DynamicMoeLazyThresholdInterface
