import Mathlib.Tactic
import LeanProject.DynamicMoeSemantics

open scoped BigOperators
open MeasureTheory

namespace DynamicMoeSemantics

theorem foldl_max_nonnegative (values : List ℝ) (initial : ℝ)
    (hinitial : 0 ≤ initial) : 0 ≤ values.foldl max initial := by
  induction values generalizing initial with
  | nil => simpa using hinitial
  | cons value values inductionHypothesis =>
      apply inductionHypothesis
      exact hinitial.trans (le_max_left initial value)

theorem latency_nonnegative {m k : ℕ} (request : Workload m)
    (allocation : IntegralAllocation m k) : 0 ≤ latency request allocation := by
  unfold latency
  exact foldl_max_nonnegative _ 0 (le_refl 0)

theorem movement_nonnegative {m k : ℕ}
    (first second : IntegralAllocation m k) : 0 ≤ movement first second := by
  unfold movement
  positivity

theorem pathCostFrom_nonnegative {m k : ℕ}
    (initial : IntegralAllocation m k) :
    ∀ requests path, 0 ≤ pathCostFrom initial requests path := by
  intro requests
  induction requests generalizing initial with
  | nil =>
      intro path
      cases path <;> simp [pathCostFrom]
  | cons request requests inductionHypothesis =>
      intro path
      cases path with
      | nil => simp [pathCostFrom]
      | cons allocation allocations =>
          simp only [pathCostFrom]
          have hlatency := latency_nonnegative request allocation
          have hmovement := movement_nonnegative initial allocation
          have hrest := inductionHypothesis allocation allocations
          linarith

theorem randomized_run_length {m k : ℕ}
    (algorithm : RandomizedOnlineAlgorithm m k) (seed : algorithm.Seed)
    (requests : List (Workload m)) :
    (algorithm.run seed requests).length = requests.length := by
  simp [RandomizedOnlineAlgorithm.run]

theorem offlineOpt_le_pathCost {m k : ℕ}
    (initial : IntegralAllocation m k) (requests : List (Workload m))
    (path : List (IntegralAllocation m k))
    (hlen : path.length = requests.length) :
    offlineOpt initial requests ≤ pathCostFrom initial requests path := by
  unfold offlineOpt
  apply csInf_le
  · refine ⟨0, ?_⟩
    intro cost hcost
    rcases hcost with ⟨candidate, _, rfl⟩
    exact pathCostFrom_nonnegative initial requests candidate
  · exact ⟨path, hlen, rfl⟩

theorem realizedCost_ge_offlineOpt {m k : ℕ}
    (algorithm : RandomizedOnlineAlgorithm m k)
    (initial : IntegralAllocation m k) (requests : List (Workload m))
    (seed : algorithm.Seed) :
    offlineOpt initial requests ≤ algorithm.realizedCost initial requests seed := by
  unfold RandomizedOnlineAlgorithm.realizedCost
  apply offlineOpt_le_pathCost
  exact randomized_run_length algorithm seed requests

theorem expectedCost_ge_offlineOpt {m k : ℕ}
    (algorithm : RandomizedOnlineAlgorithm m k)
    (initial : IntegralAllocation m k) (requests : List (Workload m))
    (hintegrable : algorithm.HasIntegrableCost) :
    offlineOpt initial requests ≤ algorithm.expectedCost initial requests := by
  letI : MeasurableSpace algorithm.Seed := algorithm.measurableSeed
  letI : IsProbabilityMeasure algorithm.seedMeasure := algorithm.probability
  have hconstant : Integrable
      (fun _ : algorithm.Seed ↦ offlineOpt initial requests)
      algorithm.seedMeasure := integrable_const _
  have hrealized : Integrable
      (fun seed ↦ algorithm.realizedCost initial requests seed)
      algorithm.seedMeasure := hintegrable initial requests
  have hmono := integral_mono hconstant hrealized
    (fun seed ↦ realizedCost_ge_offlineOpt algorithm initial requests seed)
  simpa [RandomizedOnlineAlgorithm.expectedCost] using hmono

def singletonWorkload (request : ℝ) (hrequest : 0 ≤ request) : Workload 1 where
  value _ := request
  nonnegative _ := hrequest

def singletonAllocation (k : ℕ) : IntegralAllocation 1 k where
  value _ := k
  budget := by simp

theorem singleton_allocation_value {k : ℕ}
    (allocation : IntegralAllocation 1 k) : allocation.value 0 = k := by
  have hbudget := allocation.budget
  simpa using hbudget

theorem singleton_latency {k : ℕ} (request : ℝ) (hrequest : 0 ≤ request)
    (allocation : IntegralAllocation 1 k) :
    latency (singletonWorkload request hrequest) allocation =
      request / (1 + (k : ℝ)) := by
  have hvalue := singleton_allocation_value allocation
  simp [latency, singletonWorkload, hvalue,
    div_nonneg hrequest (by positivity : (0 : ℝ) ≤ 1 + k)]

theorem singleton_offlineOpt_lower {k : ℕ}
    (initial : IntegralAllocation 1 k) (request : ℝ) (hrequest : 0 ≤ request) :
    request / (1 + (k : ℝ)) ≤
      offlineOpt initial [singletonWorkload request hrequest] := by
  unfold offlineOpt
  apply le_csInf
  · refine ⟨pathCostFrom initial [singletonWorkload request hrequest] [initial], ?_⟩
    exact ⟨[initial], by simp, rfl⟩
  · intro cost hcost
    rcases hcost with ⟨path, hlength, rfl⟩
    obtain ⟨allocation, rfl⟩ := List.length_eq_one_iff.mp hlength
    simp only [pathCostFrom]
    rw [singleton_latency]
    have hmovement := movement_nonnegative initial allocation
    linarith

def uniformWorkload (m : ℕ) (request : ℝ) (hrequest : 0 ≤ request) :
    Workload m where
  value _ := request
  nonnegative _ := hrequest

def twoExpertInitial (k : ℕ) : IntegralAllocation 2 k where
  value i := if i = 0 then k else 0
  budget := by simp

theorem foldl_max_ge_initial (values : List ℝ) (initial : ℝ) :
    initial ≤ values.foldl max initial := by
  induction values generalizing initial with
  | nil => simp
  | cons value values inductionHypothesis =>
      exact (le_max_left initial value).trans (inductionHypothesis (max initial value))

theorem foldl_max_ge_of_mem (values : List ℝ) (initial value : ℝ)
    (hvalue : value ∈ values) : value ≤ values.foldl max initial := by
  induction values generalizing initial with
  | nil => simp at hvalue
  | cons head values inductionHypothesis =>
      rcases List.mem_cons.mp hvalue with hhead | htail
      · rw [hhead]
        exact (le_max_right initial head).trans
          (foldl_max_ge_initial values (max initial head))
      · exact inductionHypothesis (max initial head) htail

theorem allocation_coordinate_le_budget {m k : ℕ}
    (allocation : IntegralAllocation m k) (i : Fin m) :
    allocation.value i ≤ k := by
  have hsingle : allocation.value i ≤ ∑ j, allocation.value j :=
    Finset.single_le_sum (fun j _ ↦ Nat.zero_le (allocation.value j))
      (Finset.mem_univ i)
  simpa [allocation.budget] using hsingle

theorem uniform_latency_lower {m k : ℕ} (hm : 0 < m)
    (request : ℝ) (hrequest : 0 ≤ request)
    (allocation : IntegralAllocation m k) :
    request / (1 + (k : ℝ)) ≤
      latency (uniformWorkload m request hrequest) allocation := by
  let i : Fin m := ⟨0, hm⟩
  have hcoordinate := allocation_coordinate_le_budget allocation i
  have hdenomLeft : 0 < 1 + (k : ℝ) := by positivity
  have hdenomRight : 0 < 1 + (allocation.value i : ℝ) := by positivity
  have hreciprocal : request / (1 + (k : ℝ)) ≤
      request / (1 + (allocation.value i : ℝ)) := by
    apply (div_le_div_iff₀ hdenomLeft hdenomRight).2
    have hdenominator : 1 + (allocation.value i : ℝ) ≤ 1 + (k : ℝ) := by
      exact_mod_cast Nat.add_le_add_left hcoordinate 1
    exact mul_le_mul_of_nonneg_left hdenominator hrequest
  unfold latency
  apply hreciprocal.trans
  apply foldl_max_ge_of_mem
  simp [uniformWorkload, i]

theorem uniform_offlineOpt_one_step_lower {m k : ℕ} (hm : 0 < m)
    (initial : IntegralAllocation m k) (request : ℝ) (hrequest : 0 ≤ request) :
    request / (1 + (k : ℝ)) ≤
      offlineOpt initial [uniformWorkload m request hrequest] := by
  unfold offlineOpt
  apply le_csInf
  · refine ⟨pathCostFrom initial [uniformWorkload m request hrequest] [initial], ?_⟩
    exact ⟨[initial], by simp, rfl⟩
  · intro cost hcost
    rcases hcost with ⟨path, hlength, rfl⟩
    obtain ⟨allocation, rfl⟩ := List.length_eq_one_iff.mp hlength
    simp only [pathCostFrom]
    have hlatency := uniform_latency_lower hm request hrequest allocation
    have hmovement := movement_nonnegative initial allocation
    linarith

/-- Any competitive factor with a horizon-independent additive term for the
original randomized integral Dynamic MoE problem is at least one. -/
theorem competitive_factor_lower_bound_at_least_one
    (k : ℕ) (Γ : ℝ) (hupper : HasCompetitiveUpperForK k Γ) : 1 ≤ Γ := by
  by_contra hnot
  have hΓ : Γ < 1 := lt_of_not_ge hnot
  obtain ⟨additive, hadditive, hinitial⟩ := hupper 2 (by norm_num)
  let initial := twoExpertInitial k
  obtain ⟨algorithm, hintegrable, hbound⟩ := hinitial initial
  have hgap : 0 < 1 - Γ := by linarith
  let request := ((1 + (k : ℝ)) * (additive + 1)) / (1 - Γ)
  have hrequest : 0 ≤ request := by
    dsimp [request]
    positivity
  let workload := uniformWorkload 2 request hrequest
  have hoffline : request / (1 + (k : ℝ)) ≤
      offlineOpt initial [workload] := by
    exact uniform_offlineOpt_one_step_lower (by norm_num) initial request hrequest
  have hexpected : offlineOpt initial [workload] ≤
      algorithm.expectedCost initial [workload] :=
    expectedCost_ge_offlineOpt algorithm initial [workload] hintegrable
  have hcompetitive := hbound [workload]
  have hupperProduct :
      (1 - Γ) * offlineOpt initial [workload] ≤ additive := by
    linarith
  have hscale :
      (1 - Γ) * (request / (1 + (k : ℝ))) = additive + 1 := by
    dsimp [request]
    field_simp [ne_of_gt hgap]
  have hlowerProduct : additive + 1 ≤
      (1 - Γ) * offlineOpt initial [workload] := by
    rw [← hscale]
    exact mul_le_mul_of_nonneg_left hoffline (le_of_lt hgap)
  linarith

theorem universal_factor_lower_bound_at_least_one (Γ : ℝ)
    (hupper : ∀ k : ℕ, 1 ≤ k → HasCompetitiveUpperForK k Γ) : 1 ≤ Γ :=
  competitive_factor_lower_bound_at_least_one 1 Γ (hupper 1 le_rfl)

#print axioms competitive_factor_lower_bound_at_least_one

end DynamicMoeSemantics
