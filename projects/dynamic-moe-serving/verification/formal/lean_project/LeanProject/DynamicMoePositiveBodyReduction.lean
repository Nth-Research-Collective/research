import LeanProject.DynamicMoePositiveBody
import LeanProject.DynamicMoePositiveBodyInterface
import LeanProject.DynamicMoeSemantics

/-!
Concrete finite translation from Dynamic MoE workloads to alternating
positive event/reset bodies. The source-theorem interface itself remains in
`DynamicMoePositiveBodyInterface` and contains no MoE definitions.
-/

open scoped BigOperators

namespace DynamicMoePositiveBodyReduction

open DynamicMoeSemantics
open DynamicMoePositiveBodyInterface

abbrev BodyCoordinate (m : ℕ) := Option (Fin m)

def zeroRow {ι : Type*} [Fintype ι] [DecidableEq ι] : PositiveRow ι where
  coefficient _ := 0
  nonnegative _ := le_rfl
  rightHandSide := 0
  rightHandSide_nonnegative := le_rfl

noncomputable def tangentRow {m k : ℕ} (request : Workload m)
    (expert : Fin m) (scaleIndex : Fin (2 * k + 1)) :
    PositiveRow (BodyCoordinate m) := by
  let requestValue := request.value expert
  let scale : ℝ := scaleIndex.val + 1
  by_cases hzero : requestValue = 0
  · exact zeroRow
  · have hrequest : 0 < requestValue :=
      lt_of_le_of_ne (request.nonnegative expert) (Ne.symm hzero)
    have hscale : 0 < scale := by
      dsimp [scale]
      positivity
    have hdenominator : 0 < 2 * scale - 1 := by
      have hone : (1 : ℝ) ≤ scale := by
        dsimp [scale]
        norm_num
      linarith
    exact {
      coefficient := fun coordinate ↦
        match coordinate with
        | none => scale ^ 2 / (requestValue * (2 * scale - 1))
        | some candidate =>
            if candidate = expert then 1 / (2 * scale - 1) else 0
      nonnegative := by
        intro coordinate
        cases coordinate with
        | none => positivity
        | some candidate =>
            change 0 ≤ if candidate = expert then
              1 / (2 * scale - 1) else 0
            by_cases hcandidate : candidate = expert
            · rw [if_pos hcandidate]
              exact div_nonneg (by norm_num) (le_of_lt hdenominator)
            · simp [hcandidate]
      rightHandSide := 1
      rightHandSide_nonnegative := by norm_num
    }

noncomputable def budgetRow {m k : ℕ} :
    PositiveRow (BodyCoordinate m) where
  coefficient coordinate :=
    match coordinate with
    | none => 0
    | some _ => 1 / (k : ℝ)
  nonnegative coordinate := by
    cases coordinate <;> positivity
  rightHandSide := 1
  rightHandSide_nonnegative := by norm_num

noncomputable def resetHeightRow {m : ℕ} (time : ℕ) :
    PositiveRow (BodyCoordinate m) where
  coefficient coordinate :=
    match coordinate with
    | none => 1 / ((1 / 2 : ℝ) ^ (time + 1))
    | some _ => 0
  nonnegative coordinate := by
    cases coordinate <;> positivity
  rightHandSide := 1
  rightHandSide_nonnegative := by norm_num

noncomputable def eventBody {m k : ℕ} (request : Workload m) :
    PositiveBody (BodyCoordinate m) where
  covering := ((Finset.univ : Finset (Fin m × Fin (2 * k + 1))).toList.map
    fun pair ↦ tangentRow request pair.1 pair.2)
  packing := [budgetRow (m := m) (k := k)]

noncomputable def resetBody {m k : ℕ} (time : ℕ) :
    PositiveBody (BodyCoordinate m) where
  covering := []
  packing := [budgetRow (m := m) (k := k), resetHeightRow time]

noncomputable def eventResetBodiesFrom {m k : ℕ} :
    ℕ → List (Workload m) → List (PositiveBody (BodyCoordinate m))
  | _, [] => []
  | time, request :: requests =>
      eventBody (k := k) request :: resetBody (m := m) (k := k) time ::
        eventResetBodiesFrom (m := m) (k := k) (time + 1) requests

noncomputable def eventResetBodies {m k : ℕ}
    (requests : List (Workload m)) :
    List (PositiveBody (BodyCoordinate m)) :=
  eventResetBodiesFrom (m := m) (k := k) 0 requests

/-- Lift one original MoE state to the comparator point used at an event body. -/
noncomputable def integralEventPoint {m k : ℕ} (request : Workload m)
    (allocation : IntegralAllocation m k) : BodyCoordinate m → ℝ
  | none => latency request allocation
  | some expert => allocation.value expert

/-- The matching reset comparator keeps the allocation and zeros the height. -/
def integralResetPoint {m k : ℕ} (allocation : IntegralAllocation m k) :
    BodyCoordinate m → ℝ
  | none => 0
  | some expert => allocation.value expert

/-- Interleave lifted event and reset points exactly as the generated bodies. -/
noncomputable def eventResetComparator {m k : ℕ} :
    List (Workload m) → List (IntegralAllocation m k) →
      List (BodyCoordinate m → ℝ)
  | request :: requests, allocation :: allocations =>
      integralEventPoint request allocation :: integralResetPoint allocation ::
        eventResetComparator requests allocations
  | _, _ => []

theorem eventResetComparator_length {m k : ℕ}
    (requests : List (Workload m)) (allocations : List (IntegralAllocation m k))
    (hlength : allocations.length = requests.length) :
    (eventResetComparator requests allocations).length = 2 * requests.length := by
  induction requests generalizing allocations with
  | nil =>
      cases allocations with
      | nil => simp [eventResetComparator]
      | cons allocation allocations => simp at hlength
  | cons request requests inductionHypothesis =>
      cases allocations with
      | nil => simp at hlength
      | cons allocation allocations =>
          have htail : allocations.length = requests.length := by
            simp only [List.length_cons] at hlength
            omega
          simp [eventResetComparator, inductionHypothesis allocations htail,
            Nat.mul_add]

theorem foldl_max_ge_initial (values : List ℝ) (initial : ℝ) :
    initial ≤ values.foldl max initial := by
  induction values generalizing initial with
  | nil => simp
  | cons value values inductionHypothesis =>
      exact (le_max_left initial value).trans
        (inductionHypothesis (max initial value))

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

theorem integralLatency_nonnegative {m k : ℕ} (request : Workload m)
    (allocation : IntegralAllocation m k) : 0 ≤ latency request allocation := by
  unfold latency
  exact foldl_max_ge_initial _ 0

theorem requestRatio_le_integralLatency {m k : ℕ} (request : Workload m)
    (allocation : IntegralAllocation m k) (expert : Fin m) :
    request.value expert / (1 + (allocation.value expert : ℝ)) ≤
      latency request allocation := by
  unfold latency
  apply foldl_max_ge_of_mem
  simp

theorem integralEventPoint_nonnegative {m k : ℕ} (request : Workload m)
    (allocation : IntegralAllocation m k) :
    ∀ coordinate, 0 ≤ integralEventPoint request allocation coordinate := by
  intro coordinate
  cases coordinate with
  | none => exact integralLatency_nonnegative request allocation
  | some expert => simp [integralEventPoint]

theorem integralResetPoint_nonnegative {m k : ℕ}
    (allocation : IntegralAllocation m k) :
    ∀ coordinate, 0 ≤ integralResetPoint allocation coordinate := by
  intro coordinate
  cases coordinate <;> simp [integralResetPoint]

/-- All completed event/reset pairs followed by the current event. -/
noncomputable def eventBodyHistoryFrom {m k : ℕ} (time : ℕ)
    (requests : List (Workload m)) :
    List (PositiveBody (BodyCoordinate m)) :=
  (eventResetBodiesFrom (m := m) (k := k) time requests).dropLast

noncomputable def eventBodyHistory {m k : ℕ}
    (requests : List (Workload m)) :
    List (PositiveBody (BodyCoordinate m)) :=
  eventBodyHistoryFrom (m := m) (k := k) 0 requests

theorem eventResetBodiesFrom_length {m k : ℕ} (time : ℕ)
    (requests : List (Workload m)) :
    (eventResetBodiesFrom (m := m) (k := k) time requests).length =
      2 * requests.length := by
  induction requests generalizing time with
  | nil => simp [eventResetBodiesFrom]
  | cons request requests inductionHypothesis =>
      simp [eventResetBodiesFrom, inductionHypothesis, Nat.mul_add]

theorem eventResetBodies_length {m k : ℕ}
    (requests : List (Workload m)) :
    (eventResetBodies (m := m) (k := k) requests).length =
      2 * requests.length := by
  unfold eventResetBodies
  exact eventResetBodiesFrom_length 0 requests

theorem eventResetBodiesFrom_take {m k : ℕ} (time rounds : ℕ)
    (requests : List (Workload m)) :
    eventResetBodiesFrom (m := m) (k := k) time (requests.take rounds) =
      (eventResetBodiesFrom (m := m) (k := k) time requests).take
        (2 * rounds) := by
  induction rounds generalizing time requests with
  | zero => simp [eventResetBodiesFrom]
  | succ rounds inductionHypothesis =>
      cases requests with
      | nil => simp [eventResetBodiesFrom]
      | cons request requests =>
          simp [eventResetBodiesFrom, inductionHypothesis, Nat.mul_add]

theorem eventResetBodies_take {m k : ℕ} (rounds : ℕ)
    (requests : List (Workload m)) :
    eventResetBodies (m := m) (k := k) (requests.take rounds) =
      (eventResetBodies (m := m) (k := k) requests).take (2 * rounds) := by
  exact eventResetBodiesFrom_take 0 rounds requests

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

theorem eventBodyHistoryFrom_take_current {m k : ℕ} (time round : ℕ)
    (requests : List (Workload m)) (hround : round < requests.length) :
    eventBodyHistoryFrom (m := m) (k := k) time
        (requests.take (round + 1)) =
      (eventResetBodiesFrom (m := m) (k := k) time requests).take
        (2 * round + 1) := by
  induction round generalizing time requests with
  | zero =>
      cases requests with
      | nil => simp at hround
      | cons request requests =>
          simp [eventBodyHistoryFrom, eventResetBodiesFrom]
  | succ round inductionHypothesis =>
      cases requests with
      | nil => simp at hround
      | cons request requests =>
          have htail : round < requests.length := by
            simp only [List.length_cons] at hround
            omega
          have htakeLength : (requests.take (round + 1)).length =
              round + 1 := by
            rw [List.length_take]
            exact Nat.min_eq_left (Nat.succ_le_iff.mpr htail)
          have htakeNonempty : requests.take (round + 1) ≠ [] := by
            intro hempty
            have := congrArg List.length hempty
            rw [htakeLength] at this
            simp at this
          have hbodiesNonempty :
              eventResetBodiesFrom (m := m) (k := k) (time + 1)
                (requests.take (round + 1)) ≠ [] := by
            cases hprefix : requests.take (round + 1) with
            | nil => exact (htakeNonempty hprefix).elim
            | cons nextRequest remaining =>
                simp [eventResetBodiesFrom]
          have hinduction :=
            inductionHypothesis (time + 1) requests htail
          unfold eventBodyHistoryFrom at hinduction
          simp [eventBodyHistoryFrom, eventResetBodiesFrom, Nat.mul_add]
          rw [List.dropLast_cons_of_ne_nil hbodiesNonempty, hinduction]

theorem eventBodyHistory_take_current {m k : ℕ} (round : ℕ)
    (requests : List (Workload m)) (hround : round < requests.length) :
    eventBodyHistory (m := m) (k := k) (requests.take (round + 1)) =
      (eventResetBodies (m := m) (k := k) requests).take
        (2 * round + 1) := by
  exact eventBodyHistoryFrom_take_current 0 round requests hround

abbrev NonemptyWorkloadHistory (m : ℕ) :=
  {history : List (Workload m) // history ≠ []}

def revealedHistories {m : ℕ} (requests : List (Workload m)) :
    List (NonemptyWorkloadHistory m) :=
  List.ofFn fun round : Fin requests.length ↦
    ⟨requests.take (round.val + 1),
      take_current_nonempty requests round.val round.isLt⟩

def revealedRequest {m : ℕ} (history : NonemptyWorkloadHistory m) :
    Workload m := history.val.getLast history.property

theorem revealedHistories_length {m : ℕ} (requests : List (Workload m)) :
    (revealedHistories requests).length = requests.length := by
  simp [revealedHistories]

theorem revealedRequests_eq {m : ℕ} (requests : List (Workload m)) :
    (revealedHistories requests).map revealedRequest = requests := by
  apply List.ext_getElem
  · simp [revealedHistories_length]
  · intro round hleft hright
    simp [revealedHistories, revealedRequest]
    simpa using getLast_take_current requests round hright

theorem revealedRun_eq {m k : ℕ} (algorithm : FractionalOnlineAlgorithm m k)
    (requests : List (Workload m)) :
    (revealedHistories requests).map (fun history ↦ algorithm.choose history.val) =
      algorithm.run requests := by
  unfold FractionalOnlineAlgorithm.run
  apply List.ext_getElem
  · simp [revealedHistories_length]
  · intro round hleft hright
    simp [revealedHistories]

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

theorem eventBodyHistoryFrom_nonempty {m k : ℕ} (time : ℕ)
    (request : Workload m) (requests : List (Workload m)) :
    eventBodyHistoryFrom (m := m) (k := k) time
      (request :: requests) ≠ [] := by
  simp [eventBodyHistoryFrom, eventResetBodiesFrom]

theorem eventBodyHistory_nonempty {m k : ℕ}
    (request : Workload m) (requests : List (Workload m)) :
    eventBodyHistory (m := m) (k := k) (request :: requests) ≠ [] := by
  exact eventBodyHistoryFrom_nonempty 0 request requests

def bodyAllocation {m : ℕ} (point : BodyCoordinate m → ℝ) : Fin m → ℝ :=
  fun expert ↦ point (some expert)

def bodyHeight {m : ℕ} (point : BodyCoordinate m → ℝ) : ℝ :=
  point none

theorem fractionalMovement_le_two_k {m k : ℕ}
    (first second : FractionalAllocation m k) :
    fractionalMovement first second ≤ 2 * k := by
  unfold fractionalMovement
  calc
    (∑ expert, |first.value expert - second.value expert|)
        ≤ ∑ expert, (first.value expert + second.value expert) := by
          apply Finset.sum_le_sum
          intro expert _
          calc
            |first.value expert - second.value expert| =
                |first.value expert + -second.value expert| := by ring_nf
            _ ≤ |first.value expert| + |-second.value expert| :=
              abs_add_le _ _
            _ = first.value expert + second.value expert := by
              rw [abs_of_nonneg (first.nonnegative expert), abs_neg,
                abs_of_nonneg (second.nonnegative expert)]
    _ = 2 * k := by
      rw [Finset.sum_add_distrib, first.budget, second.budget]
      ring

theorem bodyAllocation_l1Distance_le {m : ℕ}
    (first second : BodyCoordinate m → ℝ) :
    l1Distance (bodyAllocation first) (bodyAllocation second) ≤
      l1Distance first second := by
  unfold l1Distance bodyAllocation
  simp

theorem movementFrom_bodyAllocation_le {m : ℕ}
    (initial : BodyCoordinate m → ℝ) : ∀ path,
    movementFrom (bodyAllocation initial) (path.map bodyAllocation) ≤
      movementFrom initial path := by
  intro path
  induction path generalizing initial with
  | nil => simp [movementFrom]
  | cons point path inductionHypothesis =>
      simp only [List.map_cons, movementFrom]
      linarith [bodyAllocation_l1Distance_le initial point,
        inductionHypothesis point]

theorem balancedPath_tail_movement_le {m k : ℕ} (hm : 0 < m)
    (initial : AugmentedAllocation m k) : ∀ path : List (AugmentedAllocation m k),
    fractionalMovementFrom (initial.toBalancedFractional hm)
        (path.map fun allocation ↦ allocation.toBalancedFractional hm) ≤
      movementFrom initial.value (path.map fun allocation ↦ allocation.value) := by
  intro path
  induction path generalizing initial with
  | nil => simp [fractionalMovementFrom, movementFrom]
  | cons allocation path inductionHypothesis =>
      simp only [List.map_cons, fractionalMovementFrom, movementFrom]
      have hone := balanced_map_one_lipschitz initial allocation hm
      have hrest := inductionHypothesis allocation
      unfold l1Distance
      linarith

theorem balancedPath_movement_le {m k : ℕ} (hm : 0 < m)
    (initial : IntegralAllocation m k)
    (path : List (AugmentedAllocation m k)) :
    fractionalMovementFrom initial.toFractional
        (path.map fun allocation ↦ allocation.toBalancedFractional hm) ≤
      2 * k +
        movementFrom (fun _ : Fin m ↦ 0)
          (path.map fun allocation ↦ allocation.value) := by
  cases path with
  | nil => simp [fractionalMovementFrom, movementFrom]
  | cons allocation path =>
      simp only [List.map_cons, fractionalMovementFrom, movementFrom]
      have hfirst := fractionalMovement_le_two_k initial.toFractional
        (allocation.toBalancedFractional hm)
      have hrest := balancedPath_tail_movement_le hm allocation path
      have hnonnegative := l1Distance_nonnegative
        (fun _ : Fin m ↦ 0) allocation.value
      linarith

theorem tangentRow_support_subset {m k : ℕ} (request : Workload m)
    (expert : Fin m) (scaleIndex : Fin (2 * k + 1)) :
    (tangentRow request expert scaleIndex).support ⊆
      ({none, some expert} : Finset (BodyCoordinate m)) := by
  intro coordinate hcoordinate
  have hnonzero :
      (tangentRow request expert scaleIndex).coefficient coordinate ≠ 0 := by
    simpa [PositiveRow.support] using hcoordinate
  let requestValue := request.value expert
  let scale : ℝ := scaleIndex.val + 1
  by_cases hzero : requestValue = 0
  · have : (tangentRow request expert scaleIndex).coefficient coordinate = 0 := by
      simp [tangentRow, requestValue, hzero, zeroRow]
    exact (hnonzero this).elim
  · cases coordinate with
    | none => simp
    | some candidate =>
        by_cases hcandidate : candidate = expert
        · simp [hcandidate]
        · have : (tangentRow request expert scaleIndex).coefficient
              (some candidate) = 0 := by
            simp [tangentRow, requestValue, hzero, hcandidate]
          exact (hnonzero this).elim

theorem tangentRow_two_sparse {m k : ℕ} (request : Workload m)
    (expert : Fin m) (scaleIndex : Fin (2 * k + 1)) :
    (tangentRow request expert scaleIndex).IsTwoSparse := by
  unfold PositiveRow.IsTwoSparse
  calc
    (tangentRow request expert scaleIndex).support.card
        ≤ ({none, some expert} : Finset (BodyCoordinate m)).card :=
      Finset.card_le_card (tangentRow_support_subset request expert scaleIndex)
    _ ≤ 2 := by simp

theorem tangentRow_forces_height {m k : ℕ} (request : Workload m)
    (point : BodyCoordinate m → ℝ) (hpoint : ∀ coordinate, 0 ≤ point coordinate)
    (expert : Fin m) (scaleIndex : Fin (2 * k + 1))
    (hrow : (tangentRow request expert scaleIndex).rightHandSide ≤
      (tangentRow request expert scaleIndex).evaluate point) :
    request.value expert *
        (2 * ((scaleIndex.val : ℝ) + 1) - (1 + point (some expert))) /
          ((scaleIndex.val : ℝ) + 1) ^ 2 ≤ point none := by
  let requestValue := request.value expert
  let scale : ℝ := scaleIndex.val + 1
  by_cases hzero : requestValue = 0
  · simp [requestValue, hzero]
    exact hpoint none
  · have hrequest : 0 < requestValue :=
      lt_of_le_of_ne (request.nonnegative expert) (Ne.symm hzero)
    have hscale : 0 < scale := by
      dsimp [scale]
      positivity
    have hdenominator : 0 < 2 * scale - 1 := by
      have : (1 : ℝ) ≤ scale := by
        dsimp [scale]
        norm_num
      linarith
    have hexpanded : 1 ≤
        scale ^ 2 / (requestValue * (2 * scale - 1)) * point none +
          (1 / (2 * scale - 1)) * point (some expert) := by
      simpa [tangentRow, requestValue, scale, hzero,
        PositiveRow.evaluate] using hrow
    have hcleared : requestValue * (2 * scale - 1) ≤
        scale ^ 2 * point none + requestValue * point (some expert) := by
      have hpositive : 0 < requestValue * (2 * scale - 1) := by positivity
      have := (le_div_iff₀ hpositive).mp (show
        (1 : ℝ) ≤
          (scale ^ 2 * point none + requestValue * point (some expert)) /
            (requestValue * (2 * scale - 1)) by
        calc
          1 ≤ scale ^ 2 / (requestValue * (2 * scale - 1)) * point none +
              (1 / (2 * scale - 1)) * point (some expert) := hexpanded
          _ = (scale ^ 2 * point none + requestValue * point (some expert)) /
              (requestValue * (2 * scale - 1)) := by
                field_simp [ne_of_gt hrequest, ne_of_gt hdenominator]
                )
      simpa using this
    change requestValue * (2 * scale - (1 + point (some expert))) /
        scale ^ 2 ≤ point none
    apply (div_le_iff₀ (sq_pos_of_pos hscale)).2
    nlinarith

theorem eventBody_covering_two_sparse {m k : ℕ} (request : Workload m) :
    (eventBody (k := k) request).CoveringTwoSparse := by
  intro row hrow
  simp only [eventBody, List.mem_map, Finset.mem_toList] at hrow
  obtain ⟨pair, _, rfl⟩ := hrow
  exact tangentRow_two_sparse request pair.1 pair.2

theorem resetBody_covering_two_sparse {m k : ℕ} (time : ℕ) :
    (resetBody (m := m) (k := k) time).CoveringTwoSparse := by
  simp [PositiveBody.CoveringTwoSparse, resetBody]

theorem eventResetBodiesFrom_covering_two_sparse {m k : ℕ}
    (time : ℕ) (requests : List (Workload m)) :
    ∀ body ∈ eventResetBodiesFrom (m := m) (k := k) time requests,
      body.CoveringTwoSparse := by
  induction requests generalizing time with
  | nil => simp [eventResetBodiesFrom]
  | cons request requests inductionHypothesis =>
      intro body hbody
      simp only [eventResetBodiesFrom, List.mem_cons] at hbody
      rcases hbody with rfl | rfl | htail
      · exact eventBody_covering_two_sparse request
      · exact resetBody_covering_two_sparse time
      · exact inductionHypothesis (time + 1) body htail

theorem eventResetBodies_covering_two_sparse {m k : ℕ}
    (requests : List (Workload m)) :
    ∀ body ∈ eventResetBodies (m := m) (k := k) requests,
      body.CoveringTwoSparse := by
  exact eventResetBodiesFrom_covering_two_sparse 0 requests

theorem eventBody_packing_positive_rightHandSide {m k : ℕ}
    (request : Workload m) :
    (eventBody (k := k) request).PackingPositiveRightHandSide := by
  simp [PositiveBody.PackingPositiveRightHandSide, eventBody, budgetRow]

theorem resetBody_packing_positive_rightHandSide {m k : ℕ} (time : ℕ) :
    (resetBody (m := m) (k := k) time).PackingPositiveRightHandSide := by
  simp [PositiveBody.PackingPositiveRightHandSide, resetBody, budgetRow,
    resetHeightRow]

theorem eventResetBodiesFrom_packing_positive_rightHandSide {m k : ℕ}
    (time : ℕ) (requests : List (Workload m)) :
    ∀ body ∈ eventResetBodiesFrom (m := m) (k := k) time requests,
      body.PackingPositiveRightHandSide := by
  induction requests generalizing time with
  | nil => simp [eventResetBodiesFrom]
  | cons request requests inductionHypothesis =>
      intro body hbody
      simp only [eventResetBodiesFrom, List.mem_cons] at hbody
      rcases hbody with rfl | rfl | htail
      · exact eventBody_packing_positive_rightHandSide request
      · exact resetBody_packing_positive_rightHandSide time
      · exact inductionHypothesis (time + 1) body htail

theorem eventResetBodies_packing_positive_rightHandSide {m k : ℕ}
    (requests : List (Workload m)) :
    ∀ body ∈ eventResetBodies (m := m) (k := k) requests,
      body.PackingPositiveRightHandSide := by
  exact eventResetBodiesFrom_packing_positive_rightHandSide 0 requests

theorem eventBodyHistoryFrom_covering_two_sparse {m k : ℕ}
    (time : ℕ) (requests : List (Workload m)) :
    ∀ body ∈ eventBodyHistoryFrom (m := m) (k := k) time requests,
      body.CoveringTwoSparse := by
  intro body hbody
  exact eventResetBodiesFrom_covering_two_sparse time requests body
    (List.mem_of_mem_dropLast hbody)

theorem eventBodyHistoryFrom_packing_positive_rightHandSide {m k : ℕ}
    (time : ℕ) (requests : List (Workload m)) :
    ∀ body ∈ eventBodyHistoryFrom (m := m) (k := k) time requests,
      body.PackingPositiveRightHandSide := by
  intro body hbody
  exact eventResetBodiesFrom_packing_positive_rightHandSide time requests body
    (List.mem_of_mem_dropLast hbody)

theorem eventBodyHistory_covering_two_sparse {m k : ℕ}
    (requests : List (Workload m)) :
    ∀ body ∈ eventBodyHistory (m := m) (k := k) requests,
      body.CoveringTwoSparse := by
  exact eventBodyHistoryFrom_covering_two_sparse 0 requests

theorem eventBodyHistory_packing_positive_rightHandSide {m k : ℕ}
    (requests : List (Workload m)) :
    ∀ body ∈ eventBodyHistory (m := m) (k := k) requests,
      body.PackingPositiveRightHandSide := by
  exact eventBodyHistoryFrom_packing_positive_rightHandSide 0 requests

noncomputable def tangentHeightContribution {m k : ℕ}
    (request : Workload m) (pair : Fin m × Fin (2 * k + 1)) : ℝ :=
  let scale : ℝ := pair.2.val + 1
  request.value pair.1 * (2 * scale - 1) / scale ^ 2

theorem tangentHeightContribution_nonnegative {m k : ℕ}
    (request : Workload m) (pair : Fin m × Fin (2 * k + 1)) :
    0 ≤ tangentHeightContribution request pair := by
  let scale : ℝ := pair.2.val + 1
  have hscale : (1 : ℝ) ≤ scale := by
    dsimp [scale]
    norm_num
  unfold tangentHeightContribution
  dsimp only
  exact div_nonneg
    (mul_nonneg (request.nonnegative pair.1) (by linarith)) (sq_nonneg scale)

noncomputable def eventHeight {m k : ℕ} (request : Workload m) : ℝ :=
  ∑ pair : Fin m × Fin (2 * k + 1),
    tangentHeightContribution request pair

noncomputable def eventFeasiblePoint {m k : ℕ} (request : Workload m) :
    BodyCoordinate m → ℝ
  | none => eventHeight (k := k) request
  | some _ => 0

theorem eventHeight_nonnegative {m k : ℕ} (request : Workload m) :
    0 ≤ eventHeight (k := k) request := by
  unfold eventHeight
  exact Finset.sum_nonneg fun pair _ ↦
    tangentHeightContribution_nonnegative request pair

theorem tangentHeightContribution_le_eventHeight {m k : ℕ}
    (request : Workload m) (pair : Fin m × Fin (2 * k + 1)) :
    tangentHeightContribution request pair ≤ eventHeight (k := k) request := by
  unfold eventHeight
  exact Finset.single_le_sum
    (fun candidate _ ↦ tangentHeightContribution_nonnegative request candidate)
    (Finset.mem_univ pair)

theorem tangentRow_satisfied_by_eventPoint {m k : ℕ}
    (request : Workload m) (expert : Fin m)
    (scaleIndex : Fin (2 * k + 1)) :
    (tangentRow request expert scaleIndex).rightHandSide ≤
      (tangentRow request expert scaleIndex).evaluate
        (eventFeasiblePoint (k := k) request) := by
  let requestValue := request.value expert
  let scale : ℝ := scaleIndex.val + 1
  by_cases hzero : requestValue = 0
  · simp [tangentRow, requestValue, hzero, zeroRow,
      PositiveRow.evaluate, eventFeasiblePoint]
  · have hrequest : 0 < requestValue :=
      lt_of_le_of_ne (request.nonnegative expert) (Ne.symm hzero)
    have hscale : 0 < scale := by
      dsimp [scale]
      positivity
    have hdenominator : 0 < 2 * scale - 1 := by
      have : (1 : ℝ) ≤ scale := by
        dsimp [scale]
        norm_num
      linarith
    have hcontribution := tangentHeightContribution_le_eventHeight request
      (expert, scaleIndex)
    have hcoefficient : 0 <
        scale ^ 2 / (requestValue * (2 * scale - 1)) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hcontribution
      (le_of_lt hcoefficient)
    have hidentity :
        (scale ^ 2 / (requestValue * (2 * scale - 1))) *
            tangentHeightContribution request (expert, scaleIndex) = 1 := by
      change (scale ^ 2 / (requestValue * (2 * scale - 1))) *
        (requestValue * (2 * scale - 1) / scale ^ 2) = 1
      have hdenominatorCommuted : scale * 2 - 1 ≠ 0 := by
        nlinarith [hdenominator]
      field_simp [ne_of_gt hrequest, ne_of_gt hscale,
        ne_of_gt hdenominator, hdenominatorCommuted]
    have hheight : 1 ≤
        (scale ^ 2 / (requestValue * (2 * scale - 1))) *
          eventHeight (k := k) request := by
      calc
        1 = (scale ^ 2 / (requestValue * (2 * scale - 1))) *
            tangentHeightContribution request (expert, scaleIndex) :=
          hidentity.symm
        _ ≤ (scale ^ 2 / (requestValue * (2 * scale - 1))) *
            eventHeight (k := k) request := hscaled
    simpa [tangentRow, requestValue, scale, hzero,
      PositiveRow.evaluate, eventFeasiblePoint] using hheight

theorem tangentRow_satisfied_by_integralEventPoint {m k : ℕ}
    (request : Workload m) (allocation : IntegralAllocation m k)
    (expert : Fin m) (scaleIndex : Fin (2 * k + 1)) :
    (tangentRow request expert scaleIndex).rightHandSide ≤
      (tangentRow request expert scaleIndex).evaluate
        (integralEventPoint request allocation) := by
  let requestValue := request.value expert
  let scale : ℝ := scaleIndex.val + 1
  by_cases hzero : requestValue = 0
  · simp [tangentRow, requestValue, hzero, zeroRow,
      PositiveRow.evaluate, integralEventPoint]
  · have hrequest : 0 < requestValue :=
      lt_of_le_of_ne (request.nonnegative expert) (Ne.symm hzero)
    have hscale : 0 < scale := by
      dsimp [scale]
      positivity
    have hdenominator : 0 < 2 * scale - 1 := by
      have : (1 : ℝ) ≤ scale := by
        dsimp [scale]
        norm_num
      linarith
    have hq : 0 < 1 + (allocation.value expert : ℝ) := by positivity
    have htangent := DynamicMoePositiveBody.reciprocal_tangent_underestimate
      requestValue (1 + (allocation.value expert : ℝ)) scale
      (le_of_lt hrequest) hq hscale
    have hlatency := requestRatio_le_integralLatency request allocation expert
    have hbelow : requestValue *
          (2 * scale - (1 + (allocation.value expert : ℝ))) / scale ^ 2 ≤
        latency request allocation := htangent.trans hlatency
    have hcoefficient : 0 ≤
        scale ^ 2 / (requestValue * (2 * scale - 1)) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hbelow hcoefficient
    have hidentity :
        (scale ^ 2 / (requestValue * (2 * scale - 1))) *
            (requestValue *
              (2 * scale - (1 + (allocation.value expert : ℝ))) /
                scale ^ 2) +
          (1 / (2 * scale - 1)) * (allocation.value expert : ℝ) = 1 := by
      have hdenominatorCommuted : scale * 2 - 1 ≠ 0 := by
        nlinarith [hdenominator]
      field_simp [ne_of_gt hrequest, ne_of_gt hscale,
        ne_of_gt hdenominator, hdenominatorCommuted]
      ring
    have hrow : 1 ≤
        (scale ^ 2 / (requestValue * (2 * scale - 1))) *
            latency request allocation +
          (1 / (2 * scale - 1)) * (allocation.value expert : ℝ) := by
      calc
        1 = (scale ^ 2 / (requestValue * (2 * scale - 1))) *
              (requestValue *
                (2 * scale - (1 + (allocation.value expert : ℝ))) /
                  scale ^ 2) +
            (1 / (2 * scale - 1)) * (allocation.value expert : ℝ) :=
              hidentity.symm
        _ ≤ (scale ^ 2 / (requestValue * (2 * scale - 1))) *
              latency request allocation +
            (1 / (2 * scale - 1)) * (allocation.value expert : ℝ) :=
              by
                simpa [add_comm] using
                  (add_le_add_right hscaled
                    ((1 / (2 * scale - 1)) *
                      (allocation.value expert : ℝ)))
    simpa [tangentRow, requestValue, scale, hzero,
      PositiveRow.evaluate, integralEventPoint] using hrow

theorem eventBody_nonempty_exact {m k : ℕ} (request : Workload m) :
    ∃ point, (eventBody (k := k) request).ExactFeasible point := by
  refine ⟨eventFeasiblePoint (k := k) request, ?_, ?_, ?_⟩
  · intro coordinate
    cases coordinate with
    | none => exact eventHeight_nonnegative request
    | some _ => simp [eventFeasiblePoint]
  · intro row hrow
    simp only [eventBody, List.mem_map, Finset.mem_toList] at hrow
    obtain ⟨pair, _, rfl⟩ := hrow
    exact tangentRow_satisfied_by_eventPoint request pair.1 pair.2
  · intro row hrow
    simp only [eventBody, List.mem_singleton] at hrow
    subst row
    simp [PositiveRow.evaluate, budgetRow, eventFeasiblePoint]

theorem resetBody_nonempty_exact {m k : ℕ} (time : ℕ) :
    ∃ point, (resetBody (m := m) (k := k) time).ExactFeasible point := by
  refine ⟨fun _ ↦ 0, ?_, ?_, ?_⟩
  · simp
  · simp [resetBody]
  · intro row hrow
    simp only [resetBody, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl
    · simp [PositiveRow.evaluate, budgetRow]
    · simp [PositiveRow.evaluate, resetHeightRow]

theorem eventResetBodiesFrom_nonempty_exact {m k : ℕ}
    (time : ℕ) (requests : List (Workload m)) :
    ∀ body ∈ eventResetBodiesFrom (m := m) (k := k) time requests,
      ∃ point, body.ExactFeasible point := by
  induction requests generalizing time with
  | nil => simp [eventResetBodiesFrom]
  | cons request requests inductionHypothesis =>
      intro body hbody
      simp only [eventResetBodiesFrom, List.mem_cons] at hbody
      rcases hbody with rfl | rfl | htail
      · exact eventBody_nonempty_exact request
      · exact resetBody_nonempty_exact time
      · exact inductionHypothesis (time + 1) body htail

theorem eventResetBodies_nonempty_exact {m k : ℕ}
    (requests : List (Workload m)) :
    ∀ body ∈ eventResetBodies (m := m) (k := k) requests,
      ∃ point, body.ExactFeasible point := by
  exact eventResetBodiesFrom_nonempty_exact 0 requests

theorem eventBodyHistoryFrom_nonempty_exact {m k : ℕ}
    (time : ℕ) (requests : List (Workload m)) :
    ∀ body ∈ eventBodyHistoryFrom (m := m) (k := k) time requests,
      ∃ point, body.ExactFeasible point := by
  intro body hbody
  exact eventResetBodiesFrom_nonempty_exact time requests body
    (List.mem_of_mem_dropLast hbody)

theorem eventBodyHistory_nonempty_exact {m k : ℕ}
    (requests : List (Workload m)) :
    ∀ body ∈ eventBodyHistory (m := m) (k := k) requests,
      ∃ point, body.ExactFeasible point := by
  exact eventBodyHistoryFrom_nonempty_exact 0 requests

theorem eventBodyHistoryFrom_getLast {m k : ℕ} (time : ℕ)
    (request : Workload m) (requests : List (Workload m)) :
    (eventBodyHistoryFrom (m := m) (k := k) time
      (request :: requests)).getLast
        (eventBodyHistoryFrom_nonempty time request requests) =
      eventBody (k := k) ((request :: requests).getLast (by simp)) := by
  induction requests generalizing time request with
  | nil => simp [eventBodyHistoryFrom, eventResetBodiesFrom]
  | cons nextRequest remaining inductionHypothesis =>
      have htail : eventBodyHistoryFrom (m := m) (k := k) (time + 1)
          (nextRequest :: remaining) ≠ [] :=
        eventBodyHistoryFrom_nonempty (time + 1) nextRequest remaining
      change (eventBody (k := k) request ::
          resetBody (m := m) (k := k) time ::
            eventBodyHistoryFrom (m := m) (k := k) (time + 1)
              (nextRequest :: remaining)).getLast _ =
        eventBody (k := k)
          ((request :: nextRequest :: remaining).getLast _)
      rw [List.getLast_cons (by simp), List.getLast_cons htail,
        List.getLast_cons (by simp)]
      exact inductionHypothesis (time + 1) nextRequest

theorem eventBodyHistory_getLast {m k : ℕ}
    (request : Workload m) (requests : List (Workload m)) :
    (eventBodyHistory (m := m) (k := k)
      (request :: requests)).getLast
        (eventBodyHistory_nonempty request requests) =
      eventBody (k := k) ((request :: requests).getLast (by simp)) := by
  exact eventBodyHistoryFrom_getLast 0 request requests

theorem budgetRow_evaluate {m k : ℕ} (point : BodyCoordinate m → ℝ) :
    (budgetRow (m := m) (k := k)).evaluate point =
      (∑ i : Fin m, point (some i)) / (k : ℝ) := by
  simp [PositiveRow.evaluate, budgetRow, div_eq_mul_inv]
  rw [← Finset.mul_sum]
  ring

theorem integralAllocation_real_budget {m k : ℕ}
    (allocation : IntegralAllocation m k) :
    ∑ expert : Fin m, (allocation.value expert : ℝ) = k := by
  exact_mod_cast allocation.budget

theorem integralEventPoint_exactFeasible {m k : ℕ} (hk : 1 ≤ k)
    (request : Workload m) (allocation : IntegralAllocation m k) :
    (eventBody (k := k) request).ExactFeasible
      (integralEventPoint request allocation) := by
  refine ⟨integralEventPoint_nonnegative request allocation, ?_, ?_⟩
  · intro row hrow
    simp only [eventBody, List.mem_map, Finset.mem_toList] at hrow
    obtain ⟨pair, _, rfl⟩ := hrow
    exact tangentRow_satisfied_by_integralEventPoint request allocation
      pair.1 pair.2
  · intro row hrow
    simp only [eventBody, List.mem_singleton] at hrow
    subst row
    rw [budgetRow_evaluate]
    simp only [integralEventPoint]
    rw [integralAllocation_real_budget allocation]
    have hkReal : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
    simp [budgetRow, hkReal]

theorem integralResetPoint_exactFeasible {m k : ℕ} (hk : 1 ≤ k)
    (time : ℕ) (allocation : IntegralAllocation m k) :
    (resetBody (m := m) (k := k) time).ExactFeasible
      (integralResetPoint allocation) := by
  refine ⟨integralResetPoint_nonnegative allocation, ?_, ?_⟩
  · simp [resetBody]
  · intro row hrow
    simp only [resetBody, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl
    · rw [budgetRow_evaluate]
      simp only [integralResetPoint]
      rw [integralAllocation_real_budget allocation]
      have hkReal : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
      simp [budgetRow, hkReal]
    · simp [PositiveRow.evaluate, resetHeightRow, integralResetPoint]

theorem eventResetComparator_exactFrom {m k : ℕ} (hk : 1 ≤ k)
    (time : ℕ) (requests : List (Workload m))
    (allocations : List (IntegralAllocation m k))
    (hlength : allocations.length = requests.length) :
    IsExactComparatorPath
      (eventResetBodiesFrom (m := m) (k := k) time requests)
      (eventResetComparator requests allocations) := by
  induction requests generalizing time allocations with
  | nil =>
      cases allocations with
      | nil => simp [eventResetBodiesFrom, eventResetComparator,
          IsExactComparatorPath]
      | cons allocation allocations => simp at hlength
  | cons request requests inductionHypothesis =>
      cases allocations with
      | nil => simp at hlength
      | cons allocation allocations =>
          have htail : allocations.length = requests.length := by
            simp only [List.length_cons] at hlength
            omega
          simp only [eventResetBodiesFrom, eventResetComparator,
            IsExactComparatorPath]
          exact List.Forall₂.cons
            (integralEventPoint_exactFeasible hk request allocation)
            (List.Forall₂.cons
              (integralResetPoint_exactFeasible hk time allocation)
              (inductionHypothesis (time + 1) allocations htail))

theorem eventResetComparator_exact {m k : ℕ} (hk : 1 ≤ k)
    (requests : List (Workload m))
    (allocations : List (IntegralAllocation m k))
    (hlength : allocations.length = requests.length) :
    IsExactComparatorPath
      (eventResetBodies (m := m) (k := k) requests)
      (eventResetComparator requests allocations) := by
  exact eventResetComparator_exactFrom hk 0 requests allocations hlength

noncomputable def selectedBodyChaser {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) (m : ℕ) :
    OnlineChaser (BodyCoordinate m) :=
  Classical.choose (hchaser.2 (BodyCoordinate m))

theorem selectedBodyChaser_spec {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) (m : ℕ) :
    ∀ bodies : List (PositiveBody (BodyCoordinate m)),
      (∀ body ∈ bodies, body.CoveringTwoSparse) →
      (∀ body ∈ bodies, body.PackingPositiveRightHandSide) →
      (∀ body ∈ bodies, ∃ point, body.ExactFeasible point) →
      (∀ hnonempty : bodies ≠ [],
        (bodies.getLast hnonempty).AugmentedFeasible
          ((selectedBodyChaser hchaser m).choose bodies)) ∧
      ∀ comparator : List (BodyCoordinate m → ℝ),
        IsExactComparatorPath bodies comparator →
        (selectedBodyChaser hchaser m).movement bodies ≤
          C * movementFrom (fun _ : BodyCoordinate m ↦ 0) comparator :=
  Classical.choose_spec (hchaser.2 (BodyCoordinate m))

theorem selectedBodyChaser_movement_le_liftedComparator {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ} (hk : 1 ≤ k)
    (requests : List (Workload m))
    (allocations : List (IntegralAllocation m k))
    (hlength : allocations.length = requests.length) :
    (selectedBodyChaser hchaser m).movement
        (eventResetBodies (m := m) (k := k) requests) ≤
      C * movementFrom (fun _ : BodyCoordinate m ↦ 0)
        (eventResetComparator requests allocations) := by
  exact (selectedBodyChaser_spec hchaser m
    (eventResetBodies (m := m) (k := k) requests)
    (eventResetBodies_covering_two_sparse requests)
    (eventResetBodies_packing_positive_rightHandSide requests)
    (eventResetBodies_nonempty_exact requests)).2
      (eventResetComparator requests allocations)
      (eventResetComparator_exact hk requests allocations hlength)

theorem l1Distance_reset_event {m k : ℕ}
    (previous current : IntegralAllocation m k) (request : Workload m) :
    l1Distance (integralResetPoint previous)
        (integralEventPoint request current) =
      movement previous current + latency request current := by
  rw [l1Distance, movement]
  simp [integralResetPoint, integralEventPoint,
    abs_of_nonneg (integralLatency_nonnegative request current), add_comm]

theorem l1Distance_event_reset {m k : ℕ}
    (request : Workload m) (allocation : IntegralAllocation m k) :
    l1Distance (integralEventPoint request allocation)
        (integralResetPoint allocation) = latency request allocation := by
  rw [l1Distance]
  simp [integralEventPoint, integralResetPoint,
    abs_of_nonneg (integralLatency_nonnegative request allocation)]

theorem l1Distance_zero_reset {m k : ℕ}
    (allocation : IntegralAllocation m k) :
    l1Distance (fun _ : BodyCoordinate m ↦ 0)
        (integralResetPoint allocation) = k := by
  rw [l1Distance]
  simp [integralResetPoint, abs_of_nonneg]
  exact integralAllocation_real_budget allocation

theorem liftedComparator_movementFrom_reset_le {m k : ℕ}
    (initial : IntegralAllocation m k) (requests : List (Workload m))
    (allocations : List (IntegralAllocation m k))
    (hlength : allocations.length = requests.length) :
    movementFrom (integralResetPoint initial)
        (eventResetComparator requests allocations) ≤
      2 * pathCostFrom initial requests allocations := by
  induction requests generalizing initial allocations with
  | nil =>
      cases allocations with
      | nil => simp [eventResetComparator, movementFrom, pathCostFrom]
      | cons allocation allocations => simp at hlength
  | cons request requests inductionHypothesis =>
      cases allocations with
      | nil => simp at hlength
      | cons allocation allocations =>
          have htail : allocations.length = requests.length := by
            simp only [List.length_cons] at hlength
            omega
          have hrest := inductionHypothesis allocation allocations htail
          have hmovement : 0 ≤ movement initial allocation := by
            unfold movement
            positivity
          simp only [eventResetComparator, movementFrom, pathCostFrom,
            l1Distance_reset_event, l1Distance_event_reset]
          linarith

theorem l1Distance_triangle {ι : Type*} [Fintype ι]
    (first second third : ι → ℝ) :
    l1Distance first third ≤
      l1Distance first second + l1Distance second third := by
  unfold l1Distance
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro coordinate _
  calc
    |first coordinate - third coordinate| =
        |(first coordinate - second coordinate) +
          (second coordinate - third coordinate)| := by ring_nf
    _ ≤ |first coordinate - second coordinate| +
        |second coordinate - third coordinate| := abs_add_le _ _

theorem movementFrom_change_initial {ι : Type*} [Fintype ι]
    (first second : ι → ℝ) (path : List (ι → ℝ)) :
    movementFrom first path ≤ l1Distance first second +
      movementFrom second path := by
  cases path with
  | nil => simp [movementFrom, l1Distance_nonnegative]
  | cons point points =>
      simp only [movementFrom]
      linarith [l1Distance_triangle first second point]

def oddPositions {α : Type*} : List α → List α
  | [] => []
  | [point] => [point]
  | first :: _ :: remaining => first :: oddPositions remaining

theorem oddPositions_get? {α : Type*} (path : List α) (index : ℕ) :
    (oddPositions path)[index]? = path[2 * index]? := by
  induction index generalizing path with
  | zero =>
      cases path with
      | nil => simp [oddPositions]
      | cons first path =>
          cases path <;> simp [oddPositions]
  | succ index inductionHypothesis =>
      cases path with
      | nil => simp [oddPositions]
      | cons first path =>
          cases path with
          | nil => simp [oddPositions]
          | cons reset remaining =>
              simpa [oddPositions, Nat.mul_add, Nat.add_assoc] using
                inductionHypothesis remaining

theorem oddPositions_map_range_even {α : Type*} (rounds : ℕ)
    (point : ℕ → α) :
    oddPositions ((List.range (2 * rounds)).map point) =
      (List.range rounds).map fun round ↦ point (2 * round) := by
  apply List.ext_getElem?
  intro index
  rw [oddPositions_get?]
  by_cases hindex : index < rounds
  · have heven : 2 * index < 2 * rounds := by omega
    simp [List.getElem?_range hindex, List.getElem?_range heven]
  · have heven : ¬2 * index < 2 * rounds := by omega
    simp [hindex, heven]

theorem map_range_even_as_pairs {α : Type*} (rounds : ℕ)
    (point : ℕ → α) :
    (List.range (2 * rounds)).map point =
      (List.range rounds).flatMap fun round ↦
        [point (2 * round), point (2 * round + 1)] := by
  induction rounds with
  | zero => simp
  | succ rounds inductionHypothesis =>
      simp [Nat.mul_add, List.range_succ, inductionHypothesis]

theorem oddPositions_movement_le {ι : Type*} [Fintype ι]
    (initial : ι → ℝ) : ∀ path : List (ι → ℝ),
    movementFrom initial (oddPositions path) ≤ movementFrom initial path := by
  intro path
  induction path using List.twoStepInduction generalizing initial with
  | nil => simp [oddPositions, movementFrom]
  | singleton point => simp [oddPositions, movementFrom]
  | cons_cons first reset remaining inductionRemaining _ =>
      simp only [oddPositions, movementFrom]
      have hchange := movementFrom_change_initial first reset
        (oddPositions remaining)
      have htail := inductionRemaining reset
      linarith

noncomputable def previousResetDelta (time : ℕ) : ℝ :=
  if time = 0 then 0 else (1 / 2 : ℝ) ^ time

noncomputable def resetErrorSum : ℕ → ℕ → ℝ
  | _, 0 => 0
  | time, rounds + 1 =>
      previousResetDelta time + (1 / 2 : ℝ) ^ (time + 1) +
        resetErrorSum (time + 1) rounds

theorem resetErrorSum_bound (rounds : ℕ) : ∀ time : ℕ,
    resetErrorSum time rounds ≤
      if time = 0 then 2 else 3 * (1 / 2 : ℝ) ^ time := by
  induction rounds with
  | zero =>
      intro time
      simp [resetErrorSum]
      positivity
  | succ rounds inductionHypothesis =>
      intro time
      cases time with
      | zero =>
          have htail := inductionHypothesis 1
          norm_num [resetErrorSum, previousResetDelta] at htail ⊢
          linarith
      | succ time =>
          have htail := inductionHypothesis (time + 2)
          have htime : time + 2 ≠ 0 := by omega
          rw [if_neg htime] at htail
          have hpow : (1 / 2 : ℝ) ^ (time + 2) =
              ((1 / 2 : ℝ) ^ (time + 1)) / 2 := by
            rw [pow_succ]
            ring
          simp only [resetErrorSum, previousResetDelta, Nat.succ_ne_zero,
            ↓reduceIte]
          rw [hpow]
          have htail' : resetErrorSum (time + 2) rounds ≤
              3 * ((1 / 2 : ℝ) ^ (time + 1) / 2) := by
            calc
              resetErrorSum (time + 2) rounds
                  ≤ 3 * (1 / 2 : ℝ) ^ (time + 2) := htail
              _ = 3 * ((1 / 2 : ℝ) ^ (time + 1) / 2) := by rw [hpow]
          linarith

theorem resetErrorSum_zero_le_two (rounds : ℕ) :
    resetErrorSum 0 rounds ≤ 2 := by
  simpa using resetErrorSum_bound rounds 0

def pairCount {α : Type*} : List α → ℕ
  | _ :: _ :: remaining => pairCount remaining + 1
  | _ => 0

noncomputable def alternatingServiceCharge {m : ℕ} :
    List (BodyCoordinate m → ℝ) → ℝ
  | event :: _ :: remaining =>
      (8 / 3 : ℝ) * event none + alternatingServiceCharge remaining
  | _ => 0

noncomputable def geometricResetBounds {m : ℕ} :
    ℕ → List (BodyCoordinate m → ℝ) → Prop
  | _, [] => True
  | _, [_] => False
  | time, _ :: reset :: remaining =>
      reset none ≤ 2 * (1 / 2 : ℝ) ^ (time + 1) ∧
        geometricResetBounds (time + 1) remaining

theorem heightDistance_le_l1Distance {m : ℕ}
    (first second : BodyCoordinate m → ℝ) :
    |first none - second none| ≤ l1Distance first second := by
  unfold l1Distance
  exact Finset.single_le_sum
    (fun coordinate _ ↦ abs_nonneg (first coordinate - second coordinate))
    (Finset.mem_univ none)

theorem alternatingServiceCharge_le {m : ℕ}
    (path : List (BodyCoordinate m → ℝ)) :
    ∀ (time : ℕ) (previous : BodyCoordinate m → ℝ),
      geometricResetBounds time path →
      previous none ≤ 2 * previousResetDelta time →
      alternatingServiceCharge path ≤
        (4 / 3 : ℝ) * movementFrom previous path +
          (8 / 3 : ℝ) * resetErrorSum time (pairCount path) := by
  induction path using List.twoStepInduction with
  | nil =>
      intro time previous _ _
      simp [alternatingServiceCharge, movementFrom, pairCount, resetErrorSum]
  | singleton event =>
      intro time previous hbounds _
      simp [geometricResetBounds] at hbounds
  | cons_cons event reset remaining inductionRemaining _ =>
      intro time previous hbounds hprevious
      rcases hbounds with ⟨hreset, hremaining⟩
      have hnextPrevious :
          reset none ≤ 2 * previousResetDelta (time + 1) := by
        simpa [previousResetDelta] using hreset
      have htail := inductionRemaining (time + 1) reset hremaining hnextPrevious
      have hround := DynamicMoePositiveBody.shrinking_reset_charges_moe_service
        (event none) (previous none) (reset none)
        (previousResetDelta time) ((1 / 2 : ℝ) ^ (time + 1))
        hprevious hreset
      have hfirst := heightDistance_le_l1Distance previous event
      have hfirst' : |event none - previous none| ≤
          l1Distance previous event := by
        simpa [abs_sub_comm] using hfirst
      have hsecond := heightDistance_le_l1Distance event reset
      simp only [alternatingServiceCharge, movementFrom, pairCount,
        resetErrorSum]
      linarith

theorem liftedComparator_movement_le_pathCost {m k : ℕ}
    (initial : IntegralAllocation m k) (requests : List (Workload m))
    (allocations : List (IntegralAllocation m k))
    (hlength : allocations.length = requests.length) :
    movementFrom (fun _ : BodyCoordinate m ↦ 0)
        (eventResetComparator requests allocations) ≤
      (k : ℝ) + 2 * pathCostFrom initial requests allocations := by
  have hchange := movementFrom_change_initial
    (fun _ : BodyCoordinate m ↦ 0) (integralResetPoint initial)
    (eventResetComparator requests allocations)
  rw [l1Distance_zero_reset] at hchange
  linarith [liftedComparator_movementFrom_reset_le initial requests
    allocations hlength]

theorem selectedBodyChaser_movement_le_pathCost {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ} (hk : 1 ≤ k)
    (initial : IntegralAllocation m k) (requests : List (Workload m))
    (allocations : List (IntegralAllocation m k))
    (hlength : allocations.length = requests.length) :
    (selectedBodyChaser hchaser m).movement
        (eventResetBodies (m := m) (k := k) requests) ≤
      C * ((k : ℝ) + 2 * pathCostFrom initial requests allocations) := by
  calc
    (selectedBodyChaser hchaser m).movement
        (eventResetBodies (m := m) (k := k) requests)
        ≤ C * movementFrom (fun _ : BodyCoordinate m ↦ 0)
          (eventResetComparator requests allocations) :=
      selectedBodyChaser_movement_le_liftedComparator hchaser hk requests
        allocations hlength
    _ ≤ C * ((k : ℝ) + 2 * pathCostFrom initial requests allocations) :=
      mul_le_mul_of_nonneg_left
        (liftedComparator_movement_le_pathCost initial requests allocations hlength)
        hchaser.1

theorem selectedBodyChaser_movement_le_offlineOpt {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ} (hk : 1 ≤ k)
    (initial : IntegralAllocation m k) (requests : List (Workload m)) :
    (selectedBodyChaser hchaser m).movement
        (eventResetBodies (m := m) (k := k) requests) ≤
      C * ((k : ℝ) + 2 * offlineOpt initial requests) := by
  by_cases hCzero : C = 0
  · let allocations := List.replicate requests.length initial
    have hlength : allocations.length = requests.length := by
      simp [allocations]
    simpa [hCzero] using selectedBodyChaser_movement_le_pathCost
      hchaser hk initial requests allocations hlength
  · have hCpositive : 0 < C := lt_of_le_of_ne hchaser.1 (Ne.symm hCzero)
    have hlower :
        (((selectedBodyChaser hchaser m).movement
            (eventResetBodies (m := m) (k := k) requests)) / C - k) / 2 ≤
          offlineOpt initial requests := by
      unfold offlineOpt
      apply le_csInf
      · let allocations := List.replicate requests.length initial
        refine ⟨pathCostFrom initial requests allocations, ?_⟩
        exact ⟨allocations, by simp [allocations], rfl⟩
      · intro cost hcost
        rcases hcost with ⟨allocations, hlength, rfl⟩
        have hpath := selectedBodyChaser_movement_le_pathCost
          hchaser hk initial requests allocations hlength
        have hdiv :
            (selectedBodyChaser hchaser m).movement
                (eventResetBodies (m := m) (k := k) requests) / C ≤
              (k : ℝ) + 2 * pathCostFrom initial requests allocations :=
          (div_le_iff₀ hCpositive).2 (by simpa [mul_comm] using hpath)
        linarith
    have hdiv :
        (selectedBodyChaser hchaser m).movement
            (eventResetBodies (m := m) (k := k) requests) / C ≤
          (k : ℝ) + 2 * offlineOpt initial requests := by
      linarith
    exact (div_le_iff₀ hCpositive).1 hdiv |>.trans_eq (by ring)

noncomputable def currentEventPoint {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (requests : List (Workload m)) : BodyCoordinate m → ℝ :=
  (selectedBodyChaser hchaser m).choose
    (eventBodyHistory (m := m) (k := k) requests)

noncomputable def eventChaserPoints {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (requests : List (Workload m)) : List (BodyCoordinate m → ℝ) :=
  (List.range requests.length).map fun round ↦
    currentEventPoint hchaser (k := k) (requests.take (round + 1))

theorem eventChaserPoints_eq_odd_run {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (requests : List (Workload m)) :
    eventChaserPoints hchaser (k := k) requests =
      oddPositions ((selectedBodyChaser hchaser m).run
        (eventResetBodies (m := m) (k := k) requests)) := by
  unfold eventChaserPoints OnlineChaser.run
  rw [eventResetBodies_length, oddPositions_map_range_even]
  apply List.map_congr_left
  intro round hround
  have hroundBound : round < requests.length := List.mem_range.mp hround
  unfold currentEventPoint
  rw [eventBodyHistory_take_current round requests hroundBound]

theorem currentEventPoint_augmented {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (request : Workload m) (requests : List (Workload m)) :
    (eventBody (k := k) ((request :: requests).getLast (by simp))).AugmentedFeasible
      (currentEventPoint hchaser (k := k) (request :: requests)) := by
  have hspec := selectedBodyChaser_spec hchaser m
    (eventBodyHistory (m := m) (k := k) (request :: requests))
    (eventBodyHistory_covering_two_sparse (request :: requests))
    (eventBodyHistory_packing_positive_rightHandSide (request :: requests))
    (eventBodyHistory_nonempty_exact (request :: requests))
  have hcurrent := hspec.1 (eventBodyHistory_nonempty request requests)
  rw [eventBodyHistory_getLast request requests] at hcurrent
  exact hcurrent

theorem currentEventPoint_nonnegative {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (request : Workload m) (requests : List (Workload m)) (expert : Fin m) :
    0 ≤ bodyAllocation
      (currentEventPoint hchaser (k := k) (request :: requests)) expert := by
  exact (currentEventPoint_augmented hchaser request requests).1 (some expert)

theorem currentEventPoint_budget {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (hk : 1 ≤ k) (request : Workload m) (requests : List (Workload m)) :
    ∑ expert, bodyAllocation
        (currentEventPoint hchaser (k := k) (request :: requests)) expert ≤
      2 * k := by
  let point := currentEventPoint hchaser (k := k) (request :: requests)
  have hpacking := (currentEventPoint_augmented hchaser request requests).2.2
    (budgetRow (m := m) (k := k)) (by
      change budgetRow (m := m) (k := k) ∈ [budgetRow (m := m) (k := k)]
      exact List.mem_cons_self)
  rw [budgetRow_evaluate] at hpacking
  simp [budgetRow] at hpacking
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  change (∑ expert, point (some expert)) ≤ 2 * (k : ℝ)
  exact (div_le_iff₀ hkReal).1 hpacking

theorem currentEventPoint_coordinate_le {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (hk : 1 ≤ k) (request : Workload m) (requests : List (Workload m))
    (expert : Fin m) :
    currentEventPoint hchaser (k := k) (request :: requests) (some expert) ≤
      2 * k := by
  have hsingle : currentEventPoint hchaser (k := k)
      (request :: requests) (some expert) ≤
      ∑ candidate, currentEventPoint hchaser (k := k)
        (request :: requests) (some candidate) :=
    Finset.single_le_sum
      (fun candidate _ ↦
        (currentEventPoint_augmented hchaser request requests).1 (some candidate))
      (Finset.mem_univ expert)
  exact hsingle.trans (currentEventPoint_budget hchaser hk request requests)

theorem currentEventPoint_envelope {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (hk : 1 ≤ k) (request : Workload m) (requests : List (Workload m))
    (expert : Fin m) :
    (3 / 4 : ℝ) *
        (((request :: requests).getLast (by simp)).value expert /
          (1 + currentEventPoint hchaser (k := k)
            (request :: requests) (some expert))) ≤
      currentEventPoint hchaser (k := k) (request :: requests) none := by
  let currentRequest := (request :: requests).getLast (by simp)
  let point := currentEventPoint hchaser (k := k) (request :: requests)
  let q := 1 + point (some expert)
  have hpointNonnegative : 0 ≤ point (some expert) :=
    (currentEventPoint_augmented hchaser request requests).1 (some expert)
  have hheightNonnegative : 0 ≤ point none :=
    (currentEventPoint_augmented hchaser request requests).1 none
  have hq : 1 ≤ q := by dsimp [q]; linarith
  have hqk : q ≤ 1 + 2 * (k : ℝ) := by
    dsimp [q, point]
    linarith [currentEventPoint_coordinate_le hchaser hk request requests expert]
  obtain ⟨n, hnPositive, hnBound, htangent⟩ :=
    DynamicMoePositiveBody.integer_grid_tangent_captures_three_quarters
      (currentRequest.value expert) q k (currentRequest.nonnegative expert) hq hqk
  let scaleIndex : Fin (2 * k + 1) := ⟨n - 1, by omega⟩
  have hscale : ((scaleIndex.val : ℝ) + 1) = n := by
    dsimp [scaleIndex]
    have : n - 1 + 1 = n := Nat.sub_add_cancel hnPositive
    exact_mod_cast this
  by_cases hrequestZero : currentRequest.value expert = 0
  · simpa [currentRequest, point, hrequestZero] using hheightNonnegative
  · have hrequestPositive : 0 < currentRequest.value expert :=
      lt_of_le_of_ne (currentRequest.nonnegative expert) (Ne.symm hrequestZero)
    have hfeasible := currentEventPoint_augmented (k := k)
      hchaser request requests
    have hmembership : tangentRow currentRequest expert scaleIndex ∈
        (eventBody (k := k) currentRequest).covering := by
      simp only [eventBody, List.mem_map, Finset.mem_toList]
      exact ⟨(expert, scaleIndex), Finset.mem_univ _, rfl⟩
    have hrow := hfeasible.2.1 (tangentRow currentRequest expert scaleIndex)
      hmembership
    have hbelow := tangentRow_forces_height currentRequest point hfeasible.1
      expert scaleIndex hrow
    rw [hscale] at hbelow
    dsimp [currentRequest, q, point] at htangent ⊢
    exact htangent.trans hbelow

theorem eventResetBodiesFrom_nonempty {m k : ℕ} (time : ℕ)
    (request : Workload m) (requests : List (Workload m)) :
    eventResetBodiesFrom (m := m) (k := k) time
      (request :: requests) ≠ [] := by
  simp [eventResetBodiesFrom]

theorem eventResetBodiesFrom_getLast? {m k : ℕ} (time : ℕ)
    (request : Workload m) (requests : List (Workload m)) :
    (eventResetBodiesFrom (m := m) (k := k) time
      (request :: requests)).getLast? =
      some (resetBody (m := m) (k := k) (time + requests.length)) := by
  induction requests generalizing time request with
  | nil => simp [eventResetBodiesFrom]
  | cons nextRequest remaining inductionHypothesis =>
      have hlast := inductionHypothesis (time + 1) nextRequest
      simp only [eventResetBodiesFrom, List.getLast?_cons_cons] at hlast ⊢
      have htime : time + 1 + remaining.length =
          time + (remaining.length + 1) := by omega
      simpa [htime] using hlast

theorem eventResetBodiesFrom_getLast {m k : ℕ} (time : ℕ)
    (request : Workload m) (requests : List (Workload m)) :
    (eventResetBodiesFrom (m := m) (k := k) time
      (request :: requests)).getLast
        (eventResetBodiesFrom_nonempty time request requests) =
      resetBody (m := m) (k := k) (time + requests.length) := by
  have hlast := eventResetBodiesFrom_getLast? (m := m) (k := k)
    time request requests
  rw [List.getLast?_eq_getLast_of_ne_nil
    (eventResetBodiesFrom_nonempty time request requests)] at hlast
  exact Option.some.inj hlast

theorem eventResetBodies_nonempty {m k : ℕ}
    (request : Workload m) (requests : List (Workload m)) :
    eventResetBodies (m := m) (k := k) (request :: requests) ≠ [] := by
  exact eventResetBodiesFrom_nonempty 0 request requests

theorem eventResetBodies_getLast {m k : ℕ}
    (request : Workload m) (requests : List (Workload m)) :
    (eventResetBodies (m := m) (k := k)
      (request :: requests)).getLast
        (eventResetBodies_nonempty request requests) =
      resetBody (m := m) (k := k) requests.length := by
  simpa [eventResetBodies] using
    eventResetBodiesFrom_getLast (m := m) (k := k) 0 request requests

noncomputable def currentResetPoint {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (requests : List (Workload m)) : BodyCoordinate m → ℝ :=
  (selectedBodyChaser hchaser m).choose
    (eventResetBodies (m := m) (k := k) requests)

theorem currentResetPoint_augmented {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (request : Workload m) (requests : List (Workload m)) :
    (resetBody (m := m) (k := k) requests.length).AugmentedFeasible
      (currentResetPoint hchaser (k := k) (request :: requests)) := by
  have hspec := selectedBodyChaser_spec hchaser m
    (eventResetBodies (m := m) (k := k) (request :: requests))
    (eventResetBodies_covering_two_sparse (request :: requests))
    (eventResetBodies_packing_positive_rightHandSide (request :: requests))
    (eventResetBodies_nonempty_exact (request :: requests))
  have hcurrent := hspec.1 (eventResetBodies_nonempty request requests)
  rw [eventResetBodies_getLast request requests] at hcurrent
  exact hcurrent

theorem resetHeightRow_evaluate {m : ℕ} (time : ℕ)
    (point : BodyCoordinate m → ℝ) :
    (resetHeightRow (m := m) time).evaluate point =
      point none / ((1 / 2 : ℝ) ^ (time + 1)) := by
  simp [PositiveRow.evaluate, resetHeightRow, div_eq_mul_inv, mul_comm]

theorem currentResetPoint_height_bound {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (request : Workload m) (requests : List (Workload m)) :
    currentResetPoint hchaser (k := k) (request :: requests) none ≤
      2 * (1 / 2 : ℝ) ^ (requests.length + 1) := by
  have hpacking :=
    (currentResetPoint_augmented (k := k) hchaser request requests).2.2
    (resetHeightRow (m := m) requests.length) (by
      simp [resetBody])
  rw [resetHeightRow_evaluate] at hpacking
  have hpackingRight :
      (resetHeightRow (m := m) requests.length).rightHandSide = 1 := rfl
  rw [hpackingRight, mul_one] at hpacking
  have hdelta : 0 < (1 / 2 : ℝ) ^ (requests.length + 1) := by positivity
  exact (div_le_iff₀ hdelta).1 hpacking

theorem currentResetPoint_take_height_bound {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (requests : List (Workload m)) (round : ℕ)
    (hround : round < requests.length) :
    currentResetPoint hchaser (k := k) (requests.take (round + 1)) none ≤
      2 * (1 / 2 : ℝ) ^ (round + 1) := by
  have htakeLength : (requests.take (round + 1)).length = round + 1 := by
    rw [List.length_take]
    exact Nat.min_eq_left (Nat.succ_le_iff.mpr hround)
  have hnonempty := take_current_nonempty requests round hround
  cases hprefix : requests.take (round + 1) with
  | nil => exact (hnonempty hprefix).elim
  | cons request remaining =>
      have hremaining : remaining.length = round := by
        rw [hprefix, List.length_cons] at htakeLength
        omega
      have hbound := currentResetPoint_height_bound
        (k := k) hchaser request remaining
      simpa [hprefix, hremaining] using hbound

noncomputable def eventResetChaserPathFrom {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (requests : List (Workload m)) : ℕ → ℕ → List (BodyCoordinate m → ℝ)
  | _, 0 => []
  | time, rounds + 1 =>
      currentEventPoint hchaser (k := k) (requests.take (time + 1)) ::
        currentResetPoint hchaser (k := k) (requests.take (time + 1)) ::
          eventResetChaserPathFrom (k := k) hchaser requests (time + 1) rounds

theorem eventResetChaserPathFrom_eq_range' {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (requests : List (Workload m)) (rounds : ℕ) : ∀ time : ℕ,
    eventResetChaserPathFrom hchaser (k := k) requests time rounds =
      (List.range' time rounds).flatMap fun round ↦
        [currentEventPoint hchaser (k := k) (requests.take (round + 1)),
          currentResetPoint hchaser (k := k) (requests.take (round + 1))] := by
  induction rounds with
  | zero => simp [eventResetChaserPathFrom]
  | succ rounds inductionHypothesis =>
      intro time
      simp [eventResetChaserPathFrom, inductionHypothesis (time + 1),
        List.range'_succ]

theorem eventResetChaserPathFrom_geometricResetBounds {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (requests : List (Workload m)) (rounds : ℕ) : ∀ time : ℕ,
    time + rounds ≤ requests.length →
      geometricResetBounds time
        (eventResetChaserPathFrom hchaser (k := k) requests time rounds) := by
  induction rounds with
  | zero =>
      intro time _
      simp [eventResetChaserPathFrom, geometricResetBounds]
  | succ rounds inductionHypothesis =>
      intro time hspan
      have hround : time < requests.length := by omega
      simp only [eventResetChaserPathFrom, geometricResetBounds]
      exact ⟨currentResetPoint_take_height_bound hchaser requests time hround,
        inductionHypothesis (time + 1) (by omega)⟩

theorem alternatingServiceCharge_eventResetChaserPathFrom {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (requests : List (Workload m)) (rounds : ℕ) : ∀ time : ℕ,
    alternatingServiceCharge
        (eventResetChaserPathFrom hchaser (k := k) requests time rounds) =
      ((List.range' time rounds).map fun round ↦
        (8 / 3 : ℝ) * currentEventPoint hchaser (k := k)
          (requests.take (round + 1)) none).sum := by
  induction rounds with
  | zero =>
      intro time
      simp [eventResetChaserPathFrom, alternatingServiceCharge]
  | succ rounds inductionHypothesis =>
      intro time
      simp [eventResetChaserPathFrom, alternatingServiceCharge,
        List.range'_succ, inductionHypothesis (time + 1)]

noncomputable def eventResetChaserPath {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (requests : List (Workload m)) : List (BodyCoordinate m → ℝ) :=
  (List.range requests.length).flatMap fun round ↦
    let history := requests.take (round + 1)
    [currentEventPoint hchaser (k := k) history,
      currentResetPoint hchaser (k := k) history]

theorem eventResetChaserPath_eq_from {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (requests : List (Workload m)) :
    eventResetChaserPath hchaser (k := k) requests =
      eventResetChaserPathFrom hchaser (k := k) requests 0 requests.length := by
  unfold eventResetChaserPath
  rw [List.range_eq_range']
  exact (eventResetChaserPathFrom_eq_range' hchaser requests
    requests.length 0).symm

theorem eventResetChaserPath_geometricResetBounds {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (requests : List (Workload m)) :
    geometricResetBounds 0 (eventResetChaserPath hchaser (k := k) requests) := by
  rw [eventResetChaserPath_eq_from]
  exact eventResetChaserPathFrom_geometricResetBounds hchaser requests
    requests.length 0 (by simp)

theorem alternatingServiceCharge_eventResetChaserPath {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (requests : List (Workload m)) :
    alternatingServiceCharge (eventResetChaserPath hchaser (k := k) requests) =
      ((revealedHistories requests).map fun history ↦
        (8 / 3 : ℝ) * currentEventPoint hchaser (k := k)
          history.val none).sum := by
  rw [eventResetChaserPath_eq_from,
    alternatingServiceCharge_eventResetChaserPathFrom]
  congr 1
  apply List.ext_getElem
  · simp [revealedHistories]
  · intro round hleft hright
    simp [revealedHistories]

theorem selectedBodyChaser_run_eq_eventResetChaserPath {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (requests : List (Workload m)) :
    (selectedBodyChaser hchaser m).run
        (eventResetBodies (m := m) (k := k) requests) =
      eventResetChaserPath hchaser (k := k) requests := by
  unfold OnlineChaser.run eventResetChaserPath
  rw [eventResetBodies_length, map_range_even_as_pairs]
  apply List.flatMap_congr
  intro round hround
  have hroundBound : round < requests.length := List.mem_range.mp hround
  have hevent :
      (selectedBodyChaser hchaser m).choose
          ((eventResetBodies (m := m) (k := k) requests).take
            (2 * round + 1)) =
        currentEventPoint hchaser (k := k)
          (requests.take (round + 1)) := by
    unfold currentEventPoint
    rw [eventBodyHistory_take_current round requests hroundBound]
  have hreset :
      (selectedBodyChaser hchaser m).choose
          ((eventResetBodies (m := m) (k := k) requests).take
            (2 * round + 2)) =
        currentResetPoint hchaser (k := k)
          (requests.take (round + 1)) := by
    unfold currentResetPoint
    rw [eventResetBodies_take (round + 1) requests]
    congr 2
  simp [hevent, hreset, Nat.add_assoc]

theorem selectedBodyChaser_serviceCharge_le {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (requests : List (Workload m)) :
    alternatingServiceCharge
        ((selectedBodyChaser hchaser m).run
          (eventResetBodies (m := m) (k := k) requests)) ≤
      (4 / 3 : ℝ) * (selectedBodyChaser hchaser m).movement
          (eventResetBodies (m := m) (k := k) requests) + 16 / 3 := by
  let path := eventResetChaserPath hchaser (k := k) requests
  have hbounds : geometricResetBounds 0 path :=
    eventResetChaserPath_geometricResetBounds hchaser requests
  have hprevious : (fun _ : BodyCoordinate m ↦ 0) none ≤
      2 * previousResetDelta 0 := by simp [previousResetDelta]
  have hcharge := alternatingServiceCharge_le path 0
    (fun _ : BodyCoordinate m ↦ 0) hbounds hprevious
  have herror := resetErrorSum_zero_le_two (pairCount path)
  have hrun := selectedBodyChaser_run_eq_eventResetChaserPath
    (k := k) hchaser requests
  unfold OnlineChaser.movement
  rw [hrun]
  change alternatingServiceCharge path ≤ _
  linarith

noncomputable def currentEventAugmentedAllocation {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (hk : 1 ≤ k) (request : Workload m) (requests : List (Workload m)) :
    AugmentedAllocation m k where
  value := bodyAllocation
    (currentEventPoint hchaser (k := k) (request :: requests))
  nonnegative := currentEventPoint_nonnegative hchaser request requests
  budget := currentEventPoint_budget hchaser hk request requests

def zeroAugmentedAllocation (m k : ℕ) : AugmentedAllocation m k where
  value _ := 0
  nonnegative _ := le_rfl
  budget := by simp

noncomputable def currentEventAugmentedChoice {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ} (hk : 1 ≤ k) :
    List (Workload m) → AugmentedAllocation m k
  | [] => zeroAugmentedAllocation m k
  | request :: requests =>
      currentEventAugmentedAllocation hchaser hk request requests

noncomputable def eventAugmentedPath {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ} (hk : 1 ≤ k)
    (requests : List (Workload m)) : List (AugmentedAllocation m k) :=
  (List.range requests.length).map fun round ↦
    currentEventAugmentedChoice hchaser hk (requests.take (round + 1))

theorem eventAugmentedPath_values {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ} (hk : 1 ≤ k)
    (requests : List (Workload m)) :
    (eventAugmentedPath hchaser hk requests).map
        (fun allocation ↦ allocation.value) =
      (eventChaserPoints hchaser (k := k) requests).map bodyAllocation := by
  unfold eventAugmentedPath eventChaserPoints
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro round hround
  have hroundBound : round < requests.length := List.mem_range.mp hround
  have hnonempty := take_current_nonempty requests round hroundBound
  cases hhistory : requests.take (round + 1) with
  | nil => exact (hnonempty hhistory).elim
  | cons request remaining =>
      simp [currentEventAugmentedChoice, hhistory,
        currentEventAugmentedAllocation]

noncomputable def positiveBodyFractionalAlgorithm {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (hk : 1 ≤ k) (hm : 0 < m) (initial : IntegralAllocation m k) :
    FractionalOnlineAlgorithm m k where
  choose history :=
    match history with
    | [] => initial.toFractional
    | request :: requests =>
        (currentEventAugmentedAllocation hchaser hk request requests).toBalancedFractional hm

theorem positiveBodyFractionalAlgorithm_run {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (hk : 1 ≤ k) (hm : 0 < m) (initial : IntegralAllocation m k)
    (requests : List (Workload m)) :
    (positiveBodyFractionalAlgorithm hchaser hk hm initial).run requests =
      (eventAugmentedPath hchaser hk requests).map
        (fun allocation ↦ allocation.toBalancedFractional hm) := by
  unfold FractionalOnlineAlgorithm.run eventAugmentedPath
  rw [List.map_map]
  apply List.map_congr_left
  intro round hround
  have hroundBound : round < requests.length := List.mem_range.mp hround
  have hnonempty := take_current_nonempty requests round hroundBound
  cases hhistory : requests.take (round + 1) with
  | nil => exact (hnonempty hhistory).elim
  | cons request remaining =>
      simp [positiveBodyFractionalAlgorithm, currentEventAugmentedChoice, hhistory]

theorem positiveBodyFractionalAlgorithm_movementBridge {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (hk : 1 ≤ k) (hm : 0 < m) (initial : IntegralAllocation m k)
    (requests : List (Workload m)) :
    (positiveBodyFractionalAlgorithm hchaser hk hm initial).movementCost
        initial requests ≤
      (selectedBodyChaser hchaser m).movement
        (eventResetBodies (m := m) (k := k) requests) + 2 * k := by
  have hbalanced := balancedPath_movement_le hm initial
    (eventAugmentedPath hchaser hk requests)
  rw [eventAugmentedPath_values hchaser hk requests] at hbalanced
  have hprojection := movementFrom_bodyAllocation_le
    (fun _ : BodyCoordinate m ↦ 0)
    (eventChaserPoints hchaser (k := k) requests)
  have hprojection' :
      movementFrom (fun _ : Fin m ↦ 0)
          ((eventChaserPoints hchaser (k := k) requests).map bodyAllocation) ≤
        movementFrom (fun _ : BodyCoordinate m ↦ 0)
          (eventChaserPoints hchaser (k := k) requests) := by
    change movementFrom (bodyAllocation (fun _ : BodyCoordinate m ↦ 0))
        ((eventChaserPoints hchaser (k := k) requests).map bodyAllocation) ≤ _
    exact hprojection
  have hodd := oddPositions_movement_le
    (fun _ : BodyCoordinate m ↦ 0)
    ((selectedBodyChaser hchaser m).run
      (eventResetBodies (m := m) (k := k) requests))
  rw [← eventChaserPoints_eq_odd_run hchaser requests] at hodd
  have hbody :
      movementFrom (fun _ : BodyCoordinate m ↦ 0)
          (eventChaserPoints hchaser (k := k) requests) ≤
        (selectedBodyChaser hchaser m).movement
          (eventResetBodies (m := m) (k := k) requests) := by
    simpa [OnlineChaser.movement] using hodd
  unfold FractionalOnlineAlgorithm.movementCost
  rw [positiveBodyFractionalAlgorithm_run hchaser hk hm initial requests]
  linarith

theorem positiveBodyFractionalAlgorithm_pointwise_service {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (hk : 1 ≤ k) (hm : 0 < m) (initial : IntegralAllocation m k)
    (request : Workload m) (requests : List (Workload m)) :
    fractionalLatency ((request :: requests).getLast (by simp))
        ((positiveBodyFractionalAlgorithm hchaser hk hm initial).choose
          (request :: requests)) ≤
      (8 / 3 : ℝ) *
        currentEventPoint hchaser (k := k) (request :: requests) none := by
  let currentRequest := (request :: requests).getLast (by simp)
  let allocation := currentEventAugmentedAllocation hchaser hk request requests
  have hheight : 0 ≤ currentEventPoint hchaser (k := k)
      (request :: requests) none :=
    (currentEventPoint_augmented hchaser request requests).1 none
  have henvelope : ∀ expert : Fin m,
      (3 / 4 : ℝ) *
          (currentRequest.value expert / (1 + allocation.value expert)) ≤
        currentEventPoint hchaser (k := k) (request :: requests) none := by
    intro expert
    simpa [currentRequest, allocation, currentEventAugmentedAllocation,
      bodyAllocation] using
      currentEventPoint_envelope hchaser hk request requests expert
  have hservice := balanced_map_service_loss_eight_thirds currentRequest
    allocation hm (currentEventPoint hchaser (k := k)
      (request :: requests) none) hheight henvelope
  simpa [currentRequest, allocation, positiveBodyFractionalAlgorithm] using hservice

theorem positiveBodyFractionalAlgorithm_history_service {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (hk : 1 ≤ k) (hm : 0 < m) (initial : IntegralAllocation m k)
    (history : NonemptyWorkloadHistory m) :
    fractionalLatency (revealedRequest history)
        ((positiveBodyFractionalAlgorithm hchaser hk hm initial).choose
          history.val) ≤
      (8 / 3 : ℝ) * currentEventPoint hchaser (k := k) history.val none := by
  rcases history with ⟨history, hnonempty⟩
  cases history with
  | nil => exact (hnonempty rfl).elim
  | cons request requests =>
      simpa [revealedRequest] using
        positiveBodyFractionalAlgorithm_pointwise_service
          hchaser hk hm initial request requests

theorem positiveBodyFractionalAlgorithm_serviceTerms_le {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (hk : 1 ≤ k) (hm : 0 < m) (initial : IntegralAllocation m k) :
    ∀ histories : List (NonemptyWorkloadHistory m),
    (histories.map fun history ↦
        fractionalLatency (revealedRequest history)
          ((positiveBodyFractionalAlgorithm hchaser hk hm initial).choose
            history.val)).sum ≤
      (histories.map fun history ↦
        (8 / 3 : ℝ) * currentEventPoint hchaser (k := k)
          history.val none).sum := by
  intro histories
  induction histories with
  | nil => simp
  | cons history histories inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      have hhead := positiveBodyFractionalAlgorithm_history_service
        hchaser hk hm initial history
      linarith

theorem positiveBodyFractionalAlgorithm_serviceBridge {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser C) {m k : ℕ}
    (hk : 1 ≤ k) (hm : 0 < m) (initial : IntegralAllocation m k)
    (requests : List (Workload m)) :
    (positiveBodyFractionalAlgorithm hchaser hk hm initial).serviceCost requests ≤
      (4 / 3 : ℝ) * (selectedBodyChaser hchaser m).movement
          (eventResetBodies (m := m) (k := k) requests) + 16 / 3 := by
  let algorithm := positiveBodyFractionalAlgorithm hchaser hk hm initial
  calc
    algorithm.serviceCost requests =
        ((revealedHistories requests).map fun history ↦
          fractionalLatency (revealedRequest history)
            (algorithm.choose history.val)).sum := by
      unfold FractionalOnlineAlgorithm.serviceCost
      calc
        fractionalServiceFrom requests (algorithm.run requests) =
            fractionalServiceFrom
              ((revealedHistories requests).map revealedRequest)
              ((revealedHistories requests).map
                fun history ↦ algorithm.choose history.val) := by
          rw [revealedRequests_eq requests, revealedRun_eq algorithm requests]
        _ = ((revealedHistories requests).map fun history ↦
              fractionalLatency (revealedRequest history)
                (algorithm.choose history.val)).sum :=
          fractionalServiceFrom_revealed algorithm (revealedHistories requests)
    _ ≤ ((revealedHistories requests).map fun history ↦
        (8 / 3 : ℝ) * currentEventPoint hchaser (k := k)
          history.val none).sum :=
      positiveBodyFractionalAlgorithm_serviceTerms_le
        hchaser hk hm initial (revealedHistories requests)
    _ = alternatingServiceCharge
        (eventResetChaserPath hchaser (k := k) requests) :=
      (alternatingServiceCharge_eventResetChaserPath hchaser requests).symm
    _ = alternatingServiceCharge
        ((selectedBodyChaser hchaser m).run
          (eventResetBodies (m := m) (k := k) requests)) := by
      rw [selectedBodyChaser_run_eq_eventResetChaserPath]
    _ ≤ (4 / 3 : ℝ) * (selectedBodyChaser hchaser m).movement
          (eventResetBodies (m := m) (k := k) requests) + 16 / 3 :=
      selectedBodyChaser_serviceCharge_le hchaser requests

theorem hasPositiveBodyFractionalReduction_of_twoSparseChaser {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser.{0} C) :
    HasPositiveBodyFractionalReduction C := by
  intro k hk m hm initial
  refine ⟨{
    algorithm := positiveBodyFractionalAlgorithm hchaser hk hm initial
    bodyMovement := fun requests ↦
      (selectedBodyChaser hchaser m).movement
        (eventResetBodies (m := m) (k := k) requests)
    bodyBound := ?_
    movementBridge := ?_
    serviceBridge := ?_
  }⟩
  · intro requests
    exact selectedBodyChaser_movement_le_offlineOpt
      hchaser hk initial requests
  · intro requests
    exact positiveBodyFractionalAlgorithm_movementBridge
      hchaser hk hm initial requests
  · intro requests
    exact positiveBodyFractionalAlgorithm_serviceBridge
      hchaser hk hm initial requests

end DynamicMoePositiveBodyReduction
