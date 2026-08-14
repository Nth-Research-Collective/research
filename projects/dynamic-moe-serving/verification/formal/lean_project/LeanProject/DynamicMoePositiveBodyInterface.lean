import Mathlib.Tactic

/-!
Primitive semantic boundary for Bhattacharya--Buchbinder--Levin--Saranurak's
positive-body chasing theorem at resource augmentation `ε = 1` and covering
row sparsity two. This file is deliberately independent of Dynamic MoE.
-/

open scoped BigOperators

namespace DynamicMoePositiveBodyInterface

structure PositiveRow (ι : Type*) [Fintype ι] [DecidableEq ι] where
  coefficient : ι → ℝ
  nonnegative : ∀ i, 0 ≤ coefficient i
  rightHandSide : ℝ
  rightHandSide_nonnegative : 0 ≤ rightHandSide

def PositiveRow.evaluate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (row : PositiveRow ι) (point : ι → ℝ) : ℝ :=
  ∑ i, row.coefficient i * point i

noncomputable def PositiveRow.support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (row : PositiveRow ι) : Finset ι :=
  Finset.univ.filter fun i ↦ row.coefficient i ≠ 0

noncomputable def PositiveRow.IsTwoSparse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (row : PositiveRow ι) : Prop :=
  row.support.card ≤ 2

structure PositiveBody (ι : Type*) [Fintype ι] [DecidableEq ι] where
  covering : List (PositiveRow ι)
  packing : List (PositiveRow ι)

noncomputable def PositiveBody.CoveringTwoSparse {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    (body : PositiveBody ι) : Prop :=
  ∀ row ∈ body.covering, row.IsTwoSparse

/-- The cited theorem normalizes packing rows to right-hand side one. Strictly
positive right-hand sides are exactly the rows that admit this normalization;
zero-right-hand-side covering rows remain harmless because they are vacuous. -/
def PositiveBody.PackingPositiveRightHandSide {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    (body : PositiveBody ι) : Prop :=
  ∀ row ∈ body.packing, 0 < row.rightHandSide

def PositiveBody.ExactFeasible {ι : Type*} [Fintype ι] [DecidableEq ι]
    (body : PositiveBody ι) (point : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ point i) ∧
    (∀ row ∈ body.covering, row.rightHandSide ≤ row.evaluate point) ∧
    (∀ row ∈ body.packing, row.evaluate point ≤ row.rightHandSide)

/-- `ε = 1`: covering rows remain exact and packing rows may reach twice their
right-hand side. -/
def PositiveBody.AugmentedFeasible {ι : Type*} [Fintype ι] [DecidableEq ι]
    (body : PositiveBody ι) (point : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ point i) ∧
    (∀ row ∈ body.covering, row.rightHandSide ≤ row.evaluate point) ∧
    (∀ row ∈ body.packing,
      row.evaluate point ≤ 2 * row.rightHandSide)

def l1Distance {ι : Type*} [Fintype ι] (first second : ι → ℝ) : ℝ :=
  ∑ i, |first i - second i|

def movementFrom {ι : Type*} [Fintype ι]
    (initial : ι → ℝ) : List (ι → ℝ) → ℝ
  | [] => 0
  | point :: points => l1Distance initial point + movementFrom point points

structure OnlineChaser (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- Dependence on the revealed body history is the causality condition. -/
  choose : List (PositiveBody ι) → (ι → ℝ)

def OnlineChaser.run {ι : Type*} [Fintype ι] [DecidableEq ι]
    (chaser : OnlineChaser ι) (bodies : List (PositiveBody ι)) :
    List (ι → ℝ) :=
  (List.range bodies.length).map fun t ↦
    chaser.choose (bodies.take (t + 1))

theorem OnlineChaser.run_length {ι : Type*} [Fintype ι] [DecidableEq ι]
    (chaser : OnlineChaser ι) (bodies : List (PositiveBody ι)) :
    (chaser.run bodies).length = bodies.length := by
  simp [OnlineChaser.run]

def OnlineChaser.movement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (chaser : OnlineChaser ι) (bodies : List (PositiveBody ι)) : ℝ :=
  movementFrom (fun _ : ι ↦ 0) (chaser.run bodies)

def IsExactComparatorPath {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bodies : List (PositiveBody ι)) (path : List (ι → ℝ)) : Prop :=
  List.Forall₂ (fun body point ↦ body.ExactFeasible point) bodies path

/-- Exact primitive contract supplied by the cited positive-body theorem at
`ε = 1`, after normalizing positive packing right-hand sides, deleting vacuous
zero-right-hand-side covering rows, and absorbing the standard
upward-to-full-`L1` factor into `C`. It mentions no MoE cost. -/
def HasTwoSparsePositiveBodyChaser (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (ι : Type*) [Fintype ι] [DecidableEq ι],
    ∃ chaser : OnlineChaser ι,
      ∀ bodies : List (PositiveBody ι),
        (∀ body ∈ bodies, body.CoveringTwoSparse) →
        (∀ body ∈ bodies, body.PackingPositiveRightHandSide) →
        (∀ body ∈ bodies, ∃ point, body.ExactFeasible point) →
        (∀ hnonempty : bodies ≠ [],
          (bodies.getLast hnonempty).AugmentedFeasible
            (chaser.choose bodies)) ∧
        ∀ comparator : List (ι → ℝ),
          IsExactComparatorPath bodies comparator →
          chaser.movement bodies ≤
            C * movementFrom (fun _ : ι ↦ 0) comparator

theorem l1Distance_nonnegative {ι : Type*} [Fintype ι]
    (first second : ι → ℝ) : 0 ≤ l1Distance first second := by
  unfold l1Distance
  positivity

theorem movementFrom_nonnegative {ι : Type*} [Fintype ι]
    (initial : ι → ℝ) : ∀ path, 0 ≤ movementFrom initial path := by
  intro path
  induction path generalizing initial with
  | nil => simp [movementFrom]
  | cons point path inductionHypothesis =>
      simp only [movementFrom]
      exact add_nonneg (l1Distance_nonnegative initial point)
        (inductionHypothesis point)

end DynamicMoePositiveBodyInterface
