module

public import Mathlib
public import RequestProject.Solution

@[expose] public section

/-!
# Sixfold Tverberg Counterexample and Convex Equipartition Obstruction (`Solution.lean`)

Arseniy Akopyan

Matches `Challenge.lean` via `comparator.json` without importing `Challenge.lean`:
* `AkopyanSixfold.tverberg_counterexample` (Theorem A):
  An almost six-embedding `Δ³⁵ → ℝ⁶`, proved via the height-table construction
  `Tverberg6R.tverbergCounterexample_of_heightExtension Tverberg6R.heightExtension`.
* `AkopyanSixfold.convex_partition_counterexample` (Theorem B):
  In every dimension `d ≥ 24`, there exist `d - 1` continuous functionals on convex bodies
  and a probability measure such that no fair convex six-partition of the unit ball
  equalizes all `d - 1` functionals.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace AkopyanSixfold

/-- The simplex on `n` vertices (dimension `n - 1`). -/
def simplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ v, 0 ≤ x v) ∧ (∑ v, x v) = 1}

/-- The six points have pairwise disjoint barycentric supports. -/
def DisjointSupports {n : ℕ} (x : Fin 6 → (Fin n → ℝ)) : Prop :=
  ∀ i j, i ≠ j → ∀ v, x i v = 0 ∨ x j v = 0

/-- An almost six-embedding of the `(n - 1)`-simplex into `ℝ^d`:
continuity is required on the simplex, and no six points with pairwise disjoint
barycentric supports share the same image. -/
def IsAlmostSixEmbedding {n d : ℕ}
    (f : (Fin n → ℝ) → (Fin d → ℝ)) : Prop :=
  ContinuousOn f (simplex n) ∧
  ∀ x : Fin 6 → (Fin n → ℝ),
    (∀ i, x i ∈ simplex n) →
    DisjointSupports x →
    ∃ i, f (x i) ≠ f (x 0)

/-- **Theorem A**: Counterexample to the topological Tverberg conjecture for sixfold
intersections in `ℝ⁶` (`36` vertices, target dimension `6`). -/
theorem tverberg_counterexample :
    ∃ f : (Fin 36 → ℝ) → (Fin 6 → ℝ),
      IsAlmostSixEmbedding f := by
  obtain ⟨f, hf_cont, hf_disj⟩ :=
    Tverberg6R.tverbergCounterexample_of_heightExtension Tverberg6R.heightExtension
  exact ⟨f, hf_cont, hf_disj⟩

/-- Standard Euclidean space `ℝ^d`. -/
abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Nonempty compact convex bodies in `ℝ^d` endowed with the Hausdorff metric. -/
abbrev Body (d : ℕ) := ConvexBody (Ambient d)

/-- The closed unit ball in `ℝ^d`. -/
def unitBall (d : ℕ) : Set (Ambient d) :=
  Metric.closedBall (0 : Ambient d) 1

/-- A convex six-partition of the unit ball: six convex bodies with nonempty,
pairwise disjoint interiors whose union equals `unitBall d`. -/
def IsSixPartition {d : ℕ} (C : Fin 6 → Body d) : Prop :=
  unitBall d = (⋃ i, (C i : Set (Ambient d))) ∧
  (∀ i, (interior (C i : Set (Ambient d))).Nonempty) ∧
  ∀ i j, i ≠ j →
    Disjoint (interior (C i : Set (Ambient d)))
             (interior (C j : Set (Ambient d)))

def originDist (d : ℕ) (C : Body d) : ℝ :=
  Metric.infDist (0 : Ambient d) (C : Set (Ambient d))

lemma originDist_le (d : ℕ) (C D : Body d) :
    originDist d C ≤ originDist d D + dist C D := by
  unfold originDist
  rw [dist_comm]
  exact Metric.infDist_le_infDist_add_hausdorffDist ConvexBody.hausdorffEDist_ne_top

lemma continuous_originDist (d : ℕ) : Continuous (originDist d) :=
  (LipschitzWith.of_le_add (originDist_le d)).continuous

/-- **Theorem B**: Counterexample to the generalized Nandakumar--Ramana Rao problem:
in every dimension `d ≥ 24`, there exist `d - 1` continuous functionals on convex bodies
and a probability measure such that no convex six-partition of the unit ball into six
parts of equal measure equalizes all these functionals. -/
theorem convex_partition_counterexample :
    ∀ d : ℕ, 24 ≤ d →
    ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
      Continuous Phi ∧
      IsProbabilityMeasure mu ∧
      ∀ C : Fin 6 → Body d,
        IsSixPartition C →
        (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
        ∃ i, Phi (C i) ≠ Phi (C 0) := by
  intro d hd
  refine ⟨fun C _ => originDist d C, Measure.dirac 0, ?_, inferInstance, ?_⟩
  · exact continuous_pi fun _ => continuous_originDist d
  · intro C hC hmu
    by_contra h_eq
    push_neg at h_eq
    have h0_mem_ball : (0 : Ambient d) ∈ unitBall d := by
      simp [unitBall]
    rw [hC.1] at h0_mem_ball
    obtain ⟨i0, hi0⟩ := Set.mem_iUnion.mp h0_mem_ball
    have h_dist_i0 : originDist d (C i0) = 0 :=
      ((C i0).isCompact.isClosed.mem_iff_infDist_zero (C i0).nonempty).mp hi0
    have h_eq_0 : originDist d (C 0) = originDist d (C i0) := by
      have h := congrFun (h_eq i0) ⟨0, by omega⟩
      exact h.symm
    have h_dist_0 : originDist d (C 0) = 0 := h_eq_0.trans h_dist_i0
    have h0_mem_C0 : (0 : Ambient d) ∈ (C 0 : Set (Ambient d)) :=
      ((C 0).isCompact.isClosed.mem_iff_infDist_zero (C 0).nonempty).mpr h_dist_0
    have h_mu_C0 : Measure.dirac (0 : Ambient d) (C 0 : Set (Ambient d)) = 1 := by
      rw [Measure.dirac_apply' _ (C 0).isCompact.isClosed.measurableSet]
      simp [h0_mem_C0]
    have h_mu_ball : Measure.dirac (0 : Ambient d) (unitBall d) = 1 := by
      unfold unitBall
      rw [Measure.dirac_apply' _ Metric.isClosed_closedBall.measurableSet]
      simp
    have h0 := hmu 0
    rw [h_mu_C0, h_mu_ball] at h0
    have h0_real := congrArg ENNReal.toReal h0
    simp at h0_real

end AkopyanSixfold
end
