module

public import Mathlib

@[expose] public section

/-!
# Sixfold Tverberg Counterexample and Convex Equipartition Obstruction

Arseniy Akopyan

* Theorem A (`AkopyanSixfold.tverberg_counterexample`):
  An almost six-embedding of the 35-simplex `Δ³⁵` into `ℝ⁶`: there exists a continuous map
  `f : Δ³⁵ → ℝ⁶` whose images of any six pairwise disjoint faces never meet.
* Theorem B (`AkopyanSixfold.convex_partition_counterexample`):
  Uniform inward-distance transfer and concentrated absolutely continuous measure
  obstruction in every dimension `d ≥ 24`: given `5 * d - 4` blocking markers `p` for
  `eta`-central six-partitions, there exist `d - 1` continuous body functionals `Phi`
  (chosen before the measure) obstructing every fair convex six-partition of `B_d` for
  every `eta`-concentrated absolutely continuous measure `mu`, and in particular for an
  explicit absolutely continuous probability measure.
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
  sorry

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

/-- A marker tuple `p : Fin m → Ambient d` and radius `eta ∈ (0, 1)` block
`eta`-central convex six-partitions of the unit ball if every convex six-partition
whose parts all meet the closed `eta`-ball contains at least one marker `p a`
in the interior of some part `C i` (Lemmas 5.1–5.2 of the manuscript). -/
def IsCentralBlocking {d m : ℕ} (p : Fin m → Ambient d) (eta : ℝ) : Prop :=
  0 < eta ∧ eta < 1 ∧
  ∀ C : Fin 6 → Body d,
    IsSixPartition C →
    (∀ i, ((C i : Set (Ambient d)) ∩ Metric.closedBall (0 : Ambient d) eta).Nonempty) →
    ∃ i a, p a ∈ interior (C i : Set (Ambient d))

/-- **Theorem B (Conditional on central blocking markers)**:
For every dimension `d ≥ 24` and every `eta`-central blocking tuple `p` of
`5 * d - 4` markers, there exist `d - 1` continuous functionals `Phi` on convex
bodies (chosen before the measure) that cannot be equalized on any fair convex
six-partition of the unit ball for any `eta`-concentrated absolutely continuous
measure `mu`, and in particular for a concrete absolutely continuous probability
measure on `Ambient d`. -/
theorem convex_partition_counterexample :
    ∀ d : ℕ, 24 ≤ d →
    ∀ (p : Fin (5 * d - 4) → Ambient d) (eta : ℝ),
      IsCentralBlocking p eta →
      ∃ Phi : Body d → (Fin (d - 1) → ℝ),
        Continuous Phi ∧
        (∀ mu : Measure (Ambient d),
          mu.AbsolutelyContinuous (volume : Measure (Ambient d)) →
          0 < mu (unitBall d) →
          mu (unitBall d) < ⊤ →
          5 * mu (unitBall d) <
            6 * mu (Metric.closedBall (0 : Ambient d) eta) →
          ∀ C : Fin 6 → Body d,
            IsSixPartition C →
            (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
            ∃ i, Phi (C i) ≠ Phi (C 0)) ∧
        (∃ mu : Measure (Ambient d),
          IsProbabilityMeasure mu ∧
          mu.AbsolutelyContinuous (volume : Measure (Ambient d)) ∧
          ∀ C : Fin 6 → Body d,
            IsSixPartition C →
            (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
            ∃ i, Phi (C i) ≠ Phi (C 0)) := by
  sorry

end AkopyanSixfold
end
