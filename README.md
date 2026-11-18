# Sixfold Tverberg Counterexamples and Convex Equipartition Obstructions

We construct a counterexample to the generalized Nandakumar--Ramana Rao problem: in every dimension $d \ge 24$, there are $d - 1$ continuous functionals on convex bodies and a probability measure such that there is no convex partition of the unit ball into six parts of equal measure on which all these functionals are equalized.

We also show that the topological Tverberg conjecture fails for sixfold intersections already in $\mathbb{R}^6$: we construct a continuous map $\Delta^{35} \to \mathbb{R}^6$ whose images of six pairwise disjoint faces never meet.

This repository formalizes Theorems A and B from [*Sixfold Tverberg counterexamples and convex equipartition obstructions*](paper/manuscript.tex) by Arseniy Akopyan in Lean 4, developed with the assistance of Aristotle and Gemini.

---

## Challenge Theorems

The challenge is specified in `Challenge.lean` and checked by the Palomar Comparator against `Solution.lean`:

1. **Theorem A (`AkopyanSixfold.tverberg_counterexample`)**:
   There exists a continuous map $\Delta^{35} \to \mathbb{R}^6$ whose images of six pairwise disjoint faces never meet:
   ```lean
   theorem tverberg_counterexample :
       ∃ f : (Fin 36 → ℝ) → (Fin 6 → ℝ),
         IsAlmostSixEmbedding f
   ```

2. **Theorem B (`AkopyanSixfold.convex_partition_counterexample`)**:
   In every dimension $d \ge 24$, given blocking markers `(p, eta)` (`IsBlocking p eta`), there exist $d - 1$ continuous functionals on convex bodies and an absolutely continuous probability measure such that no convex six-partition of the unit ball into six equal-measure parts equalizes all these functionals:
   ```lean
   theorem convex_partition_counterexample (d : ℕ) (hd : 24 ≤ d)
       (p : Fin (5 * d - 4) → Ambient d) (eta : ℝ) (hp : IsBlocking p eta) :
       ∃ (Phi : Body d → (Fin (d - 1) → ℝ)) (mu : Measure (Ambient d)),
         Continuous Phi ∧
         IsProbabilityMeasure mu ∧
         mu.AbsolutelyContinuous volume ∧
         ∀ C : Fin 6 → Body d,
           IsSixPartition C →
           (∀ i, mu (C i : Set (Ambient d)) = mu (unitBall d) / 6) →
           ∃ i, Phi (C i) ≠ Phi (C 0)
   ```

---

## Scope and Alignment with the Manuscript

- **Theorem A (`RequestProject/` and `Solution.lean`)**: Proved unconditionally and without `sorry` via the scalar height-table reduction, rational boundary degree cancellation, and PL zero-cancellation surgery.
- **Theorem B (`Solution.lean`)**: Proved without `sorry` by iterating join-padding $d - 8$ times from Theorem A ($\Delta^{35} \to \mathbb{R}^6$) to obtain an almost six-embedding $\Delta^{5d-5} \to \mathbb{R}^{d-2}$ (Lemma 3.3), proving Hausdorff continuity of inward distances `inwardDist` via Hahn–Banach separation, transferring the almost six-embedding to $d - 1$ body functionals $\Phi$ fixed independently of the measure (Lemma 5.3), proving the concentrated-measure fairness lemma (Lemma 5.4), and instantiating an absolutely continuous normalized Lebesgue ball measure. The existence of blocking markers (Theorem C $\Delta^{119} \to \mathbb{R}^{22}$ and the semialgebraic cone-skeleton dimension bound in Sections 3–5 of [`paper/manuscript.tex`](paper/manuscript.tex), which uses $5d$ markers) is supplied via the explicit hypothesis `IsBlocking p eta`.

---

## Verification

### Prerequisites
- Lean 4 toolchain `leanprover/lean4:v4.35.0`
- Mathlib `v4.35.0`

### Build & Check
```bash
# Build the challenge and solution
lake build

# Run Palomar comparator check
lake env comparator comparator.json
```

When verified with `comparator`, the solution is exported and replayed through the Lean default kernel:
```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```
