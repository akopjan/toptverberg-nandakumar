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
   Unconditionally in every dimension $d \ge 288$, there exist $d - 1$ continuous functionals on convex bodies and an absolutely continuous probability measure such that no convex six-partition of the unit ball into six equal-measure parts equalizes all these functionals:
   ```lean
   theorem convex_partition_counterexample (d : ℕ) (hd : 288 ≤ d) :
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

- **Theorem A (`RequestProject/` and `Solution.lean`)**: Proved unconditionally and without `sorry` via the scalar height-table reduction, rational boundary degree cancellation, and PL zero-cancellation surgery, together with the binary join (`join_almostSixEmbedding`), general padding for all $d \ge 6$ (`tverberg_counterexample_ge_six`: $\Delta^{5d+5} \to \mathbb{R}^d$), the fivefold join (`fivefold_tverberg_join`: $\Delta^{179} \to \mathbb{R}^{34}$, `padded_tverberg_ge_36`: $\Delta^{5d-1} \to \mathbb{R}^{d-2}$ for $d \ge 36$), and the general $(k+1)$-fold join (`kfold_tverberg_join`, `padded_tverberg_ge_288`: $\Delta^{5d+35} \to \mathbb{R}^{d-2}$ for $d \ge 288$).
- **Theorem B (`Solution.lean`)**: Proved **completely unconditionally** (with no `g₀`, no `eta`, and no `IsBlocking` hypothesis in `Challenge.lean`) for every dimension $d \ge 288$ without `sorry` by: (1) constructing `5 * d + 36` central blocking markers unconditionally via `exists_isBlocking` (using Hahn–Banach separating hyperplanes, normal rank $\le 5$ in Lemma 4.2 [`central_partition_normal_rank`], Gaussian elimination to RREF [`exists_rref`], and Lebesgue measure zero of lower-dimensional differentiable images via `Measure.addHaar_submodule` and Sard/differentiable image nullity), (2) proving the Blaschke selection theorem (`blaschke_isCompact_subsets_unitBall`) and the central-avoidance margin lemma (`exists_eta_of_isBlocking`, Lemma 5.2) to deduce $\eta \in (0, 1)$, (3) combining the $41$-fold join of Theorem A with join-padding (`padded_tverberg_ge_288`) to obtain $\Delta^{5d+35} \to \mathbb{R}^{d-2}$ without `[AKS]`, and (4) transferring via Hausdorff-continuous inward distances `inwardDist` (Lemma 5.3) and concentrated-measure fairness (Lemma 5.4) with a normalized Lebesgue ball witness. Additionally, `Solution.lean` provides `convex_partition_counterexample_ge_24` ($d \ge 24$, taking $5d - 4$ central blocking markers), `convex_partition_counterexample_ge_36` ($d \ge 36$, taking $5d$ central blocking markers without `[AKS]`), `convex_partition_counterexample_ge_18` ($d \ge 18$, conditional on $\Delta^{89} \to \mathbb{R}^{16}$ and $5d$ markers), and `twofold_seven_color_join` ($\Delta^{41} \to \mathbb{R}^7 \implies \Delta^{83} \to \mathbb{R}^{15}$). Note that proving the sharp bound $d \ge 24$ unconditionally in [`paper/manuscript.tex`](paper/manuscript.tex) uses Theorem C ($\Delta^{119} \to \mathbb{R}^{22}$ via `[AKS]`) and the sharper rank-$4$/rank-$5$ semialgebraic dimension bound $5d - 1$ of Theorem 4.1 (`max {5d - 1, 4d + 23}`).

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
