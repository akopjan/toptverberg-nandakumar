module

public import RequestProject.Reduction
public import RequestProject.Balance
public import RequestProject.Construction.Assembly

@[expose] public section

/-!
# `tverberg_counterexample`, reduced to `Tverberg6R.heightExtension`

`Tverberg6R.counterexample_of_height` (proved in `RequestProject/Reduction.lean`) shows that
`TverbergCounterexample` follows from the existence of a continuous, boundary-compatible, safe
height table on the mass simplex `Δ^5`.
-/

namespace Tverberg6R

/-- The remaining obligation: a continuous, boundary-compatible height table on the mass
simplex whose heights are never all equal along a matching. -/
def HeightExtensionGoal : Prop :=
  ∃ H : (Fin 6 → ℝ) → Table, ContinuousOn H massSimplex ∧ Compatible H ∧ Safe H

/-- The reduction, packaged: the extension goal implies the comparator statement. -/
theorem tverbergCounterexample_of_heightExtension (h : HeightExtensionGoal) :
    TverbergCounterexample := by
  obtain ⟨H, hH, hC, hS⟩ := h
  exact counterexample_of_height H hH hC hS

/-- The arrangement-extension step. -/
theorem heightExtension : HeightExtensionGoal := exists_height

end Tverberg6R
