import Mathlib.Order.LiminfLimsup
import Convex.Analysis.Calculation
import Mathlib.Topology.Defs.Filter

noncomputable section

open Filter BigOperators Set Topology

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {x : E}

/- the general differential function used in the definition -/
def differential_fun (x : E) (f : E → ℝ) (u : E) :=
  fun y ↦ (f y - f x - inner u (y - x)) / ‖y - x‖

/- the definition of the Frechet subdifferential-/
def f_subdifferential (f : E → ℝ) (x : E) : Set E :=
  {v : E | Filter.liminf (differential_fun x f v) (𝓝[≠] x) ≥ 0}

/- the definition of the limit subdifferential-/
def subdifferential (f : E → ℝ) (x : E) : Set E :=
  {v₀ : E | ∃ u : ℕ → E, Tendsto u atTop (𝓝 x) ∧ Tendsto (fun n ↦ f (u n)) atTop (𝓝 (f x))
    ∧ (∃ v : ℕ → E, ∀ n, v n ∈ f_subdifferential f (u n) ∧ Tendsto v atTop (𝓝 v₀))}

/- the domain of the function is the points whose subifferential are non empty -/
def active_domain (f : E → ℝ) : Set E :=
  {x | subdifferential f x ≠ ∅}
