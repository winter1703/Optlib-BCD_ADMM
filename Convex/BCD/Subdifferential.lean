import Mathlib.Order.LiminfLimsup
import Convex.Analysis.Calculation
import Mathlib.Topology.Defs.Filter
import Convex.Function.Proximal

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

/- the critial point of a function -/
def critial_point (f : E → ℝ) : Set E :=
  {x | 0 ∈ subdifferential f x}

/-first order optimality condition for unconstrained optimization problem-/
theorem first_order_optimality_condition (f : E → ℝ) (x₀ : E) (hf: LowerSemicontinuous f)
    (hx: IsLocalMin f x₀) : 0 ∈ subdifferential f x₀ := by
  sorry

/-equivalent condition for non-convex proximal operator-/
theorem rela_proximal_operator_partial (f : E → ℝ )(x : E)(u : E)(hf: LowerSemicontinuous f)
(lbf: ∃ b : ℝ, ∀ x : E, b ≤ f x) : u ∈ prox_set f x → (x-u) ∈ subdifferential f u:=by
  sorry

/- the limit subdifferential is the subset of the Frechet subdifferential-/
theorem subdifferential_subset (f : E → ℝ )(x : E)(hf: LowerSemicontinuous f):
f_subdifferential f x ⊆  subdifferential f x:=by
  sorry

/-the Frechet subdifferential is a closed set-/
theorem f_subdifferential_closed (f : E → ℝ )(x : E): IsClosed (f_subdifferential f x) := by
  sorry

/-the Frechet subdifferential is a convex set-/
theorem f_subdifferential_convex (f : E → ℝ )(x : E): Convex ℝ  (f_subdifferential f x):=by
  sorry

--Convex ℝ  (f_subdifferential f x); ℝ ?
/-the limit subdifferential is a convex set-/
theorem subdifferential_closed (f : E → ℝ )(x : E): IsClosed (subdifferential f x):=by
  sorry

/-If f is convex , then Fenchel-subdifferential equals subdifferential equals subgradient-/
theorem convex_f_f_subdifferential_eq_subdifferential (f : E → ℝ) (x : E) (hf: LowerSemicontinuous f)
    (hconv : ConvexOn ℝ univ f): f_subdifferential f x = subdifferential f x := by
  sorry

theorem convex_f_f_subdifferantial_eq_subgradient (f : E → ℝ) (x : E) (hf: LowerSemicontinuous f)
    (hconv : ConvexOn ℝ univ f) : (f_subdifferential f x) = (SubderivAt f x) := by
  sorry
