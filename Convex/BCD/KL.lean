import Convex.Function.Proximal
import Convex.BCD.Subdifferential


open Filter BigOperators Set Topology

noncomputable section

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {x : E}

/- the definition of Φ_η, the special class of the concave function -/
def special_concave (η : ℝ) := {f : ℝ → ℝ | (ConcaveOn ℝ (Ico 0 η) f) ∧ (∀ x ∈ Ico 0 η, f x > 0)
  ∧ (f 0 = 0) ∧ (ContDiffOn ℝ 1 f (Ioo 0 η)) ∧ (ContinuousAt f 0) ∧
  (∀ x ∈ Ioo 0 η, deriv f x > 0)}

/- KL property with specific φ -/

def KL_point_with_reparameter (σ : E → ℝ) (u : E) (φ : ℝ → ℝ) : Prop :=
  ∃ η ∈ Ioi 0, ∃ s ∈ 𝓝 u, (φ ∈ special_concave η) ∧  (∀ x ∈ s ∩
  {y ∈ active_domain σ | σ u < σ y ∧ σ y < σ u + η},
  deriv φ (σ x - σ u) * (EMetric.infEdist 0 (subdifferential σ x)).toReal ≥ 1)

/- the definition of the KL property at one point -/
def KL_point (σ : E → ℝ) (u : E) : Prop :=
  ∃ η ∈ Ioi 0, ∃ s ∈ 𝓝 u, ∃ φ ∈ special_concave η, ∀ x ∈ s ∩
  {y ∈ active_domain σ | σ u < σ y ∧ σ y < σ u + η},
  deriv φ (σ x - σ u) * (EMetric.infEdist 0 (subdifferential σ x)).toReal ≥ 1

/- the definition of the KL function -/
def KL_function (σ : E → ℝ) : Prop :=
  ∀ u ∈ active_domain σ, KL_point σ u

/- the definition of the desingularization function -/
def desingularization_function (c θ : ℝ) (_ : θ ∈ Ico 0 1) (_ : 0 < c) : ℝ → ℝ :=
  λ t ↦  c * t^(1 - θ)

/- KL inequality for critical points -/
def KL_property_with_regularization (σ : E → ℝ) (u' : E) (φ : ℝ → ℝ) : Prop :=
  ∃ η ∈ Ioi 0, ∃ s ∈ 𝓝 u', (φ ∈ special_concave η) ∧
  (∀ x ∈ s ∩ {y ∈ active_domain σ | σ u' < σ y ∧ σ y < σ u' + η},
  (EMetric.infEdist 0 (subdifferential (λ u => φ (σ u - σ u')) x)).toReal ≥ 1)

/-- the non-critical KL property is naturally true -/
theorem KL_property_at_noncritical_point (h_dom : (x : E) ∈ active_domain f)
    (h_noncrit : 0 ∉ subdifferential f x) : KL_point f x := by
    sorry
/- the definition of constant on -/
def is_constant_on (σ : E → ℝ) (Ω : Set E) : Prop :=
∀ x ∈ Ω, ∀ y ∈ Ω, σ x = σ y

lemma aux {h : E → ℝ → Prop} : (∀ x, ∃ y, h x y) ↔ (∃ (z : E → ℝ), ∀ x, h x (z x)) := by
  constructor
  · intro h1
    exact Classical.skolem.mp h1
  intro h₁; rcases h₁ with ⟨z, hz⟩
  intro x1; use (z x1); exact hz x1

/-  uniformly KL property -/
theorem uniformly_KL_property {σ : E → ℝ} {Ω : Set E} (h_compact : IsCompact Ω)
    (h_Ω1 : ∀ x ∈ Ω, KL_point σ x) (h_Ω2: is_constant_on σ Ω) :
    ∃ ε ∈ Ioi 0, ∃ η ∈ Ioi 0, ∃ φ ∈ special_concave η, ∀ u ∈ Ω , ∀ x ∈
    {y : E | (EMetric.infEdist y Ω).toReal < ε} ∩ {y ∈ active_domain σ | σ u < σ y ∧ σ y < σ u + η},
    deriv φ (σ x - σ u) * (EMetric.infEdist 0 (subdifferential σ x)).toReal ≥ 1:= by
  dsimp [KL_point] at h_Ω1
  have : ∃ (η₁ : E → ℝ), ∀ x ∈ Ω, ∃ s ∈ 𝓝 x, ∃ φ ∈ special_concave (η₁ x),
      ∀ x_1 ∈ s ∩ {y | y ∈ active_domain σ ∧ σ x < σ y ∧ σ y < σ x + (η₁ x)},
      deriv φ (σ x_1 - σ x) * (EMetric.infEdist 0 (subdifferential σ x_1)).toReal ≥ 1 := by
    sorry
  sorry

/- the definition of the uniformly convex function -/
def uniformly_convex_function (f : E → ℝ) (p : ℝ) (_ : 1 ≤ p) (c : ℝ) : Prop :=
  ∀ (x : E) (y : E) (u : E) (_: u ∈ subdifferential f x),
    f y ≥ f x + inner u (y - x) + c * ‖y - x‖ ^ p

/- KL properties of uniformly convex functions -/
theorem uniformly_convex_function_KL_property (p : ℝ) (hp : 1 ≤ p) (c : ℝ)
  (hf : uniformly_convex_function f p hp c) :
  KL_function f ∧ ∃ φ : ℝ → ℝ, ∀ t, φ t = p * c^(-1 / p) * t^(1 / p) := by
  sorry

/- the difinition of arg_min-/
def arg_min (f : E → ℝ) : Set E := {x | ∀ y, f x ≤ f y}

/- the difinition of convex_function_with_growth_condition-/
def convex_function_with_growth_condition (f : E → ℝ) (r : ℝ) (_ : 1 ≤ r) (c : ℝ) (x' : E) : Prop :=
  ∃ η > 0, ∃ U ∈ 𝓝 x', ∀ (x : E), x ∈ U ∩ {x | f x' < f x ∧ f x < f x' + η} →
    f x ≥ f x' + c * (EMetric.infEdist x (arg_min f)).toReal ^ r

/- KL properties of convex function with growth condition -/
theorem convex_function_with_growth_condition_KL_property (r : ℝ) (hr : 1 ≤ r) (c : ℝ) (x' : E)
  (hf : convex_function_with_growth_condition f r hr c x') :
  KL_point f x' ∧ ∃ φ : ℝ → ℝ, ∀ t, φ t = r * c^(-1 / r) * t^(1 / r) := by
  sorry


end
