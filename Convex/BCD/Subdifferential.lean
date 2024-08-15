import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Defs.Filter
import Mathlib.Data.Real.EReal
import Mathlib.Data.Real.EReal
import Convex.Analysis.Calculation
import Convex.Function.Proximal

noncomputable section

open Filter BigOperators Set Topology

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f g : E → ℝ} {x y u v : E} {c : ℝ}

/- the general differential function used in the definition -/
def differential_fun (x : E) (f : E → ℝ) (u : E) :=
  fun y ↦ Real.toEReal ((f y - f x - inner u (y - x)) / ‖y - x‖)

/- the definition of the Frechet subdifferential-/
def f_subdifferential (f : E → ℝ) (x : E) : Set E :=
  {v : E | liminf (differential_fun x f v) (𝓝[≠] x) ≥ 0}

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

theorem has_f_subdiff_iff : u ∈ f_subdifferential f x ↔
    ∀ ε > 0, ∀ᶠ y in 𝓝 x, f y - f x - inner u (y - x) ≥ -ε * ‖y - x‖ := by
  have h0 : (∀ ε > 0, ∀ᶠ y in 𝓝[≠] x, f y - f x - inner u (y - x) > -ε * ‖y - x‖)
    ↔ ∀ ε > 0, ∀ᶠ y in 𝓝 x, f y - f x - inner u (y - x) ≥ -ε * ‖y - x‖ := by
    constructor
    · intro h ε εpos
      specialize h ε εpos
      rw [eventually_nhdsWithin_iff] at h
      filter_upwards [h] with y hy
      by_cases heq : y = x; rw [heq]; simp
      exact le_of_lt (hy heq)
    · intro h ε εpos
      specialize h (ε / 2) (by positivity)
      rw [eventually_nhdsWithin_iff]
      filter_upwards [h] with y h hy
      have : 0 < ε * ‖y - x‖ := mul_pos εpos (norm_sub_pos_iff.2 hy)
      linarith
  rw [← h0]
  simp only [f_subdifferential, mem_setOf_eq, liminf, limsInf, eventually_map]
  let sa := {a | ∀ᶠ (y : E) in 𝓝[≠] x, a ≤ differential_fun x f u y}
  constructor
  · intro (h : 0 ≤ sSup sa) ε εpos
    have hn : sa.Nonempty := by
      by_contra hn
      have : sa = ∅ := not_nonempty_iff_eq_empty.mp hn
      rw [this, sSup_empty] at h
      absurd h
      exact of_decide_eq_false rfl
    have hsa : Real.toEReal (-ε) < sSup sa := by
      apply lt_of_lt_of_le _ h
      rw [EReal.coe_neg']
      exact neg_neg_iff_pos.mpr εpos
    obtain ⟨a, as, ha⟩ := exists_lt_of_lt_csSup hn hsa
    rw [mem_setOf_eq] at as
    apply Eventually.mp as
    apply eventually_nhdsWithin_of_forall
    rintro y hy h
    have := (lt_div_iff (norm_sub_pos_iff.2 hy)).1 (EReal.coe_lt_coe_iff.1 (lt_of_lt_of_le ha h))
    linarith
  · intro h
    show 0 ≤ sSup sa
    rw [le_sSup_iff]
    intro b hb
    rw [mem_upperBounds] at hb
    contrapose! hb
    have h' : ∀ ε > 0, ∀ᶠ (y : E) in 𝓝[≠] x, differential_fun x f u y > -ε := by
      intro ε εpos
      by_cases hε : ε = ⊤
      · filter_upwards with a
        rw [hε]
        exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
      have heq : ε.toReal = ε := EReal.coe_toReal hε (LT.lt.ne_bot εpos)
      have : 0 < ε.toReal := by
        rw [← EReal.coe_lt_coe_iff]
        exact lt_of_lt_of_eq εpos (id (Eq.symm heq))
      specialize h ε.toReal this
      apply Eventually.mp h
      apply eventually_nhdsWithin_of_forall
      rintro y hy h
      rw [← heq, ← EReal.coe_neg, differential_fun, gt_iff_lt, EReal.coe_lt_coe_iff]
      rw [lt_div_iff (norm_sub_pos_iff.2 hy)]
      linarith
    by_cases hnb : b = ⊥
    · use -1
      constructor
      · specialize h' 1 (zero_lt_one' EReal)
        filter_upwards [h'] with y
        exact le_of_lt
      · rw [hnb]
        exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
    · use b / 2
      have heq : b.toReal = b := EReal.coe_toReal (LT.lt.ne_top hb) hnb
      change b < Real.toEReal 0 at hb
      rw [← heq, EReal.coe_lt_coe_iff] at hb
      constructor
      · have : Real.toEReal 0 < -(b / Real.toEReal 2) := by
          rw [← heq, ← EReal.coe_div, ← EReal.coe_neg, EReal.coe_lt_coe_iff]
          linarith
        specialize h' (-(b / 2)) this
        simp only [neg_neg] at h'
        rw [mem_setOf]
        filter_upwards [h'] with y
        exact le_of_lt
      · show b < b / Real.toEReal 2
        rw [← heq, ← EReal.coe_div, EReal.coe_lt_coe_iff]
        linarith

theorem HasGradientAt_iff_f_subdiff :
    HasGradientAt f u x ↔ u ∈ f_subdifferential f x ∧ -u ∈ f_subdifferential (-f) x := by
  rw [hasGradientAt_iff_isLittleO, Asymptotics.isLittleO_iff, has_f_subdiff_iff, has_f_subdiff_iff]
  constructor
  · intro h
    constructor
    · intro ε εpos
      filter_upwards [h εpos] with y hy
      rw [Real.norm_eq_abs, abs_le] at hy
      linarith
    · intro ε εpos
      filter_upwards [h εpos] with y hy
      rw [Real.norm_eq_abs, abs_le] at hy
      simp only [Pi.neg_apply, sub_neg_eq_add, inner_neg_left, neg_mul]
      linarith
  · intro ⟨h1, h2⟩ c cpos
    filter_upwards [h1 c cpos, h2 c cpos] with y h1y h2y
    simp only [Pi.neg_apply, sub_neg_eq_add, inner_neg_left, neg_mul] at h2y
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith

theorem f_subdiff_neg_f_subdiff_unique (hu : u ∈ f_subdifferential f x)
    (hv : v ∈ f_subdifferential (-f) x) : u = -v := by
  rw [has_f_subdiff_iff] at *
  have h : ∀ ε > 0, ∀ᶠ y in 𝓝 x, ⟪u + v, y - x⟫_ℝ ≤ ε * ‖y - x‖ := by
    intro ε εpos
    have ε2pos : 0 < ε / 2 := by positivity
    filter_upwards [hu _ ε2pos, hv _ ε2pos] with y huy hvy
    rw [InnerProductSpace.add_left]
    simp only [Pi.neg_apply, sub_neg_eq_add] at hvy
    linarith
  by_cases heq : u + v = 0; exact eq_neg_of_add_eq_zero_left heq
  apply eq_of_forall_dist_le
  rw [dist_eq_norm, sub_neg_eq_add]
  intro ε εpos
  specialize h ε εpos
  rw [Metric.eventually_nhds_iff_ball] at h
  obtain ⟨δ, δpos, hd⟩ := h
  have hne := norm_ne_zero_iff.mpr heq
  have hb : x + (δ / 2 / ‖u + v‖) • (u + v) ∈ Metric.ball x δ := by
    rw [mem_ball_iff_norm', sub_add_cancel_left]
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_div, abs_norm]
    rw [div_mul_cancel₀ _ hne, abs_of_nonneg (by positivity)]
    linarith
  specialize hd (x + ((δ / 2) / ‖u + v‖) • (u + v)) hb
  rw [add_sub_cancel_left, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_div, abs_norm] at hd
  rw [real_inner_self_eq_norm_mul_norm, ← mul_assoc, div_mul_cancel₀ _ hne] at hd
  rw [div_mul_cancel₀ _ hne, abs_of_nonneg (by positivity), mul_comm] at hd
  exact le_of_mul_le_mul_right hd (by positivity)

theorem f_subdiff_smul (h : u ∈ f_subdifferential (c • f) x) (cpos : 0 < c) :
    c⁻¹ • u ∈ f_subdifferential f x := by
  rw [has_f_subdiff_iff] at *
  intro ε εpos
  filter_upwards [h _ (mul_pos cpos εpos)] with y hy
  rw [real_inner_smul_left]
  simp only [Pi.smul_apply, smul_eq_mul, neg_mul, neg_le_sub_iff_le_add] at hy
  apply (mul_le_mul_left cpos).mp
  field_simp
  linarith

/- the limit subdifferential is the subset of the Frechet subdifferential-/
theorem subdifferential_subset (f : E → ℝ) (x : E): f_subdifferential f x ⊆ subdifferential f x :=
  fun v vin ↦ ⟨(fun _ ↦ x), tendsto_const_nhds, tendsto_const_nhds,
    ⟨fun _ ↦ v, fun _ ↦ ⟨vin, tendsto_const_nhds⟩⟩⟩

/-first order optimality condition for unconstrained optimization problem-/
theorem first_order_optimality_condition (f : E → ℝ) (x₀ : E) (hx : IsLocalMin f x₀) :
    (0 : E) ∈ f_subdifferential f x₀ := by
  rw [has_f_subdiff_iff]
  intro ε εpos
  filter_upwards [hx] with y hy
  have : 0 ≤ ε * ‖y - x₀‖ := by positivity
  simp only [inner_zero_left, sub_zero, neg_mul, ge_iff_le, neg_le_sub_iff_le_add]
  linarith

/-first order optimality condition for unconstrained optimization problem-/
theorem first_order_optimality_condition' (f : E → ℝ) (x₀ : E) (hx: IsLocalMin f x₀) :
    (0 : E) ∈ subdifferential f x₀ := by
  obtain hcon := subdifferential_subset f x₀
  apply hcon; exact first_order_optimality_condition f x₀ hx

/-The f-subdifferential of a differentiable function is its gradient set-/
theorem f_subdifferential_gradiant (f : E → ℝ) (f': E → E) (hf : ∀ x₁, HasGradientAt f (f' x₁) x₁)
    (z : E) : f_subdifferential f z = {f' z} := by
  ext u
  rw [mem_singleton_iff]
  specialize hf z
  rw [HasGradientAt_iff_f_subdiff] at hf
  constructor
  · exact fun h ↦(neg_neg (f' z)) ▸ (f_subdiff_neg_f_subdiff_unique h hf.2)
  · exact fun h ↦ h ▸ hf.1

/-The subdifferential of a differentiable function is its gradient set-/

theorem subdifferential_gradiant (f : E → ℝ)(f': E → E)(hf: ∀ x₁, HasGradientAt f (f' x₁) x₁)
(gradcon: Continuous f')(z : E): subdifferential f z = {f' z}:=by
rw[subdifferential]
ext x
constructor
· intro xin
  rw [mem_setOf] at *
  rcases xin with ⟨u,⟨utendz,⟨utendfz,⟨v,hv⟩⟩⟩⟩
  have veq: ∀ (n : ℕ), v n = f' (u n):=by
    intro n
    rcases hv n with ⟨vin,vtend⟩
    rw[f_subdifferential_gradiant f f'] at vin
    repeat' assumption
  apply tendsto_nhds_unique (hv 1).right
  rw[tendsto_congr veq]
  apply tendsto_atTop_nhds.mpr
  intro U uin uopen
  rw[continuous_def] at gradcon
  rw[tendsto_atTop_nhds] at utendz
  have invuopen:IsOpen ((f') ⁻¹' U):=by
      exact gradcon U uopen
  have zinvu: z ∈ ((f') ⁻¹' U):=by
      simp; assumption
  rcases utendz ((f') ⁻¹' U) zinvu invuopen with ⟨N,hN ⟩
  use N
  intro n nge
  change u n ∈ (f') ⁻¹' U
  apply hN n nge
· intro xin
  rw[mem_setOf,xin]
  use fun _ ↦ z
  constructor
  simp
  constructor
  simp
  use fun _ ↦f' z
  intro _ ;constructor ;
  rw[f_subdifferential_gradiant f f']
  rfl
  repeat' assumption
  simp only [tendsto_const_nhds_iff]

theorem f_subdiff_add (hf : u ∈ f_subdifferential f x) (hg : v ∈ f_subdifferential g x)
    : u + v ∈ f_subdifferential (f + g) x := by
  rw [has_f_subdiff_iff] at *
  intro ε εpos
  have ε2pos : 0 < ε / 2 := by positivity
  filter_upwards [hf _ ε2pos, hg _ ε2pos] with y hfy hgy
  simp only [Pi.add_apply, neg_mul, ge_iff_le, neg_le_sub_iff_le_add]
  rw [InnerProductSpace.add_left]
  linarith

theorem f_subdiff_add_smooth (h : u ∈ f_subdifferential f x)
    (hg : HasGradientAt g v x) : u + v ∈ f_subdifferential (f + g) x := by
  exact f_subdiff_add h (HasGradientAt_iff_f_subdiff.mp hg).1

lemma f_subdiff_prox (h : prox_prop f y x) : y - x ∈ f_subdifferential f x := by
  have : IsLocalMin (fun u ↦ f u + ‖u - y‖ ^ 2 / 2) x := by
    have := h.localize
    rwa [IsLocalMinOn, nhdsWithin_univ] at this
  have hd := first_order_optimality_condition _ _ this
  have hg :=  HasGradientAt.neg (@gradient_of_sq _ _ _ _ y x)
  have := f_subdiff_add_smooth hd hg
  simp only [neg_sub, zero_add] at this
  have hf : f = (fun u ↦ f u + ‖u - y‖ ^ 2 / 2) + fun x ↦ -(‖x - y‖ ^ 2 / 2) := by
    ext x
    simp only [Pi.add_apply, add_neg_cancel_right]
  exact hf ▸ this

lemma f_subdiff_smul_prox (h : prox_prop (c • f) u x) (cpos : 0 < c) :
    c⁻¹ • (u - x) ∈ f_subdifferential f x := f_subdiff_smul (f_subdiff_prox h) cpos

/-the Frechet subdifferential is a closed set-/
theorem f_subdifferential_closed (f : E → ℝ) (x : E) : IsClosed (f_subdifferential f x) := by
  sorry

/-the Frechet subdifferential is a convex set-/
theorem f_subdifferential_convex (f : E → ℝ) (x : E) : Convex ℝ (f_subdifferential f x):= by
  intro u hu v hv a b ha hb hab
  rw [has_f_subdiff_iff] at *
  intro ε εpos
  filter_upwards [hu _ εpos, hv _ εpos] with y hyu hyv
  sorry

--Convex ℝ  (f_subdifferential f x); ℝ ?
/-the limit subdifferential is a convex set-/
theorem subdifferential_closed (f : E → ℝ) (x : E) : IsClosed (subdifferential f x):=by
  sorry

/-If f is convex , then Fenchel-subdifferential equals subdifferential equals subgradient-/
theorem convex_f_f_subdifferential_eq_subdifferential (f : E → ℝ) (x : E) (hf: LowerSemicontinuous f)
    (hconv : ConvexOn ℝ univ f) : f_subdifferential f x = subdifferential f x := by
  sorry

theorem convex_f_f_subdifferantial_eq_subgradient (f : E → ℝ) (x : E) (hf: LowerSemicontinuous f)
    (hconv : ConvexOn ℝ univ f) : (f_subdifferential f x) = SubderivAt f x := by
  sorry
