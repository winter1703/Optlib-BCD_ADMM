import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Defs.Filter
import Convex.Analysis.Calculation
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

/- the limit subdifferential is the subset of the Frechet subdifferential-/
theorem subdifferential_subset (f : E → ℝ) (x : E): f_subdifferential f x ⊆ subdifferential f x :=
  fun v vin ↦ ⟨(fun _ ↦ x), tendsto_const_nhds, tendsto_const_nhds,
    ⟨fun _ ↦ v, fun _ ↦ ⟨vin, tendsto_const_nhds⟩⟩⟩

/-first order optimality condition for unconstrained optimization problem-/
theorem first_order_optimality_condition (f : E → ℝ) (x₀ : E) (hx : IsLocalMin f x₀) :
    (0 : E) ∈ f_subdifferential f x₀ := by
  change (0 : E) ∈ {v : E | Filter.liminf (differential_fun x₀ f v) (𝓝[≠] x₀) ≥ 0}
  rw [mem_setOf, Filter.liminf_eq]
  simp; rw [IsLocalMin] at hx
  by_cases uds : BddAbove {a | ∀ᶠ (n : E) in 𝓝[≠] x₀, a ≤ differential_fun x₀ f 0 n}
  · apply le_csSup uds
    simp
    rw [Filter.eventually_iff]
    rw [IsMinFilter, Filter.eventually_iff] at hx
    change {x | 0 ≤ (f x - f x₀ - inner (0:E) (x - x₀)) / ‖x - x₀‖} ∈ 𝓝[≠] x₀
    simp; rw [nhdsWithin]
    constructor; constructor
    apply hx; use univ; constructor
    rw[Filter.mem_principal]
    tauto; ext x; constructor
    · intro xin; rw [mem_setOf] at xin
      constructor; rw [mem_setOf]
      rw [div_nonneg_iff] at xin
      rcases xin with h1|h1
      linarith; rcases h1 with ⟨_h1', h1''⟩
      have h3 : x = x₀:=by
        have h3': x-x₀=0:= by
          apply norm_eq_zero.mp
          exact (le_antisymm h1'' (norm_nonneg _))
        rw [← zero_add x₀, ← h3']; simp
      rw [h3]; tauto
    · intro xin
      rw [mem_setOf]
      rcases xin with ⟨h1,xneq⟩
      rw [mem_setOf] at h1
      apply div_nonneg; linarith; apply norm_nonneg
  rw [Real.sSup_def]; split_ifs with h1
  exfalso; apply uds; apply h1.right; rfl

/-first order optimality condition for unconstrained optimization problem-/
theorem first_order_optimality_condition' (f : E → ℝ) (x₀ : E) (hx: IsLocalMin f x₀) :
    (0 : E) ∈ subdifferential f x₀ := by
  obtain hcon := subdifferential_subset f x₀
  apply hcon; exact first_order_optimality_condition f x₀ hx

/-The f-subdifferential of a differentiable function is its gradient set-/
theorem f_subdifferential_gradiant (f : E → ℝ) (f': E → E) (hf : ∀ x₁, HasGradientAt f (f' x₁) x₁)
    (z : E) : f_subdifferential f z = {y | y = f' z} :=by
  ext x; constructor
  · intro xin
    rw[mem_setOf]
    sorry
  · intro xin
    rw[mem_setOf] at xin
    rw[f_subdifferential, mem_setOf,xin]
    have diftends: Filter.Tendsto (differential_fun z f (f' z)) (𝓝[≠] z) (𝓝 0):=by
      change Filter.Tendsto (fun y ↦ (f y - f z - inner (f' z) (y - z)) / ‖y - z‖) (𝓝[≠] z) (𝓝 0)
      rcases hf z with hfz
      rw[hasGradientAt_iff_tendsto] at hfz
      have funtrans: (fun y ↦ (f y - f z - inner (f' z) (y - z) )/ ‖y - z‖) =
          (fun y ↦ ‖y - z‖⁻¹*(f y - f z - inner (f' z) (y - z))) := by
        ext y; rw[div_eq_mul_inv,mul_comm]
      rw[funtrans]
      simp at hfz
      apply Filter.Tendsto.mono_left
      · have lim: Tendsto (fun y ↦ ‖y - z‖⁻¹ * (f y - f z - ⟪f' z, y - z⟫_ℝ)) (𝓝 z) (𝓝 0) :=by
          have abseq: ∀ y, ‖y - z‖⁻¹ = |‖y - z‖⁻¹| :=by
            intro y; symm; apply abs_eq_self.mpr; simp
          have funtrans: (fun x' ↦ ‖x' - z‖⁻¹ * |f x' - f z - ⟪f' z, x' - z⟫_ℝ|)=
              (fun x' ↦ |‖x' - z‖⁻¹ * (f x' - f z - ⟪f' z, x' - z⟫_ℝ)|) :=by
            ext y; rw [abseq, abs_mul]; simp
          rw[funtrans] at hfz
          let g:= fun x' ↦ ‖x' - z‖⁻¹ * (f x' - f z - ⟪f' z, x' - z⟫_ℝ)
          change Tendsto g (𝓝 z) (𝓝 0)
          apply (tendsto_zero_iff_abs_tendsto_zero g).mpr
          exact hfz
        exact lim
      · exact nhdsWithin_le_nhds
    simp; apply le_of_eq; symm
    sorry
    --apply Filter.Tendsto.liminf_eq
    --rcases diftends s with hs'

/-The subdifferential of a differentiable function is its gradient set-/

theorem subdifferential_gradiant (f : E → ℝ)(f': E → E)(hf: ∀ x₁, HasGradientAt f (f' x₁) x₁)
(gradcon: Continuous f')(z : E): subdifferential f z = {y | y = f' z}:=by
rw[subdifferential]
ext x
constructor
· intro xin
  rw [mem_setOf] at *
  rcases xin with ⟨u,⟨utendz,⟨utendfz,⟨v,hv⟩⟩⟩⟩
  have veq: ∀ (n : ℕ), v n = f' (u n):=by
    intro n
    rcases hv n with ⟨vin,vtend⟩
    rw[f_subdifferential_gradiant f f',mem_setOf] at vin
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
  rw[mem_setOf] at xin
  rw[mem_setOf,xin]
  use fun _ ↦ z
  constructor
  simp
  constructor
  simp
  use fun _ ↦f' z
  intro _ ;constructor ;
  rw[f_subdifferential_gradiant f f',mem_setOf]
  repeat' assumption
  simp

/-The f-subdifferential add-/
theorem f_subdifferential_add (f : E → ℝ) (g : E → ℝ) (g' : E → E) (x : E) (hf: LowerSemicontinuous f)
    (hg: ∀ x₁, HasGradientAt g (g' x₁) x₁) (gcon: Continuous g) (z : E):
    z ∈ f_subdifferential (f + g) x ↔ ∃ zf ∈ f_subdifferential f x,
    ∃ zg ∈ f_subdifferential g x, z = zf + zg :=by
  constructor
  · intro zin
    rw[f_subdifferential] at zin
    rw[mem_setOf] at zin
    use z - g' x
    constructor
    · rw[f_subdifferential,mem_setOf]
      rw[Filter.liminf_eq]
      by_cases abds:BddAbove {a | ∀ᶠ (n : E) in 𝓝[≠] x, a ≤ differential_fun x f (z - g' x) n}
      · apply le_csSup
        exact abds
        rw[mem_setOf]
        rw[Filter.Eventually]
        rw[Filter.liminf_eq] at zin
        let A:= {a | ∀ᶠ (n : E) in 𝓝[≠] x, a ≤ differential_fun x (f + g) z n}
        have hA: (a₀ : ℝ )→ (ain: a₀ ∈ A)→(a : ℝ)→ (ale: a≤ a₀)→ a∈ A:=by
          intro a₀ ain a ale
          rw[mem_setOf]; rw[mem_setOf] at ain
          rw[Filter.eventually_iff_exists_mem]
          rw[Filter.eventually_iff_exists_mem] at ain
          rcases ain with ⟨v₀,vin,hv⟩
          use v₀
          constructor
          · apply vin
          · intro y yinv
            apply le_trans ale
            apply hv y yinv
        have zeroin: 0 ∈ A:=by
          by_contra zeronotin
          have h' : ∀ a∈ A, a< 0:=by
            intro a ain
            by_contra age
            push_neg at age
            apply zeronotin
            apply hA
            apply ain;apply age
          have suph: sSup A ≤ 0:=by
            · apply Real.sSup_nonpos
              exact fun x a ↦ le_of_not_ge fun a_1 ↦ zeronotin (hA x a 0 a_1)
          simp at zin
          apply zeronotin
          rw[mem_setOf,Filter.eventually_iff_exists_mem]
          sorry
        sorry

      rw[Real.sSup_def]
      split_ifs with h1
      exfalso
      apply abds
      apply h1.right
      rfl
    · use g' x
      constructor
      · rw[f_subdifferential_gradiant g g' hg x]
        rw[mem_setOf]
      · simp
  · intro zin
    rcases zin with ⟨zf,zfin,zg,zgin,fgadd⟩
    rw[fgadd,f_subdifferential,mem_setOf]
    rw[Filter.liminf_eq]
    rw[f_subdifferential,mem_setOf,Filter.liminf_eq] at zfin
    rw[f_subdifferential,mem_setOf,Filter.liminf_eq] at zgin
    by_cases abds: BddAbove {a | ∀ᶠ (n : E) in 𝓝[≠] x, a ≤ differential_fun x (f + g) (zf + zg) n}
    · have smono: {a | ∀ᶠ (n : E) in 𝓝[≠] x, a ≤ differential_fun x f zf n} ∩
      {a | ∀ᶠ (n : E) in 𝓝[≠] x, a ≤ differential_fun x g zg n} ⊆
      {a | ∀ᶠ (n : E) in 𝓝[≠] x, a ≤ differential_fun x (f + g) (zf + zg) n}:=by
        rintro a ⟨af,ag⟩
        rw [mem_setOf, Filter.Eventually, nhdsWithin] at *
        sorry
      sorry
    · rw[Real.sSup_def]
      split_ifs with h1
      exfalso
      apply abds
      apply h1.right
      rfl

/-The subdifferential add-/
theorem subdifferential_add (f : E → ℝ) (g : E → ℝ) (g' : E → E) (x : E) (hf : LowerSemicontinuous f)
    (hg : ∀ x₁, HasGradientAt g (g' x₁) x₁) (gcon : Continuous g) (gradcon : Continuous g') (z : E):
    z ∈ subdifferential (f + g) x ↔ ∃ zf ∈ subdifferential f x,
    ∃ zg ∈ subdifferential g x, z = zf + zg := by
constructor
· intro zin
  rw[subdifferential,mem_setOf] at zin
  rcases zin with ⟨u,hux,hufx,hv⟩
  rcases hv with ⟨v,vlim⟩
  use z - g' x
  constructor
  · rw[subdifferential,mem_setOf]
    constructor
    · constructor
      use hux
      constructor
      · have glim: Tendsto (fun n ↦ -g (u n)) atTop (𝓝 (-g x)):=by
          have contneg: Continuous (-g):=by
            exact continuous_neg_iff.mpr gcon
          apply tendsto_atTop_nhds.mpr
          intro U uin uopen
          rw[continuous_def] at contneg
          rw[tendsto_atTop_nhds] at hux
          have invuopen:IsOpen ((-g) ⁻¹' U):=by
            exact contneg U uopen
          have xinvu: x ∈ ((-g) ⁻¹' U):=by
            simp;exact uin
          rcases hux ((-g) ⁻¹' U) xinvu invuopen with ⟨N,hN ⟩
          use N
          intro n nge
          change u n ∈ (-g) ⁻¹' U
          apply hN n nge
        have functrans: (fun n ↦ f (u n)) = (fun n ↦ ((f+g) (u n)) + (-g (u n))):=by
          ext n
          simp
        rw[functrans]
        have nhds_trans: 𝓝 (f x) = (𝓝 ((f + g) x + -g x)):=by
          simp
        rw[nhds_trans]
        apply Filter.Tendsto.add hufx glim

      use fun n ↦ (v n) - (g' (u n))
      intro n
      rcases vlim n with ⟨vin,vtends⟩
      constructor
      rw[f_subdifferential_add] at vin
      rw[f_subdifferential_gradiant g g' hg] at vin
      rcases vin with ⟨zf,zfin,zg,zgin,fgadd⟩
      rw[mem_setOf] at zgin
      rw[fgadd,zgin]
      simp; assumption
      use g';exact hf;exact hg;exact gcon
      have gradlim: Tendsto (fun n ↦   g' (u n)) atTop (𝓝 (  g' x)):=by
        apply tendsto_atTop_nhds.mpr
        intro U uin uopen
        rw[continuous_def] at gradcon
        rw[tendsto_atTop_nhds] at hux
        have invuopen:IsOpen ((g') ⁻¹' U):=by
            exact gradcon U uopen
        have xinvu: x ∈ ((g') ⁻¹' U):=by
            simp;exact uin
        rcases hux ((g') ⁻¹' U) xinvu invuopen with ⟨N,hN ⟩
        use N
        intro n nge
        change u n ∈ (g') ⁻¹' U
        apply hN n nge
      apply Tendsto.sub vtends
      assumption
  · use g' x
    constructor
    · rw[subdifferential_gradiant g g' hg gradcon]
      rw[mem_setOf]
    · simp
· intro zin
  rcases zin with ⟨zf,zfin,zg,zgin,fgadd⟩
  rw[fgadd,subdifferential,mem_setOf]
  rw[subdifferential,mem_setOf] at zfin zgin
  rcases zfin with ⟨uf,ufx,uffx,hfv⟩
  rcases hfv with ⟨vf,vflim⟩
  rcases zgin with ⟨ug,ugx,uggx,hgv⟩
  rcases hgv with ⟨vg,vglim⟩
  constructor
  constructor
  use ufx
  constructor
  · apply Filter.Tendsto.add
    exact uffx
    apply tendsto_atTop_nhds.mpr
    intro U uin uopen
    rw[continuous_def] at gcon
    rw[tendsto_atTop_nhds] at ufx
    have invuopen:IsOpen ((g) ⁻¹' U):=by
      exact gcon U uopen
    have xinvu: x ∈ ((g) ⁻¹' U):=by
      simp; exact uin
    rcases ufx ((g) ⁻¹' U) xinvu invuopen with ⟨N,hN ⟩
    use N
    intro n nge
    change uf n ∈ (g) ⁻¹' U
    apply hN n nge
  · use fun n ↦ (vf n) + g' (uf n)
    intro n
    constructor
    rcases vglim n with ⟨vgin,vgtends⟩
    rcases vflim n with ⟨vfin,vftends⟩
    · rw[f_subdifferential_add f g g']
      rw[f_subdifferential_gradiant g g'];
      rw[f_subdifferential_gradiant g g',mem_setOf] at vgin
      use vf n
      constructor
      assumption
      use g' (uf n)
      constructor
      simp ;simp;
      assumption ;assumption;apply hf ;repeat' assumption;
    · apply Filter.Tendsto.add
      rcases vflim n with ⟨_,vflim⟩
      apply vflim
      have limgrad: (An : ℕ → E) → (x : E) → (Tendsto An atTop (𝓝 x)) →
          Tendsto (fun n ↦ g' (An n)) atTop (𝓝 (g' x)):=by
        intro An x antends
        apply tendsto_atTop_nhds.mpr
        intro U uin uopen
        rw[continuous_def] at gradcon
        rw[tendsto_atTop_nhds] at antends
        have invuopen:IsOpen ((g') ⁻¹' U):=by
            exact gradcon U uopen
        have xinvu: x ∈ ((g') ⁻¹' U):=by
            simp;exact uin
        rcases antends ((g') ⁻¹' U) xinvu invuopen with ⟨N,hN ⟩
        use N
        intro n nge
        change An n ∈ (g') ⁻¹' U
        apply hN n nge
      rcases vglim n with ⟨vgin,vgtends⟩
      rw[f_subdifferential_gradiant g g',mem_setOf] at vgin
      have funtrans: ∀ (n : ℕ ),  vg n = g' (ug n):=by
        intro k; rcases vglim k with ⟨vgin',vgtends'⟩; rw[f_subdifferential_gradiant g g',mem_setOf] at vgin'
        repeat' assumption
      rw[tendsto_congr funtrans] at vgtends
      have zgeq: zg = g' x:=by
        apply tendsto_nhds_unique vgtends
        apply limgrad ;apply ugx
      rw[zgeq]
      apply limgrad ; apply ufx;assumption

/-equivalent condition for non-convex proximal operator-/
theorem rela_proximal_operator_partial (f : E → ℝ )(x : E)(u : E)(hf: LowerSemicontinuous f) :
    u ∈ prox_set f x → (x-u) ∈ subdifferential f u:=by
  intro uporx
  rw [prox_set, mem_setOf, prox_prop] at uporx
  have h: (0 : E) ∈ subdifferential (fun u ↦ f u + ‖u - x‖ ^ 2 / 2) u:=by
    apply mem_of_mem_of_subset
    apply first_order_optimality_condition
    · apply IsMinOn.isLocalMin
      apply uporx; simp
    apply subdifferential_subset
  have ngradient : ∀ x₁, HasGradientAt (fun u ↦  ‖u - x‖ ^ 2 / 2) (x₁ - x) x₁ := by
    intro x₁; exact gradient_of_sq x₁
  have _ncovex: ConvexOn ℝ Set.univ (fun u ↦  ‖u - x‖ ^ 2 / 2):=by
    apply convex_of_norm_sq x; exact convex_univ
  have ncon: Continuous (fun u ↦  ‖u - x‖ ^ 2 / 2):=by
    have funtrans:(fun u ↦  ‖u - x‖ ^ 2 / 2) = (fun u ↦  (1/2)*‖u - x‖ ^ 2):=by
      simp
      ext y; rw [mul_comm, div_eq_mul_inv]
    rw[funtrans]
    apply Continuous.mul
    simp
    exact continuous_const
    apply Continuous.pow
    apply Continuous.norm
    exact continuous_sub_right x
  have gradcon: Continuous fun u ↦ u-x:=by exact continuous_sub_right x
  obtain h' := (subdifferential_add f (fun u ↦ ‖u - x‖ ^ 2 / 2) (fun x₁ ↦ x₁ - x)
    u hf ngradient ncon gradcon 0).mp h
  rcases h' with ⟨zf,zfin,zg,zgin,gfadd⟩
  have nsubdifference : subdifferential (fun u ↦ ‖u - x‖ ^ 2 / 2) u = {y|y = u - x}:=by
    exact subdifferential_gradiant (fun u ↦ ‖u - x‖ ^ 2 / 2) (fun u ↦ u - x) ngradient gradcon u
  rw [nsubdifference,mem_setOf] at zgin
  rw [zgin] at gfadd
  have zfeq : zf = - (u - x):=by
    apply add_eq_zero_iff_eq_neg.mp
    apply gfadd.symm
  rw [zfeq] at zfin
  simp at zfin
  assumption

/-the Frechet subdifferential is a closed set-/
theorem f_subdifferential_closed (f : E → ℝ) (x : E) : IsClosed (f_subdifferential f x) := by
  sorry

/-the Frechet subdifferential is a convex set-/
theorem f_subdifferential_convex (f : E → ℝ) (x : E) : Convex ℝ (f_subdifferential f x):=by
  simp only [f_subdifferential, Convex]
  intros v₁ hv₁ v₂ hv₂ a b ha hb hab
  unfold differential_fun at *
  simp only [Set.mem_setOf] at *
  have eq1 : ∀ y, inner (a • v₁ + b • v₂) (y - x) = a * inner v₁ (y - x) + b * inner v₂ (y - x):= by
    intros y
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    rfl
  have eq2 : (fun y ↦ a * (f y - f x - ⟪v₁, y - x⟫_ℝ) / ‖y - x‖) + (fun y ↦ b * (f y - f x - ⟪v₂, y - x⟫_ℝ) / ‖y - x‖)
    = fun y ↦ (f y - f x - ⟪a • v₁ + b • v₂, y - x⟫_ℝ) / ‖y - x‖:= by
    ext y
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [mul_sub, mul_sub, mul_sub, mul_sub, ← add_div, add_sub, add_sub]
    rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
    calc (a * f y + -(a * f x) + -(a * ⟪v₁, y - x⟫_ℝ) + b * f y + -(b * f x) + -(b * ⟪v₂, y - x⟫_ℝ)) / ‖y - x‖
    = (a * f y + b * f y + -(a * f x + b * f x) + -(a * ⟪v₁, y - x⟫_ℝ + b * ⟪v₂, y - x⟫_ℝ)) / ‖y - x‖ := by ring
    _ = (f y - f x - (a * ⟪v₁, y - x⟫_ℝ + b * ⟪v₂, y - x⟫_ℝ)) / ‖y - x‖ := by
      rw [← add_mul, hab, one_mul, ← add_mul, hab, one_mul, ← sub_eq_add_neg, ← sub_eq_add_neg]
    _ = (f y - f x - ⟪a • v₁ + b • v₂, y - x⟫_ℝ) / ‖y - x‖ := by rw [eq1]
  rw [← eq2]
  have ineq1 : liminf (fun y ↦ a * (f y - f x - ⟪v₁, y - x⟫_ℝ) / ‖y - x‖) (𝓝[≠] x)
  + liminf (fun y ↦ b * (f y - f x - ⟪v₂, y - x⟫_ℝ) / ‖y - x‖) (𝓝[≠] x) ≤
  liminf ((fun y ↦ a * (f y - f x - ⟪v₁, y - x⟫_ℝ) / ‖y - x‖) + fun y ↦ b * (f y - f x - ⟪v₂, y - x⟫_ℝ) / ‖y - x‖) (𝓝[≠] x)
    := by sorry

  have ineq2 : 0 ≤ liminf (fun y ↦ a * (f y - f x - ⟪v₁, y - x⟫_ℝ) / ‖y - x‖) (𝓝[≠] x)
      + liminf (fun y ↦ b * (f y - f x - ⟪v₂, y - x⟫_ℝ) / ‖y - x‖) (𝓝[≠] x) := by
    have hv₃ : liminf (fun y ↦ a * (f y - f x - ⟪v₁, y - x⟫_ℝ) / ‖y - x‖) (𝓝[≠] x) ≥ 0 := by
      simp only [liminf_eq] at hv₁ ⊢
      sorry
    have hv₄ : liminf (fun y ↦ b * (f y - f x - ⟪v₂, y - x⟫_ℝ) / ‖y - x‖) (𝓝[≠] x) ≥ 0 := by
      sorry
    exact add_nonneg (ge_iff_le.mp hv₃) (ge_iff_le.mp hv₄)
  exact ge_trans (ge_iff_le.mpr ineq1) (ge_iff_le.mpr ineq2)

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
