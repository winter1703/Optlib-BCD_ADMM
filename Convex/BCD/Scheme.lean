import Convex.Function.Proximal
import Convex.BCD.Subdifferential
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.NormedSpace.ProdLp
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.Convex.Deriv
import Convex.BCD.KL

noncomputable section

open Filter Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def limit_set (z : ℕ → E) :=
  {x | MapClusterPt x atTop z}

end

noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {H : WithLp 2 (E × F) → ℝ} {x : E} {y : F}

open Set Bornology Filter BigOperators Topology

/- The gradient of the first component -/
def grad_fst (H : WithLp 2 (E × F) → ℝ) (y : F) : E → E := gradient (fun t ↦ H (t, y))

/- The gradient function of the second component -/
def grad_fun_fst (H : WithLp 2 (E × F) → ℝ) := fun (x, y) ↦ (grad_fst H y x)

/- The gradient of the second component -/
def grad_snd (H : WithLp 2 (E × F) → ℝ) (x : E) : F → F := gradient (fun t ↦ H (x, t))

/- The gradient function of the second component -/
def grad_fun_snd (H : WithLp 2 (E × F) → ℝ) := fun (x, y) ↦ (grad_snd H x y)

/- The gradient of the prod domain -/
def grad_comp (H : WithLp 2 (E × F) → ℝ) (z : WithLp 2 (E × F)) : WithLp 2 (E × F) :=
    (WithLp.equiv 2 (E × F)).symm (grad_fst H z.2 z.1, grad_snd H z.1 z.2)

/- The gradient function of the prod domain -/
def grad_fun_comp (H : WithLp 2 (E × F) → ℝ) := fun z ↦ (grad_comp H z)

instance instNormedSpaceProdL2 : NormedSpace ℝ (WithLp 2 (E × F)) where
  norm_smul_le := by
    intro a b
    have : ‖a • b‖ ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 := by
      rw [mul_pow, WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
      simp only [WithLp.smul_fst, WithLp.smul_snd]
      rw [norm_smul, norm_smul, mul_add, mul_pow, mul_pow]
    exact norm_smul_le a b

lemma fst_norm_le_prod_L2 (z : WithLp 2 (E × F)) : ‖z.1‖ ≤ ‖z‖ := by
  have h : ‖z.1‖ ^ 2 ≤ ‖z‖ ^ 2 := by linarith [WithLp.prod_norm_sq_eq_of_L2 z, sq_nonneg ‖z.2‖]
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  rwa [← pow_two, ← pow_two]

lemma snd_norm_le_prod_L2 (z : WithLp 2 (E × F)) : ‖z.2‖ ≤ ‖z‖ := by
  have h : ‖z.2‖ ^ 2 ≤ ‖z‖ ^ 2 := by linarith [WithLp.prod_norm_sq_eq_of_L2 z, sq_nonneg ‖z.1‖]
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  rwa [← pow_two, ← pow_two]

lemma prod_norm_le_block_sum_L2 (z : WithLp 2 (E × F)) : ‖z‖ ≤ ‖z.1‖ + ‖z.2‖ := by
  have : ‖z‖ ^ 2 ≤ (‖z.1‖ + ‖z.2‖) ^ 2:= by
    simp [WithLp.prod_norm_sq_eq_of_L2, add_sq]
    positivity
  apply nonneg_le_nonneg_of_sq_le_sq (Left.add_nonneg (norm_nonneg z.1) (norm_nonneg z.2))
  rwa [← pow_two, ← pow_two]

instance instIsBoundedLinearMapL2equiv :
    @IsBoundedLinearMap ℝ _ (E × F) _ _ (WithLp 2 (E × F)) _ _ id where
  map_add := fun x ↦ congrFun rfl
  map_smul := fun c ↦ congrFun rfl
  bound := by
    use 2
    constructor
    · norm_num
    · intro z
      rw [Prod.norm_def]
      have h := @prod_norm_le_block_sum_L2 E F _ _ z
      simp only [id_eq]
      linarith [h, le_max_left ‖z.1‖ ‖z.2‖, le_max_right ‖z.1‖ ‖z.2‖]

lemma diff_from_l2 (h : Differentiable ℝ H) : @Differentiable ℝ _ (E × F) _ _ ℝ _ _ H := by
  apply Differentiable.comp h
  apply IsBoundedLinearMap.differentiable
  exact instIsBoundedLinearMapL2equiv

theorem diff_prod₁ (h : Differentiable ℝ H) (y : F) :
    Differentiable ℝ (fun x ↦ H (x, y)) := by
  apply Differentiable.comp (diff_from_l2 h)
  exact Differentiable.prod differentiable_id' (differentiable_const y)

theorem diff_prod₂ (h : Differentiable ℝ H) (x : E) :
    Differentiable ℝ (fun y ↦ H (x, y)) := by
  apply Differentiable.comp (diff_from_l2 h)
  exact Differentiable.prod (differentiable_const x) differentiable_id'

theorem grad_eq_block_grad (h : Differentiable ℝ H) : gradient H = grad_fun_comp H := by
  apply gradient_eq
  intro z
  sorry

end

noncomputable section

open Set Bornology Filter BigOperators Topology

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [ProperSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [ProperSpace F]
variable {f : E → ℝ} {g : F → ℝ}
variable {H : (WithLp 2 (E × F)) → ℝ} {x0 : E} {y0 : F} {l : NNReal}

instance Proper_Prod : ProperSpace (WithLp 2 (E × F)) where
  isCompact_closedBall := by
    rintro ⟨x, y⟩ r
    obtain h := IsCompact.prod (isCompact_closedBall x r) (isCompact_closedBall y r)
    have {a b : ℝ} : a ≤ √(a ^ 2 + b ^ 2) := by apply Real.le_sqrt_of_sq_le; linarith [sq_nonneg b]
    have hsub : @Metric.closedBall (WithLp 2 (E × F)) _ ⟨x, y⟩ r
        ⊆ Metric.closedBall x r ×ˢ Metric.closedBall y r := by
      rintro ⟨x', y'⟩ hball
      rw [mem_prod]
      simp only [mem_closedBall_iff_norm, WithLp.prod_norm_eq_of_L2] at *
      constructor
      · exact le_trans this hball
      · exact le_trans this ((add_comm (‖x' - x‖ ^ 2) _) ▸ hball)
    apply IsCompact.of_isClosed_subset h (@Metric.isClosed_ball (WithLp 2 (E × F)) _ _ _) hsub

/-
  Assumption: f and g are lower semicontinuous, H is continuously differentiable
  ∇ H is l- Lipschitz continuous, f and g are lower bounded
-/
class ProblemData (f : E → ℝ) (g : F → ℝ) (H : (WithLp 2 (E × F)) → ℝ) (l : NNReal) : Prop where
  lbdf : BddBelow (f '' univ)
  lbdg : BddBelow (g '' univ)
  hf : LowerSemicontinuous f
  hg : LowerSemicontinuous g
  conf : ContDiff ℝ 1 H
  lpos : l > (0 : ℝ)
  lip : LipschitzWith l (gradient H)

/-
  The definition of block coordinate descent
-/
structure BCD (f : E → ℝ) (g : F → ℝ) (H : (WithLp 2 (E × F)) → ℝ) (l : NNReal)
    (x0 : E) (y0 : F) extends ProblemData f g H l where
  x : ℕ → E
  y : ℕ → F
  x0 : x 0 = x0
  y0 : y 0 = y0
  c : ℕ → ℝ
  d : ℕ → ℝ
  s₁ : ∀ k, prox_prop (c k • f) (x k - c k • (grad_fst H (y k) (x k))) (x (k + 1))
  s₂ : ∀ k, prox_prop (d k • g) (y k - d k • (grad_snd H (x (k + 1)) (y k))) (y (k + 1))

open BCD

/- the notation z in BCD -/
def BCD.z {self : BCD f g H l x0 y0} : ℕ → WithLp 2 (E × F) :=
  fun n ↦ (WithLp.equiv 2 (E × F)).symm (self.x n, self.y n)

/- the notation ψ in BCD -/
def BCD.ψ {_ : BCD f g H l x0 y0} := fun z : WithLp 2 (E × F) ↦ (f z.1 + g z.2 + H z)

-- -- The lemma used in the first-order condition
-- -- bcd.f_k has Gradient x according to semicontinuous,
-- def BCD.f' {self : BCD f g H l x0 y0} (k : ℕ) : E → E :=
--   fun u => grad_fst H (self.y k) u

-- def BCD.g' {self : BCD f g H l x0 y0} (k : ℕ) : F → F :=
--   fun u => grad_snd H (self.x (k + 1)) u

-- def BCD.fprop' {self : BCD f g H l x0 y0} (k : ℕ) : E → E :=
--   (fun u ↦ (self.c k • grad_fst H (self.y k) u) +
--     (u - (self.x k - self.c k • grad_fst H (self.y k) (self.x k))))

-- -- The prop form of f will induced a function fprop
-- def BCD.fprop {self : BCD f g H l x0 y0} (k : ℕ) : E → ℝ :=
--   (fun u ↦ (self.c k • f) u + ‖u - (self.x k -
--     self.c k • grad_fst H (self.y k) (self.x k))‖ ^ 2 / 2)

-- def BCD.gprop {self : BCD f g H l x0 y0} (k : ℕ) :=
--   (fun u ↦ (self.d k • g) u + ‖u - (self.y k -
--     self.c k • grad_snd H (self.x (k + 1)) (self.y k))‖ ^ 2 / 2)

variable {alg : BCD f g H l x0 y0} (γ : ℝ) (hγ : γ > 1)

variable (ck: ∀ k, alg.c k = 1 / (γ * l)) (dk: ∀ k, alg.d k = 1 / (γ * l))

section Assumption

def addElementToSet (A : Set E) (x : E) : Set E := {a + x | a ∈ A}

lemma BCD.Hdiff : Differentiable ℝ H := alg.conf.differentiable (Preorder.le_refl 1)

lemma norm_prod' (x : E) (y : F) : ‖(x, y)‖ = max ‖x‖ ‖y‖ := rfl

lemma comp_norm_le (x : E) (y : F) : (‖x‖ ≤ ‖(x,y)‖) ∧ (‖y‖ ≤ ‖(x,y)‖) :=
  ⟨le_max_left ‖x‖ ‖y‖, le_max_right ‖x‖ ‖y‖⟩

lemma norm_prod_right_zero (x : E) :
    @norm (WithLp 2 (E × F)) _ ((x, (0 : F)) : WithLp 2 (E × F)) = ‖x‖ := by
  rw [WithLp.prod_norm_eq_of_L2] ; simp

lemma norm_prod_left_zero (y : F):
    @norm (WithLp 2 (E × F)) _ ((0 : E), y) = ‖y‖ := by
  rw [WithLp.prod_norm_eq_of_L2] ; simp

lemma BCD.cpos : ∀ k, 0 < (alg.c k) := by
  intro k
  specialize ck k; rw [ck]
  apply div_pos; norm_num
  apply mul_pos; linarith[hγ]; apply alg.lpos

lemma BCD.dpos : ∀ k, 0 < (alg.d k) := by
  intro k
  specialize dk k; rw [dk]
  apply div_pos; norm_num
  apply mul_pos; linarith[hγ]; apply alg.lpos

lemma sub_prod (x x1 : E) (y y1 : F) : ((x, y) : WithLp 2 (E × F)) - (x1, y1) = (x - x1, y - y1) := rfl

theorem BCD.lip₁ : LipschitzWith l (grad_fun_comp H) := by
  obtain lip := alg.lip
  rw [grad_eq_block_grad alg.Hdiff] at lip; exact lip

/- coordinate Lipschitz continuous -/
theorem BCD.coordinate_lip : (∀ y, LipschitzWith l (grad_fst H y))
    ∧ (∀ x, LipschitzWith l (grad_snd H x)) := by
  have h : LipschitzWith l (grad_fun_comp H) := alg.lip₁
  rw [lipschitzWith_iff_norm_sub_le] at h
  constructor
  intro y
  rw [lipschitzWith_iff_norm_sub_le]
  intro x1 x2
  specialize h (x1, y) (x2, y)
  simp [grad_fun_comp, grad_comp] at h
  apply le_trans (fst_norm_le_prod_L2 _) at h
  simp at h; rw [sub_prod, sub_self, norm_prod_right_zero] at h;
  exact h
  intro x
  rw [lipschitzWith_iff_norm_sub_le]
  intro y1 y2
  specialize h (x, y1) (x, y2)
  simp [grad_fun_comp,grad_comp] at h
  apply le_trans (snd_norm_le_prod_L2 _) at h
  simp at h; rw [sub_prod, sub_self, norm_prod_left_zero] at h;
  exact h

-- /- the composition of the subdifferential -/
-- theorem ass_comp_subdiff : ∀ (x : E) (y : F),
--   subdifferential alg.ψ (x,y) = (addElementToSet (subdifferential f x) (grad_fun_fst H (x,y))
--                                 × addElementToSet (subdifferential g y) (grad_fun_snd H (x,y))) := by
--   sorry

end Assumption

section descent

/- PALM descent -/
theorem PALM_Descent (h : E → ℝ) {h' : E → E} (Lₕ: NNReal)
    (h₁ : ∀ x₁ : E, HasGradientAt h (h' x₁) x₁) (h₂ : LipschitzWith Lₕ h')
    (σ : E → ℝ) (t : ℝ) (h₅ : 0 < t) :
    ∀ (u : E), ∀ u₁ ∈ prox_set (fun a ↦ t * (σ a)) (u - t • (h' u)),
    h u₁ + σ u₁ ≤ h u + σ u - 1 / 2 * (1 / t - Lₕ) * ‖u₁ - u‖ ^ 2 := by
  have htne0 : t ≠ 0 := ne_of_gt h₅
  intro u u₁ u₁prox
  simp only [prox_set,prox_prop,isMinOn_iff] at u₁prox
  have ht : ∀ x ∈ univ, t * (σ u₁) + ‖u₁ - (u - t • (h' u))‖ ^ 2 / 2
      ≤ t * (σ x) + ‖x - (u - t • (h' u))‖ ^ 2 / 2 := u₁prox
  specialize ht u _
  exact Set.mem_univ u
  have :u - (u - t • h' u) = t • h' u := by abel
  rw [this] at ht
  have :u₁ - (u - t • h' u) = (u₁ - u) + t • h' u := by abel
  rw [this] at ht
  simp [norm_add_sq_real,this] at ht
  have h₈ :  t * σ u₁ + ‖u₁ - u‖ ^ 2 / 2 +  ⟪u₁ - u, t • h' u⟫_ℝ ≤ t * σ u := by
    linarith [ht]
  have : ⟪u₁ - u, t • h' u⟫_ℝ =t * ⟪u₁ - u, h' u⟫_ℝ := by apply inner_smul_right
  rw [this] at h₈
  have : t * (‖u₁ - u‖ ^ 2 / (2 * t)) = ‖u₁ - u‖ ^ 2 / 2 := by
    calc
      _ = (‖u₁ - u‖ ^ 2) * (t / (2 * t)) := by ring
      _ = (‖u₁ - u‖ ^ 2) * (1 / 2) := by
        simp; left
        apply div_mul_cancel_right₀ htne0 2
      _ = ‖u₁ - u‖ ^ 2 / 2 := by
        rw [← mul_div_assoc, mul_one]
  rw [← this] at h₈
  have : t * σ u₁ + t * (‖u₁ - u‖ ^ 2 / (2 * t)) + t * ⟪u₁ - u, h' u⟫_ℝ
        = t * (σ u₁ + ‖u₁ - u‖ ^ 2 / (2 * t) + ⟪u₁ - u, h' u⟫_ℝ) := by ring
  rw [this] at h₈
  have hne : ⟪u₁ - u, h' u⟫_ℝ ≤ σ u - σ u₁ - ‖u₁ - u‖ ^ 2 / (2 * t) := by
    linarith [(mul_le_mul_left h₅).1 h₈]
  rw [real_inner_comm] at hne
  have hlip2 := lipschitz_continuos_upper_bound' h₁ h₂
  specialize hlip2 u u₁
  calc
    _ ≤ h u + σ u - σ u₁ - ‖u₁ - u‖ ^ 2 / (2 * t) + ↑Lₕ / 2 * ‖u₁ - u‖ ^ 2 + σ u₁ := by
      linarith [hne, hlip2]
    _ = h u + σ u - (1/ (2 * t) - ↑Lₕ / 2) * ‖u₁ - u‖ ^ 2 := by ring
    _ = h u + σ u - 1 / 2 * (1 / t - ↑Lₕ) * ‖u₁ - u‖ ^ 2 := by
      have : (1/ (2 * t) - ↑Lₕ / 2) = 1 / 2 * (1 / t - ↑Lₕ) := by
        have : 1 / (2 * t) = (1 / 2) * (1 / t) := by field_simp [htne0]
        rw[this]; ring
      rw [this]

/- sufficient descent -/
  -- have hz : ∃ M, ∀ (k: ℕ), ‖alg.z k‖ ≤ M := by
  --   rcases Bornology.IsBounded.exists_norm_le bd with ⟨M, hM⟩
  --   use M; intro k; specialize hM (alg.z k); simp at hM; exact hM
theorem Sufficient_Descent1 : ∃ ρ₁ > 0, ρ₁ = (γ - 1) * l ∧
  ∀ k, ρ₁ / 2 * ‖alg.z (k+1) - alg.z k‖ ^ 2 ≤ alg.ψ (alg.z k) -alg.ψ (alg.z (k + 1)) := by
  use (γ - 1) * l
  let ρ₁ := (γ - 1) * l
  have ργL : ρ₁ = (γ - 1) * l := rfl
  constructor; obtain hl := alg.lpos; apply mul_pos; linarith; exact hl;
  constructor; rfl
  obtain Hass := alg.coordinate_lip
  obtain ⟨hfstlip, hsndlip⟩ := Hass
  intro k
  have hHf : H (alg.x (k + 1), alg.y k) + f (alg.x (k + 1)) ≤ H (alg.x k, alg.y k) + f (alg.x k)
      - 1 / 2 * (γ - 1) * l * ‖alg.x (k + 1) - alg.x k‖ ^ 2 :=
    calc
      _ ≤ H (alg.x k, alg.y k) + f (alg.x k) - 1 / 2 *
          (1 / alg.c k - l)  * ‖alg.x (k + 1) - alg.x k‖ ^ 2 := by
        let h := fun x ↦ H (x,alg.y k)
        let h':= fun x ↦ grad_fst H (alg.y k) x
        have h1 : ∀ x₁ : E, HasGradientAt h (h' x₁) x₁ := by
          intro x
          have : h' x = gradient h x := by simp [h', grad_fst]
          rw [this]
          apply DifferentiableAt.hasGradientAt
          apply diff_prod₁; apply ContDiff.differentiable alg.conf (by simp)
        have cpos : 0 < (alg.c k) := alg.cpos γ hγ ck k
        obtain prop := PALM_Descent h l h1 (hfstlip _) f (alg.c k) cpos (alg.x k) (alg.x (k + 1))
        have h7 : alg.x (k + 1) ∈ prox_set (fun a ↦ alg.c k * f a)
            (alg.x k - alg.c k • h' (alg.x k)) :=by
          obtain h8 := alg.s₁ k
          rw [prox_set]; simp
          have : (fun a ↦ alg.c k * f a)= alg.c k • f := by ext x; simp
          rw [this]; exact h8
        specialize prop h7
        simp only [h] at prop; exact prop
      _ = H (alg.x k, alg.y k) + f (alg.x k) - 1 / 2 * (γ - 1) *
            l * ‖alg.x (k + 1) - alg.x k‖ ^ 2 := by
          rw [ck, one_div_one_div]; ring

  have hHg : H (alg.x (k + 1), alg.y (k + 1)) + g (alg.y (k + 1)) ≤ H (alg.x (k + 1), alg.y k)
      + g (alg.y k) - 1 / 2 * (γ - 1) * l * ‖alg.y (k + 1) - alg.y k‖ ^ 2 :=
    calc
      _ ≤ H (alg.x (k + 1), alg.y k) + g (alg.y k) - 1 / 2 *
            (1 / alg.d k - l)  * ‖alg.y (k + 1) - alg.y k‖ ^ 2 := by
          let h := fun y ↦ H (alg.x (k + 1), y)
          let h':= fun y ↦ grad_snd H (alg.x (k + 1)) y
          have h1 : ∀ y₁ : F, HasGradientAt h (h' y₁) y₁ := by
            intro y
            have : h' y = gradient h y := by simp [h',grad_snd]
            rw [this]
            apply DifferentiableAt.hasGradientAt
            apply diff_prod₂; apply ContDiff.differentiable alg.conf (by simp)
          have dpos : 0 < (alg.d k) := alg.dpos γ hγ dk k
          obtain prop := PALM_Descent h l h1 (hsndlip _) g (alg.d k) dpos (alg.y k) (alg.y (k + 1))
          have h7 : alg.y (k + 1) ∈ prox_set (fun a ↦ alg.d k * g a)
              (alg.y k - alg.d k • h' (alg.y k)) :=by
            obtain h8 := alg.s₂ k
            rw [prox_set]; simp
            have : (fun a ↦ alg.d k * g a)= alg.d k • g := by ext x; simp
            rw [this]; simp[h']; exact h8
          specialize prop h7
          simp only [h] at prop; exact prop
      _ = H (alg.x (k + 1), alg.y k) + g (alg.y k) - 1 / 2 * (γ - 1) *
            l * ‖alg.y (k + 1) - alg.y k‖^2 := by
          rw [dk, one_div_one_div]; ring

  have hPhi : alg.ψ (alg.z k) - alg.ψ (alg.z (k + 1)) ≥ ρ₁ / 2 * ‖alg.z (k + 1) - alg.z k‖  ^2 :=
    calc
      _ = H (alg.x k, alg.y k) + f (alg.x k) + g (alg.y k) - H (alg.x (k + 1), alg.y (k + 1))
          - f (alg.x (k + 1)) - g (alg.y (k + 1)) := by
        have eq1: alg.ψ (alg.z k) = H (alg.x k, alg.y k) + f (alg.x k) + g (alg.y k) := by
          have h1 : f (alg.z k).1 = f (alg.x k) := by rfl
          have h2 : g (alg.z k).2 = g (alg.y k) := by rfl
          rw [BCD.ψ, h1, h2]
          nth_rw 2 [add_assoc]; nth_rw 1 [add_comm]
          apply add_right_cancel_iff.2
          have : alg.z k = (alg.x k, alg.y k) := by rfl
          rw[this]
        have eq2: alg.ψ (alg.z (k+1)) = H (alg.x (k+1), alg.y (k+1))
            + f (alg.x (k+1)) + g (alg.y (k+1)) := by
          have h1 : f (alg.z (k+1)).1 = f (alg.x (k+1)) := by rfl
          have h2 : g (alg.z (k+1)).2 = g (alg.y (k+1)) := by rfl
          rw [BCD.ψ, h1, h2]
          nth_rw 2 [add_assoc]; nth_rw 1 [add_comm]
          apply add_right_cancel_iff.2
          have : alg.z (k+1) = (alg.x (k+1), alg.y (k+1)) := by rfl
          rw [this]
        rw [eq1, eq2]; ring
    _ ≥ 1 / 2 * (γ - 1) * l * (‖alg.x (k + 1) - alg.x k‖ ^ 2
        + ‖alg.y (k + 1) - alg.y k‖ ^ 2) := by
      linarith [hHf,hHg]
    _ = 1 / 2 * ρ₁ * (‖alg.x (k + 1) - alg.x k‖ ^ 2 + ‖alg.y (k + 1) - alg.y k‖ ^ 2) := by
      rw[ργL]; nth_rw 2 [mul_assoc]
    _ = ρ₁ / 2 * ‖alg.z (k + 1) - alg.z k‖^2 := by
      simp only [WithLp.prod_norm_sq_eq_of_L2]
      rw [Prod.fst_sub, Prod.snd_sub, BCD.z, BCD.z]
      ring_nf; simp
  exact hPhi

/- the value is monotone -/
theorem Sufficient_Descent2 :
    ∀ (k : ℕ), alg.ψ (alg.z (k+1)) ≤ alg.ψ (alg.z k) := by
  rcases Sufficient_Descent1 γ hγ ck dk with ⟨ρ₁, ⟨hρ₁, ⟨_, h2⟩⟩⟩
  intro k; specialize h2 k
  have hne : 0 ≤ ρ₁ / 2 * ‖alg.z (k + 1) - alg.z k‖ ^ 2  := by positivity
  linarith

/- The difference series squares are summable-/
theorem Sufficient_Descent3 (lbdψ : BddBelow (alg.ψ '' univ)) :
    ∃ (A : ℝ), Tendsto (fun (n : ℕ) ↦ ∑ k ∈ Finset.range n, ‖alg.z (k + 1) - alg.z k‖ ^ 2)
    atTop (𝓝 A) := by
  rcases Sufficient_Descent1 γ hγ ck dk with ⟨ρ₁, ⟨hρ₁, ⟨_, h2⟩⟩⟩
  have hρ₁ : 2 / ρ₁ ≥  0 := by positivity
  have hDescent' : ∀ k, ‖alg.z (k + 1) - alg.z k‖ ^ 2
      ≤ 2 / ρ₁ * (alg.ψ (alg.z k) - alg.ψ (alg.z (k + 1))):= by
    intro k; specialize h2 k
    obtain h1 := mul_le_mul_of_nonneg_left h2 hρ₁
    rw [← mul_assoc] at h1; field_simp at h1; field_simp; exact h1
  have hne : ∀ n, ∑ k ∈ Finset.range (n + 1), ‖alg.z (k + 1) - alg.z k‖ ^ 2
      ≤ 2 / ρ₁ * ((alg.ψ (alg.z 0)) - (alg.ψ (alg.z (n + 1)))) := by
    intro n
    induction' n with d hd
    simp; specialize hDescent' 0
    simp at hDescent'
    exact hDescent'
    have : ∀ (d : ℕ) ,∑ k ∈ Finset.range (d + 1), ‖alg.z (k + 1) - alg.z k‖ ^ 2
        = ∑ k ∈ Finset.range d, ‖alg.z (k + 1) - alg.z k‖ ^ 2 + ‖alg.z (d + 1) - alg.z d‖ ^ 2 := by
      intro d; simp [Finset.sum_range_succ]
    rw [this (d + 1)]
    have : 2 / ρ₁ * (alg.ψ (alg.z 0) - alg.ψ (alg.z (d + 1 + 1)))
          =  2 / ρ₁ * (alg.ψ (alg.z 0) - alg.ψ (alg.z (d + 1)))
          + 2 / ρ₁ * (alg.ψ (alg.z (d + 1)) - alg.ψ (alg.z (d + 1 + 1))) := by
          linarith
    rw [this]
    specialize hDescent' (d + 1)
    apply add_le_add hd hDescent'
  simp [BddBelow,lowerBounds,Set.Nonempty] at lbdψ
  rcases lbdψ with ⟨ψ₀,hψ₀⟩
  have hne' : ∀ n : ℕ ,∑ k ∈ Finset.range (n + 1), ‖alg.z (k + 1) - alg.z k‖ ^ 2
      ≤ 2 / ρ₁ * ((alg.ψ (alg.z 0))- ψ₀) := by
    intro n
    specialize hne n
    specialize hψ₀ (alg.z (n+1))
    apply le_trans hne (mul_le_mul_of_nonneg_left (by linarith) hρ₁)
  set S := fun (n : ℕ) ↦ ∑ k ∈ Finset.range n, ‖alg.z (k + 1) - alg.z k‖ ^ 2
  have hne'': ∀ n ≥ 1, S n ≤ 2 / ρ₁ * (alg.ψ (alg.z 0) - ψ₀) := by
    intros n nge1
    specialize hne' (n-1)
    rw [Nat.sub_add_cancel nge1] at hne'; exact hne'
  set M₁ := max (S 0) (2 / ρ₁ * (alg.ψ (alg.z 0) - ψ₀)) with hₘ
  have lbdS: ∀ (n : ℕ) , S n ≤ M₁ := by
    rw [hₘ]; intro n
    by_cases h0 : n = 0
    apply le_max_iff.2; left; rw [h0]
    apply le_max_iff.2; right
    apply Nat.pos_of_ne_zero at h0
    exact hne'' n (by linarith [h0])
  obtain hSum : Summable (fun k ↦ ‖alg.z (k + 1) - alg.z k‖ ^ 2) :=
    summable_of_sum_range_le (fun _ ↦ by positivity) (lbdS)
  simp [Summable] at hSum
  rcases hSum with ⟨a,ha⟩
  obtain hA := HasSum.tendsto_sum_nat ha
  use a

/- the difference squence tends to 0 -/
theorem Sufficient_Descent4 (lbdψ : BddBelow (alg.ψ '' univ)):
    Tendsto (fun k ↦ ‖alg.z (k + 1) - alg.z k‖) atTop (𝓝 0) :=by
  rcases Sufficient_Descent3 γ hγ ck dk lbdψ with ⟨A, hA⟩
  have eq: ∀ (n : ℕ), ‖alg.z (n + 1) - alg.z n‖ ^ 2 = ∑ k ∈ Finset.range (n + 1),
      ‖alg.z (k + 1) - alg.z k‖ ^ 2 - ∑ k ∈ Finset.range n, ‖alg.z (k + 1) - alg.z k‖ ^ 2 := by
    intro n; simp [Finset.sum_range_succ]
  rw [Metric.tendsto_atTop] at hA
  simp [dist_eq_norm] at hA
  rw [Metric.tendsto_atTop]; simp [dist_zero_right]
  have SqConver : ∀ (ε : ℝ), 0 < ε → ∃ N, ∀ (n : ℕ), N ≤ n → ‖alg.z (n + 1) - alg.z n‖^2 < ε := by
    intro ε εge0
    specialize hA (ε / 2)
    rcases (hA (by linarith[εge0])) with ⟨N,hNεhalf⟩
    use N; intro n ngeN
    have eq' : ‖ alg.z (n + 1) - alg.z n‖ ^ 2 = (∑ k ∈ Finset.range (n + 1), ‖alg.z (k + 1)
        - alg.z k‖ ^ 2 - A) - (∑ k ∈ Finset.range n, ‖alg.z (k + 1) - alg.z k‖ ^ 2 - A) := by
      rw [sub_sub_sub_comm]; simp; exact eq n
    rw [eq']
    obtain hNεhalf' := hNεhalf (n+1) (by linarith[ngeN])
    have hNεhalf1 : ∑ k ∈ Finset.range (n+1), ‖alg.z (k + 1) - alg.z k‖ ^ 2 - A < ε / 2 := by
      rw [abs_lt] at hNεhalf'; exact hNεhalf'.right
    have hNεhalf2: ∑ k ∈ Finset.range n, ‖alg.z (k + 1) - alg.z k‖ ^ 2 - A > - (ε / 2) := by
      specialize hNεhalf n ngeN
      rw [abs_lt] at hNεhalf; exact hNεhalf.left
    linarith[hNεhalf1, hNεhalf1]
  intro ε εge0
  set εsq := ε ^ 2 with sqeq
  specialize SqConver εsq (by positivity)
  rw [sqeq] at SqConver
  rcases SqConver with ⟨N,hN⟩
  use N
  intro n ngeN
  specialize hN n ngeN
  set a := ‖alg.z (n + 1) - alg.z n‖
  have neq : |a| < |ε| := sq_lt_sq.1 hN
  rw [abs_of_pos εge0, abs_of_nonneg (by positivity)] at neq
  exact neq

end descent

section Upperbound_subd
/-
  The section of subsequences' properties.

  The key theorems here are just Lec6 p18 & p22.

  1. Prop 1 in p 19.

  - A^k_x, A^k_y ∈ ∂Ψ(x^k, y^k).

    Akx, Aky are defined as a map, and the property will be proved into seperated parts. Just Akx in it and Aky be.

    According to the proof in p19, we prove it in the following lemmas.

    1. The first equation in p19 holds.

      ∃ uᵏ ∈ ∂f, s.t. ∇ₓH(xᵏ, yᵏ) + 1⧸cᵏ (x^(k + 1) - xᵏ) + uᵏ = 0 holds.

    (p19 eq-line 1)

    Use the *prop_prox*, and *first_order_unconstrained* we can derive the partial derivative respect to x of the PALM formula to be zero.

    One should notice that, when we use *first_order_unconstrained*, we need to provide the f' of f manually.

    The last part is use the result of *first_order_unconstrained* to get the result.

    2. The vector addition in the subdifferential set closed.

    3. The euqation "A^k_x = ∇ₓ H( x k , y k ) + uᵏ" holds.

  - Upper Bound of A^k_x.

    Nearly completed, we write the docs later.


  2. Theorem in p22, we move them to a new file "IterSequenceProp.lean", need to complete.
-/

variable {c : ℝ} {f' : E → ℝ} {x u u' : E} {y v : F}

lemma f_subdiff_block (hf : u ∈ f_subdifferential f x) (hg : v ∈ f_subdifferential g y) :
    ⟨u, v⟩ ∈ f_subdifferential (fun z ↦ f z.1 + g z.2 : WithLp 2 (E × F) → ℝ) ⟨x, y⟩ := by
  rw [has_f_subdiff_iff] at *
  intro ε εpos
  sorry

/- Define the A^k_x -/
def BCD.A_kx k := (alg.c k)⁻¹ • (alg.x k - alg.x (k + 1)) - (grad_fst H (alg.y k) (alg.x k))

/- Define the A^k_y -/
def BCD.A_ky k := (alg.d k)⁻¹ • (alg.y k - alg.y (k + 1)) - (grad_snd H (alg.x (k + 1)) (alg.y k))

def BCD.A_k (k : ℕ) : WithLp 2 (E × F) := (alg.A_kx k, alg.A_ky k)

def BCD.subdiff k := alg.A_k k + gradient H (alg.x (k + 1), alg.y (k + 1))

theorem Ψ_subdiff_bound : ∃ ρ > 0, ∀ k,
    ∃ dΨ ∈ f_subdifferential alg.ψ (alg.z (k + 1)), ‖dΨ‖ ≤ ρ * ‖alg.z (k + 1) - alg.z k‖ := by
  use l * (2 * γ + 2)
  constructor
  · let lpos := alg.lpos
    positivity
  intro k
  use alg.subdiff k
  constructor
  · apply f_subdiff_add_smooth
    · apply f_subdiff_block
      · have := f_subdiff_smul_prox (alg.s₁ k) (alg.cpos γ hγ ck k)
        rwa [sub_right_comm, smul_sub, inv_smul_smul₀ (ne_of_gt (alg.cpos γ hγ ck k))] at this
      · have := f_subdiff_smul_prox (alg.s₂ k) (alg.dpos γ hγ dk k)
        rwa [sub_right_comm, smul_sub, inv_smul_smul₀ (ne_of_gt (alg.dpos γ hγ dk k))] at this
    · exact DifferentiableAt.hasGradientAt (Differentiable.differentiableAt alg.Hdiff)
  · apply le_trans (prod_norm_le_block_sum_L2 (alg.subdiff k))
    have h1 : ‖(alg.subdiff k).1‖ ≤ l * (γ + 1) * ‖alg.z (k + 1) - alg.z k‖ := by
      simp only [BCD.subdiff, BCD.A_kx, Prod.fst_add, grad_fun_comp, grad_comp, sub_add]
      sorry
    sorry

end Upperbound_subd

section limit_point

lemma StrictMono_nat (φ : ℕ → ℕ) (hφ: StrictMono φ) : (∀ (n:ℕ), n ≤ (φ n)) :=
    fun n ↦ hφ.id_le n

lemma final (m:ℕ){α:ℕ→ℕ}(monoa:StrictMono α) : ∃ n : ℕ, m ≤ α n := by
  induction' m with m ih
  · use 1; linarith
  rcases ih with ⟨n, ieqq⟩
  use n + 1
  have :α n + 1 ≤ α (n + 1):= by
    apply Nat.succ_le_iff.mpr
    apply monoa
    norm_num
  linarith

lemma fconv (α : ℕ → ℕ) (z_ : WithLp 2 (E×F)) (monoa : StrictMono α)
    (conv : Tendsto (fun n ↦ alg.z (α n)) atTop (𝓝 z_))
    (bd : Bornology.IsBounded (alg.z '' univ)) (lbdψ : BddBelow (alg.ψ '' univ)):
    Tendsto (fun n ↦ f (alg.z (α n)).1) atTop (𝓝 (f z_.1)):=by
  apply (nhds_basis_Ioo_pos (f z_.1)).tendsto_right_iff.mpr
  rintro ε epos
  simp only [Ioo]
  have lef:∀ᶠ (x : ℕ) in atTop, f (alg.z (α x)).1>f z_.1-ε:= by
    have semi: ∀ᶠ x' in 𝓝 z_.1, f z_.1 -ε < f x':= by
      apply alg.hf z_.1
      linarith
    have :Tendsto (fun n↦ (alg.z (α n)).1) atTop (𝓝 z_.1):= Tendsto.fst_nhds conv
    exact this semi
  have rig:∀ᶠ (x : ℕ) in atTop, f (alg.z (α x)).1<f z_.1+ε:= by
    have ieq (q:ℕ)(hq:1≤α q):alg.c (α q -1) * f (alg.x (α q)) + ⟪alg.x (α q) - alg.x (α q -1),
      alg.c (α q -1) • grad_fst H (alg.y (α q -1)) (alg.x (α q -1))⟫_ℝ ≤
      alg.c (α q -1) * f z_.1 + ‖z_.1 - alg.x (α q -1)‖ ^ 2 / 2 + ⟪z_.1 - alg.x (α q -1), alg.c (α q -1)•
      grad_fst H (alg.y (α q -1)) (alg.x (α q -1))⟫_ℝ:= by
      rcases isMinOn_iff.mp (alg.s₁ (α q -1)) z_.1 trivial with ieq
      simp at ieq
      rw [←sub_add,norm_add_sq_real,←sub_add,norm_add_sq_real] at ieq
      repeat rw [add_div] at ieq
      repeat rw [←add_assoc] at ieq
      simp [hq] at ieq
      have :0≤‖alg.x (α q) - alg.x (α q - 1)‖ ^ 2 / 2 := by
        apply div_nonneg
        norm_num
        norm_num
      linarith [ieq,this]
    have Hbd : ∃ C, ∀ q : ℕ, ‖(grad_fst H (alg.y (α q -1)) (alg.x (α q -1)))‖≤C:= by
      rcases isBounded_iff_forall_norm_le.mp bd with ⟨C1,inin⟩
      have con11H:ContinuousOn (fun (x,y)↦grad_fst H y x) (Metric.closedBall (0:WithLp 2 (E×F)) C1) := by
        apply Continuous.continuousOn
        have :LipschitzWith l (fun (x,y)↦grad_fst H y x) := by
          apply lipschitzWith_iff_norm_sub_le.mpr
          rintro ⟨x1,y1⟩ ⟨x2,y2⟩
          simp
          calc
            ‖grad_fst H y1 x1 - grad_fst H y2 x2‖
              ≤‖(grad_fst H y1 x1 - grad_fst H y2 x2,grad_snd H x1 y1 - grad_snd H x2 y2)‖:= by
                exact (comp_norm_le (grad_fst H y1 x1 - grad_fst H y2 x2) (grad_snd H x1 y1 - grad_snd H x2 y2)).left
            _≤ ↑l * ‖(x1 - x2, y1 - y2)‖:= by
              have lip : LipschitzWith l (grad_fun_comp H) := alg.lip₁
              rw [lipschitzWith_iff_norm_sub_le] at lip
              specialize lip (x1,y1) (x2,y2)
              simp [grad_fun_comp, grad_comp] at lip
              rw [sub_prod] at lip
              sorry
        apply LipschitzWith.continuous this
      have :IsCompact (Metric.closedBall 0 C1) := by exact (isCompact_closedBall 0 C1)
      rcases @IsCompact.exists_bound_of_continuousOn (WithLp 2 (E×F)) E _ _ _
        (isCompact_closedBall (0:WithLp 2 (E×F)) C1) (fun (x,y)↦grad_fst H y x) con11H with ⟨C,sqsq⟩
      use C
      rintro q
      have :(alg.x (α q -1),alg.y (α q -1))∈Metric.closedBall (0:WithLp 2 (E×F)) C1 := by
        apply mem_closedBall_iff_norm.mpr
        simp
        apply inin (alg.x (α q -1),alg.y (α q -1))
        have :(alg.x (α q - 1), alg.y (α q - 1))=alg.z (α q -1):= rfl
        rw [this]
        exact mem_image_of_mem z trivial
      have hhhh:= sqsq (alg.x (α q -1),alg.y (α q -1)) this
      simp at hhhh
      exact hhhh
    rcases Hbd with ⟨C,hbd⟩
    have diflte1:∀ ε>0, ∀ᶠ (q : ℕ) in atTop,‖alg.x (α q) - alg.x (α q - 1)‖ <ε:= by
      intro ε epos
      rcases (nhds_basis_abs_sub_lt (0:ℝ)).tendsto_right_iff.mp (Sufficient_Descent4 γ hγ ck dk lbdψ) ε epos with lte
      simp at lte
      rcases lte with ⟨a,ie⟩
      simp
      rcases final (a+1) monoa with ⟨A,iee⟩
      use A
      rintro b Aleb
      have:Monotone α:= by exact StrictMono.monotone monoa
      have a1leab:a+1≤ α b := by linarith [StrictMono.monotone monoa Aleb,iee]
      have :a≤ α b -1:= by exact Nat.le_sub_one_of_lt a1leab
      calc
        ‖alg.x (α b) - alg.x (α b - 1)‖≤@norm (WithLp 2 (E × F)) (WithLp.instProdNorm 2 E F) (alg.x (α b) - alg.x (α b - 1),alg.y (α b) - alg.y (α b - 1)) :=by
          rw [WithLp.prod_norm_eq_of_L2]
          simp
          refine (Real.le_sqrt (norm_nonneg (alg.x (α b) - alg.x (α b - 1)))
            (Left.add_nonneg (sq_nonneg ‖alg.x (α b) - alg.x (α b - 1)‖)
            (sq_nonneg ‖alg.y (α b) - alg.y (α b - 1)‖ ))).mpr
            (le_add_of_nonneg_right (sq_nonneg ‖alg.y (α b) - alg.y (α b - 1)‖))
        _=‖alg.z (α b) - alg.z (α b - 1)‖:= rfl
        _<ε:= by
          have: ‖z (α b - 1 + 1) - z (α b - 1)‖ < ε:=ie (α b - 1) this
          have eqq:(α b - 1 + 1)=α b:= by
            apply Nat.sub_add_cancel
            linarith [a1leab]
          rw [eqq] at this
          assumption
    have diflte2:∀ ε>0, ∀ᶠ (q : ℕ) in atTop,‖z_.1 - alg.x (α q - 1)‖ <ε:= by
      rintro ε epos
      have : ∀ᶠ (q : ℕ) in atTop,‖z_.1 - alg.x (α q )‖ <ε/2:= by
        rcases (atTop_basis.tendsto_iff (@Metric.nhds_basis_ball _ _ z_)).mp conv (ε/2) (half_pos epos) with ⟨n1,_,ieq1⟩
        simp [dist_eq_norm] at ieq1;simp
        use n1
        rintro b n1leb
        calc
          ‖z_.1 - alg.x (α b)‖≤‖z_ -z (α b)‖ :=by
            rw [WithLp.prod_norm_eq_of_L2]
            simp
            refine (Real.le_sqrt (norm_nonneg (z_.1 - alg.x (α b)))
              (Left.add_nonneg (sq_nonneg ‖z_.1 - alg.x (α b)‖)
              (sq_nonneg ‖z_.2 - alg.y (α b)‖ ))).mpr
              (le_add_of_nonneg_right (sq_nonneg ‖z_.2 - alg.y (α b)‖))
          _<ε/2:=by
            rw [norm_sub_rev]
            exact ieq1 b n1leb
      have :∀ᶠ (q : ℕ) in atTop,‖z_.1 - alg.x (α q )‖ <ε/2∧‖alg.x (α q) - alg.x (α q - 1)‖ <ε/2:= Eventually.and this (diflte1 (ε/2) (half_pos epos))
      apply Eventually.mono this
      rintro x ⟨h1,h2⟩
      calc
        ‖z_.1 - alg.x (α x - 1)‖=‖z_.1 - alg.x (α x )+(alg.x (α x) - alg.x (α x -1))‖:= by
          simp
        _≤‖z_.1 - alg.x (α x)‖+‖alg.x (α x) - alg.x (α x - 1)‖:= by
          apply norm_add_le
        _<ε/2+ε/2:= by linarith [h1,h2]
        _=ε := by exact add_halves ε

    have (k:ℕ→E)(defle:∀ ε > 0, ∀ᶠ (q : ℕ) in atTop, ‖k q‖ < ε):∀ ε>0, ∀ᶠ (q : ℕ) in atTop,abs ⟪k q, alg.c (α q -1) • grad_fst H (alg.y (α q -1)) (alg.x (α q -1))⟫_ℝ≤ε:= by
      rintro ε epos
      simp at defle;simp
      by_cases Cpos:0<C
      · have :0<ε/(C/(γ*l)) := by
          apply div_pos epos;apply div_pos Cpos;apply mul_pos _ alg.lpos;linarith
        rcases defle (ε/(C/(γ*l))) this with ⟨nn,ieq⟩
        use nn
        rintro b nleb
        rw [ck]
        calc
          |⟪k b, (1 / (γ * ↑l)) • grad_fst H (alg.y (α b - 1)) (alg.x (α b - 1))⟫_ℝ|
            ≤‖k b‖*‖(1 / (γ * ↑l)) • grad_fst H (alg.y (α b - 1)) (alg.x (α b - 1))‖
              := by apply abs_real_inner_le_norm
          _≤ε / (C / (γ * ↑l))*‖(1 / (γ * ↑l)) • grad_fst H (alg.y (α b - 1)) (alg.x (α b - 1))‖:= by
            apply mul_le_mul (le_of_lt (ieq b nleb))
            trivial
            repeat apply norm_nonneg
            apply le_of_lt;apply div_pos;apply epos;apply div_pos Cpos;apply mul_pos _ alg.lpos;linarith
          _=ε / (C / (γ * ↑l))*(1 / (γ * ↑l)) *‖ grad_fst H (alg.y (α b - 1)) (alg.x (α b - 1))‖:= by
            rw [mul_assoc]
            apply mul_eq_mul_left_iff.mpr
            left
            refine
              norm_smul_of_nonneg ?h.ht (grad_fst H (alg.y (α b - 1)) (alg.x (α b - 1)))
            apply le_of_lt;apply div_pos;norm_num;apply mul_pos _ alg.lpos;linarith
          _=ε/C*‖ grad_fst H (alg.y (α b - 1)) (alg.x (α b - 1))‖:= by
            apply mul_eq_mul_right_iff.mpr;left
            rw [←div_mul,mul_assoc,mul_one_div,div_self,mul_one]
            have :0<γ * ↑l:=by apply mul_pos _ alg.lpos;linarith
            linarith
          _≤ε/C*C:= by
            apply mul_le_mul;trivial;apply hbd b;apply norm_nonneg
            apply le_of_lt ;apply div_pos epos Cpos
          _=ε:= by
            refine div_mul_cancel₀ ε ?h;linarith [Cpos]
      · push_neg at Cpos
        use 100000
        rintro b _
        rw [ck]
        calc
          |⟪k b,  (1 / (γ * ↑l))• grad_fst H (alg.y (α b - 1)) (alg.x (α b - 1))⟫_ℝ|
            ≤‖k b‖*‖(1 / (γ * ↑l)) • grad_fst H (alg.y (α b - 1)) (alg.x (α b - 1))‖
              := by apply abs_real_inner_le_norm
          _=‖k b‖*(1 / (γ * ↑l)) *‖grad_fst H (alg.y (α b - 1)) (alg.x (α b - 1))‖
              :=by
              rw [mul_assoc]
              apply mul_eq_mul_left_iff.mpr
              left
              refine
              norm_smul_of_nonneg ?h.ht (grad_fst H (alg.y (α b - 1)) (alg.x (α b - 1)))
          _≤‖k b‖*(1 / (γ * ↑l))*C:= by
            apply mul_le_mul
            trivial;apply hbd b;apply norm_nonneg;apply mul_nonneg;apply norm_nonneg
            apply div_nonneg;norm_num;apply mul_nonneg;linarith;linarith [alg.lpos]
          _≤0:= by
            apply mul_nonpos_iff.mpr
            left
            refine ⟨?_,Cpos⟩
            apply mul_nonneg;apply norm_nonneg
            apply div_nonneg;norm_num;apply mul_nonneg;linarith;linarith [alg.lpos]
          _≤ε:= by linarith
    simp only [ck] at ieq
    have finalpos:0<ε/(γ*l)/3:= by
      apply div_pos;apply div_pos epos;apply mul_pos;linarith;apply alg.lpos;linarith
    have h1:∀ᶠ (q : ℕ) in atTop,|⟪alg.x (α q) - alg.x (α q - 1), alg.c (α q - 1) • grad_fst H (alg.y (α q - 1)) (alg.x (α q - 1))⟫_ℝ| ≤ε / (γ * ↑l) / 3 :=
      this (fun q↦alg.x (α q) - alg.x (α q - 1)) (diflte1) (ε/(γ*l)/3) finalpos
    have h2: ∀ᶠ (q : ℕ) in atTop,|⟪z_.1 - alg.x (α q - 1), alg.c (α q - 1) • grad_fst H (alg.y (α q - 1)) (alg.x (α q - 1))⟫_ℝ| ≤ ε / (γ * ↑l) / 3:=
      this (fun q↦z_.1 - alg.x (α q - 1)) diflte2 (ε/(γ*l)/3) finalpos
    have h3: ∀ᶠ (q : ℕ) in atTop,‖z_.1 - alg.x (α q - 1)‖ ^ 2 / 2<(ε/(γ*l)/3):= by
      refine Eventually.mono (diflte2 (√(2*(ε/(γ*l)/3))) ?_) ?_
      apply Real.sqrt_pos_of_pos
      apply mul_pos;norm_num;apply finalpos
      intro x assx
      have :‖z_.1 - alg.x (α x - 1)‖^2<(2*(ε/(γ*l)/3)):= by
        refine (Real.lt_sqrt ?hx).mp ?_
        apply norm_nonneg
        exact assx
      calc
        ‖z_.1 - alg.x (α x - 1)‖ ^ 2 / 2<(2*(ε/(γ*l)/3))/2:= by
          apply (div_lt_div_right _).mpr
          apply this
          linarith
        _=(ε/(γ*l)/3):= by
          apply mul_div_cancel_left₀
          linarith
    simp at h1 h2 h3
    simp only [ck] at h1 h2 h3
    --rw [ck (α q -1)] at h1
    simp
    rcases h1 with ⟨m1,ie1⟩
    rcases h2 with ⟨m2,ie2⟩
    rcases h3 with ⟨m3,ie3⟩
    use 1+max (max m1 m2) m3
    intro q mleq
    have m1le:m1≤1+max (max m1 m2) m3:=by linarith [(le_max_left m1 m2).trans (le_max_left (max m1 m2) m3)]
    have m2le:m2≤1+max (max m1 m2) m3:= by linarith [(le_max_right m1 m2).trans (le_max_left (max m1 m2) m3)]
    have m3le:m3≤1+max (max m1 m2) m3:= by linarith [le_max_right (max m1 m2) m3]
    have :1≤α q := by
      have :α 0 < α q:= by
        apply monoa
        linarith [Nat.le_of_add_right_le mleq]
      linarith
    have key:1 / (γ * ↑l) * f (alg.x (α q)) <1 / (γ * ↑l) * f z_.1 +ε / (γ * ↑l):= by
      linarith [ieq q this,(abs_le.mp (ie1 q (m1le.trans mleq))).1,(abs_le.mp (ie2 q (m2le.trans mleq))).2,ie3 q (m3le.trans mleq),
        add_thirds (ε / (γ * ↑l))]
    have ltt:0<γ*l:= by
      apply mul_pos;linarith;linarith [alg.lpos]
    calc
      f (z (α q)).1=f (alg.x (α q)):= rfl
      _=(γ * ↑l)*(1 / (γ * ↑l) * f (alg.x (α q))):= by
        rw [←mul_assoc,mul_one_div_cancel (LT.lt.ne ltt).symm,one_mul]
      _<(γ * ↑l)*(1 / (γ * ↑l) * f z_.1 + ε / (γ * ↑l)):=(mul_lt_mul_left ltt).mpr key
      _=f z_.1 + ε:=by
        rw [mul_add,←mul_assoc,mul_one_div_cancel (LT.lt.ne ltt).symm,one_mul,mul_div_cancel₀ _ (LT.lt.ne ltt).symm]
  exact Eventually.and lef rig

lemma gconv(α:ℕ→ℕ)(z_:WithLp 2 (E×F))(monoa:StrictMono α )(conv:Tendsto (fun n ↦ alg.z (α n)) atTop (𝓝 z_))
    (bd : Bornology.IsBounded (alg.z '' univ)) (lbdψ : BddBelow (alg.ψ '' univ)):
    Tendsto (fun n ↦ g (alg.z (α n)).2) atTop (𝓝 (g z_.2)):=by
  apply (nhds_basis_Ioo_pos (g z_.2)).tendsto_right_iff.mpr
  rintro ε epos
  simp only [Ioo]
  have lef:∀ᶠ (x : ℕ) in atTop, g (alg.z (α x)).2>g z_.2-ε:= by
    have semi: ∀ᶠ x' in 𝓝 z_.2, g z_.2 -ε < g x':= by
      apply alg.hg z_.2
      linarith
    have :Tendsto (fun n↦ (alg.z (α n)).2) atTop (𝓝 z_.2):= Tendsto.snd_nhds conv
    exact this semi
  have rig:∀ᶠ (x : ℕ) in atTop, g (alg.z (α x)).2<g z_.2+ε:= by
    have ieq (q:ℕ)(hq:1≤α q):alg.d (α q - 1) * g (alg.y (α q)) +⟪alg.y (α q) - alg.y (α q - 1), alg.d (α q - 1) • grad_snd H (alg.x (α q)) (alg.y (α q - 1))⟫_ℝ≤
        alg.d (α q - 1) * g z_.2 + ‖z_.2 - alg.y (α q - 1)‖ ^ 2 / 2 +⟪z_.2 - alg.y (α q - 1), alg.d (α q - 1) • grad_snd H (alg.x (α q)) (alg.y (α q - 1))⟫_ℝ:= by
      rcases isMinOn_iff.mp (alg.s₂ (α q -1)) z_.2 trivial with ieq
      simp at ieq
      rw [←sub_add,norm_add_sq_real,←sub_add,norm_add_sq_real] at ieq
      repeat rw [add_div] at ieq
      repeat rw [←add_assoc] at ieq
      simp [hq] at ieq
      have :0≤‖alg.y (α q) - alg.y (α q - 1)‖ ^ 2 / 2 := by
        apply div_nonneg
        norm_num
        norm_num
      linarith [ieq,this]
    have Hbd :∃C,∀q:ℕ ,‖(grad_snd H (alg.x (α q )) (alg.y (α q -1)))‖≤C:= by
      rcases isBounded_iff_forall_norm_le.mp bd with ⟨C1,inin⟩
      have con11H:ContinuousOn (fun (x,y)↦grad_snd H x y) (Metric.closedBall (0:WithLp 2 (E×F)) (2*C1)) := by
        apply Continuous.continuousOn
        have :LipschitzWith l (fun (x,y)↦grad_snd H x y) := by
          apply lipschitzWith_iff_norm_sub_le.mpr
          rintro ⟨x1,y1⟩ ⟨x2,y2⟩
          simp
          calc
            ‖grad_snd H x1 y1 - grad_snd H x2 y2‖
              ≤‖(grad_fst H y1 x1 - grad_fst H y2 x2,grad_snd H x1 y1 - grad_snd H x2 y2)‖:= by
                exact (comp_norm_le (grad_fst H y1 x1 - grad_fst H y2 x2) (grad_snd H x1 y1 - grad_snd H x2 y2)).right
            _≤ ↑l * ‖(x1 - x2, y1 - y2)‖:= by
              have lip : LipschitzWith l (grad_fun_comp H) := alg.lip₁
              rw [lipschitzWith_iff_norm_sub_le] at lip
              specialize lip (x1,y1) (x2,y2)
              simp [grad_fun_comp,grad_comp] at lip
              -- exact lip
              sorry
        apply LipschitzWith.continuous this
      rcases @IsCompact.exists_bound_of_continuousOn (WithLp 2 (E×F)) F _ _ _ (isCompact_closedBall (0:WithLp 2 (E×F)) (2*C1))
        (fun (x,y)↦grad_snd H x y) con11H with ⟨C,sqsq⟩
      use C
      rintro q
      have :(alg.x (α q ),alg.y (α q -1))∈Metric.closedBall (0:WithLp 2 (E×F)) (2*C1) := by
        apply mem_closedBall_iff_norm.mpr
        simp
        calc
          @norm (WithLp 2 (E × F)) (WithLp.instProdNorm 2 E F) (alg.x (α q),alg.y (α q - 1)) ≤‖alg.x (α q)‖+‖alg.y (α q - 1)‖:=by
            apply prod_norm_le_block_sum_L2
          _≤‖alg.z (α q)‖+‖alg.z (α q -1)‖:=by
            have :‖alg.y (α q -1)‖≤‖alg.z (α q -1)‖:= by
              rw [WithLp.prod_norm_eq_of_L2]
              apply (Real.le_sqrt (norm_nonneg (alg.y (α q -1) ))
              (Left.add_nonneg (sq_nonneg ‖alg.x (α q - 1)‖)
              (sq_nonneg ‖(alg.y (α q -1) )‖ ))).mpr
              apply (le_add_of_nonneg_left (sq_nonneg ‖alg.x (α q - 1)‖))
            have :‖alg.x (α q )‖≤‖alg.z (α q )‖:= by
              rw [WithLp.prod_norm_eq_of_L2]
              apply (Real.le_sqrt (norm_nonneg (alg.x (α q ) ))
              (Left.add_nonneg (sq_nonneg ‖alg.x (α q )‖)
              (sq_nonneg ‖(alg.y (α q ) )‖ ))).mpr
              apply (le_add_of_nonneg_right (sq_nonneg ‖alg.y (α q )‖))
            linarith
          _≤C1+C1:=by
            apply add_le_add
            apply inin
            exact mem_image_of_mem z trivial
            apply inin
            exact mem_image_of_mem z trivial
          _=2*C1:=Eq.symm (two_mul C1)
      have hhhh:= sqsq (alg.x (α q ),alg.y (α q -1)) this
      simp at hhhh
      exact hhhh
    rcases Hbd with ⟨C,hbd⟩
    have diflte1:∀ ε>0, ∀ᶠ (q : ℕ) in atTop,‖alg.y (α q) - alg.y (α q - 1)‖ <ε:= by
      intro ε epos
      rcases (nhds_basis_abs_sub_lt (0:ℝ)).tendsto_right_iff.mp (Sufficient_Descent4 γ hγ ck dk lbdψ) ε epos with lte
      simp at lte
      rcases lte with ⟨a,ie⟩
      simp
      rcases final (a+1) monoa with ⟨A,iee⟩
      use A
      rintro b Aleb
      have:Monotone α:= by exact StrictMono.monotone monoa
      have a1leab:a+1≤ α b := by linarith [StrictMono.monotone monoa Aleb,iee]
      have :a≤ α b -1:= by exact Nat.le_sub_one_of_lt a1leab
      calc
        ‖alg.y (α b) - alg.y (α b - 1)‖≤@norm (WithLp 2 (E × F)) (WithLp.instProdNorm 2 E F) (alg.x (α b) - alg.x (α b - 1),alg.y (α b) - alg.y (α b - 1)) :=by
          rw [WithLp.prod_norm_eq_of_L2]
          simp
          refine (Real.le_sqrt (norm_nonneg (alg.y (α b) - alg.y (α b - 1)))
            (Left.add_nonneg (sq_nonneg ‖alg.x (α b) - alg.x (α b - 1)‖)
            (sq_nonneg ‖alg.y (α b) - alg.y (α b - 1)‖ ))).mpr
            (le_add_of_nonneg_left (sq_nonneg ‖alg.x (α b) - alg.x (α b - 1)‖))
        _=‖alg.z (α b) - alg.z (α b - 1)‖:= rfl
        _<ε:= by
          have: ‖z (α b - 1 + 1) - z (α b - 1)‖ < ε:=ie (α b - 1) this
          have eqq:(α b - 1 + 1)=α b:= by
            apply Nat.sub_add_cancel
            linarith [a1leab]
          rw [eqq] at this
          assumption
    have diflte2:∀ ε>0, ∀ᶠ (q : ℕ) in atTop,‖z_.2 - alg.y (α q - 1)‖ <ε:= by
      rintro ε epos
      have : ∀ᶠ (q : ℕ) in atTop,‖z_.2 - alg.y (α q )‖ <ε/2:= by
        rcases (atTop_basis.tendsto_iff (@Metric.nhds_basis_ball _ _ z_)).mp conv (ε/2) (half_pos epos) with ⟨n1,_,ieq1⟩
        simp [dist_eq_norm] at ieq1;simp
        use n1
        rintro b n1leb
        calc
          ‖z_.2 - alg.y (α b)‖≤‖z_ -z (α b)‖ :=by
            rw [WithLp.prod_norm_eq_of_L2]
            simp
            refine (Real.le_sqrt (norm_nonneg (z_.2 - alg.y (α b)))
              (Left.add_nonneg (sq_nonneg ‖z_.1 - alg.x (α b)‖)
              (sq_nonneg ‖z_.2 - alg.y (α b)‖ ))).mpr
              (le_add_of_nonneg_left (sq_nonneg ‖z_.1 - alg.x (α b)‖))
          _<ε/2:=by
            rw [norm_sub_rev]
            exact ieq1 b n1leb
      have :∀ᶠ (q : ℕ) in atTop,‖z_.2 - alg.y (α q )‖ <ε/2∧‖alg.y (α q) - alg.y (α q - 1)‖ <ε/2
          := Eventually.and this (diflte1 (ε/2) (half_pos epos))
      apply Eventually.mono this
      rintro x ⟨h1,h2⟩
      calc
        ‖z_.2 - alg.y (α x - 1)‖=‖z_.2 - alg.y (α x )+(alg.y (α x) - alg.y (α x -1))‖:= by
          simp
        _≤‖z_.2 - alg.y (α x)‖+‖alg.y (α x) - alg.y (α x - 1)‖:= by
          apply norm_add_le
        _<ε/2+ε/2:= by linarith [h1,h2]
        _=ε := by exact add_halves ε

    have (k:ℕ→F)(defle:∀ ε > 0, ∀ᶠ (q : ℕ) in atTop, ‖k q‖ < ε):∀ ε>0, ∀ᶠ (q : ℕ) in atTop,abs
        ⟪k q, alg.d (α q -1) • grad_snd H (alg.x (α q )) (alg.y (α q -1))⟫_ℝ≤ε:= by
      rintro ε epos
      simp at defle;simp
      by_cases Cpos:0<C
      · have :0<ε/(C/(γ*l)) := by
          apply div_pos epos;apply div_pos Cpos;apply mul_pos _ alg.lpos;linarith
        rcases defle (ε/(C/(γ*l))) this with ⟨nn,ieq⟩
        use nn
        rintro b nleb
        rw [dk]
        calc
          |⟪k b, (1 / (γ * ↑l)) • grad_snd H (alg.x (α b )) (alg.y (α b - 1))⟫_ℝ|
            ≤‖k b‖*‖(1 / (γ * ↑l)) • grad_snd H (alg.x (α b )) (alg.y (α b - 1))‖
              := by apply abs_real_inner_le_norm
          _≤ε / (C / (γ * ↑l))*‖(1 / (γ * ↑l)) • grad_snd H (alg.x (α b )) (alg.y (α b - 1))‖:= by
            apply mul_le_mul (le_of_lt (ieq b nleb))
            trivial
            repeat apply norm_nonneg
            apply le_of_lt;apply div_pos;apply epos;apply div_pos Cpos;apply mul_pos _ alg.lpos
            linarith [hγ]
          _=ε / (C / (γ * ↑l))*(1 / (γ * ↑l)) *‖ grad_snd H (alg.x (α b )) (alg.y (α b - 1))‖:= by
            rw [mul_assoc]
            apply mul_eq_mul_left_iff.mpr
            left
            refine
              norm_smul_of_nonneg ?h.ht (grad_snd H (alg.x (α b )) (alg.y (α b - 1)))
            apply div_nonneg
            norm_num;apply mul_nonneg
            linarith [hγ];linarith [alg.lpos]
          _=ε/C*‖ grad_snd H (alg.x (α b )) (alg.y (α b - 1))‖:= by
            apply mul_eq_mul_right_iff.mpr;left
            rw [←div_mul,mul_assoc,mul_one_div,div_self,mul_one]
            have :0<γ * ↑l:=by apply mul_pos _ alg.lpos;linarith
            linarith
          _≤ε/C*C:= by
            apply mul_le_mul;trivial;apply hbd b;apply norm_nonneg
            apply le_of_lt ;apply div_pos epos Cpos
          _=ε:= by
            refine div_mul_cancel₀ ε ?h;linarith [Cpos]
      · push_neg at Cpos
        use 100000
        rintro b _
        rw [dk]
        calc
          |⟪k b,  (1 / (γ * ↑l))• grad_snd H (alg.x (α b )) (alg.y (α b - 1))⟫_ℝ|
            ≤‖k b‖*‖(1 / (γ * ↑l)) • grad_snd H (alg.x (α b )) (alg.y (α b - 1))‖
              := by apply abs_real_inner_le_norm
          _=‖k b‖*(1 / (γ * ↑l)) *‖grad_snd H (alg.x (α b )) (alg.y (α b - 1))‖
              :=by
              rw [mul_assoc]
              apply mul_eq_mul_left_iff.mpr
              left
              refine
              norm_smul_of_nonneg ?h.ht (grad_snd H (alg.x (α b )) (alg.y (α b - 1)))
          _≤‖k b‖*(1 / (γ * ↑l))*C:= by
            apply mul_le_mul
            trivial;apply hbd b;apply norm_nonneg;apply mul_nonneg;apply norm_nonneg
            apply div_nonneg;norm_num;apply mul_nonneg;linarith;linarith [alg.lpos]
          _≤0:= by
            apply mul_nonpos_iff.mpr
            left
            refine ⟨?_,Cpos⟩
            apply mul_nonneg;apply norm_nonneg
            apply div_nonneg;norm_num;apply mul_nonneg;linarith;linarith [alg.lpos]
          _≤ε:= by linarith
    simp only [dk] at ieq
    have finalpos:0<ε/(γ*l)/3:= by
      apply div_pos;apply div_pos epos;apply mul_pos;linarith;apply alg.lpos;linarith
    have h1:∀ᶠ (q : ℕ) in atTop,|⟪alg.y (α q) - alg.y (α q - 1), alg.d (α q - 1) • grad_snd H
        (alg.x (α q )) (alg.y (α q - 1))⟫_ℝ| ≤ε / (γ * ↑l) / 3 :=
      this (fun q↦alg.y (α q) - alg.y (α q - 1)) (diflte1) (ε/(γ*l)/3) finalpos
    have h2: ∀ᶠ (q : ℕ) in atTop,|⟪z_.2 - alg.y (α q - 1), alg.d (α q - 1) • grad_snd H (alg.x (α q ))
        (alg.y (α q - 1))⟫_ℝ| ≤ ε / (γ * ↑l) / 3:=
      this (fun q↦z_.2 - alg.y (α q - 1)) diflte2 (ε/(γ*l)/3) finalpos
    have h3: ∀ᶠ (q : ℕ) in atTop,‖z_.2 - alg.y (α q - 1)‖ ^ 2 / 2<(ε/(γ*l)/3):= by
      refine Eventually.mono (diflte2 (√(2*(ε/(γ*l)/3))) ?_) ?_
      apply Real.sqrt_pos_of_pos
      apply mul_pos;norm_num;apply finalpos
      intro x assx
      have :‖z_.2 - alg.y (α x - 1)‖^2<(2*(ε/(γ*l)/3)):= by
        refine (Real.lt_sqrt ?hy).mp ?_
        apply norm_nonneg
        exact assx
      calc
        ‖z_.2 - alg.y (α x - 1)‖ ^ 2 / 2<(2*(ε/(γ*l)/3))/2:= by
          apply (div_lt_div_right _).mpr
          apply this
          linarith
        _=(ε/(γ*l)/3):= by
          apply mul_div_cancel_left₀
          linarith
    simp at h1 h2 h3
    simp only [dk] at h1 h2 h3
    simp
    rcases h1 with ⟨m1,ie1⟩
    rcases h2 with ⟨m2,ie2⟩
    rcases h3 with ⟨m3,ie3⟩
    use 1+max (max m1 m2) m3
    intro q mleq
    have m1le:m1≤1+max (max m1 m2) m3:=by linarith [(le_max_left m1 m2).trans (le_max_left (max m1 m2) m3)]
    have m2le:m2≤1+max (max m1 m2) m3:= by linarith [(le_max_right m1 m2).trans (le_max_left (max m1 m2) m3)]
    have m3le:m3≤1+max (max m1 m2) m3:= by linarith [le_max_right (max m1 m2) m3]
    have :1≤α q := by
      have :α 0 < α q:= by
        apply monoa
        linarith [Nat.le_of_add_right_le mleq]
      linarith
    have key:1 / (γ * ↑l) * g (alg.y (α q)) <1 / (γ * ↑l) * g z_.2 +ε / (γ * ↑l):= by
      linarith [ieq q this,(abs_le.mp (ie1 q (m1le.trans mleq))).1,(abs_le.mp (ie2 q (m2le.trans mleq))).2,
        ie3 q (m3le.trans mleq),add_thirds (ε / (γ * ↑l))]
    have ltt:0<γ*l:= by
      apply mul_pos;linarith;linarith [alg.lpos]
    calc
      g (z (α q)).2=g (alg.y (α q)):= rfl
      _=(γ * ↑l)*(1 / (γ * ↑l) * g (alg.y (α q))):= by
        rw [←mul_assoc,mul_one_div_cancel (LT.lt.ne ltt).symm,one_mul]
      _<(γ * ↑l)*(1 / (γ * ↑l) * g z_.2 + ε / (γ * ↑l)):=(mul_lt_mul_left ltt).mpr key
      _=g z_.2 + ε:=by
        rw [mul_add,←mul_assoc,mul_one_div_cancel (LT.lt.ne ltt).symm,one_mul,mul_div_cancel₀ _ (LT.lt.ne ltt).symm]
  exact Eventually.and lef rig

--the convergence of subseq implies the convergence of alg.ψ
theorem psiconv(α:ℕ→ℕ)(z_:WithLp 2 (E×F))(monoa:StrictMono α )(conv:Tendsto (fun n ↦ alg.z (α n)) atTop (𝓝 z_))
  (bd : Bornology.IsBounded (alg.z '' univ)) (lbdψ : BddBelow (alg.ψ '' univ)):
  Tendsto (fun n ↦ alg.ψ (alg.z (α n))) atTop (𝓝 (alg.ψ z_)):=by
      apply Tendsto.add
      · apply Tendsto.add
        · apply fconv γ hγ ck dk α z_ monoa conv bd lbdψ
        · apply gconv γ hγ ck dk α z_ monoa conv bd lbdψ
      exact (continuous_iff_seqContinuous.mp (ContDiff.continuous alg.conf)) conv

#check  Ψ_subdiff_bound
lemma limitset_property_1 (bd : Bornology.IsBounded (alg.z '' univ)) (lbdψ : BddBelow (alg.ψ '' univ)):
    (limit_set alg.z).Nonempty ∧ ((limit_set alg.z) ⊆ critial_point alg.ψ) := by
  constructor
  --nonempty
  have hz : ∀ (n : ℕ), alg.z n ∈ alg.z '' univ:= by intro n; use n; constructor; exact Set.mem_univ n; rfl
  have : ∃ a ∈ closure (alg.z '' univ), ∃ (φ : ℕ → ℕ), StrictMono φ ∧ Filter.Tendsto (alg.z ∘ φ) Filter.atTop (nhds a):=
    tendsto_subseq_of_bounded (bd) (hz)
  rcases this with ⟨a,ha,φ,⟨hmφ,haφ⟩⟩
  use a
  simp[limit_set]
  apply (mapClusterPt_iff _ _ _).mpr
  intro s hs
  apply Filter.frequently_iff.mpr
  intro U hU
  rw [Filter.mem_atTop_sets] at hU
  rcases hU with ⟨ax,hax⟩
  rw [mem_nhds_iff] at hs
  obtain ⟨t, t_s, ⟨isopent,a_t⟩ ⟩ := hs
  rw [tendsto_atTop_nhds] at haφ
  specialize haφ t a_t isopent
  rcases haφ with ⟨N,hN⟩
  let n := N + ax
  have hn: N ≤ n:=by simp[n]
  have hnax:ax ≤ n:=by simp[n]
  use φ n
  constructor
  apply hax
  apply le_trans hnax
  apply StrictMono_nat
  exact hmφ
  have h_t : (BCD.z (φ n)) ∈ t := hN n hn
  have h_s : (BCD.z (φ n)) ∈ s := t_s h_t
  exact h_s
  --the folllowing shows that limit_set BCD.z ⊆ critial_point BCD.ψ
  intro z_ ha
  have ha': MapClusterPt z_ atTop alg.z :=ha

  have: ∃ (φ : ℕ → ℕ), StrictMono φ ∧ Filter.Tendsto ((alg.z) ∘ φ) Filter.atTop (nhds z_) :=
    TopologicalSpace.FirstCountableTopology.tendsto_subseq ha'
  rcases this with ⟨φ,monoφ,conv⟩

  have zero_in_partial:0∈ subdifferential alg.ψ z_ :=by
    rw [subdifferential,Set.mem_setOf]
    use fun n ↦ alg.z (φ (n+1))
    constructor
    exact (tendsto_add_atTop_iff_nat 1).mpr conv
    constructor
    exact (tendsto_add_atTop_iff_nat 1).mpr (psiconv γ hγ ck dk φ z_ monoφ conv bd lbdψ)
    rcases Ψ_subdiff_bound γ hγ ck dk with ⟨ρ,ρpos,ieq⟩
    let v:=fun q↦Classical.choose (ieq (φ (q+1) -1))
    use v
    intro n
    have (q:ℕ):1≤φ (q+1):= (Nat.le_add_left 1 q).trans (StrictMono_nat φ monoφ (q+1))
    have key (q:ℕ):v q ∈ f_subdifferential alg.ψ (alg.x (φ (q+1) -1 + 1), alg.y (φ (q+1) -1 + 1))
      ∧‖v q‖ ≤ ρ * ‖alg.z (φ (q+1) -1 + 1) - alg.z (φ (q+1) -1)‖:=by
      simp [v]
      apply Classical.choose_spec (ieq (φ (q+1) -1))
    have subadd(q:ℕ):φ (q+1) -1 +1=φ (q+1):= by exact Nat.sub_add_cancel (this (sorryAx ℕ true))
    simp [subadd] at key
    constructor
    · exact (key n).1
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply (nhds_basis_Ioo_pos 0).tendsto_right_iff.mpr
    rintro ε epos
    simp
    rcases (nhds_basis_abs_sub_lt (0:ℝ)).tendsto_right_iff.mp (Sufficient_Descent4 γ hγ ck dk lbdψ)
      (ε/ρ) (div_pos epos ρpos) with lte
    simp at lte
    rcases lte with ⟨a,ieq⟩
    use a
    rintro b aleb
    constructor
    linarith [norm_nonneg (v b),epos]
    calc
      ‖v b‖≤ρ * ‖z (φ (b + 1)) - z (φ (b + 1) - 1)‖:= (key b).2
      _<ρ*(ε/ρ):=by
        apply (mul_lt_mul_left ρpos).mpr
        have :‖alg.z (φ (b + 1)-1+1) - alg.z (φ (b + 1) - 1)‖ < ε / ρ:=by
          apply ieq
          apply aleb.trans
          calc
            b=b+1-1:= by exact rfl
            _≤φ (b+1)-1:= Nat.sub_le_sub_right (StrictMono_nat φ monoφ (b+1)) 1
        simp [subadd b] at this
        exact this
      _=ε:=by
        rw [mul_comm]
        apply div_mul_cancel₀
        linarith [ρpos]
  apply Set.mem_setOf.mpr
  exact zero_in_partial


lemma limitset_property_2 (bd : Bornology.IsBounded (alg.z '' univ))(lbdψ : BddBelow (alg.ψ '' univ)):
    Tendsto (fun n ↦ (EMetric.infEdist (alg.z n) (limit_set alg.z)).toReal) atTop (𝓝 0) := by
  apply (nhds_basis_Ioo_pos 0).tendsto_right_iff.mpr
  rintro ε epos
  by_contra h
  simp at h
  --alg.z∘W is the subseq s.t. the dist is no less than ε
  let W:ℕ → ℕ:=fun n ↦
    Nat.recOn n (Classical.choose (h 0))
    fun n p ↦ (Classical.choose (h (p+1)))
  have monoW:StrictMono W:=by
    have (n:ℕ):W n+1≤W (n+1):=(Classical.choose_spec (h (W n +1))).1
    have (n:ℕ):W n<W (n+1):= this n
    apply strictMono_nat_of_lt_succ this
  have bd':Bornology.IsBounded (alg.z∘W '' univ):=by
    apply bd.subset
    intro k;simp
    exact fun x zk ↦ ⟨W x,zk⟩
  have :∃ z_∈ closure (alg.z∘W '' univ), ∃ α:ℕ → ℕ,StrictMono α∧Tendsto (fun n ↦ (alg.z∘W) (α n)) atTop (𝓝 z_):= by
    have hcs:IsSeqCompact (closure (alg.z∘W '' univ)) := by
      apply IsCompact.isSeqCompact
      exact bd'.isCompact_closure
    have even: ∃ᶠ n in atTop, (alg.z∘W) n ∈ closure (alg.z∘W '' univ) := sorryAx
      (∃ᶠ (n : ℕ) in atTop, (BCD.z∘W) n ∈ closure (alg.z∘W '' univ)) true
    apply hcs.subseq_of_frequently_in even
  rcases this with ⟨z_,_,α,⟨monoa,conv⟩⟩
  have z_in : z_ ∈ limit_set alg.z:= by
    simp [limit_set, MapClusterPt]
    apply ClusterPt.mono (ClusterPt.of_le_nhds conv)
    calc
      _ = map (fun n ↦ (alg.z∘W) n) (map α atTop) := by
        rw [map_map]
        rfl
      _ ≤ map (fun n↦ (alg.z∘W) n) atTop := map_mono (StrictMono.tendsto_atTop monoa)
      _ ≤ map (fun n↦ alg.z n) atTop:= by
        rw [←map_map]
        apply map_mono (StrictMono.tendsto_atTop monoW)
  --show the contradiction
  have z_0:(EMetric.infEdist (z_) (limit_set alg.z)).toReal=0:= by
    have :(EMetric.infEdist (z_) (limit_set alg.z))=0:=EMetric.infEdist_zero_of_mem z_in
    refine (ENNReal.toReal_eq_zero_iff _).mpr ?_
    left;exact this
  have z_ge:(EMetric.infEdist (z_) (limit_set alg.z)).toReal≥ε:=by
    have :Tendsto (fun n ↦(EMetric.infEdist ((alg.z∘W) (α n)) (limit_set alg.z)).toReal)
      atTop (𝓝 (EMetric.infEdist (z_) (limit_set alg.z)).toReal):=
      continuous_iff_seqContinuous.mp (Metric.continuous_infDist_pt (limit_set z)) conv
    apply ge_of_tendsto this
    simp
    use 1
    rintro n len
    have key:ε≤(EMetric.infEdist ((alg.z ∘ W) (α n -1 +1)) (limit_set alg.z)).toReal:=by
      apply (Classical.choose_spec (h (W (α n -1) +1))).2
      calc
        -ε<0:=by linarith
        _≤(EMetric.infEdist (alg.z (Classical.choose (h (W (α n -1) +1)))) (limit_set alg.z)).toReal:=by
          exact ENNReal.toReal_nonneg
    have :α n -1+1=α n:= tsub_add_cancel_iff_le.mpr (Nat.one_le_of_lt (monoa len))
    rw [←this]
    exact key
  linarith

lemma limitset_property_3 (bd : Bornology.IsBounded (alg.z '' univ))(lbdψ : BddBelow (alg.ψ '' univ)):
    IsCompact (limit_set alg.z) ∧ IsConnected (limit_set alg.z) := by
  have com:IsCompact (limit_set alg.z):=by
    apply Metric.isCompact_of_isClosed_isBounded
    apply isClosed_setOf_clusterPt
    apply isBounded_iff_forall_norm_le.mpr
    rcases isBounded_iff_forall_norm_le.mp bd with ⟨C,zin⟩
    use C
    rintro z_ z_in
    rcases subseq_tendsto_of_neBot z_in with ⟨φ,⟨monoφ,conv⟩⟩
    apply le_of_tendsto'
      (Tendsto.norm conv) (fun n↦zin (alg.z (φ n)) (mem_image_of_mem alg.z (mem_univ (φ n))) )
  constructor
  exact com
  --the following is the proof of connectivity
  have:IsConnected (limit_set alg.z)<->((limit_set alg.z).Nonempty ∧ IsPreconnected (limit_set alg.z)):= by rfl
  rw[this]
  constructor
  exact (limitset_property_1 γ hγ ck dk bd lbdψ).1
  rw [isPreconnected_closed_iff]
  --construct closed A,B such that A∩B=∅,A∪B=limit_set
  by_contra nonconnect
  push_neg at nonconnect
  rcases nonconnect with ⟨a,b,closea,closeb,sub_ab,nez_a,nez_b,nz_ab⟩
  let A:=(limit_set alg.z)∩a
  let B:=(limit_set alg.z)∩b
  have closeA:IsClosed A:=IsClosed.inter (isClosed_setOf_clusterPt) closea
  have closeB:IsClosed B:=IsClosed.inter (isClosed_setOf_clusterPt) closeb
  have noneptA:A.Nonempty:=nez_a
  have noneptB:B.Nonempty:=nez_b
  have eqAB:A∪B=(limit_set alg.z):=by
    simp [A,B]
    calc
      (limit_set z∩a) ∪ ( limit_set z∩ b) =  limit_set z∩(a∪b):=
        (inter_union_distrib_left (limit_set z) a b).symm
      _=limit_set z:= (left_eq_inter.mpr sub_ab).symm
  have disjoint_AB:A∩B=∅:= by
    simp [A,B]
    calc
      limit_set z ∩ a ∩ (limit_set z ∩ b)=limit_set z ∩ (a∩b):=
        (inter_inter_distrib_left (limit_set z) a b).symm
      _=∅:=nz_ab
  --ω is a function that shows the relation between z and A,B
  let ω : WithLp 2 (E × F) -> ℝ := fun z => ((EMetric.infEdist z A).toReal) /
    ((EMetric.infEdist z A).toReal+(EMetric.infEdist z B).toReal)
  have sum_ne_zero:∀ z ,(EMetric.infEdist z A).toReal+(EMetric.infEdist z B).toReal≠0:= by
    intro z eq0
    have inA:z∈A:=by
      apply EMetric.mem_closure_iff_infEdist_zero.mpr
      show EMetric.infEdist z A=0
      have net:EMetric.infEdist z A≠⊤:=by
        exact Metric.infEdist_ne_top nez_a
      have :(EMetric.infEdist z A).toReal=0:=by
        linarith [eq0,@ENNReal.toReal_nonneg (EMetric.infEdist z A),@ENNReal.toReal_nonneg (EMetric.infEdist z B)]
      exact (((fun {x y} hx hy ↦ (ENNReal.toReal_eq_toReal_iff' hx hy).mp)
          ENNReal.top_ne_zero.symm net (id (Eq.symm this)))).symm
      simp;constructor;apply closeA;exact fun ⦃a⦄ a ↦ a
    have inB:z∈B:=by
      apply EMetric.mem_closure_iff_infEdist_zero.mpr
      show EMetric.infEdist z B=0
      have net:EMetric.infEdist z B≠⊤:=by
        exact Metric.infEdist_ne_top nez_b
      have :(EMetric.infEdist z B).toReal=0:=by
        linarith [eq0,@ENNReal.toReal_nonneg (EMetric.infEdist z A),@ENNReal.toReal_nonneg (EMetric.infEdist z B)]
      exact (((fun {x y} hx hy ↦ (ENNReal.toReal_eq_toReal_iff' hx hy).mp)
          ENNReal.top_ne_zero.symm net (id (Eq.symm this)))).symm
      simp;constructor;apply closeB;exact fun ⦃a⦄ a ↦ a
    have :z∈A∩B:=mem_inter inA inB
    rw [disjoint_AB] at this
    contradiction
  have contω: Continuous ω := by
    apply Continuous.div
    exact Metric.continuous_infDist_pt A
    apply Continuous.add (Metric.continuous_infDist_pt A) (Metric.continuous_infDist_pt B)
    apply sum_ne_zero
  let U := {z:WithLp 2 (E × F)|(ω z)<(1/4)}
  let V := {z:WithLp 2 (E × F)|(3/4)<(ω z)}
  have A0:∀ z_∈A,ω z_ =0:= by
    rintro z_ zA
    rw [div_eq_zero_iff]
    left
    have :EMetric.infEdist z_ A=0:=by
      apply EMetric.infEdist_zero_of_mem zA
    rw [this];rfl
  have B1:∀z_∈ B,ω z_ =1:= by
    rintro z_ zB
    simp [ω]
    apply (div_eq_one_iff_eq (sum_ne_zero z_)).mpr
    simp
    have :EMetric.infEdist z_ B=0:=by
      apply EMetric.infEdist_zero_of_mem zB
    rw [this];rfl
  --eventually alg.z falls in U or V
  have U_V_prop:∃ k0:ℕ,∀ k:ℕ, (k0 ≤ k) -> (alg.z k ∈ U) ∨ (alg.z k ∈ V) := by
    by_contra h
    push_neg at h
    let W:ℕ→ℕ:=fun n↦
      Nat.recOn n (Classical.choose (h 0))
      fun n p ↦ (Classical.choose (h (p+1)))
    have monoW:StrictMono W:=by
      have (n:ℕ):W n+1≤W (n+1):=(Classical.choose_spec (h (W n +1))).1
      have (n:ℕ):W n<W (n+1):= this n
      apply strictMono_nat_of_lt_succ this
    have bd':Bornology.IsBounded (alg.z∘W '' univ):=by
      apply bd.subset
      intro k;simp
      exact fun x zk ↦ ⟨W x,zk⟩
    have :∃ z_∈ closure (alg.z∘W '' univ), ∃ α:ℕ → ℕ,StrictMono α∧Tendsto (fun n ↦ (alg.z∘W) (α n)) atTop (𝓝 z_):= by
      have hcs:IsSeqCompact (closure (alg.z∘W '' univ)) := by
        apply IsCompact.isSeqCompact
        exact bd'.isCompact_closure
      have even: ∃ᶠ n in atTop, (alg.z∘W) n ∈ closure (alg.z∘W '' univ) := sorryAx (∃ᶠ (n : ℕ) in atTop,
        (BCD.z∘W) n ∈ closure (alg.z∘W '' univ)) true
      apply hcs.subseq_of_frequently_in even
    rcases this with ⟨z_,_,α,⟨monoa,conv⟩⟩
    have z_in : z_ ∈ limit_set alg.z:= by
      simp [limit_set, MapClusterPt]
      apply ClusterPt.mono (ClusterPt.of_le_nhds conv)
      calc
        _ = map (fun n ↦ (alg.z∘W) n) (map α atTop) := by
          rw [map_map]
          rfl
        _ ≤ map (fun n↦ (alg.z∘W) n) atTop := map_mono (StrictMono.tendsto_atTop monoa)
        _ ≤ map (fun n↦ alg.z n) atTop:= by
          rw [←map_map]
          apply map_mono (StrictMono.tendsto_atTop monoW)
    rw [←eqAB] at z_in
    rcases z_in with zA | zB
    · have :ω z_ =0:= A0 z_ zA
      have z_ge:ω z_≥1/4:=by
        have :Tendsto (fun n ↦(ω ((alg.z∘W∘α)  n)) ) atTop (𝓝 (ω z_)):=
          continuous_iff_seqContinuous.mp (contω) conv
        apply ge_of_tendsto this
        simp
        use 1
        rintro n len
        have key:1/4≤ω ((alg.z ∘ W) (α n -1 +1)) :=by
          have :(alg.z ∘ W) (α n -1 +1)∉U:= (Classical.choose_spec (h (W (α n -1) +1))).2.1
          rw [Set.mem_setOf] at this
          push_neg at this;exact this
        have :α n -1+1=α n:= tsub_add_cancel_iff_le.mpr (Nat.one_le_of_lt (monoa len))
        rw [←this]
        simp at key;exact key
      linarith
    · have :ω z_ =1:= B1 z_ zB
      have z_ge:ω z_≤3/4:=by
        have :Tendsto (fun n ↦(ω ((alg.z∘W∘α)  n)) ) atTop (𝓝 (ω z_)):=
          continuous_iff_seqContinuous.mp (contω) conv
        apply le_of_tendsto this
        simp
        use 1
        rintro n len
        have key:ω ((alg.z ∘ W) (α n -1 +1))≤3/4 :=by
          have :(alg.z ∘ W) (α n -1 +1)∉V:= (Classical.choose_spec (h (W (α n -1) +1))).2.2
          rw [Set.mem_setOf] at this
          push_neg at this;exact this
        have :α n -1+1=α n:= tsub_add_cancel_iff_le.mpr (Nat.one_le_of_lt (monoa len))
        rw [←this]
        simp at key;exact key
      linarith
  rcases U_V_prop with ⟨k0,hk0⟩
  --eventually alg.z falls into the same U or V
  have unicont:UniformContinuousOn ω (closure (alg.z '' univ)):=IsCompact.uniformContinuousOn_of_continuous
    bd.isCompact_closure contω.continuousOn
  have :∀ε>0,∃ δ>0,∀ x1∈(closure (alg.z '' univ)), ∀x2∈(closure (alg.z '' univ)),‖x1-x2‖<δ → ‖ω x1 -ω x2‖<ε:=by
    have h:= (((@NormedAddCommGroup.uniformity_basis_dist (WithLp 2 (E×F)) _).inf
    (hasBasis_principal ((closure (alg.z '' univ)) ×ˢ(closure (alg.z '' univ))))).tendsto_iff
    (@NormedAddCommGroup.uniformity_basis_dist ℝ _) ).mp unicont
    simp at h
    rw [Eq.symm image_univ ] at h
    rintro ε epos
    rcases h ε epos with ⟨δ,⟨dpos,ieq⟩⟩
    exact ⟨δ,⟨dpos,fun x1 x1s x2 x2s dis↦ieq x1 x2 dis x1s x2s⟩⟩
  have :∀ε>0,∃ N,∀n≥N,‖ω (alg.z (n+1))-ω (alg.z n)‖<ε:=by
    rintro ε epos
    rcases this ε epos with ⟨δ,dpos,ieq⟩
    rcases (nhds_basis_abs_sub_lt (0:ℝ)).tendsto_right_iff.mp (Sufficient_Descent4 γ hγ ck dk lbdψ) δ dpos with lte
    simp at lte
    rcases lte with ⟨a,ie⟩
    use a;rintro n alen
    apply ieq
    apply subset_closure (mem_image_of_mem z (mem_univ (n+1)))
    apply subset_closure (mem_image_of_mem z (mem_univ (n)))
    apply ie n alen
  rcases this (1/2) one_half_pos with ⟨N,key⟩
  have :∃M,(∀n≥M,alg.z n ∈ U)∨(∀n≥M,alg.z n ∈ V):= by
    let M:= max k0 N
    use M
    rcases hk0 M (Nat.le_max_left k0 N) with MU|MV
    left
    have (n:ℕ):alg.z (M+n)∈U:= by
      induction' n with n ih
      · exact MU
      rcases hk0 (M+n+1) ((Nat.le_max_left k0 N).trans (Nat.le_add_right M (n + 1))) with nU|nV
      exact nU
      rw [mem_setOf] at ih nV
      linarith [(abs_lt.mp (key (M+n) ((Nat.le_max_right k0 N).trans (Nat.le_add_right M (n))))).2,ih,nV]
    rintro n Mlen
    rw [←Nat.add_sub_of_le Mlen];apply this (n - M)
    right
    have (n:ℕ):alg.z (M+n)∈V:= by
      induction' n with n ih
      · exact MV
      rcases hk0 (M+n+1) ((Nat.le_max_left k0 N).trans (Nat.le_add_right M (n + 1))) with nU|nV
      rw [mem_setOf] at ih nU
      linarith [(abs_lt.mp (key (M+n) ((Nat.le_max_right k0 N).trans (Nat.le_add_right M (n))))).1,ih,nU]
      exact nV
    rintro n Mlen
    rw [←Nat.add_sub_of_le Mlen];apply this (n - M)
  --show the contradiction
  rcases this with ⟨M,h1|h2⟩
  · rcases noneptB with ⟨z_,inB⟩
    have :z_∈limit_set alg.z:= mem_of_mem_inter_left inB
    have : ∃ (φ : ℕ → ℕ), StrictMono φ ∧ Filter.Tendsto (alg.z ∘ φ) Filter.atTop (nhds z_) :=by
      exact subseq_tendsto_of_neBot this
    rcases this with ⟨φ,monoφ,conv⟩
    have :ω z_≤1/4:= by
      apply le_of_tendsto (continuous_iff_seqContinuous.mp (contω) conv)
      simp
      use M
      rintro b Mleb
      have g:= h1 (φ b) (Mleb.trans (StrictMono_nat φ monoφ b))
      rw [mem_setOf] at g
      simp at g
      apply le_of_lt g
    linarith [this,B1 z_ inB]
  · rcases noneptA with ⟨z_,inA⟩
    have :z_∈limit_set alg.z:= mem_of_mem_inter_left inA
    have : ∃ (φ : ℕ → ℕ), StrictMono φ ∧ Filter.Tendsto (alg.z ∘ φ) Filter.atTop (nhds z_) :=by
      exact subseq_tendsto_of_neBot this
    rcases this with ⟨φ,monoφ,conv⟩
    have :ω z_≥3/4:= by
      apply ge_of_tendsto (continuous_iff_seqContinuous.mp (contω) conv)
      simp
      use M
      rintro b Mleb
      have g:= h2 (φ b) (Mleb.trans (StrictMono_nat φ monoφ b))
      rw [mem_setOf] at g
      apply le_of_lt g
    linarith [this,A0 z_ inA]


lemma limitset_property_4 (bd : Bornology.IsBounded (alg.z '' univ)) (lbdψ : BddBelow (alg.ψ '' univ)):
    ∃ (c:ℝ) , ∀ x ∈ (limit_set alg.z) , alg.ψ x = c := by
  --alg.ψ converges to same ψ_final
  have decent_ψ:∃ ψ_final, Tendsto (alg.ψ ∘ alg.z) Filter.atTop (nhds ψ_final) :=by
    have monopsi:Antitone (alg.ψ ∘alg.z):= by
      apply antitone_nat_of_succ_le
      apply Sufficient_Descent2 γ hγ ck dk
    rcases (tendsto_of_antitone monopsi) with h1|h2
    have notbd:=unbounded_of_tendsto_atBot h1
    have bdd:BddBelow (range (alg.ψ ∘ alg.z)):=by
      apply BddBelow.mono _ lbdψ
      simp
      apply range_comp_subset_range
    contradiction
    exact h2
  rcases decent_ψ with ⟨ψ_final,hψ⟩
  --show that ψ_final is what we need
  use ψ_final
  intro z_1 hz_1
  have z_1_cluster: ∃ (φ : ℕ → ℕ), StrictMono φ ∧ Filter.Tendsto (alg.z ∘ φ) Filter.atTop (nhds z_1) :=by
    exact subseq_tendsto_of_neBot hz_1
  rcases z_1_cluster with ⟨φ,⟨monoφ,conv⟩⟩
  have :alg.ψ z_1= ψ_final:=by
    have tend1:Tendsto (alg.ψ∘alg.z ∘ φ) atTop (𝓝 ψ_final):=by
      obtain monoφ' := StrictMono.tendsto_atTop monoφ
      calc
        _ ≤ map (fun n ↦ ((alg.ψ∘alg.z) n)) atTop := by
          rw [← Filter.map_map]; apply map_mono monoφ'
        _ ≤ (𝓝 ψ_final) := by
          exact hψ
    have tend2:Tendsto (alg.ψ∘alg.z ∘ φ) atTop (𝓝 (alg.ψ z_1)):=
      psiconv γ hγ ck dk φ z_1 monoφ conv bd lbdψ
    apply tendsto_nhds_unique tend2 tend1
  exact this


end limit_point

section Limited_length

lemma concave_deriv_bound {φ : ℝ → ℝ} {η x y : ℝ} (h : φ ∈ special_concave η)
    (hx : x ∈ Ioo 0 η) (hy : y ∈ Ioo 0 η) : φ x - φ y ≥ deriv φ x * (x - y) := by
  obtain ⟨h1, _, _, _, _, h6⟩ := h
  have hdiff := differentiableAt_of_deriv_ne_zero (ne_of_gt (h6 _ hx))
  let hx' := Ioo_subset_Ico_self hx
  let hy' := Ioo_subset_Ico_self hy
  rcases eq_or_ne x y with heq | hne
  · rw [heq]; simp only [sub_self, mul_zero, ge_iff_le, le_refl]
  · rw [← lt_or_lt_iff_ne] at hne
    rcases hne with ygt | xgt
    · obtain h := ConcaveOn.slope_le_deriv h1 hx' hy' ygt hdiff
      rw [slope_def_field, div_le_iff] at h
      repeat linarith
    · obtain h := ConcaveOn.deriv_le_slope h1 hy' hx' xgt hdiff
      rw [slope_def_field, le_div_iff] at h
      repeat linarith

lemma infEdist_bound {s : Set E} : ∀ x ∈ s, ‖x‖ ≥ (EMetric.infEdist 0 s).toReal := by
  intro x xs
  have : EMetric.infEdist 0 s ≤ edist 0 x := EMetric.infEdist_le_edist_of_mem xs
  rw [← dist_zero_left]
  exact ENNReal.toReal_le_of_le_ofReal dist_nonneg (edist_dist 0 x ▸ this)

lemma sq_le_mul_le_mean {a b c : ℝ} (h : a ^ 2 ≤ b * c) (hpos : 0 ≤ b + c) : 2 * a ≤ b + c := by
  have : 4 * b * c ≤ (b + c) ^ 2 := by
    have : 0 ≤ (b - c) ^ 2 := sq_nonneg _
    rw [add_sq]
    rw [sub_sq] at this
    linarith
  have : (2 * a) ^ 2 ≤ (b + c) ^ 2 := calc
    (2 * a) ^ 2 = 4 * a ^ 2 := by rw [mul_pow]; norm_num
    _ ≤ 4 * b * c := by linarith
    _ ≤ (b + c) ^ 2 := this
  exact (abs_le_of_sq_le_sq' this hpos).2


theorem Limited_length (bd : Bornology.IsBounded (alg.z '' univ)) (hψ : KL_function alg.ψ) (lbdψ : BddBelow (alg.ψ '' univ)):
    ∃ M : ℝ, ∀ n, ∑ k in Finset.range n, ‖alg.z (k + 1) - alg.z k‖ ≤ M := by
  have :∃ z_∈ closure (alg.z '' univ), ∃ α:ℕ → ℕ,StrictMono α∧Tendsto (fun n ↦ alg.z (α n)) atTop (𝓝 z_):= by
    have hcs:IsSeqCompact (closure (alg.z '' univ)) := by
      apply IsCompact.isSeqCompact
      exact bd.isCompact_closure
    have even: ∃ᶠ n in atTop, alg.z n ∈ closure (alg.z '' univ) := sorryAx (∃ᶠ (n : ℕ) in atTop,
      BCD.z n ∈ closure (alg.z '' univ)) true
    exact hcs.subseq_of_frequently_in even
  rcases this with ⟨z_,z_in,α,⟨monoa,conv⟩⟩
  rcases Sufficient_Descent1 γ hγ ck dk with ⟨ρ1,ρ1pos,suff_des⟩
  have z_in : z_ ∈ limit_set alg.z:= by
    simp [limit_set, MapClusterPt]
    apply ClusterPt.mono (ClusterPt.of_le_nhds conv)
    calc
      _ = map (fun n ↦ alg.z n) (map α atTop) := by
        rw [map_map]
        rfl
      _ ≤ map (fun  n↦ alg.z n) atTop := map_mono (StrictMono.tendsto_atTop monoa)
  have final m : ∃ n : ℕ, m ≤ α n := by
    induction' m with m ih
    · use 1; linarith
    rcases ih with ⟨n, ieqq⟩
    use n + 1
    have :α n + 1 ≤ α (n + 1):= by
      apply Nat.succ_le_iff.mpr
      apply monoa
      norm_num
    linarith
  have psiconv:Tendsto (fun n ↦ alg.ψ (alg.z (α n))) atTop (𝓝 (alg.ψ z_)):=by
    apply psiconv γ hγ ck dk α z_ monoa conv bd lbdψ
  have monopsi (m n : ℕ) : alg.ψ (alg.z (m + n)) ≤ alg.ψ (alg.z m):= by
    induction' n with n ih
    · simp
    have : alg.ψ (alg.z (m + (n + 1))) ≤ alg.ψ (alg.z (m + n)):= by
      rw [←add_assoc]
      have : alg.ψ (alg.z (m + n)) - alg.ψ (alg.z (m + n+1)) ≥ 0:= by
        calc
          _ ≥ ρ1 / 2 * ‖alg.z (m + n + 1) - alg.z (m + n)‖^2 := LE.le.ge (suff_des.2 (m + n))
          _ ≥ (ρ1 / 2) * 0 := by
            refine (mul_le_mul_iff_of_pos_left (half_pos ρ1pos)).mpr (sq_nonneg _)
          _= 0 := by norm_num
      linarith
    linarith
  by_cases h : ∀ n, alg.ψ (alg.z (α n)) > alg.ψ z_
  · have L1 : ∀ η > 0, ∃ l1 : ℕ, ∀ k ≥ l1, alg.ψ z_ < alg.ψ (alg.z k)
        ∧ alg.ψ (alg.z k) <alg.ψ z_ + η :=by
      rintro η epos
      rcases (atTop_basis.tendsto_iff (nhds_basis_Ioo_pos (alg.ψ z_))).mp
        psiconv η epos with ⟨l1,_,ieq⟩
      use α l1; rintro k kge
      constructor
      rcases final k with ⟨m,kleam⟩
      calc
        _ < alg.ψ (alg.z (α m)) := h m
        _ = alg.ψ (alg.z (k+(α m-k))) := by
          congr; exact Eq.symm (Nat.add_sub_of_le kleam)
        _ ≤ alg.ψ (alg.z k) := monopsi k (α m - k)
      calc
        _ = alg.ψ (alg.z (α l1 + (k - α l1))):= by
          congr; exact Eq.symm (Nat.add_sub_of_le kge)
        _ ≤ alg.ψ (alg.z (α l1)) := by apply monopsi
        _ < alg.ψ z_ + η := (ieq l1 left_mem_Ici).2
    have L2 : ∀ ε > 0, ∃ l2, ∀k > l2, (EMetric.infEdist (alg.z k) (limit_set alg.z)).toReal< ε := by
      rintro ε epos
      rcases limitset_property_2 bd lbdψ with tendt
      rcases (atTop_basis.tendsto_iff (nhds_basis_abs_sub_lt (0:ℝ))).mp tendt ε epos with ⟨l2,_,ieq⟩
      simp at ieq; exact ⟨l2, fun k kgt ↦ (ieq k (le_of_lt kgt))⟩
    have active (n:ℕ) (ngt0 : n>0) : alg.z n ∈ active_domain alg.ψ := by
      simp [active_domain]
      push_neg
      rcases Ψ_subdiff_bound γ hγ ck dk with ⟨_,_,ex⟩
      rcases ex (n-1) with ⟨ d,din,_⟩
      have : d ∈ subdifferential alg.ψ (alg.z n) := by
        apply subdifferential_subset
        rw [Nat.sub_add_cancel ngt0] at din; exact din
      apply Set.nonempty_of_mem this
    have wklpt : ∀ z0 ∈ (limit_set alg.z), KL_point alg.ψ z0 := by
      rintro z0 z0in; apply hψ
      simp [active_domain]
      intro empt
      have : (0 : WithLp 2 (E × F)) ∈ subdifferential alg.ψ z0 := (limitset_property_1 γ hγ ck dk bd lbdψ).2 z0in
      rw [empt] at this; exact this
    have cons : is_constant_on alg.ψ (limit_set alg.z):= by
      simp [is_constant_on]
      intro x xin y yin
      rcases limitset_property_4 γ hγ  ck dk bd lbdψ with ⟨C,heq⟩
      rw [heq x xin,heq y yin]
    have kl: ∃ ε ∈ Set.Ioi (0 : ℝ), ∃ η ∈  Set.Ioi (0 : ℝ), ∃ φ ∈ special_concave η, ∃ LL, ∀ n > LL,
        (alg.ψ z_ < alg.ψ (alg.z n) ∧ alg.ψ (alg.z n) < alg.ψ z_ + η) ∧ deriv φ (alg.ψ (alg.z n)
        - alg.ψ z_) * (EMetric.infEdist 0 (subdifferential alg.ψ (alg.z n))).toReal ≥ 1 := by
      rcases uniformly_KL_property (limitset_property_3 γ hγ ck dk bd lbdψ).1 wklpt cons
        with ⟨ε, eppos, η, etpos, φ, hφ, pro⟩
      rcases L1 η etpos with ⟨l1,lem1⟩
      rcases L2 ε eppos with ⟨l2,lem2⟩
      refine' ⟨ε,eppos,η,etpos,φ,hφ,max l1 l2,_⟩
      intro n ngt
      constructor
      · apply lem1 n (le_of_lt (lt_of_le_of_lt (le_max_left l1 l2) ngt))
      apply pro z_ z_in
      simp; constructor
      apply lem2
      apply lt_of_le_of_lt (le_max_right l1 l2) ngt
      constructor
      · exact ⟨active n (Nat.zero_lt_of_lt ngt), (lem1 n (le_of_lt
          (lt_of_le_of_lt (le_max_left l1 l2) ngt))).1⟩
      exact ⟨active n (Nat.zero_lt_of_lt ngt), (lem1 n (le_of_lt (lt_of_le_of_lt
        (le_max_left l1 l2) ngt))).2⟩
    rcases kl with ⟨ε,eppos,η,etpos,φ,hφ,LL,ieq⟩
    -- The rest of proof after using KL property
    let a := fun n ↦ φ (alg.ψ (alg.z (n + LL + 1)) - alg.ψ z_)
    let b := fun n ↦ alg.ψ (alg.z (n + LL + 1)) - alg.ψ (alg.z (n + 1 + LL + 1))
    let c := fun n ↦ ‖alg.z (n + LL + 1) - alg.z (n + LL)‖
    let d := fun n ↦ deriv φ (alg.ψ (alg.z (n + LL + 1)) - alg.ψ z_)
    let sum := fun n ↦ ∑ k ∈ Finset.range n, ‖alg.z (k + 1) - alg.z k‖
    have hlin n : alg.ψ (alg.z (n + LL + 1)) - alg.ψ z_ ∈ Ioo 0 η := by
      specialize ieq (n + LL + 1) (by linarith)
      obtain ⟨⟨h1, h2⟩, _⟩ := ieq
      constructor <;> linarith
    have hlin' n := Ioo_subset_Ico_self (hlin n)
    obtain ⟨ρ, ρpos, hsgub⟩ := Ψ_subdiff_bound γ hγ ck dk
    let C := ρ / (ρ1 / 2)
    have hnnegC : 0 ≤ C := div_nonneg (le_of_lt ρpos) (by linarith)
    have hposa n : 0 < a n := by
      obtain ⟨_, h2, _, _, _, _⟩ := hφ
      exact h2 _ (hlin' n)
    have hbd n : 2 * c (n + 1) ≤ c n + C * ((a n) - a (n + 1)) := by
      have hpc : d n * b n ≤ (a n) - a (n + 1) := by
        obtain hderiv := concave_deriv_bound hφ (hlin n) (hlin (n + 1))
        rw [sub_sub] at hderiv
        simp only [add_sub_cancel, ge_iff_le] at hderiv
        assumption
      have hposd : d n > 0 := by
        obtain ⟨_, _, _, _, _, h6⟩ := hφ
        exact h6 _ (hlin n)
      have hbd2 : 1 ≤ ρ * (c n) * d n := by
        obtain ⟨dpsi, hdp, hub⟩ := hsgub (n + LL)
        obtain hdp := subdifferential_subset _ _ hdp
        have := infEdist_bound _ hdp
        calc
          _ ≥ ‖dpsi‖ * d n := (mul_le_mul_iff_of_pos_right hposd).mpr hub
          _ ≥ (EMetric.infEdist 0 (subdifferential ψ (z (n + LL + 1)))).toReal * d n :=
              (mul_le_mul_iff_of_pos_right hposd).mpr this
          _ ≥ 1 := by rw [mul_comm]; exact (ieq (n + LL + 1) (by linarith)).2
      have hsd : ρ1 / 2 * (c (n + 1)) ^ 2 ≤ b n := by
        obtain h := suff_des.2 (n + LL + 1)
        rw [add_right_comm n LL 1] at h
        nth_rw 3 [add_right_comm n 1 LL] at h; exact h
      have hsd' : (c (n + 1)) ^ 2 ≤ b n / (ρ1 / 2) := by rwa [le_div_iff']; linarith
      have hnnegc : 0 ≤ c (n + 1) ^ 2 := sq_nonneg _
      have hnnegb' : 0 ≤ b n / (ρ1 / 2) := le_trans hnnegc hsd'
      have hposhp : 0 < (ρ1 / 2) := by linarith
      have hnnegb : 0 ≤ b n := calc
        0 ≤ b n / (ρ1 / 2) * (ρ1 / 2) := (mul_nonneg_iff_of_pos_right hposhp).mpr hnnegb'
        _ = b n := div_mul_cancel₀ _ (by linarith)
      have hnnega' : 0 ≤ (a n - a (n + 1)) :=
          le_trans ((mul_nonneg_iff_of_pos_left hposd).mpr hnnegb) hpc
      have hnnegc' : 0 ≤ C * (c n) := mul_nonneg hnnegC (norm_nonneg _)
      have hbd : (c (n + 1)) ^ 2 ≤ C * (c n) * ((a n) - a (n + 1)) := calc
        c (n + 1) ^ 2 ≤ b n / (ρ1 / 2) := hsd'
        _ ≤ b n / (ρ1 / 2) * (ρ * (c n) * d n) := le_mul_of_one_le_right hnnegb' hbd2
        _ = C * (c n) * (d n * b n) := by ring
        _ ≤ C * (c n) * ((a n) - a (n + 1)) := mul_le_mul_of_nonneg_left hpc hnnegc'
      apply sq_le_mul_le_mean
      rwa [← mul_assoc, mul_comm _ C]
      exact add_nonneg (norm_nonneg _) (mul_nonneg hnnegC hnnega')
    have hbd' n : (Finset.range (n + 1)).sum c ≤ 2 * c 0 + C * a 0 := by
      have hsum n : (Finset.range (n + 1)).sum c ≤ 2 * c 0 - c n + C * (a 0 - a n) := by
        induction' n with i h
        · simp; linarith
        · have : (Finset.range (i + 1 + 1)).sum c = (Finset.range (i + 1)).sum c + c (i + 1) :=
            Finset.sum_range_succ _ (i + 1)
          linarith [hbd i]
      have : 0 ≤ c n := norm_nonneg _
      linarith [mul_nonneg hnnegC (le_of_lt (hposa n)), hsum n]
    have hs n : sum n ≤ sum LL + (Finset.range (n + 1)).sum c := by
      have hs n : sum (n + 1) = sum n + ‖alg.z (n + 1) - alg.z n‖ :=
          Finset.sum_range_succ (fun k ↦ ‖alg.z (k + 1) - alg.z k‖) n
      have hc n : sum (n + LL + 1) = sum (n + LL) + c n := hs (n + LL)
      have : sum LL + (Finset.range (n + 1)).sum c = sum (n + LL + 1) := by
        induction' n with i hn
        · rw [hc 0]; simp
        · rw [Finset.sum_range_succ c (i + 1), hc (i + 1), add_right_comm, ← hn]; ring
      rw [this]
      have hspos n k : sum n ≤ sum (n + k) := by
        induction' k with i hk
        · rw [add_zero]
        · rw [← add_assoc, hs (n + i)]
          exact le_add_of_le_of_nonneg hk (norm_nonneg _)
      rw [add_assoc]
      exact hspos _ _
    use sum LL + 2 * c 0 + C * a 0
    show ∀ n, sum n ≤ sum LL + 2 * c 0 + C * a 0
    intro n
    linarith [hs n, hbd' n]
  · push_neg at h
    rcases h with ⟨n,eq⟩
    let N := α n
    have eq0 : ∀ i ≥ N, alg.z (i + 1) = alg.z i := by
      intro i ige
      have : ∀ k ≥ N, alg.ψ (alg.z k) = alg.ψ z_:= by
        intro k kge
        apply le_antisymm
        calc
          alg.ψ (alg.z k) = alg.ψ (alg.z (N+(k-N))) :=by
            congr; exact Eq.symm (Nat.add_sub_of_le kge)
          _ ≤ alg.ψ (alg.z N) := by apply monopsi
          _ ≤ alg.ψ (z_) := eq
        by_contra con; push_neg at con
        rcases final k with ⟨w,kleaw⟩
        have : alg.ψ z_≤ alg.ψ (alg.z k) := by
          apply le_of_tendsto psiconv
          apply atTop_basis.eventually_iff.mpr
          refine' ⟨w, trivial, _⟩
          intro x wlex
          have : k ≤ α x := by
            have : α w ≤ α x := by
              by_cases ass : w=x
              · rw [ass]
              exact Nat.le_of_succ_le (monoa (Nat.lt_of_le_of_ne wlex ass))
            linarith
          calc
            _ = alg.ψ (alg.z (k + (α x - k))) := by
              congr; exact Eq.symm (Nat.add_sub_of_le this)
            _ ≤ alg.ψ (alg.z k) := by apply monopsi
        linarith
      have : ‖alg.z (i + 1) - alg.z i‖ = 0:= by
        have : ρ1 / 2 * ‖alg.z (i + 1) - alg.z i‖ ^ 2 ≤ 0:= by
          calc
            _ ≤ alg.ψ (alg.z i) -alg.ψ (alg.z (i + 1)) := suff_des.2 i
            _ = 0 := by simp [this i ige,this (i+1) (Nat.le_add_right_of_le ige)]
        apply sq_eq_zero_iff.mp (le_antisymm (nonpos_of_mul_nonpos_right this
          (half_pos ρ1pos)) (sq_nonneg _))
      have : dist (alg.z (i + 1)) (alg.z i) = 0 := by rw [NormedAddCommGroup.dist_eq, this]
      apply dist_eq_zero.mp this
    use ∑ k in Finset.range N, ‖alg.z (k + 1) - alg.z k‖
    intro n
    by_cases nlen : n ≤ N
    · refine Finset.sum_le_sum_of_subset_of_nonneg (GCongr.finset_range_subset_of_le nlen) ?_
      exact fun a _ _ ↦norm_nonneg (alg.z (a + 1) - alg.z a)
    · push_neg at nlen
      have eq0 : ∑ i in (Finset.range n \ Finset.range N), ‖alg.z (i + 1) - alg.z i‖ = 0 := by
        apply Finset.sum_eq_zero
        rintro x xin; simp at xin
        refine norm_sub_eq_zero_iff.mpr (eq0 x xin.2)
      have epty : (Finset.range N \ Finset.range n) = ∅ :=
        Finset.sdiff_eq_empty_iff_subset.mpr (GCongr.finset_range_subset_of_le (Nat.le_of_succ_le nlen))
      refine Finset.sum_sdiff_le_sum_sdiff.mp ?_
      rw [eq0, epty]
      exact Preorder.le_refl 0

theorem Convergence_to_critpt (bd : Bornology.IsBounded (alg.z '' univ)) (hψ : KL_function alg.ψ) (lbdψ : BddBelow (alg.ψ '' univ)):
    ∃z_ : (WithLp 2 (E × F)), z_ ∈ (critial_point alg.ψ) ∧ Tendsto alg.z atTop (𝓝 z_):= by
  have : ∃ z_, Tendsto alg.z atTop (𝓝 z_) := by
    apply cauchySeq_tendsto_of_complete
    apply cauchySeq_of_summable_dist
    rcases Limited_length γ hγ ck dk bd hψ lbdψ with ⟨M,sumle⟩
    apply @summable_of_sum_range_le _ M _ _
    intro n; simp; exact dist_nonneg
    intro n
    calc
      _ = ∑ k ∈ Finset.range n, ‖alg.z (k + 1) - alg.z k‖ :=
         Finset.sum_congr rfl fun x _ ↦ (dist_eq_norm' (alg.z x) (alg.z x.succ))
      _ ≤ M := sumle n
  rcases this with ⟨z_,hzz⟩
  refine' ⟨z_, _, hzz⟩
  have z_in : z_∈limit_set alg.z := by
    simp [limit_set,MapClusterPt]
    exact ClusterPt.of_le_nhds hzz
  apply (limitset_property_1 γ hγ ck dk bd lbdψ).2 z_in

end Limited_length
