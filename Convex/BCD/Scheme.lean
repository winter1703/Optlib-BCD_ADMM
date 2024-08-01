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
variable {H : E × F → ℝ} {x : E} {y : F}

open Set Bornology Filter BigOperators Topology

/- The gradient of the first component -/
def grad_fst (H : E × F → ℝ) (y : F) : E → E := gradient (fun t ↦ H (t, y))

/- The gradient function of the second component -/
def grad_fun_fst (H : E × F → ℝ) := fun (x, y) ↦ (grad_fst H y x)

/- The gradient of the second component -/
def grad_snd (H : E × F → ℝ) (x : E) : F → F := gradient (fun t ↦ H (x, t))

/- The gradient function of the second component -/
def grad_fun_snd (H : E × F → ℝ) := fun (x, y) ↦ (grad_snd H x y)

/- The gradient of the prod domain -/
def grad_comp (H : E × F → ℝ) (x : E) (y : F) : E × F := (grad_fst H y x, grad_snd H x y)

/- The gradient function of the prod domain -/
def grad_fun_comp (H : E × F → ℝ) := fun (x, y) ↦ (grad_comp H x y)

theorem diff_prod₁ (h : Differentiable ℝ H) (y : F) :
    Differentiable ℝ (fun z ↦ H (z, y)) := by
  apply Differentiable.comp h
  exact Differentiable.prod differentiable_id' (differentiable_const y)

theorem diff_prod₂ (h : Differentiable ℝ H) (x : E) :
    Differentiable ℝ (fun z ↦ H (x, z)) := by
  apply Differentiable.comp h
  exact Differentiable.prod (differentiable_const x) differentiable_id'

end

noncomputable section

open Set Bornology Filter BigOperators Topology

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [ProperSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [ProperSpace F]
variable {f : E → ℝ} {g : F → ℝ}
variable {H : E × F → ℝ} {x0 : E} {y0 : F} {l : NNReal}

instance Proper_Prod : ProperSpace (WithLp 2 (E × F)) where
  isCompact_closedBall := by
    rintro z0 r
    apply IsSeqCompact.isCompact
    rintro z zin
    have in1 : ∀ n, (z n).1 ∈ Metric.closedBall z0.1 r := by
      intro n
      have : ‖(z n).1 - z0.1‖ ≤ ‖z n - z0‖ := by
        rw [WithLp.prod_norm_eq_of_L2]
        refine (Real.le_sqrt (norm_nonneg _) (Left.add_nonneg (sq_nonneg _) (sq_nonneg _))).mpr
          (le_add_of_nonneg_right (sq_nonneg _))
      simp only [mem_closedBall_iff_norm]
      linarith [mem_closedBall_iff_norm.mp (zin n)]
    have in2 : ∀ n :ℕ, (z n).2 ∈ Metric.closedBall z0.2 r:= by
      intro n
      have : ‖(z n).2 - z0.2‖ ≤ ‖z n - z0‖:= by
        rw [WithLp.prod_norm_eq_of_L2]
        refine (Real.le_sqrt (norm_nonneg _) (Left.add_nonneg (sq_nonneg _) (sq_nonneg _))).mpr
          (le_add_of_nonneg_left (sq_nonneg _))
      simp only [mem_closedBall_iff_norm]
      linarith [mem_closedBall_iff_norm.mp (zin n)]
    obtain sub1 := ((isCompact_closedBall z0.1 r).isSeqCompact).subseq_of_frequently_in
      (frequently_of_forall in1)
    rcases sub1 with ⟨a, _, φ1, h1⟩
    obtain _ : ∀ ε >0, ∀ᶠ n in atTop, (z (φ1 n)).1 ∈ Metric.ball a ε :=
      Filter.Tendsto.basis_right h1.2 Metric.nhds_basis_ball
    obtain sub2 := ((isCompact_closedBall z0.2 r).isSeqCompact).subseq_of_frequently_in
      (frequently_of_forall fun x ↦ in2 (φ1 x))
    rcases sub2 with ⟨b, _, φ2, h2⟩
    obtain eve2 := Filter.Tendsto.basis_right h2.2 Metric.nhds_basis_ball
    have eve1 : ∀ ε > 0, ∀ᶠ n in atTop, (z (φ1 (φ2 n))).1 ∈ Metric.ball a ε:= by
      have : Tendsto ((fun n ↦ (z (φ1 n)).1) ∘ φ2) atTop (𝓝 a) := by
        obtain mono2 := StrictMono.tendsto_atTop h2.1
        calc
          _ ≤ map (fun n ↦ (z (φ1 n)).1) atTop := by
            rw [← Filter.map_map]; apply map_mono mono2
          _ ≤ (𝓝 a) := by exact h1.2
      apply Filter.Tendsto.basis_right this Metric.nhds_basis_ball
    have tend : Tendsto (z ∘ φ1 ∘ φ2) atTop (𝓝 (a, b)):= by
      apply (@Metric.nhds_basis_ball _ _ (a,b)).tendsto_right_iff.mpr
      intro ε epos
      have hR : ∀ n, (z (φ1 (φ2 n))).2 ∈ Metric.ball b (ε / 2) ∧ (z (φ1 (φ2 n))).1 ∈
          Metric.ball a (ε / 2) → (z ∘ φ1 ∘ φ2) n ∈ Metric.ball (a, b) ε := by
        rintro n ⟨ieq2,ieq1⟩
        refine mem_ball_iff_norm'.mpr ?intro.a
        calc
          _ ≤ ε / 2 := by
            refine norm_prod_le_iff.mpr ?_; simp
            exact ⟨le_of_lt (mem_ball_iff_norm'.mp ieq1),le_of_lt (mem_ball_iff_norm'.mp ieq2)⟩
          _< ε := div_two_lt_of_pos epos
      apply Filter.Eventually.mono _ hR
      apply Eventually.and (eve2 (ε / 2) (half_pos epos)) (eve1 (ε / 2) (half_pos epos))
    refine' ⟨(a, b), _, φ1 ∘ φ2, _, _⟩
    · apply (@Metric.isClosed_ball _ _ z0 r).mem_of_tendsto tend
        (eventually_of_forall fun x ↦ zin ((φ1 ∘ φ2) x))
    · exact fun x y xlty ↦  h1.1 (h2.1 xlty)
    · exact tend

/-
  Assumption: f and g are lower semicontinuous, H is continuously differentiable
  ∇ H is l- Lipschitz continuous, f and g are lower bounded
-/
class ProblemData (f : E → ℝ) (g : F → ℝ) (H : E × F → ℝ) (l : NNReal) : Prop where
  lbdf : BddBelow (f '' univ)
  lbdg : BddBelow (g '' univ)
  hf : LowerSemicontinuous f
  hg : LowerSemicontinuous g
  conf : ContDiff ℝ 1 H
  lpos : l > (0 : ℝ)
  lip : LipschitzWith l (grad_fun_comp H)

/-
  The definition of block coordinate descent
-/
structure BCD (f : E → ℝ) (g : F → ℝ) (H : E × F → ℝ) (l : NNReal)
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

/- Define the A^k_x -/
def BCD.A_kx {self : BCD f g H l x0 y0} : ℕ → E :=
  fun k => (1/(self.c k)) •
  (self.x k - self.x (k + 1)) - (grad_fst H (self.y k) (self.x k))

/- Define the A^k_y -/
def BCD.A_ky {self : BCD f g H l x0 y0} : ℕ → F :=
  fun k => (1/(self.c k)) • (self.y k - self.y (k + 1)) - (grad_snd H  (self.x (k + 1)) (self.y k))

-- The lemma used in the first-order condition
-- bcd.f_k has Gradient x according to semicontinuous,
def BCD.f' {self : BCD f g H l x0 y0} (k : ℕ) : E → E :=
  fun u => grad_fst H (self.y k) u

def BCD.g' {self : BCD f g H l x0 y0} (k : ℕ) : F → F :=
  fun u => grad_snd H (self.x (k + 1)) u

def BCD.fprop' {self : BCD f g H l x0 y0} (k : ℕ) : E → E :=
  (fun u ↦ (self.c k • grad_fst H (self.y k) u) +
    (u - (self.x k - self.c k • grad_fst H (self.y k) (self.x k))))

-- The prop form of f will induced a function fprop
def BCD.fprop {self : BCD f g H l x0 y0} (k : ℕ) : E → ℝ :=
  (fun u ↦ (self.c k • f) u + ‖u - (self.x k -
    self.c k • grad_fst H (self.y k) (self.x k))‖ ^ 2 / 2)

def BCD.gprop {self : BCD f g H l x0 y0} (k : ℕ) :=
  (fun u ↦ (self.d k • g) u + ‖u - (self.y k -
    self.c k • grad_snd H (self.x (k + 1)) (self.y k))‖ ^ 2 / 2)

variable {alg : BCD f g H l x0 y0} (γ : ℝ) (hγ : γ > 1)

variable (ck: ∀ k, alg.c k = 1 / (γ * l)) (dk: ∀ k, alg.d k = 1 / (γ * l))

section Assumption

def addElementToSet (A : Set E) (x : E) : Set E := {a + x | a ∈ A}

lemma norm_prod' (x : E) (y : F) : ‖(x, y)‖ = max ‖x‖ ‖y‖ := rfl

lemma comp_norm_le (x : E) (y : F) : (‖x‖ ≤ ‖(x,y)‖) ∧ (‖y‖ ≤ ‖(x,y)‖) :=
  ⟨le_max_left ‖x‖ ‖y‖, le_max_right ‖x‖ ‖y‖⟩

lemma norm_prod_right_zero (x : E) : ‖(x, (0 : F))‖ = ‖x‖ := by
  rw [norm_prod']
  rw [norm_zero]; apply le_antisymm
  apply max_le_iff.2
  constructor; norm_num
  exact norm_nonneg x
  apply le_max_iff.2
  left; norm_num

lemma norm_prod_left_zero (y : F): ‖((0 : E), y)‖ = ‖y‖ := by
  rw [norm_prod']
  rw [norm_zero]; apply le_antisymm
  apply max_le_iff.2
  constructor; exact norm_nonneg y
  norm_num
  apply le_max_iff.2
  right; norm_num

lemma stepsize_c_lq_zero : ∀ k, 0 < (alg.c k) := by
  intro k
  specialize ck k; rw [ck]
  apply div_pos; norm_num
  apply mul_pos; linarith[hγ]; apply alg.lpos

lemma stepsize_d_lq_zero : ∀ k, 0 < (alg.d k) := by
  intro k
  specialize dk k; rw [dk]
  apply div_pos; norm_num
  apply mul_pos; linarith[hγ]; apply alg.lpos

/- coordinate Lipschitz continuous -/
theorem ass_coordinate_lip : (∀ y, LipschitzWith l (grad_fst H y))
    ∧ (∀ x, LipschitzWith l (grad_snd H x)) := by
  obtain lip : LipschitzWith l (grad_fun_comp H) := alg.lip
  rw [lipschitzWith_iff_norm_sub_le] at lip
  constructor
  intro y
  rw [lipschitzWith_iff_norm_sub_le]
  intro x1 x2
  specialize lip (x1,y) (x2,y)
  simp [grad_fun_comp,grad_comp] at lip
  apply le_trans ((comp_norm_le _ _).left) at lip
  rw [norm_prod_right_zero] at lip
  exact lip
  intro x
  rw [lipschitzWith_iff_norm_sub_le]
  intro y1 y2
  specialize lip (x, y1) (x, y2)
  simp [grad_fun_comp,grad_comp] at lip
  apply le_trans (comp_norm_le _ _).right at lip
  rw [norm_prod_left_zero] at lip
  exact lip

/- the composition of the subdifferential -/
theorem ass_comp_subdiff : ∀ (x : E) (y : F),
  subdifferential alg.ψ (x,y) = (addElementToSet (subdifferential f x) (grad_fun_fst H (x,y))
                                × addElementToSet (subdifferential g y) (grad_fun_snd H (x,y))) := by
  sorry

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
  obtain Hass := @ass_coordinate_lip E F _ _ _ _ _ _ f g H x0 y0 l alg
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
          apply diff_prod₁; apply ContDiff.differentiable alg.conf (by rfl)
        have cpos : 0 < (alg.c k) := stepsize_c_lq_zero γ hγ ck k
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
            apply diff_prod₂; apply ContDiff.differentiable alg.conf (by rfl)
          have dpos : 0 < (alg.d k) := stepsize_d_lq_zero γ hγ dk k
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

lemma f_hasDeriv (k : ℕ) : ∀ (x : E), HasGradientAt f ((fun x => grad_fst H (alg.y k) x) x) x := by
  sorry

theorem rw_fprop (k : ℕ) : alg.fprop k = (fun u ↦ (alg.c k • f) u +
  ‖u - (alg.x k - alg.c k • grad_fst H (alg.y k) (alg.x k))‖^2 / 2) := by rfl

theorem fprop_HasGradient (k : ℕ) : ∀ (x : E), HasGradientAt (alg.fprop k) (alg.fprop' k x) x := by
  intro x
  sorry

theorem fprop_Continuous (k : ℕ) : ContinuousOn (alg.fprop' k) univ := by
  sorry

lemma fprop'_eq_zero_at_xk (k : ℕ) : (alg.fprop' k) (alg.x (k + 1)) = 0:= by
  obtain propx := (alg.s₁ k)
  rw [prox_prop, ← rw_fprop k] at propx
  apply first_order_unconstrained (fprop_HasGradient k) (by trivial)
  apply fprop_Continuous

lemma g_hasGradient_at_yk (k : ℕ) : ∀ (y : F), HasGradientAt g (alg.g' k y) y := by
  sorry

lemma g'_eq_zero_at_xk (k : ℕ) : ∀ (y : F), alg.g' k y = 0 := by
  sorry

-- The prop 1 in Lec6.p18
theorem A_ks_both_are_subdiff (k : ℕ) :
    (alg.A_kx k ∈ f_subdifferential f (alg.x k)) ∧ (alg.A_ky k ∈ f_subdifferential g (alg.y k)) := by
  -- Rename some long expr
  let xk := (alg.x k)
  have h1: xk = (alg.x k) := by rfl
  rw[← h1]

  let fn := (fun u ↦ (alg.c k • f) u + ‖u - (alg.x k - alg.c k • grad_fst H (alg.y k) (alg.x k))‖^2 / 2)
  have h_fn: fn = (fun u ↦ (alg.c k • f) u + ‖u - (alg.x k - alg.c k • grad_fst H (alg.y k) (alg.x k))‖^2 / 2) := by rfl

  let prox_x := alg.s₁ k
  rw[prox_prop] at prox_x
  rw [← h_fn] at prox_x

  -- Formal Proof
  apply And.intro
  .
    let fn' := (fun (u : E) ↦ (grad_fst H (alg.y k) u + ((1/(alg.c k)) • (u - (alg.x k)))))
    have lem_fn': fn' = (fun (u : E) ↦ (grad_fst H (alg.y k) u + ((1/(alg.c k)) • (u - (alg.x k))))) := by rfl

    have h_fn: ∀ x : E, HasGradientAt fn (fn' x) x := by
      sorry

    have h_fnc : ContinuousOn fn' univ := by
      sorry

    have h_d_0: grad_fst H (alg.y k) (alg.x (k + 1))  + (1 / alg.c k) • ((alg.x (k + 1))  - alg.x k) = 0 := by
      apply first_order_unconstrained h_fn prox_x h_fnc

    have h_ukx: (grad_fst H (alg.y k) (alg.x k)) ∈ f_subdifferential f xk := by
      sorry

    have h_part_x: grad_fst H (alg.y k) (alg.x (k + 1)) + (1 / alg.c k) • (alg.x (k + 1) - alg.x k) ∈ f_subdifferential f xk := by
      sorry

    have h_Akx: ∀ (k : ℕ), alg.A_kx k = grad_fst H (alg.y (k + 1)) (alg.x (k + 1)) + (1 / alg.c k) • (alg.x (k + 1) - alg.x k) - (grad_fst H (alg.y k) (alg.x k)) := by
      intro k
      rw[A_kx]

      sorry

    have rst: alg.A_kx k ∈ f_subdifferential f xk := by
      rw[A_kx]
      sorry

    sorry

  . sorry

theorem A_ky_upper_bound : ∀ k, ‖alg.A_ky k‖ ≤ ((1 / (alg.d k)) + 1) * l * ‖alg.z k - alg.z (k + 1)‖ := by
  sorry

theorem A_ks_uppder_bound : ∀ k, ∃ (γ : ℝ), ‖alg.A_kx k‖ ≤ (2 * γ + 2) * l * ‖alg.z k - alg.z (k + 1)‖ := by
  sorry

theorem Ψ_subdiff_bound : ∃ ρ > 0, ∀ k, ∃ dΨ ∈ f_subdifferential alg.ψ ((alg.x (k + 1), alg.y (k + 1))),
  ‖dΨ‖ ≤ ρ * ‖alg.z (k + 1) - alg.z k‖ := by sorry

end Upperbound_subd

section limit_point

lemma StrictMono_nat (φ : ℕ → ℕ) (hφ: StrictMono φ) : (∀ (n:ℕ), n ≤ (φ n)) := by
    intro n
    induction' n with k hk
    exact Nat.zero_le _
    have : (k + 1) ≤ φ k + 1 := by linarith
    apply le_trans this
    have : φ k + 1 = (φ k).succ := by simp
    rw [this]; apply Nat.succ_le_iff.mpr; apply hφ; simp

lemma limitset_property_1 (bd : Bornology.IsBounded (alg.z '' univ)) :
    (limit_set alg.z).Nonempty ∧ ((limit_set alg.z) ⊆ critial_point alg.ψ) := by
  constructor
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
  --至此，非空证明完毕，下面开始证明更强的结论limit_set BCD.z ⊆ critial_point BCD.ψ
  intro a ha
  have ha': MapClusterPt a atTop alg.z :=ha

  have: ∃ (φ : ℕ → ℕ), StrictMono φ ∧ Filter.Tendsto ((alg.z) ∘ φ) Filter.atTop (nhds a) :=
    TopologicalSpace.FirstCountableTopology.tendsto_subseq ha'
  rcases this with ⟨φ,Monoφ,convergentφ⟩
  have hH := convergentφ
  simp [BCD.z, Function.comp] at hH
  have htendx: Filter.Tendsto (alg.x ∘ φ) Filter.atTop (nhds a.1) := by
    have tendH:= Filter.Tendsto.fst_nhds hH
    have:(∀ n:ℕ ,((WithLp.equiv 2 (E × F)).symm (alg.x (φ n),alg.y (φ n))).1 =(alg.x (φ n), alg.y (φ n)).1):=by
      intro n
      exact WithLp.equiv_symm_fst (alg.x (φ n), alg.y (φ n))
    have:(fun a ↦ ((WithLp.equiv 2 (E × F)).symm (alg.x (φ a), alg.y (φ a))).1) = (fun a => (alg.x (φ a), alg.y (φ a)).1):=by
      ext n
      exact this n
    rw[this] at tendH
    exact tendH
  have htendy: Filter.Tendsto (alg.y ∘ φ) Filter.atTop (nhds a.2) := by
    have tendH:= Filter.Tendsto.snd_nhds hH
    have:(∀ n:ℕ ,((WithLp.equiv 2 (E × F)).symm (alg.x (φ n),alg.y (φ n))).2 =(alg.x (φ n), alg.y (φ n)).2):=by
      intro n
      exact WithLp.equiv_symm_snd (alg.x (φ n), alg.y (φ n))
    have:(fun a ↦ ((WithLp.equiv 2 (E × F)).symm (alg.x (φ a), alg.y (φ a))).2) = (fun a => (alg.x (φ a), alg.y (φ a)).2):=by
      ext n
      exact this n
    rw[this] at tendH
    exact tendH
  have lower_x: f (a.1) ≤ Filter.liminf (f ∘ (alg.x ∘ φ)) Filter.atTop := by
    have key : Filter.liminf (f ∘ (alg.x ∘ φ)) Filter.atTop = Filter.liminf f (Filter.map (alg.x ∘ φ) Filter.atTop):=
      Filter.liminf_comp _ _ _
    --利用适当函数性质，去证这个(f ∘ (alg.x ∘ φ))必将大于f (a.1)，因为(alg.x ∘ φ)收敛到a.1
    sorry
  have lower_y: g (a.2) ≤ Filter.liminf (g ∘ (alg.y ∘ φ)) Filter.atTop := by
    --同样利用适当函数的性质，这个过程是同上的
    sorry
  --上面主要是证明左不等号，拿x来说就是f (a.1) ≤ Filter.liminf (f ∘ (alg.x ∘ φ)) Filter.atTop
  --下面需要证明反不等号也即是Filter.liminf (f ∘ (alg.x ∘ φ)) Filter.atTop≤f (a.1)
  --这样可以得到等号，即可完成证明

  --下面这个不等式主要利用x的迭代公式
  have a_1_le_x :∀ k:ℕ ,((inner (alg.x (k+1)-alg.x k) (grad_fst H (alg.y k) (alg.x k)))+((2/(alg.c k))*(‖alg.x (k+1)-alg.x k‖^2))
      +(f (alg.x (k+1)))≤(inner (a.1-alg.x k) (grad_fst H (alg.y k) (alg.x k)))+((2/(alg.c k))*(‖a.1-alg.x k‖^2))+(f (a.1))) :=
    by
      intro k
      have := alg.s₁
      simp[prox_prop] at this
      specialize this k
      rw[isMinOn_iff] at this
      specialize this a.1
      have a1_univ : a.1 ∈ univ:= trivial
      have:= this a1_univ
      have le_1:(alg.c k * f (alg.x (k + 1)) + ‖alg.x (k + 1) - (alg.x k - alg.c k • grad_fst H (alg.y k) (alg.x k))‖ ^ 2 / 2) /
          alg.c k ≤(alg.c k * f a.1 + ‖a.1 - (alg.x k - alg.c k • grad_fst H (alg.y k) (alg.x k))‖ ^ 2 / 2) / alg.c k:=
        div_le_div_of_nonneg_right this (le_of_lt sorry)
      ring_nf at le_1
      rw[mul_comm,<-mul_assoc] at le_1
      ring_nf at le_1
      rw[mul_inv_cancel,one_mul,one_mul] at le_1
      ring
      sorry
      exact (ne_of_gt sorry)
  --下面两个大have利用上面不等式去证明反不等号
  have x_sup_le:Filter.limsup (f ∘ (alg.x ∘ φ)) Filter.atTop ≤ Filter.limsup (fun q =>(inner (a.1-(alg.x ∘ φ) (q-1))
      (grad_fst H ((alg.y∘φ) (q-1)) ((alg.x∘ φ ) (q-1))))+((2/((alg.c ∘ φ) (q-1)))*
      (‖a.1-(alg.x∘φ) (q-1)‖^2))+(f (a.1))) Filter.atTop :=
    by
    have argmin_le_x:∀ q:ℕ ,(inner ((alg.x ∘ φ) q -(alg.x ∘ φ) (q-1)) (grad_fst H ((alg.y ∘ φ) (q-1))
        ((alg.x∘φ) (q-1)))+((2/((alg.c ∘ φ) (q-1)))*(‖((alg.x ∘ φ) (q))-((alg.x∘φ) (q-1))‖^2))+(f ((alg.x ∘ φ) (q)))
        ≤(inner (a.1-(alg.x ∘ φ) (q-1)) (grad_fst H ((alg.y∘φ) (q-1)) ((alg.x∘ φ ) (q-1))))+((2/((alg.c ∘ φ) (q-1)))
        *(‖a.1-(alg.x∘φ) (q-1)‖^2))+(f (a.1)) ):=
      by sorry
    sorry
  have subφ_xconvergent: Tendsto (f ∘ (alg.x ∘ φ)) atTop (nhds (f (a.1))):=
    by
    have sup_x_le:Filter.limsup (f ∘ (alg.x ∘ φ)) Filter.atTop ≤ f (a.1):=
      by sorry
    sorry

  --x的部分已然证明，下面去证明y的部分，这个部分与x是一致对称的
  have a_2_le_y :∀ k:ℕ ,(inner (alg.y (k+1)-alg.y k) (grad_snd H (alg.x k) (alg.y k)))+((2/(alg.d k))*
      (‖alg.y (k+1)-alg.y k‖^2))+(g (alg.y (k+1)))≤(inner (a.2-alg.y k) (grad_snd H (alg.x k) (alg.y k)))
      +((2/(alg.d k))*(‖a.2-alg.y k‖^2))+(g (a.2)) :=
    by
      intro k
      have := alg.s₂
      simp[prox_prop] at this
      specialize this k
      rw[isMinOn_iff] at this
      specialize this a.2
      have a2_univ : a.2 ∈ univ:= trivial
      have:= this a2_univ
      have le_2:(alg.d k * g (alg.y (k + 1)) + ‖alg.y (k + 1) - (alg.y k - alg.d k • grad_snd H
        (alg.x (k+1)) (alg.y k))‖ ^ 2 / 2) /alg.d k ≤(alg.d k * g a.2 + ‖a.2 - (alg.y k - alg.d k •
        grad_snd H (alg.x (k+1)) (alg.y k))‖ ^ 2 / 2) / alg.d k:=div_le_div_of_nonneg_right this (le_of_lt sorry)
      ring_nf at le_2
      rw[mul_comm,<-mul_assoc] at le_2
      ring_nf at le_2
      rw[mul_inv_cancel,one_mul,one_mul] at le_2
      ring_nf
      sorry
      exact (ne_of_gt sorry)
  --这个部分也与x部分一致，定理的名称是对称的
  have y_sup_le:Filter.limsup (g ∘ (alg.y ∘ φ)) Filter.atTop ≤ Filter.limsup (fun q =>(inner (a.2-(alg.y ∘ φ) (q-1))
      (grad_snd H ((alg.x∘φ) (q)) ((alg.y∘ φ ) (q-1))))+((2/((alg.d ∘ φ) (q-1)))
      *(‖a.2-(alg.y∘φ) (q-1)‖^2))+(g (a.2))) Filter.atTop :=
    by
    have argmin_le_y:∀ q:ℕ ,(inner ((alg.y ∘ φ) q -(alg.y ∘ φ) (q-1)) (grad_snd H ((alg.x ∘ φ) q)
        ((alg.y∘φ) (q-1)))+((2/((alg.d ∘ φ) (q-1)))*(‖((alg.y ∘ φ) (q))-((alg.y∘φ) (q-1))‖^2))+
        (g ((alg.y ∘ φ) (q)))≤(inner (a.2-(alg.y ∘ φ) (q-1)) (grad_snd H ((alg.x∘φ) (q)) ((alg.y∘ φ ) (q-1))))
        +((2/((alg.d ∘ φ) (q-1)))*(‖a.2-(alg.y∘φ) (q-1)‖^2))+(g (a.2)) ):=
      by sorry
    sorry
  have subφ_yconvergent: Tendsto (g ∘ (alg.y ∘ φ)) atTop (nhds (g (a.2))):=
    by
    have sup_y_le:Filter.limsup (g ∘ (alg.y ∘ φ)) Filter.atTop ≤ g (a.2):=
      by sorry
    sorry
  --x，y部分都证明完等式之后，直接利用定义去证我们需要的结论
  have zero_in_partial:(0,0)∈ subdifferential alg.ψ (a.1,a.2) :=
    by
    have sub_convergent : Tendsto (fun q => alg.ψ (((alg.x∘ φ) q),((alg.y ∘ φ) q))) Filter.atTop (nhds (alg.ψ ((a.1),(a.2)))) :=
      by sorry
    have A_in_partial: ∀ q:ℕ ,(((alg.A_kx ∘ φ) q),((alg.A_ky ∘ φ) q)) ∈ f_subdifferential alg.ψ ((alg.x ∘ φ) q,(alg.y ∘ φ) q) :=
      by sorry
    have A_convergent: Tendsto (fun q=>(((alg.A_kx ∘ φ) q),((alg.A_ky ∘ φ) q))) Filter.atTop (nhds (0,0)) :=
      by sorry
    sorry
  apply Set.mem_setOf.mpr
  exact zero_in_partial

lemma limitset_property_2 (bd : Bornology.IsBounded (alg.z '' univ)):
    Tendsto (fun n ↦ (EMetric.infEdist (alg.z n) (limit_set alg.z)).toReal) atTop (𝓝 0) := by
  have : ∃ za ∈limit_set alg.z, ∃ (φ : ℕ → ℕ), StrictMono φ ∧ Filter.Tendsto (alg.z ∘ φ) Filter.atTop (nhds za) := by
    unfold limit_set
    --rw[Set.mem_setOf] at za_limit_set
    --have:=TopologicalSpace.FirstCountableTopology.tendsto_subseq za_limit_set
    --rcases this with ⟨φ,⟨StrictMono_φ,Filter.Tendsto_φ⟩⟩
    --use φ
    sorry
  rcases this with ⟨za, za_limit_set, φ, ⟨StrictMono_φ, Filter.Tendsto_φ⟩⟩
  --下面这个have是三角不等式
  have: ∀n:ℕ ,∀q:ℕ,(EMetric.infEdist (alg.z n) (limit_set alg.z)).toReal ≤ (EMetric.infEdist
      ((alg.z ∘ φ) q) (limit_set alg.z)).toReal + (∑ (x ∈ Finset.Icc n q), (fun c =>‖alg.z (c-1)-alg.z c‖) x):=
    by
      sorry
  --下面一个have结论需要使用到充分下降原理，类似cauthy定理那样，去证明邻项也趋于同一个极限，从而完成证明
  have: Tendsto (fun n ↦ (EMetric.infEdist (alg.z n) (limit_set alg.z)).toReal) atTop (𝓝 0) :=
    by sorry
  exact this

lemma limitset_property_3 (bd : Bornology.IsBounded (alg.z '' univ)):
    IsCompact (limit_set alg.z) ∧ IsConnected (limit_set alg.z) := by
  constructor
  let set_le :ℕ -> Set ℕ := (fun k => {x | k≤ x})
  let Z:ℕ -> Set (WithLp 2 (E × F)) := (fun k => closure (⋃ (q∈ (set_le q)),{alg.z q}))
  --下面这个have是关键，正是注意到limit_set alg.z的这种表达形式，才可完成证明
  have: (limit_set alg.z) = (⨅ q ∈ (Set.Ioi 0), Z q) :=
    by sorry
  --每个zk都是紧集
  have compact_zk:∀ k:ℕ,IsCompact (Z k) :=by
    intro k
    apply Metric.isCompact_iff_isClosed_bounded.mpr
    sorry
  --利用代数性质即可证明结论
  have:IsCompact (limit_set alg.z):=by
    sorry
  exact this

  --紧集证明完毕，还需要证明连通，此处利用反证法
  have:IsConnected (limit_set alg.z)<->((limit_set alg.z).Nonempty ∧ IsPreconnected (limit_set alg.z)):= by rfl
  rw[this]
  constructor
  exact (limitset_property_1 (bd)).1
  have : IsPreconnected (limit_set alg.z) =   ∀ (u v : Set (WithLp 2 (E × F))), IsOpen u
      → IsOpen v → (limit_set alg.z) ⊆ u ∪ v → ((limit_set alg.z) ∩ u).Nonempty →
      ((limit_set alg.z) ∩ v).Nonempty → ((limit_set alg.z) ∩ (u ∩ v)).Nonempty:=by rfl
  rw[this]
  --上面都是些准备工作，下面利用反证法去证明结论
  by_contra nonconnect
  push_neg at nonconnect
  rcases nonconnect with ⟨A,B,openA,openB,sub_AB,nez_A,nez_B,nz_AB⟩
  let γ : (E × F) -> ℝ := fun z => ((EMetric.infEdist z A).toReal) /
    ((EMetric.infEdist z A).toReal+(EMetric.infEdist z B).toReal)
  --这里γ是一个距离定义的函数，而距离连续，从而容易知道其连续，正如下面这个have所说的。
  have : Continuous γ := by sorry
  --A,B分别是连续函数γ在0，1下的完全原象
  have A_eq: A = Set.preimage γ ({0}) := by sorry
  have B_eq: B = Set.preimage γ ({1}) := by sorry
  let U : Set (E × F) := {z:(E × F)|(γ z)<(1/4)}
  let V : Set (E × F) := {z:(E × F)|(3/4)<(γ z)}
  --alg.z 终将落到U或者V中
  have U_V_prop:∃ k0:ℕ,∀ k:ℕ, (k0 ≤ k) -> (alg.z k ∈ U) ∨ (alg.z k ∈ V) := by
    by_contra h_contra
    sorry
  rcases U_V_prop with ⟨k0,hk0⟩
  let r : ℕ ->ℝ := fun k => (γ ∘ alg.z) k
  have r_prop:(∀ k:ℕ ,(k0≤k) -> (r k) ∉ (Set.Icc (1/4) (3/4))) ∧ Infinite ({k:ℕ | r k < 1/4})
      ∧ Infinite ({k:ℕ | 3/4 < r k}) ∧ Tendsto (fun k => |r (k+1)-r k|) Filter.atTop (nhds 0) :=
    by sorry
  --下面就可以引入矛盾，因为由于充分下降，zk与zk+1终将无限接近
  --但是上面这个r表明，将会有无限的r k分别小于1/4与大于3/4，这显然矛盾，这正是下面这个sorry的内容
  sorry

lemma limitset_property_4 (bd : Bornology.IsBounded (alg.z '' univ)):
    ∃ (c:ℝ) , ∀ x ∈ (limit_set alg.z) , alg.ψ x = c := by
  --下面这个have主要是充分下降中的定理，其中告诉我们这么个定理
  --alg.ψ必将收敛到一个（局部极小）值
  have decent_ψ:∃ ψ_final, Tendsto (alg.ψ ∘ alg.z) Filter.atTop (nhds ψ_final) :=
    by sorry
  rcases decent_ψ with ⟨ψ_final,hψ⟩
  --我们证明这个收敛到的值正是我们要证的c
  use ψ_final
  intro z_1 hz_1
  --z_1是聚点，自然有下面这个结论
  have z_1_cluster: ∃ (φ : ℕ → ℕ), StrictMono φ ∧ Filter.Tendsto (alg.z ∘ φ) Filter.atTop (nhds z_1) :=
    by sorry
  --利用上面的limitset_property_1'的第二个结论，可知这个聚点必在crit中，即可完成证明
  have :alg.ψ z_1= ψ_final:=
    by sorry
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

theorem tri (z : WithLp 2 (E × F)) : ‖z‖ ≤ ‖z.1‖ + ‖z.2‖:= by
  have : ‖z‖ ^ 2 ≤ (‖z.1‖ + ‖z.2‖) ^ 2:= by
    simp [WithLp.prod_norm_sq_eq_of_L2, add_sq]
    refine mul_nonneg (mul_nonneg ?ha (norm_nonneg _)) (norm_nonneg _)
    norm_num
  apply nonneg_le_nonneg_of_sq_le_sq (Left.add_nonneg (norm_nonneg z.1) (norm_nonneg z.2))
  rw [← pow_two, ← pow_two]
  exact this

theorem Limited_length (bd : Bornology.IsBounded (alg.z '' univ)) (hψ : KL_function alg.ψ):
    ∃ M : ℝ, ∀ n, ∑ k in Finset.range n, ‖alg.z (k + 1) - alg.z k‖ ≤ M := by
  obtain h1 := (IsCompact.isSeqCompact bd.isCompact_closure).subseq_of_frequently_in
    (sorryAx (∃ᶠ (n : ℕ) in atTop, BCD.z n ∈ closure (alg.z '' univ)) true)
  rcases h1 with ⟨z_, z_in, α, ⟨monoa, conv⟩⟩
  rcases Sufficient_Descent1 γ hγ ck dk with ⟨ρ1,ρ1pos,suff_des⟩
  have z_in : z_ ∈ limit_set alg.z:= by
    simp [limit_set, MapClusterPt]
    apply ClusterPt.mono (ClusterPt.of_le_nhds conv)
    calc
      _ = map (fun n ↦ alg.z n) (map α atTop) := by rw [map_map]
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
  have psiconv : Tendsto (fun n ↦ alg.ψ (alg.z (α n))) atTop (𝓝 (alg.ψ z_)):=by
    sorry

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
      rcases limitset_property_2 bd with tendt
      rcases (atTop_basis.tendsto_iff (nhds_basis_abs_sub_lt (0:ℝ))).mp tendt ε epos with ⟨l2,_,ieq⟩
      simp at ieq; exact ⟨l2, fun k kgt ↦ (ieq k (le_of_lt kgt))⟩
    have active (n:ℕ) (ngt0 : n>0) : alg.z n ∈ active_domain alg.ψ := by
      simp [active_domain]
      push_neg
      rcases @Ψ_subdiff_bound E F _ _ _ _ _ _ f g H x0 y0 l alg with ⟨_,_,ex⟩
      rcases ex (n-1) with ⟨ d,din,_⟩
      have : d ∈ subdifferential alg.ψ (alg.z n) := by
        apply subdifferential_subset
        rw [Nat.sub_add_cancel ngt0] at din; exact din
      apply Set.nonempty_of_mem this
    have wklpt : ∀ z0 ∈ (limit_set alg.z), KL_point alg.ψ z0 := by
      rintro z0 z0in; apply hψ
      simp [active_domain]
      intro empt
      have : (0 : WithLp 2 (E × F)) ∈ subdifferential alg.ψ z0 := (limitset_property_1 bd).2 z0in
      rw [empt] at this; exact this
    have cons : is_constant_on alg.ψ (limit_set alg.z):= by
      simp [is_constant_on]
      intro x xin y yin
      rcases limitset_property_4 bd with ⟨C,heq⟩
      rw [heq x xin,heq y yin]
    have kl: ∃ ε ∈ Set.Ioi (0 : ℝ), ∃ η ∈  Set.Ioi (0 : ℝ), ∃ φ ∈ special_concave η, ∃ LL, ∀ n > LL,
        (alg.ψ z_ < alg.ψ (alg.z n) ∧ alg.ψ (alg.z n) < alg.ψ z_ + η) ∧ deriv φ (alg.ψ (alg.z n)
        - alg.ψ z_) * (EMetric.infEdist 0 (subdifferential alg.ψ (alg.z n))).toReal ≥ 1 := by
      rcases uniformly_KL_property (limitset_property_3 bd).1 wklpt cons
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
    obtain ⟨ρ, ρpos, hsgub⟩ := @Ψ_subdiff_bound E F _ _ _ _ _ _ f g H x0 y0 l alg
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
        have : (alg.x (n + LL + 1), alg.y (n + LL + 1)) = (alg.z (n + LL + 1)) := by rfl
        rw [this] at hdp
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

theorem Convergence_to_critpt (bd : Bornology.IsBounded (alg.z '' univ)) (hψ : KL_function alg.ψ) :
    ∃z_ : (WithLp 2 (E × F)), z_ ∈ (critial_point alg.ψ) ∧ Tendsto alg.z atTop (𝓝 z_):= by
  have : ∃ z_, Tendsto alg.z atTop (𝓝 z_) := by
    apply cauchySeq_tendsto_of_complete
    apply cauchySeq_of_summable_dist
    rcases Limited_length γ hγ ck dk bd hψ with ⟨M,sumle⟩
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
  apply (limitset_property_1 bd).2 z_in

end Limited_length
end
