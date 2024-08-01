import Convex.Function.Proximal
import Mathlib.Topology.Instances.EReal
import Convex.ADMM.Real_liminf
noncomputable section

open Set InnerProductSpace Topology Filter Real_liminf

-- The image of the subgradient is closed
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (f : E → ℝ )(x' : E)( g' : E)
variable (x : ℕ → E )(x_converge: Tendsto x atTop (𝓝 x'))
variable (g : ℕ → E )(g_converge : Tendsto g atTop (𝓝 g'))
variable (lscf: LowerSemicontinuous f)(cf : ConvexOn ℝ univ f)
variable (nonempty :  ∀ n ,(g n) ∈ SubderivAt f (x n))

variable (y : E )
lemma inequ₁ : ∀ n , f y ≥ f (x n) +  ⟪ g n , y - x n⟫_ℝ :=by
  intro n
  exact nonempty n y

lemma inequ₃2': Tendsto (fun n => ⟪ g n , y - x n⟫_ℝ) atTop (𝓝 ⟪ g' , y - x'⟫_ℝ) := by
  apply Tendsto.inner g_converge
  apply Tendsto.const_sub
  exact x_converge

lemma fx_BddAbove_tendsto: Tendsto (fun n => (f y) - ⟪ g n , y - x n⟫_ℝ)
atTop (𝓝 ( (f y) - ⟪ g' , y - x'⟫_ℝ)) := by
  apply Tendsto.const_sub
  apply inequ₃2' x' g' x x_converge g g_converge

lemma fx_BddAbove': BddAbove (range  (fun n => (f y) - ⟪ g n , y - x n⟫_ℝ)) := by
  apply Tendsto.bddAbove_range
  apply fx_BddAbove_tendsto f x' g' x x_converge g g_converge y

lemma fx_BddAbove'': ∀ (a : ℕ), (f ∘ x) a ≤ f y - ⟪g a, y - x a⟫_ℝ :=by
  intro n
  have := inequ₁ f x g nonempty y n
  simp only [Function.comp_apply, ge_iff_le]
  linarith [this]

lemma fx_BddAbove: BddAbove (range (f ∘ x)) := by
  apply BddAbove.range_mono (fun n => (f y) - ⟪ g n , y - x n⟫_ℝ)
  apply fx_BddAbove''
  exact nonempty
  apply fx_BddAbove' f x' g' x x_converge g g_converge y

@[simp]
def fx : real_liminf := comp_real_liminf f lscf x' x x_converge
  (fx_BddAbove f x' g' x x_converge g g_converge nonempty y)


def gy : real_liminf := tendsto_real_liminf ( ⟪ g' , y - x'⟫_ℝ) (fun n => ⟪ g n , y - x n⟫_ℝ)
(inequ₃2' x' g' x x_converge g g_converge y)

local notation "F" => fx f x' g' x x_converge g g_converge lscf nonempty y
local notation "G" => gy x' g' x x_converge g g_converge y

lemma hax' : (F).x = f ∘ x := rfl

lemma hax :  BddAbove (range (F).x) :=by
  rw[hax']
  apply fx_BddAbove f x' g' x x_converge g g_converge nonempty y

lemma hag' : (G).x = (fun n => ⟪ g n , y - x n⟫_ℝ) := rfl

lemma hag :  BddAbove (range (G).x) :=by
  rw[hag']
  apply Tendsto.bddAbove_range (inequ₃2' x' g' x x_converge g g_converge y)

local notation "hxa" => hax f x' g' x x_converge g g_converge lscf nonempty y
local notation "hga" => hag x' g' x x_converge g g_converge y

lemma inequ₂' : lim_inf (const_real_liminf (f y)) ≥ lim_inf (add_real_liminf F G hxa hga)
:= by
  apply ge_of_liminf
  apply inequ₁
  exact nonempty

lemma inequ₂'' : lim_inf (const_real_liminf (f y)) =  f y := by apply liminf_const_eq

lemma inequ₂ : f y ≥
lim_inf (add_real_liminf F G hxa hga) := by
  rw[← inequ₂'' f y];
  exact inequ₂' f x' g' x x_converge g g_converge lscf nonempty y;

lemma inequ₃1 : lim_inf (F) ≥ f x' := by
  apply le_liminf_of_lowerSemicontinuous f lscf x' x x_converge

lemma inequ₃2 : lim_inf (G) = ⟪ g' , y - x'⟫_ℝ := by
  apply Real_liminf.liminf_eq

lemma inequ₃3 : lim_inf (F) + lim_inf (G) ≥  f x' + ⟪ g' , y - x'⟫_ℝ := by
  rw[inequ₃2 x' g' x x_converge g g_converge y];simp only [ge_iff_le, add_le_add_iff_right];
  apply inequ₃1

lemma inequ₃3':  lim_inf (G) ≥ ⟪ g' , y - x'⟫_ℝ :=by
  rw[inequ₃2 x' g' x x_converge g g_converge y];

lemma inequ₃''': lim_inf (add_real_liminf F G hxa hga)
≥ lim_inf (F)  + lim_inf (G) := by
  apply Real_liminf.add_liminf_ge_liminf_add

lemma inequ₃ : lim_inf (add_real_liminf F G hxa hga)
≥ f x' + ⟪ g' , y - x'⟫_ℝ :=by
  calc lim_inf (add_real_liminf F G hxa hga)
    _≥ lim_inf (F)  + lim_inf (G) := inequ₃''' f x' g' x x_converge g g_converge lscf  nonempty y
    _≥ f x' + ⟪ g' , y - x'⟫_ℝ := inequ₃3 f x' g' x x_converge g g_converge lscf  nonempty y

lemma inequ₄ : f y ≥  f x' + ⟪ g' , y - x'⟫_ℝ := by
  simp
  apply le_trans (inequ₃ f x' g' x x_converge g g_converge lscf  nonempty  y)
    (inequ₂ f x' g' x x_converge g g_converge lscf nonempty y)

-- 参考书P64 定理2.19
theorem Image_subgradient_closed : g' ∈ SubderivAt f x' :=by
  intro y
  exact (inequ₄ f x' g' x x_converge g g_converge lscf nonempty y)
