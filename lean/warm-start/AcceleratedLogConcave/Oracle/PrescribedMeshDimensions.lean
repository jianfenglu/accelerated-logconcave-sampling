import AcceleratedLogConcave.Numerics.PrescribedMeshCardinality
import AcceleratedLogConcave.Oracle.RecursiveCallOccurrence

/-! Real-valued cardinality accounting for literal prescribed meshes. Every
mesh equality is explicit; no arbitrary geometry is asserted to satisfy the
node budget. B and the public resolution cap remain separate obligations. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.PrescribedMeshDimensions
open Numerics Numerics.AffineGraph Numerics.GeometricMesh Numerics.PrescribedMeshCardinality
open scoped BigOperators

/-- Exact source count for the prescribed positive-length probability mesh. -/
theorem probability_card (m : ℕ) (a b h₀ : ℝ) (hab : a < b) (hb : b < 1) (hh : 0 < h₀) :
    Fintype.card ((probabilityGeometricInterval a b h₀ hab hb hh).Source m) = cellCount a b h₀*m := by
  rw [IntervalMesh.card_source, probabilityGeometricInterval_cellCount]

theorem kernel_card (m : ℕ) (R h₀ : ℝ) (hR : 0 < R) (hRh : R ≤ 1/2) (hh : 0 < h₀) :
    Fintype.card ((actualKernelInterval R h₀ hR hRh hh).Source m) =
      cellCount 0 (backwardEnd R) h₀*m := by
  rw [IntervalMesh.card_source]
  change (cellCount 0 (backwardEnd R) h₀-1+1)*m = _
  rw [Nat.sub_add_cancel (show 1 ≤ cellCount 0 (backwardEnd R) h₀ from kernel_cellCount_pos hR hRh hh)]

private theorem drop_origin {k : ℕ} {P : ℝ} (h : ((k+1 : ℕ):ℝ) ≤ P) : (k:ℝ) ≤ P := by
  push_cast at h
  linarith

/-- Pure real polynomial estimate. P is exactly 16*m*X, never rounded. -/
theorem polynomial_bound {m X : ℝ} (hm : 1 ≤ m) (hX : 1 ≤ X) :
    1+m+m*(16*m*X)+m*(16*m*X)^2+m^2*(16*m*X)^2 ≤ 1280*m^4*X^2 := by
  let P := 16*m*X
  have hm0 : 0 ≤ m := by linarith
  have hp : 1 ≤ P := by dsimp [P]; nlinarith [mul_le_mul hm hX (by norm_num) hm0]
  have hp0 : 0 ≤ P := by linarith
  have hm2 : 1 ≤ m^2 := one_le_pow₀ hm
  have hp2 : 1 ≤ P^2 := one_le_pow₀ hp
  have hmm : m ≤ m^2 := by nlinarith
  have h1 : 1 ≤ m^2*P^2 := one_le_mul_of_one_le_of_one_le hm2 hp2
  have h2 : m ≤ m^2*P^2 := hmm.trans (le_mul_of_one_le_right (sq_nonneg m) hp2)
  have hmp : 1 ≤ m*P := one_le_mul_of_one_le_of_one_le hm hp
  have h3 : m*P ≤ m^2*P^2 := by nlinarith [sq_nonneg (m*P-1)]
  have h4 : m*P^2 ≤ m^2*P^2 := mul_le_mul_of_nonneg_right hmm (sq_nonneg P)
  have hs : 1+m+m*P+m*P^2+m^2*P^2 ≤ 5*m^2*P^2 := by linarith
  calc
    _ ≤ 5*m^2*P^2 := hs
    _ = _ := by dsimp [P]; ring

theorem mean_card_le {m : ℕ} (G : MeanGeometry m) (hm : 2 ≤ m)
    (h₀ : ℝ) (hh : 0 < h₀) (hhh : h₀ ≤ 1/2)
    (hback : G.backward = actualKernelInterval G.R h₀ G.R_pos G.R_le_half hh)
    (hconditional : ∀ ρ, G.conditional ρ = conditionalGeometricInterval h₀ hh)
    (hforward : ∀ ρ, G.forward ρ = forwardGeometricInterval G ρ h₀ hh) :
    (Fintype.card G.MeanNode : ℝ) ≤ 1280*(m:ℝ)^4*(meshBudget G.R h₀)^2 := by
  let P := 16*(m:ℝ)*meshBudget G.R h₀
  have hP : 0 ≤ P := by dsimp [P, meshBudget]; positivity
  have hk : (Fintype.card G.Kernel : ℝ) ≤ P := by
    change (Fintype.card (Option (G.backward.Source m)) : ℝ) ≤ P
    rw [Fintype.card_option, hback, kernel_card]
    exact backward_count_le m hm G.R_pos G.R_le_half le_rfl G.backwardEnd_pos.le hh hhh
  have hb : (Fintype.card (G.backward.Source m) : ℝ) ≤ P := by
    apply drop_origin
    simpa only [MeanGeometry.Kernel, Fintype.card_option] using hk
  have hc (ρ : G.Kernel) : (Fintype.card ((G.conditional ρ).Source m) : ℝ) ≤ P := by
    rw [hconditional, conditionalGeometricInterval, probability_card]
    exact drop_origin (conditional_count_le m hm G.R_pos G.R_le_half le_rfl conditionalEnd_pos.le hh hhh)
  have hf (ρ : G.Kernel) : (Fintype.card ((G.forward ρ).Source m) : ℝ) ≤ P := by
    rw [hforward, forwardGeometricInterval, probability_card]
    exact drop_origin (backward_count_le m hm G.R_pos G.R_le_half (G.rho_mem ρ).1 (G.rho_mem ρ).2.le hh hhh)
  have hcs : (∑ ρ : G.Kernel, (Fintype.card ((G.conditional ρ).Source m) : ℝ)) ≤ P^2 := by
    calc
      _ ≤ ∑ _ : G.Kernel, P := Finset.sum_le_sum (fun ρ _ => hc ρ)
      _ = (Fintype.card G.Kernel : ℝ)*P := by simp
      _ ≤ P*P := mul_le_mul_of_nonneg_right hk hP
      _ = _ := (pow_two P).symm
  have hfs : (∑ ρ : G.Kernel, (Fintype.card ((G.forward ρ).Source m) : ℝ)) ≤ P^2 := by
    calc
      _ ≤ ∑ _ : G.Kernel, P := Finset.sum_le_sum (fun ρ _ => hf ρ)
      _ = (Fintype.card G.Kernel : ℝ)*P := by simp
      _ ≤ P*P := mul_le_mul_of_nonneg_right hk hP
      _ = _ := (pow_two P).symm
  have he : (Fintype.card G.MeanNode : ℝ) = 1+(m:ℝ)+(m:ℝ)*(Fintype.card (G.backward.Source m):ℝ)+
      (m:ℝ)*(∑ ρ : G.Kernel, (Fintype.card ((G.conditional ρ).Source m):ℝ))+
      (m:ℝ)^2*(∑ ρ : G.Kernel, (Fintype.card ((G.forward ρ).Source m):ℝ)) := by
    have h := G.card_meanNode
    simpa only [pow_two] using (show (Fintype.card G.MeanNode : ℝ) = _ from by exact_mod_cast h)
  rw [he]
  apply le_trans _ (polynomial_bound (by exact_mod_cast (show 1 ≤ m by omega)) (meshBudget_ge_one hh hhh))
  change _ ≤ 1+(m:ℝ)+(m:ℝ)*P+(m:ℝ)*P^2+(m:ℝ)^2*P^2
  nlinarith [mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg m),
    mul_le_mul_of_nonneg_left hcs (Nat.cast_nonneg m),
    mul_le_mul_of_nonneg_left hfs (sq_nonneg (m:ℝ))]

/-- Sampling has at most P nodes; unlike Kernel, its Node type has no extra origin. -/
theorem sampling_card_le {m : ℕ} (S : SamplingGeometry m) (hm : 2 ≤ m)
    (h₀ : ℝ) (hh : 0 < h₀) (hhh : h₀ ≤ 1/2)
    (hmesh : S.mesh = probabilityGeometricInterval 0 (samplingEnd S.τ) h₀
      S.samplingEnd_pos S.samplingEnd_lt_one hh) :
    (Fintype.card S.Node : ℝ) ≤ 16*(m:ℝ)*meshBudget S.R h₀ := by
  change (Fintype.card (S.mesh.Source m):ℝ) ≤ _
  rw [hmesh, probability_card]
  exact drop_origin (sampling_count_le m hm S.R_pos S.R_le_τ S.τ_le_one
    le_rfl S.samplingEnd_pos.le hh hhh)

theorem sampling_card_le_common {m : ℕ} (S : SamplingGeometry m) (hm : 2 ≤ m)
    (h₀ : ℝ) (hh : 0 < h₀) (hhh : h₀ ≤ 1/2)
    (hmesh : S.mesh = probabilityGeometricInterval 0 (samplingEnd S.τ) h₀
      S.samplingEnd_pos S.samplingEnd_lt_one hh) :
    (Fintype.card S.Node : ℝ) ≤ 1280*(m:ℝ)^4*(meshBudget S.R h₀)^2 := by
  have hs := sampling_card_le S hm h₀ hh hhh hmesh
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hX := meshBudget_ge_one (R := S.R) hh hhh
  have hp : 0 ≤ 16*(m:ℝ)*meshBudget S.R h₀ := by positivity
  apply hs.trans (le_trans _ (polynomial_bound hmR hX))
  nlinarith [mul_le_mul_of_nonneg_right hmR hp,
    mul_nonneg (Nat.cast_nonneg m) (sq_nonneg (16*(m:ℝ)*meshBudget S.R h₀)),
    mul_nonneg (sq_nonneg (m:ℝ)) (sq_nonneg (16*(m:ℝ)*meshBudget S.R h₀))]

/-- Square-root budget in the real X parameter. -/
theorem sqrt_card_le {n m : ℕ} {X : ℝ} (hX : 0 ≤ X)
    (hn : (n:ℝ) ≤ 1280*(m:ℝ)^4*X^2) :
    Real.sqrt n ≤ Real.sqrt 1280*(m:ℝ)^2*X := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ 1280*(m:ℝ)^4*X^2 := hn
    _ = (Real.sqrt 1280*(m:ℝ)^2*X)^2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ)≤1280)]
      ring

set_option backward.isDefEq.respectTransparency false in
/-- The actual Source equivalences turn the real cardinality budget into the
precise two dimension hypotheses. B's lower bound stays explicit. -/
theorem source_dimension_bounds {m n ns : ℕ} (C : RecursiveCall.Source m n ns) (hm : 2 ≤ m)
    (hδ : 0 < C.δ) (hhalf : C.δ^C.w ≤ 1/2) (hR : C.M.R = C.δ^C.t)
    (hback : C.M.backward = actualKernelInterval C.M.R (C.δ^C.w)
      C.M.R_pos C.M.R_le_half (Real.rpow_pos_of_pos hδ C.w))
    (hconditional : ∀ ρ, C.M.conditional ρ = conditionalGeometricInterval (C.δ^C.w)
      (Real.rpow_pos_of_pos hδ C.w))
    (hforward : ∀ ρ, C.M.forward ρ = forwardGeometricInterval C.M ρ (C.δ^C.w)
      (Real.rpow_pos_of_pos hδ C.w))
    (hsampling : C.S.mesh = probabilityGeometricInterval 0 (samplingEnd C.S.τ) (C.δ^C.w)
      C.S.samplingEnd_pos C.S.samplingEnd_lt_one (Real.rpow_pos_of_pos hδ C.w))
    (B : ℝ) (hB : Real.sqrt 1280*(m:ℝ)^2*(1+|Real.log (C.δ^C.t)|) ≤ B) :
    Real.sqrt n ≤ B*C.δ^(-C.w) ∧ Real.sqrt ns ≤ B*C.δ^(-C.w) := by
  have hh := Real.rpow_pos_of_pos hδ C.w
  have hX : 0 ≤ meshBudget C.M.R (C.δ^C.w) := (by norm_num : (0:ℝ)≤1).trans (meshBudget_ge_one hh hhalf)
  have hn : (n:ℝ) ≤ 1280*(m:ℝ)^4*(meshBudget C.M.R (C.δ^C.w))^2 := by
    have he : n = Fintype.card C.M.MeanNode := by simpa using Fintype.card_congr C.nodes
    calc
      (n:ℝ) = (Fintype.card C.M.MeanNode:ℝ) := congrArg Nat.cast he
      _ ≤ _ := mean_card_le C.M hm _ hh hhalf hback hconditional hforward
  have hns : (ns:ℝ) ≤ 1280*(m:ℝ)^4*(meshBudget C.M.R (C.δ^C.w))^2 := by
    have he : ns = Fintype.card C.S.Node := by
      simpa only [SamplingGeometry.Node, RecursiveCall.Source.S, RecursiveExecutable.privateGeometry, Fintype.card_fin] using Fintype.card_congr C.snodes
    calc
      (ns:ℝ) = (Fintype.card C.S.Node:ℝ) := congrArg Nat.cast he
      _ ≤ _ := sampling_card_le_common C.S hm _ hh hhalf hsampling
  have hscale : Real.sqrt 1280*(m:ℝ)^2*meshBudget C.M.R (C.δ^C.w) ≤ B*C.δ^(-C.w) := by
    rw [meshBudget, hR, Real.rpow_neg hδ.le]
    calc
      _ = (Real.sqrt 1280*(m:ℝ)^2*(1+|Real.log (C.δ^C.t)|))*(C.δ^C.w)⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hB (inv_nonneg.mpr hh.le)
  exact ⟨(sqrt_card_le hX hn).trans hscale, (sqrt_card_le hX hns).trans hscale⟩
end AcceleratedLogConcave.Oracle.PrescribedMeshDimensions
