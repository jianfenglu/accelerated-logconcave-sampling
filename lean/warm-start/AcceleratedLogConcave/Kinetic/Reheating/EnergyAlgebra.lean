import AcceleratedLogConcave.Kinetic.Reheating.Loss
import AcceleratedLogConcave.Kinetic.Mixing.Energy

/-! Hilbert and scalar algebra for the correlated reheating estimate.
These intermediate lemmas expose their residual/current premises; the physical
wrapper must supply them using the actual Gaussian and heat theorems. -/
noncomputable section
open InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
section Geometry
variable {H K S : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]

/-- Orthogonality removes the hidden average before Cauchy--Schwarz. -/
theorem centered_observation_pairing_bound (I : S →ₗᵢ[ℝ] H) (B : K →ₗᵢ[ℝ] H)
    (A : K →L[ℝ] K) (r : ℝ)
    (hA : ∀ x, ‖B (A x) - I (I.toContinuousLinearMap.adjoint (B (A x)))‖ ≤ r*‖x‖)
    (w : H) (hw : I.toContinuousLinearMap.adjoint w = 0) (x : K) :
    |inner ℝ (A x) (B.toContinuousLinearMap.adjoint w)| ≤ r*‖x‖*‖w‖ := by
  have he : inner ℝ (A x) (B.toContinuousLinearMap.adjoint w) =
      inner ℝ (B (A x) - I (I.toContinuousLinearMap.adjoint (B (A x)))) w := by
    have hi := I.toContinuousLinearMap.adjoint_inner_right
      (I.toContinuousLinearMap.adjoint (B (A x))) w
    change inner ℝ (I.toContinuousLinearMap.adjoint (B (A x))) (I.toContinuousLinearMap.adjoint w) =
      inner ℝ (I (I.toContinuousLinearMap.adjoint (B (A x)))) w at hi
    rw [hw, inner_zero_right] at hi
    rw [inner_sub_left, ← hi, sub_zero]
    exact B.toContinuousLinearMap.adjoint_inner_right _ _
  rw [he]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hA x) (norm_nonneg w))

/-- All three extra corrector terms for a hidden-centered perturbation. -/
theorem centered_observation_current_bound (I : S →ₗᵢ[ℝ] H) (B : K →ₗᵢ[ℝ] H)
    (A : K →L[ℝ] K) (r : ℝ) (hr : 0 ≤ r)
    (hA : ∀ x, ‖B (A x) - I (I.toContinuousLinearMap.adjoint (B (A x)))‖ ≤ r*‖x‖)
    (hAd : ∀ x, ‖B (A.adjoint x) - I (I.toContinuousLinearMap.adjoint (B (A.adjoint x)))‖ ≤ r*‖x‖)
    (w : H) (hw : I.toContinuousLinearMap.adjoint w = 0) (v₀ : K) :
    let u := B.toContinuousLinearMap.adjoint w
    |inner ℝ (A (v₀+u)) (v₀+u) - inner ℝ (A v₀) v₀| ≤
      2*r*‖v₀‖*‖w‖ + r*‖w‖^2 := by
  dsimp only
  let u := B.toContinuousLinearMap.adjoint w
  have h1 := centered_observation_pairing_bound I B A r hA w hw v₀
  have h2 := centered_observation_pairing_bound I B A.adjoint r hAd w hw v₀
  have h3 := centered_observation_pairing_bound I B A r hA w hw u
  have hu : ‖u‖ ≤ ‖w‖ := by
    have hh := isometry_adjoint_loss B w
    change ‖w‖^2 - ‖u‖^2 = _ at hh
    nlinarith [sq_nonneg ‖w-B u‖, norm_nonneg u, norm_nonneg w]
  have h2' : |inner ℝ (A u) v₀| ≤ r*‖v₀‖*‖w‖ := by
    rw [← A.adjoint_inner_right u v₀, real_inner_comm]
    exact h2
  have h3' : |inner ℝ (A u) u| ≤ r*‖w‖^2 := h3.trans (by
    have hh := mul_le_mul_of_nonneg_left hu hr
    nlinarith [mul_le_mul_of_nonneg_right hh (norm_nonneg w)])
  change |inner ℝ (A (v₀+u)) (v₀+u) - inner ℝ (A v₀) v₀| ≤ _
  have he : inner ℝ (A (v₀+u)) (v₀+u) - inner ℝ (A v₀) v₀ =
      inner ℝ (A v₀) u + inner ℝ (A u) v₀ + inner ℝ (A u) u := by
    simp only [map_add, inner_add_left, inner_add_right]
    ring
  rw [he]
  calc
    _ ≤ |inner ℝ (A v₀) u| + |inner ℝ (A u) v₀| + |inner ℝ (A u) u| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by linarith
end Geometry

/-- The source constants from ordinary loss ≤8D and hidden norm squared ≤3D. -/
theorem reheating_current_scalar {t D Dg N G W V J : ℝ}
    (ht : 0 ≤ t) (hD : 0 ≤ D) (hDg : 0 ≤ Dg) (hN : 0 ≤ N)
    (hG : 0 ≤ G) (hGN : G ≤ N) (hW : 0 ≤ W) (_hV : 0 ≤ V) (hVN : V ≤ N)
    (hloss : Dg ≤ 8*D) (hw : W^2 ≤ 3*D)
    (hJ : J ≤ (t/4)*G^2 + Real.sqrt (t*Dg)*G +
      2*Real.sqrt t*V*W + Real.sqrt t*W^2) :
    J ≤ (t/4)*N^2 + 7*Real.sqrt (t*D)*N + 3*Real.sqrt t*D := by
  have hd := Real.sq_sqrt hD
  have htd := Real.sq_sqrt (mul_nonneg ht hD)
  have htg := Real.sq_sqrt (mul_nonneg ht hDg)
  have hw' : W ≤ 2*Real.sqrt D := by nlinarith [Real.sqrt_nonneg D]
  have hg' : Real.sqrt (t*Dg) ≤ 3*Real.sqrt (t*D) := by
    nlinarith [mul_le_mul_of_nonneg_left hloss ht, Real.sqrt_nonneg (t*Dg), Real.sqrt_nonneg (t*D)]
  have hsq : G^2 ≤ N^2 := by nlinarith
  have hterm1 := mul_le_mul_of_nonneg_left hsq (div_nonneg ht (by norm_num : (0:ℝ) ≤ 4))
  have hterm2 := mul_le_mul hg' hGN hG (by positivity : 0 ≤ 3*Real.sqrt (t*D))
  have hterm3 := mul_le_mul hVN hw' hW hN
  have hterm3' := mul_le_mul_of_nonneg_left hterm3 (by positivity : 0 ≤ 2*Real.sqrt t)
  have hterm4 := mul_le_mul_of_nonneg_left hw (Real.sqrt_nonneg t)
  simp only [Real.sqrt_mul ht] at hterm2 hJ ⊢
  nlinarith

/-- The exact source Young absorption gives the universal constant 100. -/
theorem reheating_energy_scalar {ε t D N J₀ Jₜ : ℝ}
    (hε : 0 ≤ ε) (ht : 0 ≤ t) (hD : 0 ≤ D) (_hN : 0 ≤ N)
    (hsmall : ε*Real.sqrt t ≤ 1/24)
    (hJ : |Jₜ-J₀| ≤ (t/4)*N^2 + 7*Real.sqrt (t*D)*N + 3*Real.sqrt t*D) :
    (1/2:ℝ)*(N^2-D)+ε*Jₜ ≤
      (1/2:ℝ)*N^2+ε*J₀-D/4+100*(ε+ε^2)*t*N^2 := by
  have hd := Real.sq_sqrt hD
  have ht' := Real.sq_sqrt ht
  have hy := sq_nonneg (Real.sqrt D - 28*ε*Real.sqrt t*N)
  have he : (Real.sqrt D - 28*ε*Real.sqrt t*N)^2 =
      D - 56*ε*Real.sqrt t*Real.sqrt D*N + 784*ε^2*t*N^2 := by
    calc
      _ = (Real.sqrt D)^2 - 56*ε*Real.sqrt t*Real.sqrt D*N +
          784*ε^2*(Real.sqrt t)^2*N^2 := by ring
      _ = _ := by rw [hd, ht']
  rw [he] at hy
  have hy' : 7*ε*Real.sqrt (t*D)*N ≤ D/8+98*ε^2*t*N^2 := by
    rw [Real.sqrt_mul ht]
    nlinarith
  have hs : 3*ε*Real.sqrt t*D ≤ D/8 := by
    nlinarith [mul_le_mul_of_nonneg_right hsmall hD]
  have hj := mul_le_mul_of_nonneg_left ((le_abs_self (Jₜ-J₀)).trans hJ) hε
  have hn : 0 ≤ ε*t*N^2 := mul_nonneg (mul_nonneg hε ht) (sq_nonneg N)
  have hn' : 0 ≤ ε^2*t*N^2 := mul_nonneg (mul_nonneg (sq_nonneg ε) ht) (sq_nonneg N)
  nlinarith

end AcceleratedLogConcave.Kinetic.Reheating
