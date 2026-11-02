import AcceleratedLogConcave.Tensor.ActualHessianCoefficient
import AcceleratedLogConcave.Tensor.ActualCoefficientBudget

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability

private theorem matrix_identity_norm_le (D : ℕ) :
    ‖matrixCLMEquiv (1 : Matrix (Fin D) (Fin D) ℝ)‖ ≤ 1 := by
  have he : matrixCLMEquiv (1 : Matrix (Fin D) (Fin D) ℝ) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin D)) := by
    ext v i
    rw [matrixCLMEquiv_apply]
    simp [Matrix.one_apply]
  rw [he]
  exact ContinuousLinearMap.norm_id_le

/-- Any two-slot Euclidean identity tensor has split norm at most one,
including zero physical dimension. -/
theorem pairIdentity_splitNorm_le {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (hcard : Fintype.card Slot = 2) (p q : Slot) (hpq : p ≠ q) {D : ℕ}
    (S : Finset Slot) (hS : NontrivialSplit S) :
    splitNorm D S (WithLp.toLp 2 (fun a : Slot → Fin D =>
      inner ℝ (coordinateDirection D (a p)) (coordinateDirection D (a q)))) ≤ 1 := by
  classical
  have hc : S.card = 1 := by
    have hp := Finset.card_pos.mpr hS.1
    have hcp := Finset.card_pos.mpr hS.2
    rw [Finset.card_compl] at hcp
    have hle := Finset.card_le_univ S
    rw [hcard] at hcp hle
    omega
  obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hc
  have hc' : ({i}ᶜ : Finset Slot).card = 1 := by simp [Finset.card_compl,hcard]
  obtain ⟨j,hj⟩ := Finset.card_eq_one.mp hc'
  have hji : j ≠ i := by
    have : j ∈ ({i}ᶜ : Finset Slot) := by rw [hj]; simp
    simpa using this
  let il : ({i} : Finset Slot) := ⟨i,by simp⟩
  let ir : {s : Slot // s ∉ ({i} : Finset Slot)} := ⟨j,by simpa using hji⟩
  let er : LeftAssignment D {i} → Fin D := fun a => a il
  let ec : RightAssignment D {i} → Fin D := fun a => a ir
  have her : Function.Injective er := by
    intro a b hab
    funext s
    have hs : s = il := Subtype.ext (Finset.mem_singleton.mp s.property)
    simpa [er,hs] using hab
  have hec : Function.Injective ec := by
    intro a b hab
    funext s
    have hs : s = ir := by
      apply Subtype.ext
      have hh : s.val ∈ ({i}ᶜ : Finset Slot) := by simpa using s.property
      simpa [hj] using hh
    simpa [ec,hs] using hab
  have hm : unfoldEquiv D {i} (WithLp.toLp 2 (fun a : Slot → Fin D =>
      inner ℝ (coordinateDirection D (a p)) (coordinateDirection D (a q)))) =
      (1 : Matrix (Fin D) (Fin D) ℝ).submatrix er ec := by
    ext a b
    rw [unfold_apply]
    change inner ℝ (coordinateDirection D ((fun s => if h : s ∈ ({i} : Finset Slot) then a ⟨s,h⟩ else b ⟨s,h⟩) p))
      (coordinateDirection D ((fun s => if h : s ∈ ({i} : Finset Slot) then a ⟨s,h⟩ else b ⟨s,h⟩) q)) = _
    have hpj : p = i ∨ p = j := by
      by_cases hp : p = i
      · exact Or.inl hp
      · right
        have : p ∈ ({i}ᶜ : Finset Slot) := by simpa using hp
        simpa [hj] using this
    have hqj : q = i ∨ q = j := by
      by_cases hq : q = i
      · exact Or.inl hq
      · right
        have : q ∈ ({i}ᶜ : Finset Slot) := by simpa using hq
        simpa [hj] using this
    rcases hpj with rfl | rfl <;> rcases hqj with rfl | rfl <;>
      simp_all [er,ec,il,ir,coordinateDirection,EuclideanSpace.inner_single_left,
        PiLp.single_apply,Matrix.submatrix,Matrix.one_apply,eq_comm]
  change ‖matrixCLMEquiv (unfoldEquiv D {i} _)‖ ≤ 1
  rw [hm]
  exact (matrixCLM_submatrix_norm_le _ er her ec hec).trans (matrix_identity_norm_le D)

theorem identityCoefficient_splitNorm_le {D : ℕ} (S : Finset (Fin 2))
    (hS : NontrivialSplit S) : splitNorm D S (identityCoefficient (D := D)) ≤ 1 := by
  exact pairIdentity_splitNorm_le (by simp) (0 : Fin 2) 1 (by decide) S hS

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
