import AcceleratedLogConcave.Tensor.FlowOrderGrowthScalars
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic

/-!

-/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace AcceleratedLogConcave.Tensor.FlowInduction

/-- Labelings of k segments of prescribed sizes which induce exactly f.
The direction e : Sigma slots ≃ labels avoids arbitrary within-block orders. -/
abbrev CompatibleLabeling {n k : ℕ} (j : Fin k → ℕ) (f : Fin n → Fin k) :=
  {e : (Σ i : Fin k, Fin (j i)) ≃ Fin n // ∀ p, f (e p) = p.1}

/-- Restrict an actual labeling to a single block fiber. -/
def labelingFiberEquiv {n k : ℕ} {j : Fin k → ℕ} {f : Fin n → Fin k}
    (e : CompatibleLabeling j f) (i : Fin k) :
    Fin (j i) ≃ {x : Fin n // f x = i} :=
  Equiv.ofBijective (fun r => ⟨e.val ⟨i,r⟩, e.property ⟨i,r⟩⟩) (by
    constructor
    · intro r s h
      have he : e.val ⟨i,r⟩ = e.val ⟨i,s⟩ := congrArg Subtype.val h
      have hp := e.val.injective he
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hp
    · intro x
      obtain ⟨⟨a,r⟩, hx⟩ := e.val.surjective x.val
      have ha : a = i := by
        have he := e.property ⟨a,r⟩
        rw [hx] at he
        exact he.symm.trans x.property
      subst a
      exact ⟨r, Subtype.ext hx⟩)

/-- Independent choices of an ordering of every fiber reconstruct a unique
label permutation. This is the complete within-segment fiber equivalence. -/
def compatibleLabelingEquiv {n k : ℕ} (j : Fin k → ℕ) (f : Fin n → Fin k) :
    CompatibleLabeling j f ≃ (∀ i, Fin (j i) ≃ {x : Fin n // f x = i}) where
  toFun e i := labelingFiberEquiv e i
  invFun g := ⟨(Equiv.sigmaCongrRight g).trans (Equiv.sigmaFiberEquiv f), by
    intro p
    exact (g p.1 p.2).property⟩
  left_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro p
    rfl
  right_inv g := by
    funext i
    apply Equiv.ext
    intro r
    apply Subtype.ext
    rfl

/-- Exact fiber cardinality. Its only premise is the cardinality of each
block, not a factorial counting assertion or a recurrence. -/
theorem compatibleLabeling_card {n k : ℕ} (j : Fin k → ℕ) (f : Fin n → Fin k)
    (hsize : ∀ i, Fintype.card {x : Fin n // f x = i} = j i) :
    Fintype.card (CompatibleLabeling j f) = ∏ i, (j i).factorial := by
  classical
  rw [Fintype.card_congr (compatibleLabelingEquiv j f), Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  let g : Fin (j i) ≃ {x : Fin n // f x = i} :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using (hsize i).symm)
  simpa only [Fintype.card_fin] using Fintype.card_equiv g

/-- Forgetting the induced block assignment is an equivalence, not just a
surjection. Every label permutation induces its unique assignment f. -/
def labelingDecompositionEquiv {n k : ℕ} (j : Fin k → ℕ) :
    (Σ f : Fin n → Fin k, CompatibleLabeling j f) ≃
      ((Σ i : Fin k, Fin (j i)) ≃ Fin n) :=
  Equiv.ofBijective (fun x => x.2.val) (by
    constructor
    · rintro ⟨f,e⟩ ⟨g,d⟩ h
      change e.val = d.val at h
      have hfg : f = g := by
        funext x
        obtain ⟨p,hp⟩ := e.val.surjective x
        have he := e.property p
        have hd := d.property p
        rw [← h] at hd
        rw [hp] at he hd
        exact he.trans hd.symm
      subst g
      have hed : e = d := Subtype.ext h
      subst d
      rfl
    · intro e
      refine ⟨⟨fun x => (e.symm x).1, e, ?_⟩, rfl⟩
      intro p
      simp)

/-- There are n! labelings in total, decomposed by their unique ordered
block assignment. This statement is finite and has no positive-size premise;
positivity is only needed later to identify these with nonempty blocks. -/
theorem compatibleLabeling_total {n k : ℕ} (j : Fin k → ℕ)
    (hsum : (∑ i, j i) = n) :
    (∑ f : Fin n → Fin k, Fintype.card (CompatibleLabeling j f)) = n.factorial := by
  classical
  let e : (Σ i : Fin k, Fin (j i)) ≃ Fin n :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_sigma, Fintype.card_fin] using hsum)
  have h := Fintype.card_congr (labelingDecompositionEquiv (n := n) j)
  rw [Fintype.card_sigma, Fintype.card_equiv e] at h
  simpa only [Fintype.card_sigma, Fintype.card_fin, hsum] using h

/-- Equal block sizes do not reduce the k! permutation multiplicity. -/
theorem growth_block_permutation_weight {k : ℕ} (w : Fin k → ℝ)
    (π : Equiv.Perm (Fin k)) : (∏ i, w (π i)) = ∏ i, w i := by
  exact Fintype.prod_equiv π _ _ (fun _ => rfl)

/-- The weighted sum over all permutations pays exactly k!, irrespective
of repeated weights or repeated block sizes. -/
theorem growth_sum_block_permutations {k : ℕ} (w : Fin k → ℝ) :
    (∑ π : Equiv.Perm (Fin k), ∏ i, w (π i)) =
      (k.factorial : ℝ) * ∏ i, w i := by
  simp_rw [growth_block_permutation_weight]
  simp [Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

end AcceleratedLogConcave.Tensor.FlowInduction
