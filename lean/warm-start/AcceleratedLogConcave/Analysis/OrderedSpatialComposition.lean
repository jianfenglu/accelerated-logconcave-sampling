import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Order.Fin.Tuple
import Mathlib.Tactic

/-!

-/
noncomputable section
set_option autoImplicit false
open Set Function
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.SpatialPartition

namespace OrderedFinpartition

/-- The unique partition consisting of one block, with the original slot order. -/
def oneBlock (n : ℕ) (hn : 0 < n) : OrderedFinpartition n where
  length := 1
  partSize _ := n
  partSize_pos _ := hn
  emb _ := id
  emb_strictMono _ := strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint := by
    intro i hi j hj hij
    exact (hij (Subsingleton.elim _ _)).elim
  cover j := ⟨0, j, rfl⟩

lemma sum_partSize {n : ℕ} (c : OrderedFinpartition n) :
    ∑ i, c.partSize i = n := by
  simpa using c.sum_sigma_eq_sum (fun _ => (1 : ℕ))

/-- This proof uses ordered embeddings, so no symmetry of a derivative is needed. -/
lemma eq_oneBlock_of_length_eq_one {n : ℕ} (hn : 0 < n)
    (c : OrderedFinpartition n) (hc : c.length = 1) : c = oneBlock n hn := by
  rcases c with ⟨l, p, hp, e, he, hm, hd, hcover⟩
  dsimp at hc
  subst l
  have hs : ∑ i, p i = n :=
    sum_partSize ⟨1, p, hp, e, he, hm, hd, hcover⟩
  have hp0 : p 0 = n := by simpa using hs
  have hpall : p = fun _ => n := by
    funext i
    have : i = 0 := Subsingleton.elim _ _
    simpa [this] using hp0
  subst p
  have heall : e = fun _ => id := by
    funext i j
    have hl : j ≤ e i j := (he i).id_le j
    have hu : e i j ≤ j := by
      simpa using
        ((Fin.rev_strictAnti.comp_strictMono (he i)).comp Fin.rev_strictAnti).id_le
          (Fin.rev j)
    exact le_antisymm hu hl
  subst e
  rfl

lemma eq_oneBlock_iff {n : ℕ} (hn : 0 < n) (c : OrderedFinpartition n) :
    c = oneBlock n hn ↔ c.length = 1 := by
  constructor
  · rintro rfl
    rfl
  · exact eq_oneBlock_of_length_eq_one hn c

/-- Strict lower-order support of every non-top partition, at arbitrary n. -/
lemma partSize_lt_of_ne_oneBlock {n : ℕ} (hn : 0 < n)
    (c : OrderedFinpartition n) (hc : c ≠ oneBlock n hn) (i : Fin c.length) :
    c.partSize i < n := by
  have hlen : 1 < c.length := by
    have hpos := c.length_pos hn
    have hne : c.length ≠ 1 := fun h => hc (eq_oneBlock_of_length_eq_one hn c h)
    omega
  obtain ⟨j, hji⟩ : ∃ j : Fin c.length, j ≠ i := by
    by_cases hi : i.val = 0
    · refine ⟨⟨1, hlen⟩, ?_⟩
      intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro h
      exact hi (congrArg Fin.val h).symm
  calc
    c.partSize i < ∑ k, c.partSize k :=
      Finset.single_lt_sum hji (Finset.mem_univ _) (Finset.mem_univ _)
        (c.partSize_pos j) (fun k _ _ => Nat.zero_le (c.partSize k))
    _ = n := sum_partSize c

end OrderedFinpartition

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The literal multilinear partition term, retaining all slot labels. -/
def spatialTerm (g : F → G) (f : E → F) (x : E) {n : ℕ}
    (c : OrderedFinpartition n) : E [×n]→L[ℝ] G :=
  c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length g (f x))
    (fun i => iteratedFDeriv ℝ (c.partSize i) f x)

lemma spatialTerm_apply (g : F → G) (f : E → F) (x : E) {n : ℕ}
    (c : OrderedFinpartition n) (v : Fin n → E) :
    spatialTerm g f x c v = iteratedFDeriv ℝ c.length g (f x)
      (fun i => iteratedFDeriv ℝ (c.partSize i) f x (v ∘ c.emb i)) := rfl

lemma spatialTerm_oneBlock (g : F → G) (f : E → F) (x : E)
    (n : ℕ) (hn : 0 < n) :
    spatialTerm g f x (OrderedFinpartition.oneBlock n hn) =
      (fderiv ℝ g (f x)).compContinuousMultilinearMap (iteratedFDeriv ℝ n f x) := by
  ext v
  simp [spatialTerm_apply, OrderedFinpartition.oneBlock,
    ContinuousLinearMap.compContinuousMultilinearMap_coe]

/-- Finite forcing at order n. For n=1 this sum is empty. -/
def spatialForcing (g : F → G) (f : E → F) (x : E) (n : ℕ) (hn : 0 < n) :
    E [×n]→L[ℝ] G :=
  ∑ c ∈ (Finset.univ : Finset (OrderedFinpartition n)).erase
      (OrderedFinpartition.oneBlock n hn), spatialTerm g f x c

/-- Full operator equality, not just a diagonal or repeated-direction formula. -/
theorem iteratedFDeriv_comp_separated {g : F → G} {f : E → F} {x : E}
    (hg : ContDiffAt ℝ ∞ g (f x)) (hf : ContDiffAt ℝ ∞ f x)
    (n : ℕ) (hn : 0 < n) :
    iteratedFDeriv ℝ n (g ∘ f) x =
      (fderiv ℝ g (f x)).compContinuousMultilinearMap (iteratedFDeriv ℝ n f x) +
        spatialForcing g f x n hn := by
  classical
  rw [iteratedFDeriv_comp hg hf (by simp : (n : WithTop ℕ∞) ≤ ∞)]
  change (∑ c : OrderedFinpartition n, spatialTerm g f x c) = _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (OrderedFinpartition.oneBlock n hn))]
  rw [spatialTerm_oneBlock]
  exact add_comm _ _

/-- Every inner derivative in the explicit forcing lies in the induction range. -/
theorem spatialForcing_support (n : ℕ) (hn : 0 < n)
    (c : OrderedFinpartition n)
    (hc : c ∈ (Finset.univ : Finset (OrderedFinpartition n)).erase
      (OrderedFinpartition.oneBlock n hn)) (i : Fin c.length) :
    1 ≤ c.partSize i ∧ c.partSize i < n := by
  exact ⟨c.partSize_pos i,
    OrderedFinpartition.partSize_lt_of_ne_oneBlock hn c (Finset.mem_erase.mp hc).1 i⟩

/-- The outer derivative in every forcing term has order between two and n. -/
theorem spatialForcing_outer_order (n : ℕ) (hn : 0 < n)
    (c : OrderedFinpartition n)
    (hc : c ∈ (Finset.univ : Finset (OrderedFinpartition n)).erase
      (OrderedFinpartition.oneBlock n hn)) : 2 ≤ c.length ∧ c.length ≤ n := by
  have hpos := c.length_pos hn
  have hne : c.length ≠ 1 := fun h => (Finset.mem_erase.mp hc).1
    (OrderedFinpartition.eq_oneBlock_of_length_eq_one hn c h)
  exact ⟨by omega, c.length_le⟩

/-- Provenance: holding the flow value and strictly lower jets fixed holds
all forcing fixed. The unknown nth flow derivative is not accessed. -/
theorem spatialForcing_congr_lower (g : F → G) {f h : E → F} (x : E)
    (n : ℕ) (hn : 0 < n) (hvalue : f x = h x)
    (hjets : ∀ j, 1 ≤ j → j < n →
      iteratedFDeriv ℝ j f x = iteratedFDeriv ℝ j h x) :
    spatialForcing g f x n hn = spatialForcing g h x n hn := by
  classical
  apply Finset.sum_congr rfl
  intro c hc
  unfold spatialTerm
  rw [hvalue]
  congr 1
  funext i
  have hs := spatialForcing_support n hn c hc i
  exact hjets (c.partSize i) hs.1 hs.2

/-- Direct full operator-norm majorant; no polarization loss, no coordinate
choice, no positive-dimension hypothesis, and no unknown top jet on the RHS. -/
theorem norm_spatialForcing_le (g : F → G) (f : E → F) (x : E)
    (n : ℕ) (hn : 0 < n) :
    ‖spatialForcing g f x n hn‖ ≤
      ∑ c ∈ (Finset.univ : Finset (OrderedFinpartition n)).erase
          (OrderedFinpartition.oneBlock n hn),
        ‖iteratedFDeriv ℝ c.length g (f x)‖ *
          ∏ i, ‖iteratedFDeriv ℝ (c.partSize i) f x‖ := by
  classical
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c hc =>
    c.norm_compAlongOrderedFinpartition_le _ _)

end AcceleratedLogConcave.Analysis.SpatialPartition
