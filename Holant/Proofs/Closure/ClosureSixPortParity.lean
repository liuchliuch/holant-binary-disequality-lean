import Holant.Projective.BinaryPencil
import Holant.Certificates.MatchingContractionClosure.Presentation
import Holant.Dihedral.EndpointParallelogram.Source
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-! NEW UNVERIFIED direct six-port support consequence of the actual ordered
zero-safe monomial-product root deck. No sector/ruling/alignment or atlas is
supplied. Degree-two interpolation retains all vanishing pencils, including
m=3 when two common nonzero phases need not exist. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant Holant.Projective
open Holant.Certificates.MatchingContractionClosure
open scoped BigOperators

abbrev Word (n : ℕ) := Fin n → Bool
def bit (b : Bool) : ZMod 2 := if b then 1 else 0
def parity {n : ℕ} (x : Word n) : ZMod 2 := ∑ i, bit (x i)

theorem bit_xor (a b : Bool) : bit a + bit b = bit (a ^^ b) := by
  cases a <;> cases b <;> decide

theorem rootMonomial_support_parity {m : ℕ} {B : Kernel ℂ}
    (h : IsRootMonomial m B) : ∃ p : Bool, ∀ a b, B a b ≠ 0 → (a ^^ b) = p := by
  rcases h with ⟨h01,h10,_⟩ | ⟨h00,h11,_⟩
  · refine ⟨false,?_⟩
    intro a b hn
    cases a <;> cases b <;> simp_all
  · refine ⟨true,?_⟩
    intro a b hn
    cases a <;> cases b <;> simp_all

/-- Literal product of nonsingular current root-monomial binaries. The
matching, individual factors and scalar may vary at every sampled card. -/
def RootMatching {n : ℕ} (m : ℕ) (q : Signature ℂ n) : Prop :=
  ∃ M : Presentation ℂ (Fin n), (∀ e, IsRootMonomial m (M.matrix e)) ∧
    M.scalar ≠ 0 ∧ q = M.tensor

theorem presentation_support_parity {n m : ℕ} (M : Presentation ℂ (Fin n))
    (mono : ∀ e, IsRootMonomial m (M.matrix e)) :
    ∃ p : ZMod 2, ∀ x : Word n, M.tensor x ≠ 0 → parity x = p := by
  choose p hp using fun e => rootMonomial_support_parity (mono e)
  refine ⟨∑ e, bit (p e),?_⟩
  intro x hx
  have hprod : (∏ e, M.matrix e (x (M.ports (e,false))) (x (M.ports (e,true)))) ≠ 0 := by
    exact (mul_ne_zero_iff.mp hx).2
  have he (e : Fin M.edges) :
      (x (M.ports (e,false)) ^^ x (M.ports (e,true))) = p e :=
    hp e _ _ ((Finset.prod_ne_zero_iff.mp hprod) e (Finset.mem_univ e))
  unfold parity
  rw [←Equiv.sum_comp M.ports (fun i => bit (x i)),Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Fintype.sum_bool]
  rw [bit_xor,Bool.xor_comm,he e]

theorem rootMatching_cross_parity {m : ℕ} {q : Signature ℂ 4}
    (hq : q = 0 ∨ RootMatching m q) (x y : Word 4) (different : parity x ≠ parity y) :
    q x * q y = 0 := by
  rcases hq with rfl | ⟨M,mono,_,rfl⟩
  · simp
  obtain ⟨p,hp⟩ := presentation_support_parity M mono
  by_cases hx : M.tensor x = 0
  · rw [hx,zero_mul]
  by_cases hy : M.tensor y = 0
  · rw [hy,mul_zero]
  exact False.elim (different ((hp x hx).trans (hp y hy).symm))

def fillSix (e : Equiv.Perm (Fin 6)) (a p : Bool) (x : Word 4) : Word 6 :=
  fun i => (Fin.cons a (Fin.cons (a ^^ p) x) : Word 6) (e.symm i)
def sliceSix (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) (p a : Bool) : Signature ℂ 4 :=
  fun x => h (fillSix e a p x)
def phaseCard (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) (p : Bool) (t : ℂ) : Signature ℂ 4 :=
  sliceSix h e p false + t • sliceSix h e p true

def OrderedRootDeck (m : ℕ) (h : Signature ℂ 6) : Prop :=
  ∀ e : Equiv.Perm (Fin 6), ∀ p : Bool, ∀ t : ℂ, t^m = 1 →
    phaseCard h e p t = 0 ∨ RootMatching m (phaseCard h e p t)

/-- This is the actual finite-sum kernel contraction, not an assumed pencil. -/
theorem phaseCard_actual (h : Signature ℂ 6) (e : Equiv.Perm (Fin 6)) (p : Bool) (t : ℂ) :
    phaseCard h e p t = Holant.Dihedral.EndpointParallelogram.card h e p t 1 := by
  funext x
  change h (fun i => (Fin.cons false (Fin.cons (false ^^ p) x) : Word 6) (e.symm i)) +
    t * h (fun i => (Fin.cons true (Fin.cons (true ^^ p) x) : Word 6) (e.symm i)) = _
  cases p <;> simp [Holant.Dihedral.EndpointParallelogram.card,
    Holant.Dihedral.EndpointParallelogram.phaseKernel,Fintype.sum_bool] <;> ring

/-- Opposite residual parities cannot both occur in the union of the two raw
endpoint supports. No sample is divided by, and the zero sector remains legal. -/
theorem endpoint_cross_parity {m : ℕ} (hm : 3 ≤ m) (h : Signature ℂ 6)
    (deck : OrderedRootDeck m h) (e : Equiv.Perm (Fin 6)) (p : Bool)
    (x y : Word 4) (different : parity x ≠ parity y) :
    (sliceSix h e p false x = 0 ∧ sliceSix h e p true x = 0) ∨
      (sliceSix h e p false y = 0 ∧ sliceSix h e p true y = 0) := by
  apply affine_product_zero_on_rootPolygon hm
  intro t ht
  exact rootMatching_cross_parity (deck e p t ht) x y different

theorem endpoint_supported_parity {m : ℕ} (hm : 3 ≤ m) (h : Signature ℂ 6)
    (deck : OrderedRootDeck m h) (e : Equiv.Perm (Fin 6)) (p a b : Bool)
    (x y : Word 4) (hx : sliceSix h e p a x ≠ 0) (hy : sliceSix h e p b y ≠ 0) :
    parity x = parity y := by
  by_contra different
  rcases endpoint_cross_parity hm h deck e p x y different with hz | hz
  · cases a
    · exact hx hz.1
    · exact hx hz.2
  · cases b
    · exact hy hz.1
    · exact hy hz.2

/-- Reconstruct the SAME original word from this ordered deleted pair. -/
def residualSix (e : Equiv.Perm (Fin 6)) (w : Word 6) : Word 4 :=
  fun i => w (e i.succ.succ)

theorem fillSix_reconstruct (e : Equiv.Perm (Fin 6)) (w : Word 6) :
    fillSix e (w (e 0)) (w (e 0) ^^ w (e 1)) (residualSix e w) = w := by
  funext i
  obtain ⟨j,rfl⟩ := e.surjective i
  simp only [fillSix,Equiv.symm_apply_apply]
  fin_cases j <;> simp [residualSix] <;> rfl

theorem parity_fillSix (e : Equiv.Perm (Fin 6)) (a p : Bool) (x : Word 4) :
    parity (fillSix e a p x) = bit p + parity x := by
  have pairBit : bit a + bit (a ^^ p) = bit p := by
    cases a <;> cases p <;> decide
  unfold parity
  rw [←Equiv.sum_comp e (fun i => bit (fillSix e a p x i))]
  simp only [fillSix,Equiv.symm_apply_apply]
  change (∑ i : Fin 6, bit ((Fin.cons a (Fin.cons (a ^^ p) x) : Word 6) i)) = _
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ]
  rw [←add_assoc,pairBit]

theorem same_deleted_parity {m : ℕ} (hm : 3 ≤ m) (h : Signature ℂ 6)
    (deck : OrderedRootDeck m h) (e : Equiv.Perm (Fin 6))
    (w v : Word 6) (hw : h w ≠ 0) (hv : h v ≠ 0)
    (same : (w (e 0) ^^ w (e 1)) = (v (e 0) ^^ v (e 1))) : parity w = parity v := by
  let p := w (e 0) ^^ w (e 1)
  have hx : sliceSix h e p (w (e 0)) (residualSix e w) ≠ 0 := by
    simpa only [sliceSix,p,fillSix_reconstruct] using hw
  have hy : sliceSix h e p (v (e 0)) (residualSix e v) ≠ 0 := by
    rw [show p = (v (e 0) ^^ v (e 1)) from same]
    simpa only [sliceSix,fillSix_reconstruct] using hv
  have residual := endpoint_supported_parity hm h deck e p _ _ _ _ hx hy
  rw [←fillSix_reconstruct e w,←fillSix_reconstruct e v,parity_fillSix,parity_fillSix,same,residual]

private theorem three_pair_disagreements : ∀ a b c A B C : Bool,
    (a ^^ b) ≠ (A ^^ B) → (a ^^ c) ≠ (A ^^ C) →
      (b ^^ c) ≠ (B ^^ C) → False := by decide

/-- Actual ordered monomial-product card closure forces global tensor parity.
This is a conclusion from the root deck, including the m=3/zero-pencil cases. -/
theorem supported_words_same_parity {m : ℕ} (hm : 3 ≤ m) (h : Signature ℂ 6)
    (deck : OrderedRootDeck m h) (w v : Word 6) (hw : h w ≠ 0) (hv : h v ≠ 0) :
    parity w = parity v := by
  by_contra different
  have pairs (e : Equiv.Perm (Fin 6)) :
      (w (e 0) ^^ w (e 1)) ≠ (v (e 0) ^^ v (e 1)) := by
    intro he
    exact different (same_deleted_parity hm h deck e w v hw hv he)
  apply three_pair_disagreements (w 0) (w 1) (w 2) (v 0) (v 1) (v 2)
  · exact pairs (Equiv.refl _)
  · simpa [Equiv.swap_apply_def] using pairs (Equiv.swap (1 : Fin 6) 2)
  · simpa [Equiv.swap_apply_def] using pairs ((Equiv.swap (0 : Fin 6) 1).trans (Equiv.swap 0 2))

theorem exists_global_parity {m : ℕ} (hm : 3 ≤ m) (h : Signature ℂ 6)
    (nonzero : h ≠ 0) (deck : OrderedRootDeck m h) :
    ∃ p : ZMod 2, ∀ w : Word 6, parity w ≠ p → h w = 0 := by
  have witness : ∃ w, h w ≠ 0 := by
    by_contra none
    push_neg at none
    exact nonzero (funext none)
  obtain ⟨w,hw⟩ := witness
  refine ⟨parity w,?_⟩
  intro v different
  by_contra hv
  exact different (supported_words_same_parity hm h deck v w hv hw)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
