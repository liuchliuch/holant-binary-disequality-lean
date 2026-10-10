import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSystematicSupport
import Holant.Tractable.SymmetricBinaryPullback.LocalAffine

/-! Checked ordered-port permutations for the actual LocalAffine descent.
Physical port relabelling transports every supported local twist exactly;
logical information-set relabelling is a separate support-chart operation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalPermutation
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Tractable.SymmetricBinaryPullback
open OrdinaryNegativeAffineSystematicSupport
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n r : ℕ}

def word (e : Equiv.Perm (Fin n)) (x : Word n) : Word n := fun i=>x (e i)

theorem word_affine (e : Equiv.Perm (Fin n)) : TwoTranslate.IsAffineMap (word e) := coordinates_isAffineMap e

theorem twist (e : Equiv.Perm (Fin n)) (f : Signature AlgebraicComplex n) (a : Word n) :
    localTwist a (Tensor.reindex e f)=Tensor.reindex e (localTwist (word e a) f) := by
  funext x
  simp only [localTwist_apply,Tensor.reindex_apply,word]
  rw [Equiv.prod_comp e (fun j=>if a j && x j then zetaEight else 1)]

theorem local_reindex (e : Equiv.Perm (Fin n)) (f : Signature AlgebraicComplex n) (hl : LocalAffine f) :
    LocalAffine (Tensor.reindex e f) := by
  intro a supported
  rw [twist]
  exact (hl (word e a) supported).precompose (word e) (word_affine e)

theorem reindex_cancel (e : Equiv.Perm (Fin n)) (f : Signature AlgebraicComplex n) :
    Tensor.reindex e.symm (Tensor.reindex e f)=f := by
  funext x
  simp only [Tensor.reindex_apply,Equiv.symm_apply_apply]

theorem local_iff (e : Equiv.Perm (Fin n)) (f : Signature AlgebraicComplex n) :
    LocalAffine (Tensor.reindex e f) ↔ LocalAffine f := by
  constructor
  · intro hl
    have h:=local_reindex e.symm (Tensor.reindex e f) hl
    rwa [reindex_cancel] at h
  · exact local_reindex e f

variable {f : Signature AlgebraicComplex n} (D : SystematicSupport f r)

def physical (e : Equiv.Perm (Fin n)) : SystematicSupport (Tensor.reindex e f) r where
  ports i := e (D.ports i)
  injective := e.injective.comp D.injective
  encode z := word e.symm (D.encode z)
  affine := affine_map_comp (word e.symm) D.encode (word_affine e.symm) D.affine
  free z i := by simp [word,D.free]
  supported z := by
    simpa only [Tensor.reindex_apply,word,Equiv.symm_apply_apply] using D.supported z
  covers x hx := by
    have he:=D.covers (word e x) hx
    dsimp only [word] at he
    funext i
    change D.encode (fun j=>x (e (D.ports j))) (e.symm i)=x i
    simpa only [word,Equiv.apply_symm_apply] using congrFun he (e.symm i)

def logical (e : Equiv.Perm (Fin r)) : SystematicSupport f r where
  ports i := D.ports (e i)
  injective := D.injective.comp e.injective
  encode z := D.encode (word e.symm z)
  affine := affine_map_comp D.encode (word e.symm) D.affine (word_affine e.symm)
  free z i := by simp [D.free,word]
  supported z := D.supported _
  covers x hx := by
    have he : word e.symm (fun j=>x (D.ports (e j)))=(fun j=>x (D.ports j)) := by
      funext j
      simp [word]
    rw [he]
    exact D.covers x hx

theorem pair_permutation {α : Type*} [DecidableEq α] (p q i j : α) (pq : p≠q) (ij : i≠j) :
    ∃e : Equiv.Perm α,e p=i ∧ e q=j := by
  let base := Equiv.swap p i
  have cancel (x : α) : base (base x)=x := by simp [base]
  have first : base p=i := by simp [base]
  have away : base j≠p := by
    intro he
    have hh:=congrArg base he
    rw [cancel,first] at hh
    exact ij hh.symm
  refine ⟨(Equiv.swap q (base j)).trans base,?_,?_⟩
  · change base ((Equiv.swap q (base j)) p)=i
    rw [Equiv.swap_apply_of_ne_of_ne pq (Ne.symm away),first]
  · change base ((Equiv.swap q (base j)) q)=j
    rw [Equiv.swap_apply_left,cancel]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalPermutation
end
