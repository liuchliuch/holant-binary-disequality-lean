import Holant.ReedMuller.Steiner.Configuration

namespace Holant.ReedMuller.Steiner
open Holant.ReedMuller.LowArity Holant.ReedMuller.CoefficientAtlas
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
variable {n : ℕ}

def embed (e : Fin 8 ↪ Fin n) : BinaryVector 8 →ₗ[ZMod 2] BinaryVector n where
  toFun := fun x i => ∑ k : Fin 8,if e k=i then x k else 0
  map_add' := by
    intro x y
    funext i
    change (∑ k : Fin 8,if e k=i then x k+y k else 0)=
      (∑ k : Fin 8,if e k=i then x k else 0)+(∑ k : Fin 8,if e k=i then y k else 0)
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : e k=i <;> simp [h]
  map_smul' := by
    intro c x
    funext i
    change (∑ k : Fin 8,if e k=i then c*x k else 0)=c*(∑ k : Fin 8,if e k=i then x k else 0)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : e k=i <;> simp [h]

@[simp] theorem embed_apply (e : Fin 8 ↪ Fin n) (x : BinaryVector 8) (k : Fin 8) :
    embed e x (e k)=x k := by
  change (∑ j : Fin 8,if e j=e k then x j else 0)=x k
  simp [e.injective.eq_iff]

theorem embed_outside (e : Fin 8 ↪ Fin n) (x : BinaryVector 8) (i : Fin n)
    (hi : ∀ k,e k≠i) : embed e x i=0 := by
  change (∑ k : Fin 8,if e k=i then x k else 0)=0
  simp [hi]

theorem embed_indicator (e : Fin 8 ↪ Fin n) (S : Finset (Fin 8)) :
    embed e (indicator S)=indicator (S.image e) := by
  funext i
  by_cases hi : ∃ k,e k=i
  · obtain ⟨k,rfl⟩ := hi
    rw [embed_apply]
    simp [indicator,e.injective.eq_iff]
  · have hn : ∀ k,e k≠i := by simpa using hi
    rw [embed_outside e _ i hn]
    simp [indicator,Finset.mem_image,hn]

def prototypeBlocks : Fin 4 → Finset (Fin 8) :=
  ![{0,1,2,3},{0,1,4,5},{0,2,4,6},{0,3,4,7}]

def pointPermutation : Equiv.Perm (Fin 8) where
  toFun := ![7,5,6,4,3,1,2,0]
  invFun := ![7,5,6,4,3,1,2,0]
  left_inv := by decide
  right_inv := by decide

def prototype (a : Param) : BinaryVector 8 := fun k => evaluate a (pointPermutation k)

def prototypeCoefficient (a : Param) : Fin 4 → ZMod 2 := ![a 3,a 1+a 0,a 2+a 0,a 0]

theorem prototype_expansion : ∀ a : Param,
    prototype a=∑ j : Fin 4,prototypeCoefficient a j • indicator (prototypeBlocks j) := by decide

theorem prototype_orthogonal_complete : ∀ x : BinaryVector 8,
    (∀ a : Param,dot x (prototype a)=0) → ∃ a : Param,prototype a=x := by decide

theorem prototype_min_weight : ∀ a : Param,prototype a≠0 → 4≤(support (prototype a)).card := by decide

theorem Configuration.basis_mem {D : BinaryCode n} (C : Configuration D) (j : Fin 4) :
    embed C.points (indicator (prototypeBlocks j))∈D := by
  rw [embed_indicator]
  fin_cases j
  · simpa [prototypeBlocks] using C.block0.2
  · simpa [prototypeBlocks] using C.block1.2
  · simpa [prototypeBlocks] using C.block2.2
  · simpa [prototypeBlocks] using C.block3.2

theorem Configuration.prototype_mem {D : BinaryCode n} (C : Configuration D) (a : Param) :
    embed C.points (prototype a)∈D := by
  rw [prototype_expansion,map_sum]
  apply D.sum_mem
  intro j _
  rw [map_smul]
  exact D.smul_mem _ (C.basis_mem j)

theorem dot_embed (e : Fin 8 ↪ Fin n) (w : BinaryVector n) (x : BinaryVector 8) :
    dot w (embed e x)=dot (fun k => w (e k)) x := by
  change (∑ i : Fin n,w i*(∑ k : Fin 8,if e k=i then x k else 0))=
    ∑ k : Fin 8,w (e k)*x k
  simp_rw [Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  simp

/-- Orthogonality to the four real blocks forces every restricted codeword
into the actual eight-coordinate RM code. -/
theorem Configuration.restriction {D : BinaryCode n} (C : Configuration D) (hD : SelfDual D)
    (w : BinaryVector n) (hw : w∈D) :
    ∃ a : Param,prototype a=fun k => w (C.points k) := by
  apply prototype_orthogonal_complete
  intro a
  rw [←dot_embed]
  exact (hD w).mp hw _ (C.prototype_mem a)

end
end Holant.ReedMuller.Steiner
