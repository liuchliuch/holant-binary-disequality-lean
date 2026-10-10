import Holant.ReedMuller.SignedRadon.Basic
import Holant.ReedMuller.CharacterFlat.Converse

/-! Existence of the actual graph network, from the proved retained-resource
converse. Its scalar and port direction are retained in the witness. -/
namespace Holant.ReedMuller.SignedRadon
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.CharacterFlat
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def graphCode (A : OrthogonalMap n) : BinaryCode (n+n) where
  carrier := {x | rightVector x=A (leftVector x)}
  zero_mem' := A.map_zero.symm
  add_mem' := by
    intro x y hx hy
    change rightVector x+rightVector y=A (leftVector x+leftVector y)
    rw [A.map_add,hx,hy]
  smul_mem' := by
    intro c x hx
    change c • rightVector x=A (c • leftVector x)
    rw [A.map_smul,hx]

@[simp] theorem mem_graphCode (A : OrthogonalMap n) (x : BinaryVector (n+n)) :
    x∈graphCode A ↔ rightVector x=A (leftVector x) := Iff.rfl

theorem graphCode_selfDual (A : OrthogonalMap n) : SelfDual (graphCode A) := by
  intro x
  constructor
  · intro hx y hy
    rw [dot_parts,hx,hy,A.isometry,add_self_zero]
  · intro h
    apply dot_ext
    intro z
    have hz : joinVector (A.symm z) z∈graphCode A := by simp
    have hh := h _ hz
    rw [dot_parts,left_join,right_join,←A.adjoint] at hh
    exact ((FlatNetwork.add_eq_zero_iff _ _).mp hh).symm

def graphSignature (A : OrthogonalMap n) : Signature ℂ (n+n) :=
  fun x => if rightVector (vectorWord x)=A (leftVector (vectorWord x)) then 1 else 0

theorem graphSignature_flat (A : OrthogonalMap n) : NonzeroFlat (graphSignature A) := by
  refine ⟨1,0,graphCode A,0,graphCode_selfDual A,?_⟩
  funext x
  simp [graphSignature,signature,value]

/-- A fixed, actually constructed native graph with the functional direction
`output=A(input)`, the original input/output block order and nonzero scalar. -/
structure ActualGraph (κ : ZMod 2 → ZMod 2 → ℂ) (A : OrthogonalMap n) where
  network : Network ℂ (n+n)
  scalar : ℂ
  scalar_ne : scalar≠0
  uses : ∀ v,(⟨network.shape.arity v,network.vertex v⟩ : AnySignature ℂ)∈retainedFamily κ
  native : ∀ e,network.edge e=Signature.disequality
  denote : network.denote=scalar • graphSignature A

theorem exists_actualGraph (κ : ZMod 2 → ZMod 2 → ℂ) (hκ : ∀ d l,κ d l≠0)
    (A : OrthogonalMap n) : Nonempty (ActualGraph κ A) := by
  have hh : n+n=2*n := by omega
  let e : Fin (n+n) ≃ Fin (2*n) := finCongr hh
  obtain ⟨N,c,hc,hv,he,hd,_,_,_⟩ := source_character_network_converse κ hκ n
    (Tensor.reindex e (graphSignature A)) ((graphSignature_flat A).reindex e _)
  refine ⟨⟨GenerationNetwork.reindex N e.symm,c,hc,hv,he,?_⟩⟩
  rw [GenerationNetwork.denote_reindex,hd]
  funext x
  simp [Tensor.reindex]

end
end Holant.ReedMuller.SignedRadon
